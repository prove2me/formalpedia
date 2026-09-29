-- Prove2me | solution 1 for Rudin.ch06_stieltjes_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T20:01:45.900285+00:00
-- url     : https://prove2.me/submissions/9c233307-b2c7-42f6-835e-04c5554aa96c

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace IBPaux

open Rudin

/-- The division points of a partition increase along the index. -/
lemma partition_le {a b : ℝ} (P : Partition a b) :
    ∀ j, j ≤ P.n → ∀ i, i ≤ j → P.x i ≤ P.x j := by
  intro j
  induction j with
  | zero => intro _ i hi; simp [Nat.le_zero.mp hi]
  | succ k ih =>
      intro hk i hi
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · have hik : i ≤ k := Nat.lt_succ_iff.mp h
        have hkn : k ≤ P.n := le_trans (Nat.le_succ k) hk
        exact le_trans (ih hkn i hik) (P.mono k (lt_of_lt_of_le (Nat.lt_succ_self k) hk))
      · have : i = k + 1 := le_antisymm hi h
        simp [this]

/-- Every division point lies in `[a, b]`. -/
lemma partition_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) :
    P.x i ∈ Set.Icc a b := by
  constructor
  · have := partition_le P i hi 0 (Nat.zero_le i)
    rwa [P.first] at this
  · have := partition_le P P.n le_rfl i hi
    rwa [P.last] at this

/-- On the `i`-th subinterval, the supremum of a monotone `f` is its value at the right endpoint. -/
lemma sSup_eq_right {a b : ℝ} (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc a b))
    (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) = f (P.x (i + 1)) := by
  have hle : P.x i ≤ P.x (i + 1) := P.mono i hi
  have hmemi : P.x i ∈ Set.Icc a b := partition_mem P (le_of_lt hi)
  have hmemj : P.x (i + 1) ∈ Set.Icc a b := partition_mem P hi
  refine IsGreatest.csSup_eq ⟨⟨P.x (i + 1), ⟨hle, le_rfl⟩, rfl⟩, ?_⟩
  rintro y ⟨t, ⟨ht1, ht2⟩, rfl⟩
  have htmem : t ∈ Set.Icc a b := ⟨le_trans hmemi.1 ht1, le_trans ht2 hmemj.2⟩
  exact hf htmem hmemj ht2

/-- On the `i`-th subinterval, the infimum of a monotone `f` is its value at the left endpoint. -/
lemma sInf_eq_left {a b : ℝ} (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc a b))
    (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) = f (P.x i) := by
  have hle : P.x i ≤ P.x (i + 1) := P.mono i hi
  have hmemi : P.x i ∈ Set.Icc a b := partition_mem P (le_of_lt hi)
  have hmemj : P.x (i + 1) ∈ Set.Icc a b := partition_mem P hi
  refine IsLeast.csInf_eq ⟨⟨P.x i, ⟨le_rfl, hle⟩, rfl⟩, ?_⟩
  rintro y ⟨t, ⟨ht1, ht2⟩, rfl⟩
  have htmem : t ∈ Set.Icc a b := ⟨le_trans hmemi.1 ht1, le_trans ht2 hmemj.2⟩
  exact hf hmemi htmem ht1

/-- The upper sum of a monotone integrand, computed. -/
lemma upperSum_eq {a b : ℝ} (f α : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc a b))
    (P : Partition a b) :
    upperSum f α P =
      ∑ i ∈ Finset.range P.n, f (P.x (i + 1)) * (α (P.x (i + 1)) - α (P.x i)) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [sSup_eq_right f hf P (Finset.mem_range.mp hi)]

/-- The lower sum of a monotone integrand, computed. -/
lemma lowerSum_eq {a b : ℝ} (f α : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc a b))
    (P : Partition a b) :
    lowerSum f α P =
      ∑ i ∈ Finset.range P.n, f (P.x i) * (α (P.x (i + 1)) - α (P.x i)) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [sInf_eq_left f hf P (Finset.mem_range.mp hi)]

/-- Abel summation, first form: `U(P, f, α) + L(P, α, f) = f(b)α(b) - f(a)α(a)`. -/
lemma abel_upper_lower {a b : ℝ} (f α : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc a b))
    (hα : MonotoneOn α (Set.Icc a b)) (P : Partition a b) :
    upperSum f α P + lowerSum α f P = f b * α b - f a * α a := by
  rw [upperSum_eq f α hf P, lowerSum_eq α f hα P, ← Finset.sum_add_distrib]
  have key : ∀ i ∈ Finset.range P.n,
      f (P.x (i + 1)) * (α (P.x (i + 1)) - α (P.x i)) +
        α (P.x i) * (f (P.x (i + 1)) - f (P.x i)) =
      (fun j => f (P.x j) * α (P.x j)) (i + 1) - (fun j => f (P.x j) * α (P.x j)) i := by
    intro i _; simp only; ring
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub (fun j => f (P.x j) * α (P.x j)) P.n,
    P.first, P.last]

/-- Abel summation, second form: `L(P, f, α) + U(P, α, f) = f(b)α(b) - f(a)α(a)`. -/
lemma abel_lower_upper {a b : ℝ} (f α : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc a b))
    (hα : MonotoneOn α (Set.Icc a b)) (P : Partition a b) :
    lowerSum f α P + upperSum α f P = f b * α b - f a * α a := by
  rw [lowerSum_eq f α hf P, upperSum_eq α f hα P, ← Finset.sum_add_distrib]
  have key : ∀ i ∈ Finset.range P.n,
      f (P.x i) * (α (P.x (i + 1)) - α (P.x i)) +
        α (P.x (i + 1)) * (f (P.x (i + 1)) - f (P.x i)) =
      (fun j => f (P.x j) * α (P.x j)) (i + 1) - (fun j => f (P.x j) * α (P.x j)) i := by
    intro i _; simp only; ring
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub (fun j => f (P.x j) * α (P.x j)) P.n,
    P.first, P.last]

/-- The increments of `α` over a partition telescope. -/
lemma sum_delta {a b : ℝ} (α : ℝ → ℝ) (P : Partition a b) :
    ∑ i ∈ Finset.range P.n, (α (P.x (i + 1)) - α (P.x i)) = α b - α a := by
  rw [Finset.sum_range_sub (fun j => α (P.x j)) P.n, P.first, P.last]

/-- Every upper sum of a monotone integrand is at least `f(a)(α(b) - α(a))`. -/
lemma upperSum_lower_bound {a b : ℝ} (f α : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc a b))
    (hα : MonotoneOn α (Set.Icc a b)) (P : Partition a b) :
    f a * (α b - α a) ≤ upperSum f α P := by
  rw [upperSum_eq f α hf P]
  have h1 : f a * (α b - α a) = ∑ i ∈ Finset.range P.n, f a * (α (P.x (i + 1)) - α (P.x i)) := by
    rw [← Finset.mul_sum, sum_delta α P]
  rw [h1]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hik : i < P.n := Finset.mem_range.mp hi
  have hmemi : P.x i ∈ Set.Icc a b := partition_mem P (le_of_lt hik)
  have hmemj : P.x (i + 1) ∈ Set.Icc a b := partition_mem P hik
  have hΔ : 0 ≤ α (P.x (i + 1)) - α (P.x i) :=
    sub_nonneg.mpr (hα hmemi hmemj (P.mono i hik))
  have hfa : f a ≤ f (P.x (i + 1)) := hf ⟨le_rfl, le_trans hmemi.1 hmemi.2⟩ hmemj hmemj.1
  exact mul_le_mul_of_nonneg_right hfa hΔ

/-- Every lower sum of a monotone integrand is at most `f(b)(α(b) - α(a))`. -/
lemma lowerSum_upper_bound {a b : ℝ} (f α : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc a b))
    (hα : MonotoneOn α (Set.Icc a b)) (P : Partition a b) :
    lowerSum f α P ≤ f b * (α b - α a) := by
  rw [lowerSum_eq f α hf P]
  have h1 : f b * (α b - α a) = ∑ i ∈ Finset.range P.n, f b * (α (P.x (i + 1)) - α (P.x i)) := by
    rw [← Finset.mul_sum, sum_delta α P]
  rw [h1]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hik : i < P.n := Finset.mem_range.mp hi
  have hmemi : P.x i ∈ Set.Icc a b := partition_mem P (le_of_lt hik)
  have hmemj : P.x (i + 1) ∈ Set.Icc a b := partition_mem P hik
  have hΔ : 0 ≤ α (P.x (i + 1)) - α (P.x i) :=
    sub_nonneg.mpr (hα hmemi hmemj (P.mono i hik))
  have hfb : f (P.x i) ≤ f b := hf hmemi ⟨le_trans hmemi.1 hmemi.2, le_rfl⟩ hmemi.2
  exact mul_le_mul_of_nonneg_right hfb hΔ

/-- The trivial one-subinterval partition. -/
def triv {a b : ℝ} (hab : a ≤ b) : Partition a b where
  n := 1
  x := fun i => if i = 0 then a else b
  first := by simp
  last := by simp
  mono := by
    intro i hi
    interval_cases i
    simpa using hab

/-- If `sInf S + sSup T = C` whenever `T` is the pointwise reflection of `S` in `C/2`. -/
lemma sInf_add_sSup {C : ℝ} {S T : Set ℝ} (hS : S.Nonempty)
    (hbdd : BddBelow S) (hmap : ∀ u, u ∈ S ↔ C - u ∈ T) (hT : ∀ v ∈ T, C - v ∈ S) :
    sInf S + sSup T = C := by
  have hTne : T.Nonempty := by
    obtain ⟨u, hu⟩ := hS
    exact ⟨C - u, (hmap u).mp hu⟩
  have hTbdd : BddAbove T := by
    obtain ⟨c, hc⟩ := hbdd
    refine ⟨C - c, ?_⟩
    intro v hv
    have := hc (hT v hv)
    linarith
  have h1 : sSup T ≤ C - sInf S := by
    refine csSup_le hTne ?_
    intro v hv
    have h := csInf_le hbdd (hT v hv)
    linarith
  have h2 : C - sSup T ≤ sInf S := by
    refine le_csInf hS ?_
    intro u hu
    have h := le_csSup hTbdd ((hmap u).mp hu)
    linarith
  linarith

end IBPaux

open Rudin IBPaux in
/-- Rudin, Theorem 6.22 in Stieltjes form: for two monotonically increasing functions the
integration-by-parts identity holds at the level of upper and lower integrals. -/
theorem solution (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Icc a b)) (hα : MonotoneOn α (Set.Icc a b)) :
    upperIntegral a b f α + lowerIntegral a b α f = f b * α b - f a * α a ∧
      lowerIntegral a b f α + upperIntegral a b α f = f b * α b - f a * α a ∧
      (RSIntegrable a b f α ↔ RSIntegrable a b α f) ∧
      (RSIntegrable a b f α →
        RSIntegral a b f α + RSIntegral a b α f = f b * α b - f a * α a) := by
  set C : ℝ := f b * α b - f a * α a with hC
  -- first identity
  have key1 : upperIntegral a b f α + lowerIntegral a b α f = C := by
    refine sInf_add_sSup (C := C) ⟨upperSum f α (triv hab), ⟨triv hab, rfl⟩⟩
      ⟨f a * (α b - α a), ?_⟩ ?_ ?_
    · rintro u ⟨P, rfl⟩
      exact upperSum_lower_bound f α hf hα P
    · intro u
      constructor
      · rintro ⟨P, rfl⟩
        refine ⟨P, ?_⟩
        have := abel_upper_lower f α hf hα P
        linarith
      · rintro ⟨P, hP⟩
        refine ⟨P, ?_⟩
        have := abel_upper_lower f α hf hα P
        linarith
    · rintro v ⟨P, rfl⟩
      refine ⟨P, ?_⟩
      have := abel_upper_lower f α hf hα P
      linarith
  have key2 : upperIntegral a b α f + lowerIntegral a b f α = C := by
    refine sInf_add_sSup (C := C) ⟨upperSum α f (triv hab), ⟨triv hab, rfl⟩⟩
      ⟨α a * (f b - f a), ?_⟩ ?_ ?_
    · rintro u ⟨P, rfl⟩
      exact upperSum_lower_bound α f hα hf P
    · intro u
      constructor
      · rintro ⟨P, rfl⟩
        refine ⟨P, ?_⟩
        have := abel_lower_upper f α hf hα P
        linarith
      · rintro ⟨P, hP⟩
        refine ⟨P, ?_⟩
        have := abel_lower_upper f α hf hα P
        linarith
    · rintro v ⟨P, rfl⟩
      refine ⟨P, ?_⟩
      have := abel_lower_upper f α hf hα P
      linarith
  refine ⟨key1, by linarith [key2], ?_, ?_⟩
  · constructor
    · intro h
      unfold RSIntegrable at h ⊢
      linarith [key1, key2]
    · intro h
      unfold RSIntegrable at h ⊢
      linarith [key1, key2]
  · intro h
    have h2 : upperIntegral a b α f = lowerIntegral a b α f := by
      unfold RSIntegrable at h
      linarith [key1, key2]
    unfold RSIntegral
    linarith [key1, h2]

