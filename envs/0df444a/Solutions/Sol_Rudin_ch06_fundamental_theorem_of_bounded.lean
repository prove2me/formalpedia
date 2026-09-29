-- Prove2me | solution 1 for Rudin.ch06_fundamental_theorem_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T13:14:12.657181+00:00
-- url     : https://prove2.me/submissions/d35a1b66-5c7c-4e15-a5dd-a183b11e42f5

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace RudinFTC

open Rudin

/-- The division points of a partition increase. -/
lemma px_mono {a b : ℝ} (P : Partition a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.n) :
    P.x i ≤ P.x j := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    simp [this]
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with h | h
    · have him : i ≤ m := Nat.lt_succ_iff.mp h
      exact le_trans (ih him (by omega)) (P.mono m (by omega))
    · have : i = m + 1 := le_antisymm hij h
      simp [this]

lemma px_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  constructor
  · have := px_mono P (Nat.zero_le i) hi
    rwa [P.first] at this
  · have := px_mono P hi (le_refl P.n)
    rwa [P.last] at this

/-- The trivial partition `{a, b}`. -/
def trivialPartition {a b : ℝ} (hab : a ≤ b) : Partition a b where
  n := 1
  x := fun i => if i = 0 then a else b
  first := by norm_num
  last := by norm_num
  mono := by
    intro i hi
    have : i = 0 := by omega
    subst this
    norm_num
    exact hab

/-- On a subinterval `[u, v]` of `[a, b]`, the increment of `F` is squeezed between the
infimum and the supremum of `f = F'` times the length. -/
lemma increment_bounds {a b u v M : ℝ} {f F : ℝ → ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    sInf (f '' Set.Icc u v) * (v - u) ≤ F v - F u ∧
      F v - F u ≤ sSup (f '' Set.Icc u v) * (v - u) := by
  have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hau hvb
  rcases eq_or_lt_of_le huv with heq | hlt
  · subst heq
    simp
  · have hcont : ContinuousOn F (Set.Icc u v) := by
      intro x hx
      exact ((hF x (hsub hx)).continuousAt).continuousWithinAt
    obtain ⟨t, ht, hslope⟩ :=
      exists_hasDerivAt_eq_slope F f hlt hcont (fun x hx => hF x (hsub (Set.Ioo_subset_Icc_self hx)))
    have htmem : t ∈ Set.Icc u v := Set.Ioo_subset_Icc_self ht
    have hFt : F v - F u = f t * (v - u) := by
      field_simp at hslope
      linarith [hslope]
    have hmem : f t ∈ f '' Set.Icc u v := ⟨t, htmem, rfl⟩
    have hbddA : BddAbove (f '' Set.Icc u v) :=
      ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hM y (hsub hy))).2⟩
    have hbddB : BddBelow (f '' Set.Icc u v) :=
      ⟨-M, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hM y (hsub hy))).1⟩
    have hlen : (0:ℝ) ≤ v - u := by linarith
    constructor
    · rw [hFt]
      exact mul_le_mul_of_nonneg_right (csInf_le hbddB hmem) hlen
    · rw [hFt]
      exact mul_le_mul_of_nonneg_right (le_csSup hbddA hmem) hlen

/-- Every lower sum is at most `F b - F a`, and `F b - F a` is at most every upper sum. -/
lemma sums_squeeze {a b M : ℝ} {f F : ℝ → ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (P : Partition a b) :
    lowerSum f id P ≤ F b - F a ∧ F b - F a ≤ upperSum f id P := by
  have htel : ∑ i ∈ Finset.range P.n, (F (P.x (i + 1)) - F (P.x i)) = F b - F a := by
    rw [Finset.sum_range_sub (fun i => F (P.x i)) P.n, P.first, P.last]
  have key : ∀ i ∈ Finset.range P.n,
      sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) * (id (P.x (i + 1)) - id (P.x i))
          ≤ F (P.x (i + 1)) - F (P.x i) ∧
      F (P.x (i + 1)) - F (P.x i)
          ≤ sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) * (id (P.x (i + 1)) - id (P.x i)) := by
    intro i hi
    have hi' : i < P.n := Finset.mem_range.mp hi
    have h1 : P.x i ∈ Set.Icc a b := px_mem P (le_of_lt hi')
    have h2 : P.x (i + 1) ∈ Set.Icc a b := px_mem P hi'
    simpa using increment_bounds h1.1 (P.mono i hi') h2.2 hF hM
  constructor
  · calc lowerSum f id P
        ≤ ∑ i ∈ Finset.range P.n, (F (P.x (i + 1)) - F (P.x i)) :=
          Finset.sum_le_sum (fun i hi => (key i hi).1)
      _ = F b - F a := htel
  · calc F b - F a = ∑ i ∈ Finset.range P.n, (F (P.x (i + 1)) - F (P.x i)) := htel.symm
      _ ≤ upperSum f id P := Finset.sum_le_sum (fun i hi => (key i hi).2)

end RudinFTC

open Rudin RudinFTC in
/-- Rudin, Theorem 6.21 (the fundamental theorem of calculus), with the boundedness hypothesis
of Chapter 6. -/
theorem solution (a b : ℝ) (hab : a ≤ b) (f F : ℝ → ℝ)
    (hf : RiemannIntegrable a b f)
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) :
    RiemannIntegral a b f = F b - F a := by
  obtain ⟨M, hM⟩ := hfb
  have hlow : lowerIntegral a b f id ≤ F b - F a := by
    refine csSup_le ⟨lowerSum f id (trivialPartition hab), ⟨_, rfl⟩⟩ ?_
    rintro y ⟨P, rfl⟩
    exact (sums_squeeze hab hF hM P).1
  have hupp : F b - F a ≤ upperIntegral a b f id := by
    refine le_csInf ⟨upperSum f id (trivialPartition hab), ⟨_, rfl⟩⟩ ?_
    rintro y ⟨P, rfl⟩
    exact (sums_squeeze hab hF hM P).2
  have hEq : upperIntegral a b f id = lowerIntegral a b f id := hf
  have : RiemannIntegral a b f = upperIntegral a b f id := rfl
  rw [this]
  have h1 : upperIntegral a b f id ≤ F b - F a := by rw [hEq]; exact hlow
  linarith
