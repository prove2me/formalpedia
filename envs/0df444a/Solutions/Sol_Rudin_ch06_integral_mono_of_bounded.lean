-- Prove2me | solution 1 for Rudin.ch06_integral_mono_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T05:34:09.209095+00:00
-- url     : https://prove2.me/submissions/29b5c85d-c7ed-427b-9b89-25c816ef2ddd

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace RudinFix6

open Filter Topology Rudin

variable {a b : ℝ}

/-- The division points of a partition increase. -/
theorem x_mono (P : Partition a b) : ∀ i j, i ≤ j → j ≤ P.n → P.x i ≤ P.x j := by
  intro i j hij hj
  induction j with
  | zero => simp_all
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (P.mono j (by omega))
    · have : i = j + 1 := by omega
      subst this
      exact le_rfl

/-- The division points of a partition lie in `[a, b]`. -/
theorem x_mem (P : Partition a b) (i : ℕ) (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  · have h := x_mono P 0 i (Nat.zero_le i) hi
    rwa [P.first] at h
  · have h := x_mono P i P.n hi le_rfl
    rwa [P.last] at h

/-- Each subinterval of a partition sits inside `[a, b]`. -/
theorem sub_Icc (P : Partition a b) (i : ℕ) (hi : i < P.n) :
    Set.Icc (P.x i) (P.x (i + 1)) ⊆ Set.Icc a b := by
  intro t ht
  exact ⟨le_trans (x_mem P i hi.le).1 ht.1, le_trans ht.2 (x_mem P (i + 1) hi).2⟩

/-- On each subinterval the image of a bounded `f` is nonempty and bounded. -/
theorem image_nonempty (P : Partition a b) (f : ℝ → ℝ) (i : ℕ) (hi : i < P.n) :
    (f '' Set.Icc (P.x i) (P.x (i + 1))).Nonempty :=
  ⟨f (P.x i), ⟨P.x i, ⟨le_rfl, P.mono i hi⟩, rfl⟩⟩

theorem image_bddAbove {M : ℝ} (P : Partition a b) (f : ℝ → ℝ)
    (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (i : ℕ) (hi : i < P.n) :
    BddAbove (f '' Set.Icc (P.x i) (P.x (i + 1))) := by
  refine ⟨M, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  exact (abs_le.1 (hM t (sub_Icc P i hi ht))).2

/-- The supremum over a subinterval is bounded by the bound of `|f|`. -/
theorem sSup_abs_le {M : ℝ} (P : Partition a b) (f : ℝ → ℝ)
    (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (i : ℕ) (hi : i < P.n) :
    |sSup (f '' Set.Icc (P.x i) (P.x (i + 1)))| ≤ M := by
  have hne := image_nonempty P f i hi
  have hbdd := image_bddAbove P f hM i hi
  refine abs_le.2 ⟨?_, ?_⟩
  · have h1 : f (P.x i) ≤ sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) :=
      le_csSup hbdd ⟨P.x i, ⟨le_rfl, P.mono i hi⟩, rfl⟩
    have h2 : -M ≤ f (P.x i) := (abs_le.1 (hM _ (x_mem P i hi.le))).1
    linarith
  · refine csSup_le hne ?_
    rintro y ⟨t, ht, rfl⟩
    exact (abs_le.1 (hM t (sub_Icc P i hi ht))).2

/-- The increments of a monotone integrator are nonnegative and telescope. -/
theorem dalpha_nonneg (hab : a ≤ b) (α : ℝ → ℝ) (hα : MonotoneOn α (Set.Icc a b))
    (P : Partition a b) (i : ℕ) (hi : i < P.n) :
    0 ≤ α (P.x (i + 1)) - α (P.x i) := by
  have h := hα (x_mem P i hi.le) (x_mem P (i + 1) hi) (P.mono i hi)
  linarith

theorem dalpha_sum (α : ℝ → ℝ) (P : Partition a b) :
    ∑ i ∈ Finset.range P.n, (α (P.x (i + 1)) - α (P.x i)) = α b - α a := by
  rw [Finset.sum_range_sub (fun i => α (P.x i))]
  rw [P.first, P.last]


/-- The trivial partition `a = x₀ ≤ x₁ = b`. -/
def trivialPartition (hab : a ≤ b) : Partition a b where
  n := 1
  x := fun i => if i = 0 then a else b
  first := by simp
  last := by simp
  mono := by
    intro i hi
    interval_cases i
    simpa using hab

/-! ### Rudin 6.12(d): the integral is bounded by `M (α b - α a)` -/

theorem upperSum_abs_le {M : ℝ} (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (P : Partition a b) : |upperSum f α P| ≤ M * (α b - α a) := by
  rw [upperSum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h : ∀ i ∈ Finset.range P.n,
      |sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) * (α (P.x (i + 1)) - α (P.x i))|
        ≤ M * (α (P.x (i + 1)) - α (P.x i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [abs_mul, abs_of_nonneg (dalpha_nonneg hab α hα P i hi)]
    exact mul_le_mul_of_nonneg_right (sSup_abs_le P f hM i hi) (dalpha_nonneg hab α hα P i hi)
  refine le_trans (Finset.sum_le_sum h) ?_
  rw [← Finset.mul_sum, dalpha_sum]

theorem upperIntegral_abs_le {M : ℝ} (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    |upperIntegral a b f α| ≤ M * (α b - α a) := by
  have hne : {y : ℝ | ∃ P : Partition a b, y = upperSum f α P}.Nonempty :=
    ⟨_, ⟨trivialPartition hab, rfl⟩⟩
  have hbdd : BddBelow {y : ℝ | ∃ P : Partition a b, y = upperSum f α P} := by
    refine ⟨-(M * (α b - α a)), ?_⟩
    rintro y ⟨P, rfl⟩
    exact (abs_le.1 (upperSum_abs_le hab f α hα hM P)).1
  rw [upperIntegral, abs_le]
  constructor
  · refine le_csInf hne ?_
    rintro y ⟨P, rfl⟩
    exact (abs_le.1 (upperSum_abs_le hab f α hα hM P)).1
  · exact le_trans (csInf_le hbdd ⟨trivialPartition hab, rfl⟩)
      (abs_le.1 (upperSum_abs_le hab f α hα hM (trivialPartition hab))).2

theorem ch06_abs_integral_le (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (M : ℝ) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    |RSIntegral a b f α| ≤ M * (α b - α a) :=
  upperIntegral_abs_le hab f α hα hM

/-! ### Rudin 6.12(b): monotonicity in the integrand -/

theorem upperSum_mono {Mg : ℝ} (hab : a ≤ b) (f g α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (hMg : ∀ x ∈ Set.Icc a b, |g x| ≤ Mg)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) (P : Partition a b) :
    upperSum f α P ≤ upperSum g α P := by
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  refine mul_le_mul_of_nonneg_right ?_ (dalpha_nonneg hab α hα P i hi)
  refine csSup_le (image_nonempty P f i hi) ?_
  rintro y ⟨t, ht, rfl⟩
  exact le_trans (hfg t (sub_Icc P i hi ht))
    (le_csSup (image_bddAbove P g hMg i hi) ⟨t, ht, rfl⟩)

theorem ch06_integral_mono (a b : ℝ) (hab : a ≤ b) (f g α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    RSIntegral a b f α ≤ RSIntegral a b g α := by
  obtain ⟨Mf, hMf⟩ := hfb
  obtain ⟨Mg, hMg⟩ := hgb
  have hAbdd : BddBelow {y : ℝ | ∃ P : Partition a b, y = upperSum f α P} := by
    refine ⟨-(Mf * (α b - α a)), ?_⟩
    rintro y ⟨P, rfl⟩
    exact (abs_le.1 (upperSum_abs_le hab f α hα hMf P)).1
  have hBne : {y : ℝ | ∃ P : Partition a b, y = upperSum g α P}.Nonempty :=
    ⟨_, ⟨trivialPartition hab, rfl⟩⟩
  rw [RSIntegral, RSIntegral, upperIntegral, upperIntegral]
  refine le_csInf hBne ?_
  rintro y ⟨P, rfl⟩
  exact le_trans (csInf_le hAbdd ⟨P, rfl⟩) (upperSum_mono hab f g α hα hMg hfg P)

end RudinFix6

open Filter Topology Rudin in
theorem solution (a b : ℝ) (hab : a ≤ b) (f g α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    RSIntegral a b f α ≤ RSIntegral a b g α :=
  RudinFix6.ch06_integral_mono a b hab f g α hα hfb hgb hfg
