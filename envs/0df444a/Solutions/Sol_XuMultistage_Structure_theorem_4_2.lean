-- Prove2me | solution 1 for XuMultistage.Structure.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T10:09:33.280225+00:00
-- url     : https://prove2.me/submissions/d2455195-b155-4c21-a460-c7e6174eb8e3

import Definitions.Def_XuMultistage_Structure_Revenue
import Definitions.Def_XuMultistage_Structure_RevenueOrdered
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi

-- Component: P067Data
open scoped BigOperators
open XuMultistage.Structure

namespace S02Multistage

noncomputable section

variable {n₁ n₂ : ℕ}

def weight (M : Model n₁ n₂) (i : Fin (n₁ + 1)) (j : Fin (n₂ + 1)) : ℝ :=
  Real.exp (M.μ₁ i) * Real.exp (M.μ₂ j)

def mass (M : Model n₁ n₂) (X : PathMatrix n₁ n₂) : ℝ :=
  ∑ i, ∑ j, if X i j = true then weight M i j else 0

def total (M : Model n₁ n₂) (X : PathMatrix n₁ n₂) : ℝ :=
  ∑ i, ∑ j, if X i j = true then weight M i j * (M.p₁ i + M.p₂ j) else 0

def score (M : Model n₁ n₂) (R : ℝ) (i : Fin (n₁ + 1)) : ℝ :=
  (M.p₁ i - R) + ∑ j, if j = 0 then 0
    else Real.exp (M.μ₂ j) * max (M.p₁ i + M.p₂ j - R) 0

def threshold (M : Model n₁ n₂) (R : ℝ) : PathMatrix n₁ n₂ := by
  classical
  exact fun i j => decide ((i = 0 ∨ 0 ≤ score M R i) ∧
    (j = 0 ∨ 0 ≤ M.p₁ i + M.p₂ j - R))

end

end S02Multistage

-- Component: P067Collapse
set_option autoImplicit false

open scoped BigOperators
open XuMultistage.Structure

namespace S02Multistage

noncomputable section

variable {n₁ n₂ : ℕ}

theorem weight_pos (M : Model n₁ n₂) (i : Fin (n₁ + 1)) (j : Fin (n₂ + 1)) :
    0 < weight M i j :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

/-- The compulsory path (0,0) makes the total attraction positive. -/
theorem mass_pos (M : Model n₁ n₂) (X : PathMatrix n₁ n₂) (hX : Feasible X) :
    0 < mass M X := by
  classical
  unfold mass
  apply Finset.sum_pos'
  · intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact (weight_pos M i j).le
    · exact le_rfl
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro j hj
      split_ifs
      · exact (weight_pos M 0 j).le
      · exact le_rfl
    · exact ⟨0, Finset.mem_univ _, by rw [if_pos hX.1]; exact weight_pos M 0 0⟩

/-- Every row mass includes its normalized outside weight one. -/
theorem rowMass_pos (M : Model n₁ n₂) (X : PathMatrix n₁ n₂)
    (i : Fin (n₁ + 1)) : 0 < rowMass M X i := by
  have hnonneg : 0 ≤ ∑ j, rowAttraction M X i j := by
    apply Finset.sum_nonneg
    intro j hj
    unfold rowAttraction
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  unfold rowMass
  linarith

/-- For an active row, the outside term is exactly the offered path at zero. -/
theorem rowMass_eq_sum (M : Model n₁ n₂) (X : PathMatrix n₁ n₂)
    (i : Fin (n₁ + 1)) (hi : X i 0 = true) :
    rowMass M X i = ∑ j, if X i j = true then Real.exp (M.μ₂ j) else 0 := by
  classical
  calc
    rowMass M X i = (∑ j, rowAttraction M X i j) +
        ∑ j : Fin (n₂ + 1), if j = 0 then (1 : ℝ) else 0 := by
      simp [rowMass]
    _ = ∑ j, (rowAttraction M X i j + (if j = 0 then (1 : ℝ) else 0)) :=
      Finset.sum_add_distrib.symm
    _ = ∑ j, if X i j = true then Real.exp (M.μ₂ j) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        simp [rowAttraction, hi, M.μ₂_zero]
      · simp [rowAttraction, hj0]

/-- An active row's second-stage choice is its offered attraction divided by
the row mass, including its outside option. -/
theorem secondProbability_eq (M : Model n₁ n₂) (X : PathMatrix n₁ n₂)
    (i : Fin (n₁ + 1)) (hi : X i 0 = true) (j : Fin (n₂ + 1)) :
    secondProbability M X i j =
      (if X i j = true then Real.exp (M.μ₂ j) else 0) / rowMass M X i := by
  by_cases hj : j = 0
  · subst j
    simp [secondProbability, hi, M.μ₂_zero]
  · simp [secondProbability, hi, hj, FlagshipMEA.Monopoly.logitShare,
      rowAttraction, rowMass]

/-- At discount one the first-stage attraction equals the sum of path weights. -/
theorem firstWeight_one_eq (M : Model n₁ n₂) (X : PathMatrix n₁ n₂)
    (hX : Feasible X) (i : Fin (n₁ + 1)) :
    firstWeight M 1 X i = ∑ j, if X i j = true then weight M i j else 0 := by
  classical
  by_cases hi : X i 0 = true
  · rw [firstWeight, if_pos hi, Real.rpow_one, rowMass_eq_sum M X i hi,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hx : X i j = true <;> simp [weight, hx]
  · have hrow : ∀ j, X i j ≠ true := fun j hj => hi (hX.2 i j hj)
    simp [firstWeight, hi, hrow]

/-- Elementary row cancellation, kept separate from the probability definitions. -/
theorem weighted_row_identity {α : Type*} [Fintype α]
    (W A x : ℝ) (b p : α → ℝ) (hA : A = ∑ j, b j) (hA0 : A ≠ 0) :
    W * A * (x + ∑ j, (b j / A) * p j) =
      ∑ j, W * b j * (x + p j) := by
  have hsum : (∑ j, (b j / A) * p j) = (∑ j, b j * p j) / A := by
    simp only [div_mul_eq_mul_div, Finset.sum_div]
  calc
    W * A * (x + ∑ j, (b j / A) * p j) =
        W * (A * x + ∑ j, b j * p j) := by
      rw [hsum]
      field_simp [hA0]
    _ = W * ((∑ j, b j) * x + ∑ j, b j * p j) := by rw [hA]
    _ = ∑ j, W * (b j * x + b j * p j) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul]
    _ = ∑ j, W * b j * (x + p j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Row mass cancels when first-stage attraction multiplies conditional revenue. -/
theorem firstWeight_mul_conditionalRevenue (M : Model n₁ n₂)
    (X : PathMatrix n₁ n₂) (hX : Feasible X) (i : Fin (n₁ + 1)) :
    firstWeight M 1 X i * conditionalRevenue M X i =
      ∑ j, if X i j = true then weight M i j * (M.p₁ i + M.p₂ j) else 0 := by
  classical
  by_cases hi : X i 0 = true
  · rw [firstWeight, if_pos hi, Real.rpow_one, conditionalRevenue, if_pos hi]
    simp_rw [secondProbability_eq M X i hi]
    calc
      Real.exp (M.μ₁ i) * rowMass M X i *
          (M.p₁ i + ∑ j,
            ((if X i j = true then Real.exp (M.μ₂ j) else 0) / rowMass M X i) *
              M.p₂ j) =
          ∑ j, Real.exp (M.μ₁ i) *
            (if X i j = true then Real.exp (M.μ₂ j) else 0) *
              (M.p₁ i + M.p₂ j) :=
        weighted_row_identity _ _ _ _ _ (rowMass_eq_sum M X i hi)
          (ne_of_gt (rowMass_pos M X i))
      _ = ∑ j, if X i j = true then weight M i j * (M.p₁ i + M.p₂ j) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hx : X i j = true <;> simp [weight, hx]
  · have hrow : ∀ j, X i j ≠ true := fun j hj => hi (hX.2 i j hj)
    simp [firstWeight, conditionalRevenue, hi, hrow]

/-- The exact multistage objective at discount one is a ratio of finite path sums. -/
theorem revenue_one_eq (M : Model n₁ n₂) (X : PathMatrix n₁ n₂)
    (hX : Feasible X) : revenue M 1 X = total M X / mass M X := by
  have hden : (∑ i, firstWeight M 1 X i) = mass M X := by
    simp only [firstWeight_one_eq M X hX, mass]
  unfold revenue firstProbability
  rw [hden]
  calc
    (∑ i, firstWeight M 1 X i / mass M X * conditionalRevenue M X i) =
        (∑ i, firstWeight M 1 X i * conditionalRevenue M X i) / mass M X := by
      simp only [div_mul_eq_mul_div, Finset.sum_div]
    _ = total M X / mass M X := by
      congr 1
      unfold total
      apply Finset.sum_congr rfl
      intro i hi
      exact firstWeight_mul_conditionalRevenue M X hX i

end

end S02Multistage

-- Component: P067Optimization
set_option autoImplicit false

open scoped BigOperators
open XuMultistage.Structure

namespace S02Multistage

noncomputable section

variable {n₁ n₂ : ℕ}

/-- A row's residual before multiplying by its first-stage attraction. -/
def rowResidual (M : Model n₁ n₂) (R : ℝ) (X : PathMatrix n₁ n₂)
    (i : Fin (n₁ + 1)) : ℝ :=
  ∑ j, if X i j = true then
    Real.exp (M.μ₂ j) * (M.p₁ i + M.p₂ j - R) else 0

theorem threshold_feasible (M : Model n₁ n₂) (R : ℝ) :
    Feasible (threshold M R) := by
  classical
  constructor
  · simp [threshold]
  · intro i j hij
    have hi : i = 0 ∨ 0 ≤ score M R i := by
      exact (of_decide_eq_true hij).1
    simp [threshold, hi]

/-- The outside option contributes the compulsory term in an active row. -/
theorem score_eq_sum (M : Model n₁ n₂) (R : ℝ) (i : Fin (n₁ + 1)) :
    score M R i = ∑ j : Fin (n₂ + 1), if j = 0 then M.p₁ i - R
      else Real.exp (M.μ₂ j) * max (M.p₁ i + M.p₂ j - R) 0 := by
  classical
  unfold score
  calc
    _ = (∑ j : Fin (n₂ + 1), if j = 0 then M.p₁ i - R else 0) +
        ∑ j : Fin (n₂ + 1), if j = 0 then 0
          else Real.exp (M.μ₂ j) * max (M.p₁ i + M.p₂ j - R) 0 := by simp
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = 0 <;> simp [hj]

theorem residual_eq_sum_rows (M : Model n₁ n₂) (R : ℝ)
    (X : PathMatrix n₁ n₂) :
    total M X - R * mass M X =
      ∑ i, Real.exp (M.μ₁ i) * rowResidual M R X i := by
  unfold total mass rowResidual weight
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : X i j = true
  · simp only [if_pos hij]
    ring
  · simp only [if_neg hij, mul_zero, sub_self]

/-- Selecting a negative continuation cannot improve an active row's residual. -/
theorem rowResidual_le_score_of_active (M : Model n₁ n₂) (R : ℝ)
    (X : PathMatrix n₁ n₂) (i : Fin (n₁ + 1)) (hi : X i 0 = true) :
    rowResidual M R X i ≤ score M R i := by
  classical
  rw [score_eq_sum]
  unfold rowResidual
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j = 0
  · subst j
    simp [hi, M.μ₂_zero, M.p₂_zero]
  · simp only [if_neg hj]
    by_cases hij : X i j = true
    · simp only [if_pos hij]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_nonneg _)
    · simp only [if_neg hij]
      exact mul_nonneg (Real.exp_nonneg _) (le_max_right _ _)

/-- Feasibility makes every entry of an inactive row unavailable. -/
theorem rowResidual_eq_zero_of_inactive (M : Model n₁ n₂) (R : ℝ)
    (X : PathMatrix n₁ n₂) (hX : Feasible X) (i : Fin (n₁ + 1))
    (hi : X i 0 ≠ true) : rowResidual M R X i = 0 := by
  have hnone : ∀ j, X i j ≠ true := fun j hij => hi (hX.2 i j hij)
  simp [rowResidual, hnone]

/-- An active threshold row selects precisely the nonnegative continuations. -/
theorem rowResidual_threshold_of_active (M : Model n₁ n₂) (R : ℝ)
    (i : Fin (n₁ + 1)) (hi : i = 0 ∨ 0 ≤ score M R i) :
    rowResidual M R (threshold M R) i = score M R i := by
  classical
  rw [score_eq_sum]
  unfold rowResidual
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = 0
  · subst j
    simp [threshold, hi, M.μ₂_zero, M.p₂_zero]
  · by_cases hm : 0 ≤ M.p₁ i + M.p₂ j - R
    · simp [threshold, hi, hj, hm, max_eq_left hm]
    · have hmle : M.p₁ i + M.p₂ j - R ≤ 0 := (lt_of_not_ge hm).le
      simp [threshold, hi, hj, hm, max_eq_right hmle]

theorem rowResidual_threshold_of_inactive (M : Model n₁ n₂) (R : ℝ)
    (i : Fin (n₁ + 1)) (hi : ¬ (i = 0 ∨ 0 ≤ score M R i)) :
    rowResidual M R (threshold M R) i = 0 := by
  classical
  simp [rowResidual, threshold, hi]

/-- Row zero is compulsory. Other rows are kept exactly when their best
feasible residual is nonnegative. -/
theorem rowResidual_le_threshold (M : Model n₁ n₂) (R : ℝ)
    (Y : PathMatrix n₁ n₂) (hY : Feasible Y) (i : Fin (n₁ + 1)) :
    rowResidual M R Y i ≤ rowResidual M R (threshold M R) i := by
  by_cases hi : Y i 0 = true
  · have hupper := rowResidual_le_score_of_active M R Y i hi
    by_cases hactive : i = 0 ∨ 0 ≤ score M R i
    · rw [rowResidual_threshold_of_active M R i hactive]
      exact hupper
    · rw [rowResidual_threshold_of_inactive M R i hactive]
      exact hupper.trans (lt_of_not_ge (fun hs => hactive (Or.inr hs))).le
  · rw [rowResidual_eq_zero_of_inactive M R Y hY i hi]
    by_cases hactive : i = 0 ∨ 0 ≤ score M R i
    · rw [rowResidual_threshold_of_active M R i hactive]
      rcases hactive with hzero | hscore
      · subst i
        exact (hi hY.1).elim
      · exact hscore
    · rw [rowResidual_threshold_of_inactive M R i hactive]

/-- At any proposed revenue level, threshold choices maximize the total
numerator-minus-level-times-denominator residual over every feasible policy. -/
theorem residual_le_threshold (M : Model n₁ n₂) (R : ℝ)
    (Y : PathMatrix n₁ n₂) (hY : Feasible Y) :
    total M Y - R * mass M Y ≤
      total M (threshold M R) - R * mass M (threshold M R) := by
  rw [residual_eq_sum_rows, residual_eq_sum_rows]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (rowResidual_le_threshold M R Y hY i)
    (Real.exp_nonneg _)

end
end S02Multistage

-- Component: P067Ordered
set_option autoImplicit false

open Classical
open XuMultistage.Structure
open scoped BigOperators

namespace S02Multistage

/-- A set of ordinary indices is a price-order prefix when it is closed under
smaller positive indices. Inserting zero also handles the empty set. -/
theorem revenueOrdered_of_downward {n : ℕ} (S : Finset (Fin (n + 1)))
    (hzero : 0 ∉ S)
    (hdown : ∀ i ∈ S, ∀ k : Fin (n + 1), 0 < k → k ≤ i → k ∈ S) :
    RevenueOrdered S := by
  let T := insert (0 : Fin (n + 1)) S
  have hT : T.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨T.max' hT, ?_⟩
  intro i
  constructor
  · intro hi
    have hne : i ≠ 0 := by
      intro hi0
      exact hzero (hi0 ▸ hi)
    exact ⟨Fin.pos_iff_ne_zero.mpr hne,
      T.le_max' i (Finset.mem_insert_of_mem hi)⟩
  · rintro ⟨hpos, hle⟩
    have hm : T.max' hT ∈ T := T.max'_mem hT
    rcases Finset.mem_insert.mp hm with hm | hm
    · have hle0 : i ≤ 0 := hm ▸ hle
      exact False.elim ((not_lt_of_ge hle0) hpos)
    · exact hdown _ hm i hpos hle

/-- The explicit threshold policy excludes zero from each ordinary assortment. -/
noncomputable def thresholdPolicy {n₁ n₂ : ℕ} (M : Model n₁ n₂) (R : ℝ) :
    Policy n₁ n₂ where
  first := Finset.univ.filter (fun i => i ≠ 0 ∧ 0 ≤ score M R i)
  next := fun i => Finset.univ.filter (fun j => j ≠ 0 ∧ 0 ≤ M.p₁ i + M.p₂ j - R)
  first_noZero := by simp
  next_noZero := by intro i; simp

@[simp] theorem mem_thresholdPolicy_first {n₁ n₂ : ℕ} (M : Model n₁ n₂) (R : ℝ)
    (i : Fin (n₁ + 1)) :
    i ∈ (thresholdPolicy M R).first ↔ i ≠ 0 ∧ 0 ≤ score M R i := by
  simp [thresholdPolicy]

@[simp] theorem mem_thresholdPolicy_next {n₁ n₂ : ℕ} (M : Model n₁ n₂) (R : ℝ)
    (i : Fin (n₁ + 1)) (j : Fin (n₂ + 1)) :
    j ∈ (thresholdPolicy M R).next i ↔ j ≠ 0 ∧ 0 ≤ M.p₁ i + M.p₂ j - R := by
  simp [thresholdPolicy]

/-- Adding the outside options to the policy gives exactly the threshold matrix. -/
theorem thresholdPolicy_paths {n₁ n₂ : ℕ} (M : Model n₁ n₂) (R : ℝ) :
    (thresholdPolicy M R).paths = threshold M R := by
  funext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [Policy.paths, thresholdPolicy, threshold, hi, hj]

/-- The optimized residual score increases with the first-stage price. -/
theorem score_mono_price {n₁ n₂ : ℕ} (M : Model n₁ n₂) (R : ℝ)
    {i k : Fin (n₁ + 1)} (hp : M.p₁ i ≤ M.p₁ k) :
    score M R i ≤ score M R k := by
  unfold score
  refine add_le_add (sub_le_sub_right hp R) (Finset.sum_le_sum ?_)
  intro j _
  by_cases hj : j = 0
  · simp only [if_pos hj, le_refl]
  · simp only [if_neg hj]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
    exact max_le_max (sub_le_sub_right (add_le_add hp (le_refl (M.p₂ j))) R) le_rfl

/-- Higher-priced earlier products have no smaller residual score. -/
theorem score_antitone_index {n₁ n₂ : ℕ} (M : Model n₁ n₂) (R : ℝ)
    (horder : M.Ordered) {i k : Fin (n₁ + 1)} (hk : 0 < k) (hki : k ≤ i) :
    score M R i ≤ score M R k :=
  score_mono_price M R (horder.1 k i hk hki)

/-- The threshold first assortment is a prefix, including on price ties. -/
theorem thresholdPolicy_first_ordered {n₁ n₂ : ℕ} (M : Model n₁ n₂) (R : ℝ)
    (horder : M.Ordered) : RevenueOrdered (thresholdPolicy M R).first := by
  apply revenueOrdered_of_downward _ (thresholdPolicy M R).first_noZero
  intro i hi k hk hki
  apply (mem_thresholdPolicy_first M R k).mpr
  exact ⟨ne_of_gt hk, ((mem_thresholdPolicy_first M R i).mp hi).2.trans
    (score_antitone_index M R horder hk hki)⟩

/-- Every continuation is a prefix; the first-stage outside row is included. -/
theorem thresholdPolicy_next_ordered {n₁ n₂ : ℕ} (M : Model n₁ n₂) (R : ℝ)
    (horder : M.Ordered) (i : Fin (n₁ + 1)) :
    RevenueOrdered ((thresholdPolicy M R).next i) := by
  apply revenueOrdered_of_downward _ ((thresholdPolicy M R).next_noZero i)
  intro j hj k hk hkj
  apply (mem_thresholdPolicy_next M R i k).mpr
  refine ⟨ne_of_gt hk, ((mem_thresholdPolicy_next M R i j).mp hj).2.trans ?_⟩
  exact sub_le_sub_right (add_le_add (le_refl (M.p₁ i)) (horder.2 k j hk hkj)) R

/-- Continuations are nested in first-stage price order. The outside row need
not be compared with any ordinary row. -/
theorem thresholdPolicy_nested {n₁ n₂ : ℕ} (M : Model n₁ n₂) (R : ℝ)
    (horder : M.Ordered) {i k : Fin (n₁ + 1)} (hk : 0 < k) (hki : k ≤ i) :
    (thresholdPolicy M R).next i ⊆ (thresholdPolicy M R).next k := by
  intro j hj
  apply (mem_thresholdPolicy_next M R k j).mpr
  obtain ⟨hj0, hjthreshold⟩ := (mem_thresholdPolicy_next M R i j).mp hj
  refine ⟨hj0, hjthreshold.trans ?_⟩
  exact sub_le_sub_right (add_le_add (horder.1 k i hk hki) (le_refl (M.p₂ j))) R

/-- Every policy contains both outside options whenever its row is offered. -/
theorem policy_paths_feasible {n₁ n₂ : ℕ} (π : Policy n₁ n₂) : Feasible π.paths := by
  constructor
  · simp [Policy.paths]
  · intro i j hij
    have hi : i = 0 ∨ i ∈ π.first := (of_decide_eq_true hij).1
    simpa [Policy.paths] using hi

end S02Multistage

-- Component: P067Endgame
set_option autoImplicit false

open scoped BigOperators
open XuMultistage.Structure

namespace S02Multistage

theorem exists_threshold_ratio_optimal {n₁ n₂ : ℕ} (M : Model n₁ n₂)
    (hmass : ∀ X : PathMatrix n₁ n₂, Feasible X → 0 < mass M X)
    (hfeasible : ∀ R : ℝ, Feasible (threshold M R))
    (hdom : ∀ (R : ℝ) (Y : PathMatrix n₁ n₂), Feasible Y →
      total M Y - R * mass M Y ≤
        total M (threshold M R) - R * mass M (threshold M R)) :
    ∃ R : ℝ, ∀ Y : PathMatrix n₁ n₂, Feasible Y →
      total M Y / mass M Y ≤ total M (threshold M R) / mass M (threshold M R) := by
  classical
  let A : Finset (PathMatrix n₁ n₂) := Finset.univ.filter Feasible
  have hA : A.Nonempty := by
    refine ⟨fun _ _ => true, ?_⟩
    simp [A, Feasible]
  obtain ⟨X, hX, hmax⟩ := A.exists_max_image (fun Y => total M Y / mass M Y) hA
  have hXF : Feasible X := (Finset.mem_filter.mp hX).2
  let R := total M X / mass M X
  have hzero : total M X - R * mass M X = 0 := by
    dsimp [R]
    rw [div_mul_cancel₀ _ (ne_of_gt (hmass X hXF))]
    exact sub_self _
  have hres := hdom R X hXF
  rw [hzero] at hres
  have hR : R ≤ total M (threshold M R) / mass M (threshold M R) := by
    apply (le_div_iff₀ (hmass _ (hfeasible R))).2
    linarith
  refine ⟨R, fun Y hY => ?_⟩
  exact (hmax Y (by simp [A, hY])).trans hR

end S02Multistage

-- Component: P067
set_option autoImplicit false

open XuMultistage.Structure S02Multistage

theorem solution {n₁ n₂ : ℕ} (M : Model n₁ n₂) (horder : M.Ordered) :
    ∃ π : Policy n₁ n₂, IsOptimalPolicy M 1 π ∧
      RevenueOrdered π.first ∧
      (∀ i : Fin (n₁ + 1), (i = 0 ∨ i ∈ π.first) → RevenueOrdered (π.next i)) ∧
      (∀ i ∈ π.first, ∀ k ∈ π.first, k ≤ i → π.next i ⊆ π.next k) := by
  obtain ⟨R, hR⟩ := exists_threshold_ratio_optimal M
    (mass_pos M) (threshold_feasible M) (residual_le_threshold M)
  refine ⟨thresholdPolicy M R, ?_, thresholdPolicy_first_ordered M R horder,
    fun i _ => thresholdPolicy_next_ordered M R horder i, ?_⟩
  · intro σ
    change revenue M 1 σ.paths ≤ revenue M 1 (thresholdPolicy M R).paths
    rw [thresholdPolicy_paths]
    rw [revenue_one_eq M σ.paths (policy_paths_feasible σ),
      revenue_one_eq M (threshold M R) (threshold_feasible M R)]
    exact hR σ.paths (policy_paths_feasible σ)
  · intro i _ k hk hki
    exact thresholdPolicy_nested M R horder
      (Fin.pos_iff_ne_zero.mpr (((mem_thresholdPolicy_first M R k).mp hk).1)) hki

#print axioms solution
