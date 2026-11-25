-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lead_tri_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:35.560194+00:00
-- url     : https://prove2.me/submissions/f6d53aa1-aa46-4dd7-b3c8-683069278506

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_Minors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private lemma sub_lower_mul {i : ℕ} (hi : i ≤ n) {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (c * M).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      c.submatrix (Fin.castLE hi) (Fin.castLE hi) * M.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ (fun k => rfl)
  intro k hk
  have hk' : i ≤ (k : ℕ) := by
    by_contra h
    exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩
  have ha := a.2
  rw [hc _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]
private lemma sub_mul_upper {i : ℕ} (hi : i ≤ n) {c' : Matrix (Fin n) (Fin n) ℂ} (hc' : IsUpperTri c')
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (M * c').submatrix (Fin.castLE hi) (Fin.castLE hi) =
      M.submatrix (Fin.castLE hi) (Fin.castLE hi) * c'.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ (fun k => rfl)
  intro k hk
  have hk' : i ≤ (k : ℕ) := by
    by_contra h
    exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩
  have hb := b.2
  unfold IsUpperTri at hc'
  rw [hc' _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]
private lemma lowerTri_sub {i : ℕ} (hi : i ≤ n) {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) :
    (c.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsLowerTriangular := by
  intro a b hab
  have hab' : a < b := hab
  apply hc
  rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
  exact hab'
private lemma upperTri_sub {i : ℕ} (hi : i ≤ n) {c' : Matrix (Fin n) (Fin n) ℂ} (hc' : IsUpperTri c') :
    (c'.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsUpperTriangular := by
  intro a b hab
  have hab' : b < a := hab
  apply hc'
  rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
  exact hab'
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {c z c' : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) (hc' : IsUpperTri c') (i : ℕ) (hi : i ≤ n) :
    lead i (c * z * c') =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), c l l * c' l l) * lead i z := by
  have hp : ∀ f : Fin n → ℂ, ∏ a : Fin i, f (Fin.castLE hi a) =
      ∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), f l := by
    intro f
    rw [Finset.prod_filter]
    refine Fintype.prod_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ ?_
    · intro k hk
      rw [if_neg]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    · intro a
      rw [if_pos (by rw [Fin.coe_castLE]; exact a.2)]
  unfold lead
  rw [dif_pos hi, dif_pos hi, sub_mul_upper hi hc', sub_lower_mul hi hc, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_of_lowerTriangular _ (lowerTri_sub hi hc), Matrix.det_of_upperTriangular (upperTri_sub hi hc'),
    Finset.prod_mul_distrib, ← hp (fun l => c l l), ← hp (fun l => c' l l)]
  simp only [Matrix.submatrix_apply]
  ring
end ReciprocityTheory.ChartRestriction.DS.S7
