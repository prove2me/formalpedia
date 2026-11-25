-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hs_le_colsV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:31.263609+00:00
-- url     : https://prove2.me/submissions/70d07fde-9454-41fb-bfb2-ea3109cb9188

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_gJgH_VG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_mul_P0V_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_sum_SgIxV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} (s : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    hs g ≤ n + 2 * hsRV (g * signedIdentityColumns ε s) := by
  have h := gJgH_VG hg
  let σ : Fin n → ℝ := fun a => if ε a then 1 else -1
  have hJσ : Jm ε = Matrix.diagonal fun a => ((σ a : ℝ) : ℂ) := by
    unfold Jm
    congr 1
    funext a
    simp only [σ]
    split_ifs <;> simp
  have hterm : ∀ i j, g i j * ((σ j : ℝ) : ℂ) * star (g i j) = ((σ j * ‖g i j‖ ^ 2 : ℝ) : ℂ) := by
    intro i j
    rw [mul_comm (g i j), mul_assoc, Complex.star_def, Complex.mul_conj']
    push_cast
    ring
  have hrow : ∀ i, ∑ j, σ j * ‖g i j‖ ^ 2 = σ i := by
    intro i
    have h1 := congrFun (congrFun h i) i
    rw [hJσ, Matrix.mul_apply] at h1
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq, hterm] at h1
    exact_mod_cast h1
  have hcols : hsRV (g * signedIdentityColumns ε s) = ∑ i, ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0 := by
    unfold hsRV
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mul_P0V_apply]
    exact sum_SgIxV ε s (fun j => ‖g i j‖ ^ 2)
  have hpt : ∀ i j, ‖g i j‖ ^ 2 = (if s then -1 else 1) * (σ j * ‖g i j‖ ^ 2) +
      2 * (if ε j = s then ‖g i j‖ ^ 2 else 0) := by
    intro i j
    by_cases h1 : ε j = true <;> cases s <;> simp [σ, h1] <;> ring
  have hσ : ∀ i, (if s then (-1:ℝ) else 1) * σ i ≤ 1 := by
    intro i
    by_cases h1 : ε i = true <;> cases s <;> simp [σ, h1]
  unfold hs
  rw [hcols]
  calc ∑ i, ∑ j, ‖g i j‖ ^ 2
      = ∑ i, ((if s then -1 else 1) * σ i + 2 * ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_congr rfl fun j _ => hpt i j, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hrow i]
    _ ≤ ∑ i : Fin n, (1 + 2 * ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun i _ => by linarith [hσ i]
    _ = n + 2 * ∑ i, ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
end ReciprocityTheory.ChartRestriction.DS.S7
