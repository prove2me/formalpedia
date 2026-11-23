-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_inv_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:42.085804+00:00
-- url     : https://prove2.me/submissions/08a5da1b-7f3d-4625-bc80-7127363fb565

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_RightHolRightHolEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private theorem contDiff_det_k_type {m : ℕ} {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun z : Matrix (Fin m) (Fin m) ℂ => z.det) := by
  have h : (fun z : Matrix (Fin m) (Fin m) ℂ => z.det) =
      fun z => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, z (σ i) i := by
    funext z
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  rw [h]
  exact ContDiff.sum fun σ _ => contDiff_const.mul
    (contDiff_prod fun i _ => contDiff_pi.1 (contDiff_pi.1 contDiff_id (σ i)) i)
private theorem contDiff_adjugate' {m : ℕ} {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun z : Matrix (Fin m) (Fin m) ℂ => z.adjugate) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.adjugate_apply]
  have hrow : ContDiff ℂ k
      (fun x : Matrix (Fin m) (Fin m) ℂ => x.updateRow j (Pi.single i 1)) := by
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    by_cases hab : a = j
    · subst hab
      simp only [Matrix.updateRow_self]
      exact contDiff_const
    · simp only [Matrix.updateRow_ne hab]
      exact contDiff_pi.1 (contDiff_pi.1 contDiff_id a) b
  exact contDiff_det_k_type.comp hrow
private theorem contDiffOn_inv_det_ne_zero' {m : ℕ} {k : WithTop ℕ∞} :
    ContDiffOn ℂ k (fun z : Matrix (Fin m) (Fin m) ℂ => z⁻¹) {z | z.det ≠ 0} := by
  have h : (fun z : Matrix (Fin m) (Fin m) ℂ => z⁻¹) = fun z => (z.det)⁻¹ • z.adjugate := by
    funext z
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (contDiff_det_k_type.contDiffOn.inv fun z hz => hz).smul contDiff_adjugate'.contDiffOn
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution :
    ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹) {z | z.det ≠ 0} := by
  exact contDiffOn_inv_det_ne_zero'
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
