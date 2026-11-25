-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapAd.coef_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:55.840129+00:00
-- url     : https://prove2.me/submissions/5065053d-6e7d-45a9-8947-073efb9c885f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.CapAd
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapAd
theorem _root_.solution (P : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • ∏ j, P (c j) (σ j) = (P.submatrix c id).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Units.smul_def]
  rfl
end ReciprocityTheory.ChartRestriction.DS.S7.CapAd
