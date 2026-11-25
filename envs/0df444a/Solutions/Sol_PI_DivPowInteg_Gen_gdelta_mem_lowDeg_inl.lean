-- Prove2me | solution 1 for PI.DivPowInteg.Gen.gdelta_mem_lowDeg_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:28.094812+00:00
-- url     : https://prove2.me/submissions/2851daa5-6bda-4672-be65-188ad35382fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenVan
import Theorems.Thm_PI_DivPowInteg_Gen_pderiv_mem_lowDeg
import Theorems.Thm_PI_DivPowInteg_Gen_pderiv_mem_lowDeg_of_succ
import Theorems.Thm_P2M_RH_PI_DivPowInteg_Gen_gdelta_apply_40cc7e38269bf342

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
namespace PI.DivPowInteg.Gen
theorem _root_.solution (κ : I → J → K) {t : ℕ} {R : MvPolynomial (I ⊕ J) K}
    (h : R ∈ lowDeg (Sum.inl : I → I ⊕ J) (t + 1)) :
    gdelta κ R ∈ lowDeg (Sum.inl : I → I ⊕ J) t := by
  rw [gdelta_apply]
  refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ?_))
  exact pderiv_mem_lowDeg_of_succ (f := Sum.inl) i (pderiv_mem_lowDeg (Sum.inr j) h)
end PI.DivPowInteg.Gen
