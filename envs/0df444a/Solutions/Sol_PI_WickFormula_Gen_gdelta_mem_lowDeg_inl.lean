-- Prove2me | solution 1 for PI.WickFormula.Gen.gdelta_mem_lowDeg_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:11.814556+00:00
-- url     : https://prove2.me/submissions/9689c828-f0fd-4e10-844e-57db0a7e7990

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenVan
import Theorems.Thm_PI_WickFormula_Gen_pderiv_mem_lowDeg
import Theorems.Thm_PI_WickFormula_Gen_pderiv_mem_lowDeg_of_succ
import Theorems.Thm_P2M_RH_PI_WickFormula_Gen_gdelta_apply_432825626bc43230

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Gen
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
namespace PI.WickFormula.Gen
theorem _root_.solution (κ : I → J → K) {t : ℕ} {R : MvPolynomial (I ⊕ J) K}
    (h : R ∈ lowDeg (Sum.inl : I → I ⊕ J) (t + 1)) :
    gdelta κ R ∈ lowDeg (Sum.inl : I → I ⊕ J) t := by
  rw [gdelta_apply]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact pderiv_mem_lowDeg_of_succ (f := (Sum.inl : I → I ⊕ J)) i (pderiv_mem_lowDeg _ h)
end PI.WickFormula.Gen
