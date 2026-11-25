-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_pairNum_eq_5208b844af2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:43.645637+00:00
-- url     : https://prove2.me/submissions/33e489c7-dd7a-4e15-b736-70f68648cfaf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_ratCyc_eq_f84cd3040ff4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_vEval_eq_85c4d0bed24d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_polyNum_eq_classNum_8d89639b44f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isHomogeneous_divDiff_55f04f213f1e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
set_option linter.unusedSectionVars false
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (P : Ideal (MRing ι O)) (d : ℕ) {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    {G : MvPolynomial (Fin r) ℤ} (hG : G.IsHomogeneous (d + 1)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
                              y y' f g G =
      pairNum P y y' f g
        (fun l => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G)) [] := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [vEval_eq, ratCyc_eq]
  congr 1
  funext W
  refine polyNum_eq_classNum (Fin.append y y') finSumFinEquiv.symm (Sum.elim y y') ?_
    (isHomogeneous_divDiff l hG) W
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl, Fin.append_left]
  · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Fin.append_right]
end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
