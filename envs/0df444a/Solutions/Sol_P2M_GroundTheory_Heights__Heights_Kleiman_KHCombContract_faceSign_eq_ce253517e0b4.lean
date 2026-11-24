-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_faceSign_eq_ce253517e0b4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:35.881411+00:00
-- url     : https://prove2.me/submissions/d5fa81cc-7677-4a22-9845-8c14278775f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
theorem _root_.solution (T : ∀ k, Finset (ι k)) (l : K) (i : ι l) :
    KH.faceSign T l i = (-1) ^ ((T l).filter (· < i)).card *
      (-1) ^ ∑ x ∈ Finset.univ.filter (· < l), ((T x).card - 1) := by
  rw [KH.faceSign, pow_add]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
