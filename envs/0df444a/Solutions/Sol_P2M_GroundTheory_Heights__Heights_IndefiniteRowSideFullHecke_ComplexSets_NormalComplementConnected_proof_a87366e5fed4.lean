-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalComplementConnected_proof_a87366e5fed4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:36.299377+00:00
-- url     : https://prove2.me/submissions/60abc2ef-7856-4fd8-b868-f959622ba0f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVanishNearPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalComplementConnected
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroSetIn_isAnalyticNear_607ded16a998
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroSetIn_subset_closure_diff_d630fe876a88


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalComplementConnected
theorem _root_.solution (hvan : VanishNearPoint.Statement)
    (hgerm : NormalGermIrreducible.Statement) (hconn : IrreducibleGermComplementConnected.Statement) :
    NormalComplementConnected.Statement := by
  intro σ _ I h w hI hnorm hh hw U hU
  have hne : ¬ ∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z h = 0 := by
    intro hev
    have hcl := zeroSetIn_subset_closure_diff hvan I h hI hh hw
    rw [mem_closure_iff_nhds] at hcl
    obtain ⟨z, hzt, hzZ, hzh⟩ := hcl _ hev
    exact hzh (hzt hzZ)
  exact hconn σ (zeroSetIn I) w (fun z => eval z h) (zeroSetIn_isAnalyticNear I w)
    (hgerm σ I w hI hnorm hw) (AnalyticOnNhd.eval_mvPolynomial h w trivial) hne U hU
end NormalComplementConnected
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
