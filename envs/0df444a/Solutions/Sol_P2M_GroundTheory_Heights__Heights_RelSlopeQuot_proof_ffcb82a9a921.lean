-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RelSlopeQuot_proof_ffcb82a9a921
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:08:05.193306+00:00
-- url     : https://prove2.me/submissions/ef69d48b-dc72-4422-8ab6-a1c77fbb8e19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PExactSequence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PChainSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Slopes_PRelSlopeQuot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_eq_deg_sub_462229a1e5e8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_Saturated_comap_subtype_d827eb6d48d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_arithDegree_eq_add_d3246defcd21
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_comap_84fe70e9ccca


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace RelSlopeQuot
theorem _root_.solution : RelSlopeQuot.Statement := by
  intro K _ _ E F G hF hFG
  set F' := F.comap G.subtype
  set hF' := hF.comap_subtype G
  set X := HermitianBundle.subQuotExtension (E.sub G) F' hF'
  have hdeg : (E.sub G).deg = ((E.sub G).sub F').deg + ((E.sub G).quot F' hF').deg := by
    simp only [HermitianBundle.deg]
    rw [X.arithDegree_eq_add, add_div]
  have hsubF : ((E.sub G).sub F').deg = (E.sub F).deg :=
    LatticeLemmas.ChainSum.deg_sub_comap E hFG.le
  have hrk := X.finrank_eq
  have hrkF : Module.finrank (𝓞 K) ((E.sub G).sub F').carrier = Module.finrank (𝓞 K) F :=
    (Submodule.comapSubtypeEquivOfLe hFG.le).finrank_eq
  have hrk' : (E.rank G : ℝ) - E.rank F =
      Module.finrank (𝓞 K) ((E.sub G).quot F' hF').carrier := by
    have h : E.rank G = E.rank F + Module.finrank (𝓞 K) ((E.sub G).quot F' hF').carrier := by
      rw [HermitianBundle.rank, HermitianBundle.rank, ← hrkF]
      exact hrk
    rw [h, Nat.cast_add, add_sub_cancel_left]
  rw [HermitianBundle.relSlope, hrk', HermitianBundle.normDegree_eq_deg_sub,
    HermitianBundle.normDegree_eq_deg_sub, hdeg, hsubF, add_sub_cancel_left,
    HermitianBundle.bundleSlope]
  rfl
end RelSlopeQuot
end GroundTheory.Heights₂.Heights
