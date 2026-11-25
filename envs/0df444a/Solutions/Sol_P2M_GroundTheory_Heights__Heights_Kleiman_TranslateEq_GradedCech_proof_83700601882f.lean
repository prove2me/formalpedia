-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedCech_proof_83700601882f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:46.138957+00:00
-- url     : https://prove2.me/submissions/9f4b2656-f293-47ae-8dce-c626dd68e96e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqCech
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedCech_hEquiv_mk_ddf70a59c8c8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
open GradedCech
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace GradedCech
theorem _root_.solution : GradedCech.Statement := by
  intro S _ N
  refine ⟨fun M _ _ _ _ G i c => hEquiv G c i, ?_, ?_⟩
  · intro M M' _ _ _ _ _ _ _ _ G G' f hf i c z
    induction z using Submodule.Quotient.induction_on with
    | H w =>
      rw [hEquiv_mk]
      change hEquiv G' c i (Submodule.Quotient.mk ((IndefiniteRowSideFullHecke.Kleiman.gradedHom S N hf c).Zmap i w)) =
        Submodule.Quotient.mk _
      rw [hEquiv_mk]
      congr 1
  · intro M _ _ _ _ G c m hm z hz
    rw [hEquiv_mk]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext J
    change locEquiv S N M J.1.1 (z.1 J.1.1) =
      (LocalizedModule.mk m 1 : LocalizedModule (Kleiman.monos (S := S) J.1.1) M)
    rw [hz, IndefiniteRowSideFullHecke.Kleiman.unitCochain, if_pos (show J.1.1.card = 1 from J.2)]
    change (LocalizedModule.mk m ⟨IndefiniteRowSideFullHecke.Kleiman.Xprod S N J.1.1 ^ 0, _⟩ :
      LocalizedModule (Kleiman.monos (S := S) J.1.1) M) = LocalizedModule.mk m 1
    congr 1
end GradedCech
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
