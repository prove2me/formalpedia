-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleCech_proof_45d15e1c9549
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:13.419386+00:00
-- url     : https://prove2.me/submissions/e9bb68ff-d109-4ce7-9293-bbe01353fc8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistPowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechHdegOfSubSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZRowsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleCech

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
noncomputable section
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleCech
theorem _root_.solution (hFam : VeryAmpleZFamily.Statement.{u, v, w})
    (hFin : VeryAmpleZFinite.Statement.{u, v, w}) (hTw : VeryAmpleZTwist.Statement.{u, v, w})
    (hPow : SubFamilyTwistPow.Statement.{u, v, w}) (hSub : CechHdegOfSub.Statement.{u, v, w})
    (hDbl : CechDouble.Statement.{u, v, w}) (hCol : VeryAmpleZColumns.Statement.{u, v, w})
    (hRow : VeryAmpleZRows.Statement.{u, v, w}) : VeryAmpleCech.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H r h hH
  obtain ⟨F', hF'⟩ := hFam S Ω N x E F H r h hH
  have hmem : ∀ J e, e ∈ F'.sub J ↔ e ∈ secsOnZ F.toSubSystem H.toSubSystem h J := fun J e => by
    rw [← hF' J, Submodule.restrictScalars_mem]
  refine ⟨F', fun J => ?_, fun a i => ?_⟩
  ·
    obtain ⟨t, ht, hle⟩ := hFin S Ω N x E F hF H r h hH J
    exact ⟨t, le_antisymm (Submodule.span_le.mpr fun e he => (hmem J e).mpr (ht he))
      fun e he => hle ((hmem J e).mp he)⟩
  ·
    obtain ⟨G, hG⟩ := hPow S Ω N x E F H.toSubFamily a

    obtain ⟨e₁⟩ := hSub S Ω N x E G.toSubSystem i

    obtain ⟨e₂⟩ := hDbl S Ω N r x h E (fun I => (G.sub I).restrictScalars S)
      (secsOnZ G.toSubSystem H.toSubSystem h) (secsOnZChart G.toSubSystem H.toSubSystem h)
      (fun I I' J hI => (hRow S Ω N x E G H r h hH J).1 I I' hI)
      (fun I J J' hJ => (hCol S Ω N x E G H r h hH I).1 J J' hJ)
      (fun I => (hCol S Ω N x E G H r h hH I).2) (fun J => (hRow S Ω N x E G H r h hH J).2) i

    obtain ⟨e₃⟩ := hSub S Ω r h E (F'.twist (twistSys S h (a : ℤ))) i
    have hfun : (fun J => ((F'.twist (twistSys S h (a : ℤ))).sub J).restrictScalars S) =
        secsOnZ G.toSubSystem H.toSubSystem h := by
      funext J
      rw [hG, ← hTw S Ω N x E F H r h hH a J]
      change (Submodule.span (chartRing S h J)
        {z | ∃ q ∈ twistMod S h (a : ℤ) J, ∃ y ∈ F'.sub J, z = q • y}).restrictScalars S = _
      congr 3
      ext z
      simp only [hmem J]
    rw [hfun] at e₃
    rw [← hG]
    exact ⟨e₁.trans (e₂.trans e₃.symm)⟩
end VeryAmpleCech
end GroundTheory.Heights₂.Heights.Kleiman
