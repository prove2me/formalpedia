-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistVanish_proof_0d13fb95bbdf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:53.482818+00:00
-- url     : https://prove2.me/submissions/9b0cb4e3-d862-4c52-a534-6869dcf96b4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistVanish

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
open MvPolynomial
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace TwistVanish
theorem _root_.solution (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun b c hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c 1
  have := hc₀ 1 le_rfl c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩
end TwistVanish
end GroundTheory.Heights₂.Heights.Kleiman
