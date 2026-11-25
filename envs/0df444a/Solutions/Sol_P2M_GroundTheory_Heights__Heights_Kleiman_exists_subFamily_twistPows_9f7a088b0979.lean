-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_subFamily_twistPows_9f7a088b0979
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:23.868104+00:00
-- url     : https://prove2.me/submissions/0a94b7eb-318c-427d-ab67-b5425d769462

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotDevissage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_twistMul_fe4f7be26a50


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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hB : SubFamilyTwist.Statement.{u, v, w}) (F : SubFamily S x E)
    (hF : ∀ I, (F.sub I).FG) : ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      ∃ H : SubFamily S x E, H.toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n ∧
        ∀ I, (H.sub I).FG
  | 0, _, _ => ⟨F, rfl, hF⟩
  | t + 1, L, n => by
    obtain ⟨H, hH, hHfg⟩ := solution hB F hF t (fun j => L j.castSucc) (fun j => n j.castSucc)
    obtain ⟨P, hP⟩ := exists_lineBundle_twistMul (L (Fin.last t)) (n (Fin.last t)) 0
    obtain ⟨G, hG, hGfg⟩ := hB S Ω N x E H P hHfg
    refine ⟨G, ?_, hGfg⟩
    rw [hG, hP, hH, twistMul, SubSystem.twist_twistSys_zero]
    rfl
end GroundTheory.Heights₂.Heights.Kleiman
