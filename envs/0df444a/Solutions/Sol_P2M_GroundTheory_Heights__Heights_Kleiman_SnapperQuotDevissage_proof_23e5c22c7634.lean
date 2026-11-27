-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotDevissage_proof_23e5c22c7634
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:02:40.769862+00:00
-- url     : https://prove2.me/submissions/16a4c95a-daab-46a3-9893-92f5c0ad058c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotDevissage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_mono_a1444dbbcbc5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_sub_mono_1795938819b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_subFamily_twistPows_9f7a088b0979
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_eulerCharQuot_self_9762b655af6d


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
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SnapperQuotDevissage
theorem _root_.solution (hF : SnapperQuotFilt.Statement.{u, v, w})
    (hI : SnapperQuotIso.Statement.{u, v, w, w}) (hA : SnapperQuotAdd.Statement.{u, v, w})
    (hB : SubFamilyTwist.Statement.{u, v, w}) : SnapperQuotDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ hfg hle J hJ hxJ hJF
  obtain ⟨r, G, pp, a, hGfg, hG0, hGr, hmono, hpp, hiso⟩ := hF k Ω N x E F₁ F₂ hfg hle J hJ hxJ hJF
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  have hH : ∀ m, ∃ H : SubFamily k x E, H.toSubSystem =
      ((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) ∧
        ∀ I, (H.sub I).FG := fun m => by
    obtain ⟨H, hH, hHfg⟩ := exists_subFamily_twistPows hB (G m) (hGfg m) t L n
    obtain ⟨H', hH', hH'fg⟩ := hB k Ω N x E H (twistBundle k x c) hHfg
    exact ⟨H', by rw [hH', hH]; rfl, hH'fg⟩
  choose H hHeq hHfg using hH
  have hHmono : ∀ m < r, ∀ I, (H m).sub I ≤ (H (m + 1)).sub I := fun m hm I => by
    rw [hHeq, hHeq]
    exact twist_sub_mono (twistPows_sub_mono (hmono m hm) t _ n) _ I
  have hstep : ∀ m (hm : m < r), eulerCharQuot k (H (m + 1)).toSubSystem (H m).toSubSystem =
      pieceChar k (pp ⟨m, hm⟩) (a ⟨m, hm⟩) L n c := fun m hm => by
    rw [hHeq, hHeq]
    exact hI k Ω N x E Ω _ _ _ _ (hiso ⟨m, hm⟩ t L n c).some
  have key : ∀ m ≤ r, (∀ I, (H 0).sub I ≤ (H m).sub I) ∧
      eulerCharQuot k (H m).toSubSystem (H 0).toSubSystem =
        ∑ i ∈ Finset.range m, (if h : i < r then pieceChar k (pp ⟨i, h⟩) (a ⟨i, h⟩) L n c else 0) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨fun I => le_rfl, by simp [eulerCharQuot_self]⟩
    | succ m ih =>
      intro hm
      obtain ⟨h0, hχ⟩ := ih (by omega)
      refine ⟨fun I => (h0 I).trans (hHmono m (by omega) I), ?_⟩
      rw [hA k Ω N x E (H (m + 1)) (H m) (H 0) (hHfg _) (hHmono m (by omega)) h0, hχ,
        hstep m (by omega), Finset.sum_range_succ, dif_pos (by omega), add_comm]
  rw [← hGr, ← hG0, ← hHeq r, ← hHeq 0, (key r le_rfl).2, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp [i.2]
end SnapperQuotDevissage
end GroundTheory.Heights₂.Heights.Kleiman
