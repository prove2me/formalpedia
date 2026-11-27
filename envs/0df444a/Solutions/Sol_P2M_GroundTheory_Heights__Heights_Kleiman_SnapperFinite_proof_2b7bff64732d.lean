-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperFinite_proof_2b7bff64732d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:44.66836+00:00
-- url     : https://prove2.me/submissions/76c9ef2f-622c-4467-83ee-1186a0c3d7ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteESt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistTildeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeShiftSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tildeSys_twist_dbe5ec796d37


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
namespace SnapperFinite
theorem _root_.solution (hE : Extension.Statement.{u, v, w}) (hEL : Extension.Statement.{u, w, w})
    (hT : TwistTilde.Statement.{u, v, w}) (hTL : TwistTilde.Statement.{u, w, w})
    (hS : TildeShift.Statement.{u, v, w}) (hF : TildeFiniteE.Statement.{u, v, w}) :
    SnapperFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF0 t L n c i

  have hpow : ∀ (Lb : LineBundle k x) (m : ℕ), ∃ Q : FinGradedSub (S := k) (x := x) Ω,
      Lb.toSubSystem.pow m = Q.tildeSys 0 := by
    intro Lb m
    induction m with
    | zero =>
      refine ⟨coordGraded k x, ?_⟩
      change twistSys k x 0 = _
      rw [← coordGraded_tildeSys_twist (twistSys k x 0), SubSystem.twist_twistSys_zero]
    | succ m ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨QL, -, hQL⟩ := hEL k Ω N x Ω Lb.toSubFamily Lb.fg
      obtain ⟨P, -, hP⟩ := hTL k Ω N x Ω Q QL
      refine ⟨P, ?_⟩
      have hL : Lb.toSubSystem = QL.tildeSys 0 := SubSystem.ext_sub fun I => (hQL I).symm
      change (Lb.toSubSystem.pow m).twist Lb.toSubSystem = _
      rw [hQ, hL]
      exact SubSystem.ext_sub hP

  have hpows : ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∃ P : FinGradedSub (S := k) (x := x) E,
        F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n = P.tildeSys 0 := by
    intro t
    induction t with
    | zero =>
      intro L n
      obtain ⟨M, -, hM⟩ := hE k Ω N x E F hF0
      exact ⟨M, SubSystem.ext_sub fun I => (hM I).symm⟩
    | succ t ih =>
      intro L n
      obtain ⟨P, hP⟩ := ih (fun j => L j.castSucc) (fun j => n j.castSucc)
      obtain ⟨Q, hQ⟩ := hpow (L (Fin.last t)) (n (Fin.last t))
      obtain ⟨P', -, hP'⟩ := hT k Ω N x E P Q
      refine ⟨P', ?_⟩
      change (F.toSubSystem.twistPows t (fun j => (L j.castSucc).toSubSystem)
        (fun j => n j.castSucc)).twist ((L (Fin.last t)).toSubSystem.pow (n (Fin.last t))) = _
      rw [hP, hQ]
      exact SubSystem.ext_sub hP'
  obtain ⟨P, hP⟩ := hpows t L n
  rw [hP, ← hS k Ω N x E P c]
  exact hF k Ω N x E P i c
end SnapperFinite
end GroundTheory.Heights₂.Heights.Kleiman
