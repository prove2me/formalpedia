-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepTwo_Reduce_proof_d427b891ed9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:46.570185+00:00
-- url     : https://prove2.me/submissions/083cf2ec-d86a-463a-afbd-2ce883d8ab77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoPieceSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepTwoReduce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tildeSys_twist_mono_7b53b83e8b56
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotH_self_subsingleton_0e9c59d3c9e0

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
namespace StepTwo.Reduce
theorem _root_.solution (hF : StepTwo.Filt.Statement.{u, v, w}) (hT : QuotTrans.Statement.{u, v, w})
    (hP : StepTwo.Piece.Statement.{u, v, w}) : StepTwo.Reduce.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M₁ M₂ h21 J hJ
  obtain ⟨n, Nf, g, deg, pr, h0, hlast, hk⟩ := hF S Ω N x E M₁ M₂ h21 J hJ
  refine ⟨n, pr, fun i => -deg i, fun i => ⟨(hk i).1, (hk i).2.1, (hk i).2.2.1, (hk i).2.2.2.1⟩, ?_⟩
  intro Q c hQ
  have key : ∀ (m : ℕ) (hm : m < n + 1), (∀ a, (Nf 0).piece a ≤ (Nf ⟨m, hm⟩).piece a) ∧
      Subsingleton (SubSystem.quotH (((Nf ⟨m, hm⟩).tildeSys 0).twist (Q.twist (twistSys S x c)))
        (((Nf 0).tildeSys 0).twist (Q.twist (twistSys S x c))) 1) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun _ => le_rfl, quotH_self_subsingleton _ 1⟩
    | succ m ih =>
      intro hm
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨hpr, hhom, hprx, -, hg, hsup, hann⟩ := hk ⟨m, by omega⟩
      have hstep := hP S Ω N x E _ _ (g ⟨m, by omega⟩) (deg ⟨m, by omega⟩) (pr ⟨m, by omega⟩) hpr hhom
        hprx hg hsup hann Q c (fun hrel => by rw [sub_eq_add_neg]; exact hQ ⟨m, by omega⟩ hrel)
      have hle : ∀ a, (Nf ⟨m, by omega⟩).piece a ≤ (Nf ⟨m + 1, hm⟩).piece a := fun a => by
        rw [show (⟨m + 1, hm⟩ : Fin (n + 1)) = Fin.succ ⟨m, by omega⟩ from rfl, hsup a]
        exact le_sup_left
      exact ⟨fun a => (ih1 a).trans (hle a), hT S Ω N x E _ _ _ (tildeSys_twist_mono ih1 _)
        (tildeSys_twist_mono hle _) ih2 hstep⟩
  obtain ⟨-, h⟩ := key n (Nat.lt_succ_self n)
  rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, hlast, h0] at h
  exact h
end StepTwo.Reduce
end GroundTheory.Heights₂.Heights.Kleiman
