-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.kill_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:30.10909+00:00
-- url     : https://prove2.me/submissions/b654de66-987c-4b0d-b1f2-28364270b410

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocalIdempotentExistence
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_PI_FinKW_ratV_add__0cc5b55a46e7
import Theorems.Thm_P2M_PI_FinKW_ratV_zero__d853635dcea6
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (hn : 0 < I.n) (c : RV I v)
    (h : ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = 0) : c = 0 := by
  have key : ∀ x ∈ Submodule.span I.E (I.L : Set (Fin I.n → I.E)),
      c • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact h _ (Submodule.subset_span ⟨y, hy, rfl⟩)
    | zero => rw [PI.FinKW.ratV_zero', smul_zero]
    | add y z _ _ hy hz => rw [PI.FinKW.ratV_add', smul_add, hy, hz, add_zero]
    | smul a y _ hy =>
      have e : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (a • y) =
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) a) •
            Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) y := by
        funext i
        simp only [Formalism.L2.SG.Sub.ratV, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [e, smul_comm, hy, smul_zero]
  have h0 := key (Pi.single ⟨0, hn⟩ 1) (by rw [I.L_span]; exact Submodule.mem_top)
  have e1 : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (Pi.single ⟨0, hn⟩ (1 : I.E)) =
      Pi.single ⟨0, hn⟩ 1 := by
    funext i
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      simp [Formalism.L2.SG.Sub.ratV]
    · simp [Formalism.L2.SG.Sub.ratV, hi]
  rw [e1] at h0
  have h1 := congrFun h0 ⟨0, hn⟩
  simpa using h1
end PI.UnitaryGroupMassFormula.ScXuExists
