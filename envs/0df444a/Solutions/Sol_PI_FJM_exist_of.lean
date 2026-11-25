-- Prove2me | solution 1 for PI.FJM.exist_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:16.253138+00:00
-- url     : https://prove2.me/submissions/a63912e3-c3f6-4aef-824a-0d80a6c56cfc

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJM
namespace PI.FJM
theorem _root_.solution (hN : VecNe) (hJ : VecJ) (h1 : VecHW1) (h2 : VecHW2) : Exist := by
  intro p q r s μ μ' hcorr
  obtain ⟨a, b, c, d, ha, hc, hb, hd, hpa, hpb, hpc, hpd, hl1, hl2, hl3, hl4, hμ, hμ'⟩ := hcorr
  have hS : ShapeData p q r s a b c d := ⟨ha, hc, hb, hd, hpa, hpb, hpc, hpd, hl1, hl2, hl3, hl4⟩
  have hL : wtOf1 p q r s a b c d = μ := by
    funext x
    have h := congrFun hμ x
    cases x <;> simp only [wtOf1, sh1, FockH1Action.shiftNu, Sum.elim_inl, Sum.elim_inr] at h ⊢ <;> linarith
  have hR : wtOf2 p q r s a b c d = μ' := by
    funext x
    have h := congrFun hμ' x
    cases x <;> simp only [wtOf2, sh2, FockH1Action.shiftNu, Sum.elim_inl, Sum.elim_inr] at h ⊢ <;> linarith
  have hA := h1 p q r s a b c d hS
  have hB := h2 p q r s a b c d hS
  rw [hL] at hA
  rw [hR] at hB
  refine ⟨hwVec p q r s a b c d, ?_, hN p q r s a b c d hS⟩
  unfold JH
  exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hA, hB⟩, Submodule.subset_span (hJ p q r s a b c d hS)⟩
end PI.FJM
