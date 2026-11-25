-- Prove2me | solution 1 for PI.FJM.jointMult_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:21.760169+00:00
-- url     : https://prove2.me/submissions/9e103fcc-8cbf-4a7d-b36b-72a0b41aa17f

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix FockH1Action
namespace PI.FJM
private theorem finrank_eq_one_of_ne_zero_mem_of_le_span_singleton {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Submodule ℂ V}
    {P v : V} (hP : P ∈ S) (hP0 : P ≠ 0) (hv : S ≤ Submodule.span ℂ {v}) : Module.finrank ℂ S = 1 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hv hP)
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hP0
    rw [← ha, smul_zero]
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hP0
    rw [← ha, zero_smul]
  have heq : S = Submodule.span ℂ {v} := by
    apply le_antisymm hv
    rw [Submodule.span_le, Set.singleton_subset_iff]
    have hva : v = a⁻¹ • P := by
      rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    rw [hva]
    exact S.smul_mem _ hP
  rw [heq]
  exact finrank_span_singleton hv0
end PI.FJM
end
end

set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJM
namespace PI.FJM
theorem _root_.solution (he : Exist) (hs : ShapeOf) (hr : RankLe) : PI.FockDegreeTwoParts.JointMult := by
  intro p q r s μ μ'
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · change Module.finrank ℂ (JH p q r s μ μ') = 1
    obtain ⟨P, hP, hP0⟩ := he p q r s μ μ' hc
    obtain ⟨v, hv⟩ := hr p q r s μ μ' hc
    exact finrank_eq_one_of_ne_zero_mem_of_le_span_singleton hP hP0 hv
  · change JH p q r s μ μ' = ⊥
    rw [Submodule.eq_bot_iff]
    intro P hP
    by_contra hP0
    exact hc (hs p q r s μ μ' P hP hP0)
end PI.FJM
