-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepData_Jg_tilde_b79af9a41a80
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:56.414263+00:00
-- url     : https://prove2.me/submissions/2cc63e0e-40a9-4e46-90a1-3a4d36619e45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq

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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
variable (T : StepData k x)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace StepData
theorem _root_.solution (I : Chart x) : (T.Jg.tildeSys 0).sub I = idealMod T.J I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ idealMod T.J I)
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨f, e', hf, hfe, rfl, rfl⟩
      have he : e' = e := by omega
      subst he
      exact Submodule.subset_span ⟨f, s, e', hf, hs, hfe, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro c z _ hz; rw [smul_comm]; exact (idealMod T.J I).smul_of_tower_mem c hz
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    exact Submodule.subset_span ⟨aeval x f, s, e, e, hs, hse,
      Submodule.subset_span ⟨f, e, hf, hfe, rfl, rfl⟩, sub_self _, by rw [smul_eq_mul, div_eq_inv_mul]⟩
end StepData
end GroundTheory.Heights₂.Heights.Kleiman
