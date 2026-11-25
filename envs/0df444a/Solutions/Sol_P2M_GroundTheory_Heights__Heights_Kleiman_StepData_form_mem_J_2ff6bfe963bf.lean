-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepData_form_mem_J_2ff6bfe963bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:44.218774+00:00
-- url     : https://prove2.me/submissions/e34f5c91-113b-4eb6-bb08-79698440a356

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_form_mul_mem_twistMod_68a967b0a55b

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
theorem _root_.solution {f : Poly k N} {e : ℕ} (hf : f ∈ T.J) (he : f.IsHomogeneous e) (I : Chart x)
    {δ : Ω} (hδ : δ ∈ T.D.sub I) : ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o := by
  have hG : ∀ g ∈ {f : Poly k N | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ T.D.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f * δ = T.si * o}, g.IsHomogeneous g.totalDegree :=
    fun g ⟨c, hc, _⟩ => isHomogeneous_totalDegree hc
  have hmem := mem_span_forms_of_mem_ideal _ hG hf he
  refine Submodule.span_induction (p := fun f _ => ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o)
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨g, ⟨c, hc, hg⟩, h, d', hh, hd, rfl⟩
    by_cases h0 : g = 0
    · exact ⟨0, Submodule.zero_mem _, by rw [h0, mul_zero, map_zero, zero_mul, mul_zero]⟩
    obtain ⟨o, ho, hgo⟩ := hg I δ hδ
    rw [hc.totalDegree h0] at hd
    refine ⟨aeval x h * o, ?_, by rw [map_mul, mul_assoc, hgo, mul_left_comm]⟩
    have := form_mul_mem_twistMod hh I ho
    rwa [show (c : ℤ) + d' = e by omega] at this
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, zero_mul, mul_zero]⟩
  · rintro _ _ _ _ ⟨o, ho, h1⟩ ⟨o', ho', h2⟩
    exact ⟨o + o', Submodule.add_mem _ ho ho', by rw [map_add, add_mul, h1, h2, mul_add]⟩
  · rintro a _ _ ⟨o, ho, h1⟩
    refine ⟨a • o, (twistMod k x e I).smul_of_tower_mem a ho, ?_⟩
    rw [map_smul, smul_mul_assoc, h1, mul_smul_comm]
end StepData
end GroundTheory.Heights₂.Heights.Kleiman
