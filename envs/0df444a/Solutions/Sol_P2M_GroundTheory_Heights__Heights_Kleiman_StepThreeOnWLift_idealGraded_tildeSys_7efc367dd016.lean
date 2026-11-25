-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_tildeSys_7efc367dd016
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:36.372209+00:00
-- url     : https://prove2.me/submissions/041b457c-613c-42ca-8ff7-041a6395595e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWLift

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
open GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
theorem _root_.solution (P : Ideal (Poly k N)) : (idealGraded x P).tildeSys 0 = idealSys x P := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hm' : m ∈ Submodule.span k {z | ∃ (f : Poly k N) (e' : ℕ), f ∈ P ∧ f.IsHomogeneous e' ∧
        (e' : ℤ) = a ∧ z = aeval x f} := hm
    show (aeval x s)⁻¹ • m ∈ idealMod (x := x) P I
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ idealMod (x := x) P I)
      ?_ ?_ ?_ ?_ hm'
    · rintro _ ⟨f, e', hfP, hf, he', rfl⟩
      have hee : e' = e := by omega
      subst hee
      exact Submodule.subset_span ⟨f, s, e', hfP, hs, hf, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_of_tower_mem _ r ha
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, hfP, hs, hf, hse, rfl⟩
    exact Submodule.subset_span ⟨aeval x f, s, e, e, hs, hse,
      Submodule.subset_span ⟨f, e, hfP, hf, rfl, rfl⟩, by simp, by rw [smul_eq_mul, div_eq_inv_mul]⟩
end GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
