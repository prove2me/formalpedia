-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_kill_499fcffa6e8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:13.225622+00:00
-- url     : https://prove2.me/submissions/13b4e452-00f4-4480-9a08-306887063075

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
theorem _root_.solution {J : Ideal (Poly k N)} (P : Ideal (Poly k N)) (Jg : FinGradedSub (S := k) (x := x) Ω)
    (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ J ∧
      f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) :
    ∀ (f : Poly k N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ (idealGraded x P).piece a, aeval x f • z ∈ Jg.piece (a + e) := by
  intro f e hf hfe a z hz
  have hz' : z ∈ Submodule.span k {z | ∃ (g : Poly k N) (e' : ℕ), g ∈ P ∧ g.IsHomogeneous e' ∧
      (e' : ℤ) = a ∧ z = aeval x g} := hz
  rw [hJg]
  refine Submodule.span_induction (p := fun z _ => aeval x f • z ∈ Submodule.span k {z |
    ∃ (f : Poly k N) (e'' : ℕ), f ∈ J ∧ f.IsHomogeneous e'' ∧ (e'' : ℤ) = a + e ∧ z = aeval x f})
    ?_ ?_ ?_ ?_ hz'
  · rintro _ ⟨g, e', -, hg, he', rfl⟩
    exact Submodule.subset_span ⟨f * g, e + e', J.mul_mem_right g hf, hfe.mul hg,
      by push_cast; omega, by rw [map_mul, smul_eq_mul]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha
end GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
