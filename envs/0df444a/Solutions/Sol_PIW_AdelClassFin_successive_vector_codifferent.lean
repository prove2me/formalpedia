-- Prove2me | solution 1 for PIW.AdelClassFin.successive_vector_codifferent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:38.316015+00:00
-- url     : https://prove2.me/submissions/bc9ecc91-60c1-46e8-a34f-22c12cc230ba

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorCodifferent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open NumberField
namespace PIW.AdelClassFin
theorem _root_.solution : SvCodiff := by
  intro E _ _
  refine ⟨(NumberField.discr E).natAbs, Int.natAbs_pos.2 (NumberField.discr_ne_zero E), fun y hy => ?_⟩
  have hmem : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hy a'
  have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) (b := integralBasis E)
    (fun i => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
    (Submodule.mem_one.2 ⟨1, map_one _⟩) hmem
  rw [← NumberField.coe_discr] at hint
  have hx : IsIntegral ℤ (((NumberField.discr E : ℤ) : E) * y) := by
    convert hint using 1
    rw [Algebra.smul_def, mul_one, map_intCast]
  obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (NumberField.discr E).natAbs := ⟨_, rfl⟩
  rw [← hn]
  rcases Int.natAbs_eq (NumberField.discr E) with h | h
  · rw [← hn] at h
    refine ⟨z, ?_⟩
    rw [hz, h, Int.cast_natCast]
  · rw [← hn] at h
    refine ⟨-z, ?_⟩
    rw [map_neg, hz, h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]
end PIW.AdelClassFin
