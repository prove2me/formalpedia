-- Prove2me | solution 1 for PI.SqPairLocal.RU.exists_conjugation_fixed_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:27.124676+00:00
-- url     : https://prove2.me/submissions/dcf6b4f7-5d6f-4af2-9121-e8e261e1dc83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsConjugationFixedUniformizer
import Theorems.Thm_PI_SqPairLocal_RU_cj_coe
import Theorems.Thm_PI_SqPairLocal_RU_cj_cj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal PI.SqPairLocal.RU
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal.RU
theorem _root_.solution (hE : PI.IsCMUnram E) (Q : Ideal (𝓞 E)) (hQ : Q.IsMaximal)
    (hc : Q.comap (cj E) = Q) : ∃ ϖ : 𝓞 E, cj E ϖ = ϖ ∧ ϖ ∈ Q ∧ ϖ ∉ Q ^ 2 := by
  have hcQ : ∀ y ∈ Q, cj E y ∈ Q := fun y hy => by
    rw [← Ideal.mem_comap, hc]; exact hy
  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField E)
  have hlt : Q ^ 2 < Q := by
    have := @Ideal.pow_succ_lt_pow _ _ _ Q hQ.isPrime hQ0 1
    rwa [pow_one] at this
  obtain ⟨x, hxQ, hx2⟩ := SetLike.exists_of_lt hlt
  obtain ⟨θ, t, ht, hθt⟩ := hE.2.2 Q hQ
  have htc : t = cj E θ := by
    apply RingOfIntegers.ext
    rw [cj_coe]
    exact ht
  subst htc
  have hrad : (Q ^ 2).radical = Q := by
    rw [Ideal.radical_pow _ two_ne_zero, hQ.isPrime.radical]
  have hprim : ∀ y, (θ - cj E θ) * y ∈ Q ^ 2 → y ∈ Q ^ 2 := by
    intro y hy
    have hP : (Q ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hQ)
    rw [mul_comm] at hy
    rcases (Ideal.isPrimary_iff.mp hP).2 hy with h | h
    · exact h
    · rw [hrad] at h
      exact absurd h hθt
  have hfix : ∀ y, cj E (y + cj E y) = y + cj E y := fun y => by
    rw [map_add, cj_cj, add_comm]
  have hcomb : (θ * x + cj E (θ * x)) - cj E θ * (x + cj E x) = (θ - cj E θ) * x := by
    rw [map_mul]; ring
  by_cases h2 : x + cj E x ∈ Q ^ 2
  · refine ⟨θ * x + cj E (θ * x), hfix _, ?_, ?_⟩
    · exact Q.add_mem (Q.mul_mem_left θ hxQ) (hcQ _ (Q.mul_mem_left θ hxQ))
    · intro h1
      apply hx2
      apply hprim
      rw [← hcomb]
      exact (Q ^ 2).sub_mem h1 ((Q ^ 2).mul_mem_left _ h2)
  · exact ⟨x + cj E x, hfix _, Q.add_mem hxQ (hcQ _ hxQ), h2⟩
end PI.SqPairLocal.RU
