-- Prove2me | solution 1 for PI.RayBoundIQW.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:33.589699+00:00
-- url     : https://prove2.me/submissions/733682bc-e25a-42e2-b596-e10f48bf6a59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_GenCoprime
import Theorems.Thm_PI_RayBoundIQW_gen_spec
import Theorems.Thm_PI_RayBoundIQW_gen_ne_zero
import Theorems.Thm_PI_RayBoundIQW_gen_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open PI PI.RayBoundIQW
variable {K0 : Type} [Field K0] [NumberField K0] (qq : Ideal (𝓞 K0))
namespace PI.RayBoundIQW
theorem _root_.solution (hre : IsEmpty (K0 →+* ℝ)) (J J' : PrimeTo qq) (h : inv qq J = inv qq J') :
    rayRel K0 qq J J' := by
  have hc : cls qq J = cls qq J' := congrArg Prod.fst h
  have hr : Ideal.Quotient.mk qq (gen qq J) = Ideal.Quotient.mk qq (gen qq J') :=
    congrArg Prod.snd h
  have hJ := gen_spec qq J
  have hJ' := gen_spec qq J'
  rw [← hc] at hJ'
  have hdiff : gen qq J - gen qq J' ∈ qq := Ideal.Quotient.eq.mp hr
  have hmul : Ideal.span {gen qq J'} * J.1 = Ideal.span {gen qq J} * J'.1 := by
    rw [hJ, hJ']; ring
  obtain ⟨t, q, hq, htq⟩ := Ideal.mem_span_singleton_sup.mp
    ((gen_coprime qq J).symm ▸ Submodule.mem_top : (1 : 𝓞 K0) ∈ Ideal.span {gen qq J} ⊔ qq)
  by_cases ht : t = 0
  · have htop : qq = ⊤ := by
      rw [Ideal.eq_top_iff_one]; rw [ht, zero_mul, zero_add] at htq; exact htq ▸ hq
    refine ⟨gen qq J', gen qq J, gen_ne_zero qq J', gen_ne_zero qq J, ?_, ?_, ?_, hmul⟩
    · exact (mul_one (gen qq J' - 1)) ▸ qq.mul_mem_left _ ((Ideal.eq_top_iff_one qq).mp htop)
    · exact (mul_one (gen qq J - 1)) ▸ qq.mul_mem_left _ ((Ideal.eq_top_iff_one qq).mp htop)
    · intro σ; exact isEmptyElim σ
  · refine ⟨t * gen qq J', t * gen qq J, mul_ne_zero ht (gen_ne_zero qq J'),
      mul_ne_zero ht (gen_ne_zero qq J), ?_, ?_, ?_, ?_⟩
    · have e : t * gen qq J' - 1 = (-t) * (gen qq J - gen qq J') + -q := by
        linear_combination htq
      rw [e]; exact qq.add_mem (qq.mul_mem_left _ hdiff) (qq.neg_mem hq)
    · have e : t * gen qq J - 1 = -q := by linear_combination htq
      rw [e]; exact qq.neg_mem hq
    · intro σ; exact isEmptyElim σ
    · rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
        mul_assoc, mul_assoc, hmul]
end PI.RayBoundIQW
