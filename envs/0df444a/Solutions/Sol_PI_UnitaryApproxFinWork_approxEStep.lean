-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.approxEStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:18.016414+00:00
-- url     : https://prove2.me/submissions/b47cf584-468b-4e72-922a-aa681e70e81e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_ApproxE
import Theorems.Thm_PI_UnitaryApproxFinWork_exists_span_int
import Theorems.Thm_PI_UnitaryApproxFinWork_tensor_decomp
import Theorems.Thm_PI_UnitaryApproxFinWork_inclE_mem_Sv
import Theorems.Thm_PI_UnitaryApproxFinWork_one_tmul_mem_Sv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution : ApproxEStep := by
  intro hW
  unfold ApproxE
  intro F E _ _ _ _ _ T x D hD
  obtain ⟨d, b, hbint, hb⟩ := exists_span_int (F := F) (E := E)
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : Fin d → v.adicCompletion F,
      x v = ∑ k, b k ⊗ₜ[F] c k := fun v => tensor_decomp b hb (x v)
  choose c hc using hc
  have ha : ∀ k, ∃ a : F, ∀ v ∈ T, ∃ t ∈ v.adicCompletionIntegers F,
      c v k - algebraMap F (v.adicCompletion F) a = algebraMap F (v.adicCompletion F) (D : F) * t :=
    fun k => hW F T (fun v => c v k) D hD
  choose a ht using ha
  refine ⟨∑ k, a k • b k, fun v hv => ?_⟩
  choose t htO hteq using fun k => ht k v hv
  refine ⟨∑ k, (1 : E) ⊗ₜ[F] t k * PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (b k), ?_, ?_⟩
  · exact Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (one_tmul_mem_Sv v (htO k)) (inclE_mem_Sv v (hbint k))
  · rw [hc v, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [PI.UnitaryApproxDefs.inclE, dv, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [TensorProduct.smul_tmul, ← TensorProduct.tmul_sub, Algebra.smul_def (a k), mul_one, hteq k,
      ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]
end PI.UnitaryApproxFinWork
