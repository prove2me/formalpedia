-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.tT_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:20:05.635684+00:00
-- url     : https://prove2.me/submissions/33a1d571-c678-4cf7-a0f0-418dbdcb6be5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_alg_int_mem
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_tT_tmul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution (τ : E →ₗ[F] F)
    (hτ : ∀ c : 𝓞 E, ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = τ (algebraMap (𝓞 E) E c))
    (z : E ⊗[F] Af F) (hz : z ∈ IntAf F E) : tT τ z ∈ Formalism.UG.intAd F := by
  let f : 𝓞 E →ₐ[ℤ] E ⊗[F] Af F :=
    ((Formalism.UG.inclE (F := F) (Af F)).comp (algebraMap (𝓞 E) E)).toIntAlgHom
  let g : Formalism.UG.intAd F →ₐ[ℤ] E ⊗[F] Af F :=
    (((Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F) : Af F →+* E ⊗[F] Af F).comp
      (Formalism.UG.intAd F).subtype).toIntAlgHom
  have hP : ∀ w, tT τ (Algebra.TensorProduct.productMap f g w) ∈ Formalism.UG.intAd F := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      have hfg : f c * g b = (algebraMap (𝓞 E) E c) ⊗ₜ[F] (b : Af F) := by
        show ((algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] (b : Af F)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hfg, tT_tmul]
      obtain ⟨d, hd⟩ := hτ c
      rw [← hd]
      exact mul_mem (alg_int_mem F d) b.2
    | add w w' hw hw' =>
      rw [map_add, map_add]
      exact add_mem hw hw'
  have hle : IntAf F E ≤ (Algebra.TensorProduct.productMap f g).range.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨c, rfl⟩ := RingHom.mem_range.1 hx
      refine ⟨c ⊗ₜ 1, ?_⟩
      show (Algebra.TensorProduct.productMap f g) (c ⊗ₜ[ℤ] 1) = (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Af F)
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      show ((algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Af F)) *
        ((1 : E) ⊗ₜ[F] ((1 : Formalism.UG.intAd F) : Af F)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp
    · refine ⟨1 ⊗ₜ ⟨y, hy⟩, ?_⟩
      show (Algebra.TensorProduct.productMap f g) (1 ⊗ₜ[ℤ] ⟨y, hy⟩) = (1 : E) ⊗ₜ[F] y
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      show ((algebraMap (𝓞 E) E 1) ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, map_one, one_mul, one_mul]
  obtain ⟨w, rfl⟩ := (AlgHom.mem_range _).1 (Subalgebra.mem_toSubring.1 (hle hz))
  exact hP w
end PI.ScPsiExists.UnitaryGroupMassFormula
