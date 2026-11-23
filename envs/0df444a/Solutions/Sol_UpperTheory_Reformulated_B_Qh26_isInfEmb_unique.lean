-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qh26.isInfEmb_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:41.373806+00:00
-- url     : https://prove2.me/submissions/565b791f-3099-4e34-8d31-cc4b39944d01

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInfEmbUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh26
theorem _root_.solution :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E] (τ : E →+* ℂ)
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qh26.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qh26.IsInfEmb τ θ' → θ = θ' := by
  intro F E _ _ _ _ _ τ θ θ' h h'
  have hd : DenseRange (algebraMap F (UpperTheory.Reformulated.B.Qh26.Ainf F)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have key : ∀ x : F, (algebraMap F (UpperTheory.Reformulated.B.Qh26.Ainf F) x) ⊗ₜ[F] (1 : E)
      = (1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] (algebraMap F E x) := by
    intro x
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h1 : (fun a : UpperTheory.Reformulated.B.Qh26.Ainf F ↦ θ (a ⊗ₜ[F] (1 : E)))
      = fun a : UpperTheory.Reformulated.B.Qh26.Ainf F ↦ θ' (a ⊗ₜ[F] (1 : E)) := by
    refine hd.equalizer h.2 h'.2 ?_
    funext x
    simp only [Function.comp_apply]
    rw [key, h.1, h'.1]
  refine RingHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a e =>
    have hs : a ⊗ₜ[F] e = (a ⊗ₜ[F] (1 : E)) * ((1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] e) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hs, map_mul, map_mul, h.1, h'.1, congrFun h1 a]
end UpperTheory.Reformulated.B.Qh26
