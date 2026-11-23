-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qf27.infEmb_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:35:44.756902+00:00
-- url     : https://prove2.me/submissions/e682f7e7-5ffb-42d9-895a-5cd3b2616d78

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfEmbUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf27
theorem _root_.solution :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] {τ : E →+* ℂ}
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ' → θ = θ' := by
  intro F E _ _ _ _ τ θ θ' h h'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hd : DenseRange (algebraMap F (UpperTheory.Reformulated.B.Qf27.Ainf F)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have key : ∀ c : F, (algebraMap F (UpperTheory.Reformulated.B.Qf27.Ainf F) c) ⊗ₜ[F] (1 : E)
      = (1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] (algebraMap F E c) := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hA : (fun a : UpperTheory.Reformulated.B.Qf27.Ainf F ↦ θ (a ⊗ₜ[F] (1 : E)))
      = fun a : UpperTheory.Reformulated.B.Qf27.Ainf F ↦ θ' (a ⊗ₜ[F] (1 : E)) := by
    refine hd.equalizer h2 h2' ?_
    funext c
    simp only [Function.comp_apply]
    rw [key, h1, h1']
  refine RingHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x =>
    have e : a ⊗ₜ[F] x = (a ⊗ₜ[F] (1 : E)) * ((1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h1, h1', congrFun hA a]
end UpperTheory.Reformulated.B.Qf27
