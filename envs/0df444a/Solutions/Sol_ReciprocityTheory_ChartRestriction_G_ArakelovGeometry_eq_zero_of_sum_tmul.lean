-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_zero_of_sum_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:35.043267+00:00
-- url     : https://prove2.me/submissions/6c96ba9c-5c8e-463e-8ce9-bf677229a838

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Jacobson.Ring
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {Ω E : Type*} [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E] {r : ℕ}
    {s : Fin r → Ω} (hs : LinearIndependent ℚ s) {e : Fin r → E}
    (h : ∑ k, e k ⊗ₜ[ℚ] s k = 0) : e = 0 := by
  classical
  let W := Submodule.span ℚ (Set.range s)
  let 𝒞 : Module.Basis (Fin r) ℚ W := Module.Basis.span hs
  have hinj : Function.Injective (LinearMap.lTensor E W.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective
  have h0 : (∑ k, e k ⊗ₜ[ℚ] 𝒞 k : E ⊗[ℚ] W) = 0 := by
    apply hinj
    rw [map_sum, map_zero]
    have hc : ∀ k, ((𝒞 k : W) : Ω) = s k := fun k => by
      show ((Module.Basis.span hs k : W) : Ω) = s k
      rw [Module.Basis.span_apply]
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, hc]
    exact h
  have hb := TensorProduct.sum_tmul_basis_right_eq_zero 𝒞 (Finsupp.equivFunOnFinite.symm e) (by
    rw [Finsupp.sum_fintype _ _ (by intros; simp)]
    simpa using h0)
  funext k
  have hk := congrArg (fun b => b k) hb
  simpa using hk
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
