-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coord_div_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:48.566583+00:00
-- url     : https://prove2.me/submissions/68acc3f3-8167-46e4-9ebe-9ba8207f89bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coord_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_coord_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK

set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField
variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) (i : ι) :
    IsIntegral (chartRing (x ∘ e)) (x i / x (e 0)) := by
  set y := x ∘ e with hy
  change IsIntegral _ (x i / y 0)
  have hl : y 0 ≠ 0 := coord_ne_zero y h.free 0
  have hinj : Function.Injective (coneMap ℤ y) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have : f ∈ coordIdeal ℤ y := by rw [coordIdeal, RingHom.mem_ker]; exact hf
    rwa [h.free, Ideal.mem_bot] at this
  let eqv : MvPolynomial (Fin (D + 1)) ℤ ≃ₐ[ℤ] coneRing ℤ y := AlgEquiv.ofInjective (coneMap ℤ y) hinj
  let w : Fin (D + 1) → chartRing y := fun k =>
    if hk : k = 0 then 1 else ⟨chartGen y ⟨k, hk⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩
  have hw : ∀ k, algebraMap (chartRing y) Ω (w k) = y k * (y 0)⁻¹ := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [w, mul_inv_cancel₀ hl]
    · simp only [w, dif_neg hk]
      change y k / y 0 = _
      exact div_eq_mul_inv _ _
  let ψ : Polynomial Ω →+* Ω := Polynomial.evalRingHom (y 0)⁻¹
  have hev : ∀ f : MvPolynomial (Fin (D + 1)) ℤ,
      ψ (coneMap ℤ y f) = MvPolynomial.aeval (fun k => y k * (y 0)⁻¹) f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [coneMap, ψ]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p k hp => rw [map_mul, map_mul, map_mul, hp]; simp [coneMap, ψ]
  let φ : coneRing ℤ y →+* chartRing y :=
    (MvPolynomial.aeval w).toRingHom.comp eqv.symm.toAlgHom.toRingHom
  have hrel : (algebraMap (chartRing y) Ω).comp φ = ψ.comp (algebraMap (coneRing ℤ y) _) := by
    ext r
    obtain ⟨f, rfl⟩ := eqv.surjective r
    have h1 : ((eqv f : coneRing ℤ y) : Polynomial Ω) = coneMap ℤ y f := rfl
    change algebraMap _ Ω (MvPolynomial.aeval w (eqv.symm (eqv f))) =
      ψ ((eqv f : coneRing ℤ y) : Polynomial Ω)
    rw [eqv.symm_apply_apply, h1, hev, ← MvPolynomial.aeval_algebraMap_apply,
      show (⇑(algebraMap (chartRing y) Ω) ∘ w) = fun k => y k * (y 0)⁻¹ from funext hw]
  have := IsIntegral.map_of_comp_eq φ ψ hrel (h.integral i)
  simpa [ψ, div_eq_mul_inv] using this
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
