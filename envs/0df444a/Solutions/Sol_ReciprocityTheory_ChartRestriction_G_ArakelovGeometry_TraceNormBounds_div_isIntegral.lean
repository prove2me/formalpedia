-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.div_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:42.315708+00:00
-- url     : https://prove2.me/submissions/2fe5e1b9-cac5-4624-8078-5ae93dfe49aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisFurther
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_aeval_mem_field
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_div_mem_fnField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) (i : κ) :
    IsIntegral (fnField (x ∘ e)) (x i / x (e 0)) := by
  set y := x ∘ e with hy
  let ψ : Polynomial Ω →+* Ω := Polynomial.evalRingHom (y 0)⁻¹
  change IsIntegral _ (x i / y 0)
  have hev : ∀ f : MvPolynomial (Fin (D + 1)) ℚ,
      ψ (coneMap ℚ y f) = MvPolynomial.aeval (fun k => y k * (y 0)⁻¹) f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [coneMap, ψ]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p k hp => rw [map_mul, map_mul, map_mul, hp]; simp [coneMap, ψ]
  have hmem : ∀ r : coneRing ℚ y, ψ r ∈ fnField y := by
    intro r
    obtain ⟨f, hf⟩ := r.2
    rw [← hf]
    change ψ (coneMap ℚ y f) ∈ _
    rw [hev]
    refine aeval_mem_field _ (fun a => IntermediateField.algebraMap_mem _ a) _ (fun k => ?_) f
    simpa [div_eq_mul_inv] using div_mem_fnField y k 0
  let φ : coneRing ℚ y →+* fnField y :=
    (ψ.comp (coneRing ℚ y).val.toRingHom).codRestrict (fnField y).toSubfield.toSubring hmem
  have := IsIntegral.map_of_comp_eq φ ψ (by ext r; rfl) (h.integral i)
  simpa [ψ, div_eq_mul_inv] using this
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
