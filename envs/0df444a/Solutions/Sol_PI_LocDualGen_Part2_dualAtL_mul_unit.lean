-- Prove2me | solution 1 for PI.LocDualGen.Part2.dualAtL_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:17.429904+00:00
-- url     : https://prove2.me/submissions/8bca98dc-68c8-469a-8854-15e25a6b7cca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit
import Theorems.Thm_PI_LocDualGen_Part2_alg_mem_O

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocDualGen PI.LocDualGen.Part2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)
namespace PI.LocDualGen.Part2
theorem _root_.solution (δ : A.Fp) (u : 𝒪[A.Fp]) (hu : IsUnit u) (h : DualAtL A δ) :
    DualAtL A (δ * (u : A.Fp)) := by
  intro x
  rw [← h x]
  obtain ⟨v, rfl⟩ := hu
  have hv : ((v : 𝒪[A.Fp]) : A.Fp) * ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  set a := algebraMap A.Fp A.Ep ((v : 𝒪[A.Fp]) : A.Fp)
  set b := algebraMap A.Fp A.Ep ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp)
  have hab : a * b = 1 := by rw [← map_mul, hv, map_one]
  have hinv : (((v : 𝒪[A.Fp]) : A.Fp))⁻¹ = ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp) :=
    inv_eq_of_mul_eq_one_right hv
  have key : algebraMap A.Fp A.Ep (δ * ((v : 𝒪[A.Fp]) : A.Fp))⁻¹ = algebraMap A.Fp A.Ep δ⁻¹ * b := by
    rw [mul_inv, map_mul, hinv]
  constructor
  · intro H y hy
    have := H (y * a) (A.O.mul_mem hy (alg_mem_O A _))
    rwa [key, show x * (y * a) * (algebraMap A.Fp A.Ep δ⁻¹ * b) = x * y * algebraMap A.Fp A.Ep δ⁻¹ * (a * b) by ring,
      hab, mul_one] at this
  · intro H y hy
    have := H (y * b) (A.O.mul_mem hy (alg_mem_O A _))
    rwa [key, show x * y * (algebraMap A.Fp A.Ep δ⁻¹ * b) = x * (y * b) * algebraMap A.Fp A.Ep δ⁻¹ by ring]
end PI.LocDualGen.Part2
