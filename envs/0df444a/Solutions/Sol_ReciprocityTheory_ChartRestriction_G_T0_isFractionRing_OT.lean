-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_OT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:43.905972+00:00
-- url     : https://prove2.me/submissions/f1c4b50d-8522-4709-90df-0c6beaa1fb5c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution :
    letI := algOTKT (K := K) D N
    IsFractionRing (OT K D N) (KTf K D N) := by
  letI := algOTKT (K := K) D N
  have hinj : Function.Injective (algebraMap (OT K D N) (KTf K D N)) :=
    (IsFractionRing.injective (KTp K D N) (KTf K D N)).comp
      (MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K))
  haveI : FaithfulSMul (OT K D N) (KTf K D N) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (KTp K D N) z
  letI : Algebra (OT K D N) (KTp K D N) := MvPolynomial.algebraMvPolynomial
  haveI := MvPolynomial.isLocalization (σ := TVar D N) (nonZeroDivisors (𝓞 K)) K
  obtain ⟨⟨P, ⟨_, a, ha, rfl⟩⟩, hP⟩ :=
    IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := TVar D N))) p
  obtain ⟨⟨Q, ⟨_, b, hb, rfl⟩⟩, hQ⟩ :=
    IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := TVar D N))) q
  refine ⟨P * MvPolynomial.C b, Q * MvPolynomial.C a, ?_⟩
  have e : ∀ X : OT K D N, algebraMap (OT K D N) (KTf K D N) X =
      algebraMap (KTp K D N) (KTf K D N) (algebraMap (OT K D N) (KTp K D N) X) := fun X => rfl
  have hC : ∀ c ∈ nonZeroDivisors (𝓞 K),
      algebraMap (KTp K D N) (KTf K D N) (algebraMap (OT K D N) (KTp K D N) (MvPolynomial.C c)) ≠ 0 := by
    intro c hc
    rw [← e]
    exact (map_ne_zero_iff _ hinj).mpr (by
      rw [Ne, MvPolynomial.C_eq_zero]; exact nonZeroDivisors.ne_zero hc)
  have hq0 : algebraMap (KTp K D N) (KTf K D N) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K D N) (KTf K D N))).mpr
      (nonZeroDivisors.ne_zero hq)
  simp only at hP hQ
  rw [e, e, map_mul, map_mul, map_mul, map_mul, ← hP, ← hQ, map_mul, map_mul]
  have ha := hC a ha
  have hb := hC b hb
  field_simp
end ReciprocityTheory.ChartRestriction.G.T0
