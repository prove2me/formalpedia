-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_integralModel_genericIdeal_df324174d2b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:06:49.461889+00:00
-- url     : https://prove2.me/submissions/5dbb6eef-8016-4e88-90b1-8d30520ab1f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_comap_C_e18d6e2b5341

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
theorem _root_.solution (P : Ideal (MRing (PBlk n))) [hP : P.IsPrime]
    (hh : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal P) :
    integralModel (genericIdeal P) = P.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)) := by
  set J := IndefiniteRowSideFullHecke.ArithBezout.finIdeal P with hJdef
  haveI hJ : J.IsPrime := Ideal.comap_isPrime _ _
  have hJC : J.comap (C : ℤ →+* MvPolynomial (Fin n) ℤ) = ⊥ := by
    rw [hJdef, finIdeal_comap_C]
    exact hh
  have key : (J.map (MvPolynomial.map (Int.castRingHom ℚ))).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) = J := by
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) :=
      MvPolynomial.algebraMvPolynomial
    haveI : IsLocalization ((nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ))
        (MvPolynomial (Fin n) ℚ) := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors ℤ) ℚ
    have hdisj : Disjoint (((nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ) :
        Submonoid (MvPolynomial (Fin n) ℤ)) : Set (MvPolynomial (Fin n) ℤ)) J := by
      refine Set.disjoint_left.mpr fun x hx hxJ => ?_
      obtain ⟨a, ha, rfl⟩ := hx
      have : a ∈ J.comap (C : ℤ →+* MvPolynomial (Fin n) ℤ) := hxJ
      rw [hJC, Ideal.mem_bot] at this
      exact nonZeroDivisors.ne_zero ha this
    have := IsLocalization.under_map_of_isPrime_disjoint
      ((nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ)) (MvPolynomial (Fin n) ℚ) hJ hdisj
    exact this
  have hm : ∀ f : MvPolynomial (Fin n) (𝓞 ℚ),
      MvPolynomial.map (algebraMap (𝓞 ℚ) ℚ) f =
        MvPolynomial.map (Int.castRingHom ℚ) (MvPolynomial.map (ι.symm : 𝓞 ℚ →+* ℤ) f) := by
    intro f
    have e : algebraMap (𝓞 ℚ) ℚ = (Int.castRingHom ℚ).comp (ι.symm : 𝓞 ℚ →+* ℤ) := by
      ext z
      simp [Rat.ringOfIntegersEquiv_apply_coe]
    rw [MvPolynomial.map_map, ← e]
  ext f
  rw [integralModel, Ideal.mem_comap, hm, ← Ideal.mem_comap, genericIdeal, ← hJdef, key, hJdef,
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rfl
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
