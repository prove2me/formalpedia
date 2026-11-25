-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_WeightedDegree_ringKrullDim_quotient_map_le_da526a2ebdd7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:29.975881+00:00
-- url     : https://prove2.me/submissions/c48aa48a-9e28-4156-b839-e15d32bbd3bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConservationOfNumberLE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightedHomogeneousComponentMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumbersDVR
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.WeightedDegree
variable {K : Type} {ι : K → Type} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (M₀ : Submonoid R) [IsLocalization M₀ R']
include M₀
namespace GroundTheory.Heights₂.Heights.WeightedDegree
theorem _root_.solution (I : Ideal (MRing ι R)) :
    ringKrullDim (MRing ι R' ⧸ I.map (algebraMap (MRing ι R) (MRing ι R'))) ≤
      ringKrullDim (MRing ι R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  let f : PrimeSpectrum.zeroLocus (R := MRing ι R') (I.map (algebraMap (MRing ι R) (MRing ι R'))) →
      PrimeSpectrum.zeroLocus (R := MRing ι R) I :=
    fun Q ↦ ⟨PrimeSpectrum.comap (algebraMap (MRing ι R) (MRing ι R')) Q.1, by
      have h := Q.2
      simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at h ⊢
      exact Ideal.map_le_iff_le_comap.mp h⟩
  refine Order.krullDim_le_of_strictMono f (Monotone.strictMono_of_injective ?_ ?_)
  · intro Q₁ Q₂ h
    exact Ideal.comap_mono (f := algebraMap (MRing ι R) (MRing ι R')) h
  · intro Q₁ Q₂ h
    apply Subtype.ext
    apply PrimeSpectrum.localization_comap_injective (MRing ι R') (M₀.map (C (σ := Σ k, ι k)))
    exact congrArg Subtype.val h
end GroundTheory.Heights₂.Heights.WeightedDegree
