-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericFibProps_proof_2daf7a7447fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:43.038151+00:00
-- url     : https://prove2.me/submissions/526bd93d-52e0-44a5-9891-cbd7edba722f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericFibProps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_map_2b7a12218846

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace GenericFibProps
theorem _root_.solution : GenericFibProps.Statement := by
  intro O _ _ _ K _ _ ι _ P hP hT
  set φ := algebraMap O (FractionRing O) with hφ
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C (σ := Σ k, ι k))
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  have hmap : algebraMap (MRing ι O) (MRing ι (FractionRing O)) = MvPolynomial.map φ := rfl
  have hdisj : Disjoint (M : Set (MRing ι O)) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmP
    have : m ∈ P.comap (C : O →+* MRing ι O) := hmP
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hm this
  have hgen : genFib P = Ideal.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) P := rfl
  have hprime : (genFib P).IsPrime :=
    hgen ▸ IsLocalization.isPrime_of_isPrime_disjoint M _ P hP.isPrime hdisj
  have hunder : (genFib P).comap (MvPolynomial.map φ) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O)) hP.isPrime hdisj
  refine ⟨hprime, ?_, ?_⟩
  · intro x hx b
    rw [hgen, IsLocalization.mem_map_algebraMap_iff M] at hx
    obtain ⟨⟨⟨p, hp⟩, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := hx
    simp only [hmap, map_C] at h
    have hm0 : φ m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    have hx' : x = C (φ m)⁻¹ * MvPolynomial.map φ p := by
      rw [← h, mul_comm x, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]
    rw [hx', weightedHomogeneousComponent_C_mul, weightedHomogeneousComponent_map]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hP.multiHomog p hp b))
  · intro s c hs hsP
    refine ⟨?_, ?_⟩
    · intro d hd
      apply hs
      intro h0
      rw [coeff_map, h0, map_zero] at hd
      exact hd rfl
    · intro h
      apply hsP
      rw [← hunder]
      exact h
end GenericFibProps
end GroundTheory.Heights₂.Heights.NumbersDVR
