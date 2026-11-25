-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_aff_indep_da9caeaf1b77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:46.59386+00:00
-- url     : https://prove2.me/submissions/8bd30acd-2a39-4255-8b55-3916628747ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_xc_ne_zero_d6f9f1c37a1d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety
variable (K : Type) [Field K] [NumberField K] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety
theorem _root_.solution : AlgebraicIndependent ℚ (aff K n) := by
  let L := Localization.Away (X 0 : MvPolynomial (Fin (n + 1)) K)
  have hu : IsUnit (dehom K n (X 0)) := by simp [dehom]
  have hv : IsUnit (xc K n 0) := (xc_ne_zero K n 0).isUnit
  let ψ : L →+* MvPolynomial (Fin n) K := IsLocalization.Away.lift (X 0) hu
  let ι : L →+* ProjField K (n + 1) := IsLocalization.Away.lift (X 0) hv
  let s : Fin n → L := fun l =>
    IsLocalization.mk' L (X l.succ) (⟨X 0, Submonoid.mem_powers _⟩ : Submonoid.powers (X 0 : MvPolynomial (Fin (n + 1)) K))
  have hψ : ψ ∘ s = X := by
    funext l
    exact (IsLocalization.lift_mk'_spec _ _ _ _).mpr (by simp [dehom])
  have hι : ι ∘ s = aff K n := by
    funext l
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    have := xc_ne_zero K n 0
    simp only [aff]
    field_simp
  have hs : AlgebraicIndependent ℚ s := by
    refine AlgebraicIndependent.of_comp ψ.toRatAlgHom ?_
    change AlgebraicIndependent ℚ (ψ ∘ s)
    rw [hψ]
    exact (algebraicIndependent_X (Fin n) K).restrictScalars (algebraMap ℚ K).injective
  have hL : Function.Injective (algebraMap (MvPolynomial (Fin (n + 1)) K) L) :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))
  have hinj : Function.Injective ι :=
    (IsLocalization.lift_injective_iff _).mpr fun a b =>
      hL.eq_iff.trans (IsFractionRing.injective _ (ProjField K (n + 1))).eq_iff.symm
  rw [← hι]
  exact hs.map' (f := ι.toRatAlgHom) hinj
end GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety
