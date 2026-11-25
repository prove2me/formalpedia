-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_chart_pow_mul_eq_zero_30c9ede0b670
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:41:24.231962+00:00
-- url     : https://prove2.me/submissions/3c8031d9-fa7b-4d40-80ad-51c13b431f3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_chartPsi_comp_phi_ace8d4395081

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {D : Type*} [CommRing D] {n : ℕ}
variable (e : ℕ) (R : Type*) [CommRing R] [Algebra (MvPolynomial (Par e n) D) R]
variable (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) (S : Submonoid (MvPolynomial (Par e n) D))
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution [IsDomain D] [Q.IsPrime] [IsLocalization S R]
    (hQ : ∀ c : D, C c ∈ Q → c = 0) (c : D) (hc : c ≠ 0)
    (b : SecAlg (chartModel e R Q) (chartPar D e R))
    (hb : algebraMap R _ (algebraMap (MvPolynomial (Par e n) D) R (C c)) * b = 0) :
    ∃ N : ℕ, secCoord (chartModel e R Q) (chartPar D e R) j ^ N * b = 0 := by
  by_cases hxj : (X j : MvPolynomial (Fin n) D) ∈ Q
  · refine ⟨1, ?_⟩
    have h0 : secCoord (chartModel e R Q) (chartPar D e R) j = 0 := by
      rw [← chartKappa_X, chartKappa_eq_zero e R Q hxj]
    rw [h0, pow_one, zero_mul]
  have hx0 : chartCoordinate Q j ≠ 0 := fun h => hxj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have : IsDomain (ChartDj Q j) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  have hΦ : chartPhi e R Q j S b = 0 := by
    have h := congrArg (chartPhi e R Q j S) hb
    rw [map_mul, map_zero] at h
    have hc' : chartPhi e R Q j S (algebraMap R _ (algebraMap (MvPolynomial (Par e n) D) R (C c))) =
        algebraMap (MvPolynomial (Par e n) (ChartDj Q j)) (ChartE' e Q j S)
          (C (algebraMap _ (ChartDj Q j) (Ideal.Quotient.mk Q (C c)))) := by
      show chartPhi0 e R Q j S (C (algebraMap (MvPolynomial (Par e n) D) R (C c))) = _
      rw [chartPhi0, eval₂Hom_C, chartHomR_algebraMap]
      simp only [chartHomA, eval₂Hom_C, RingHom.comp_apply]
    rw [hc'] at h
    have hcE : (C (algebraMap _ (ChartDj Q j) (Ideal.Quotient.mk Q (C c))) :
        MvPolynomial (Par e n) (ChartDj Q j)) ≠ 0 := by
      intro h0
      have h1 := C_injective (Par e n) (ChartDj Q j) (h0.trans (map_zero C).symm)
      have h2 := IsLocalization.injective (ChartDj Q j) (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
        (h1.trans (map_zero _).symm)
      exact hc (hQ c (Ideal.Quotient.eq_zero_iff_mem.mp h2))
    by_cases h0 : (0 : MvPolynomial (Par e n) (ChartDj Q j)) ∈ S.map (chartHomA e Q j)
    · have := IsLocalization.uniqueOfZeroMem (S := ChartE' e Q j S) h0
      exact Subsingleton.elim _ _
    · have hT := le_nonZeroDivisors_of_noZeroDivisors h0
      have : IsDomain (ChartE' e Q j S) := IsLocalization.isDomain_localization hT
      refine (mul_eq_zero.mp h).resolve_left fun h3 => hcE ?_
      exact IsLocalization.injective (ChartE' e Q j S) hT (h3.trans (map_zero _).symm)
  have hB : algebraMap _ (ChartBj e R Q j) b = 0 := by
    rw [← RingHom.congr_fun (chartPsi_comp_phi e R Q j S) b, RingHom.comp_apply, hΦ, map_zero]
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (secCoord (chartModel e R Q) (chartPar D e R) j)) (ChartBj e R Q j) b).mp hB
  exact ⟨N, hN⟩
end GroundTheory.Heights₂.Heights.Vertical
