-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ThetaCubeParseval_proof_725a8adfa3d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:04.578147+00:00
-- url     : https://prove2.me/submissions/2c30723f-8ab7-40da-a756-72ff0ecc50c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaCubeParseval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_norm_torusChar_5b8d1269a090
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_torusChar_mul_conj_7974dddcddd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_continuous_torusChar_a506262f8410
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_measureReal_cube_c63ba2eef981

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
open MeasureTheory Real ComplexConjugate
noncomputable section
open KThetaCubeParseval
namespace GroundTheory.Heights₂.Heights
namespace ThetaCubeParseval
theorem _root_.solution (h : ThetaCharIntegral.Statement) : ThetaCubeParseval.Statement := by
  intro g c hc
  set μ := volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)

  set F : (Fin g → ℤ) × (Fin g → ℤ) → (Fin g → ℝ) → ℂ :=
    fun p u => c p.1 * conj (c p.2) * torusChar (p.1 - p.2) u with hF
  have hnorm1 : ∀ u, Summable fun k => ‖c k * torusChar k u‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hnorm2 : ∀ u, Summable fun l => ‖conj (c l) * conj (torusChar l u)‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hpt : ∀ u, ((‖∑' k, c k * torusChar k u‖ ^ 2 : ℝ) : ℂ) = ∑' p, F p u := by
    intro u
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, Complex.conj_tsum]
    simp only [map_mul]
    rw [tsum_mul_tsum_of_summable_norm (hnorm1 u) (hnorm2 u)]
    congr 1
    ext p
    rw [hF]
    dsimp only
    rw [← torusChar_mul_conj]
    ring
  have hnormF : ∀ p u, ‖F p u‖ = ‖c p.1‖ * ‖c p.2‖ := by
    intro p u
    simp [hF, norm_torusChar]
  have hint : ∀ p, Integrable (F p) μ := fun p =>
    ((continuous_torusChar (p.1 - p.2)).const_smul (c p.1 * conj (c p.2))).integrableOn_Icc
  have hμ : μ.real Set.univ = 1 := measureReal_cube g
  have hsum : Summable fun p => ∫ u, ‖F p u‖ ∂μ := by
    simp only [hnormF, integral_const, hμ, one_smul]
    exact Summable.mul_of_nonneg hc hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hterm : ∀ p, ∫ u, F p u ∂μ = if p.1 - p.2 = 0 then c p.1 * conj (c p.2) else 0 := by
    intro p
    rw [hF]
    dsimp only
    rw [integral_const_mul, h g (p.1 - p.2)]
    split_ifs <;> simp
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_tsum]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hterm]
  have hinj : Function.Injective fun k : Fin g → ℤ => (k, k) := fun a b hab => (Prod.mk.inj hab).1
  rw [← hinj.tsum_eq]
  · congr 1
    ext k
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · intro p hp
    have : p.1 - p.2 = 0 := by
      by_contra hne
      exact hp (by simp [hne])
    exact ⟨p.1, Prod.ext rfl (sub_eq_zero.mp this)⟩
end ThetaCubeParseval
end GroundTheory.Heights₂.Heights
