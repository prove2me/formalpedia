-- Prove2me | solution 1 for PI.ET.horn_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:02.912129+00:00
-- url     : https://prove2.me/submissions/65617a94-3c30-4229-b091-f6abbab3909a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
import Theorems.Thm_PI_ET_HornW_unit_star_mul
import Theorems.Thm_PI_ET_HornW_conj_herm
import Theorems.Thm_PI_ET_HornW_exp_conj
import Theorems.Thm_PI_ET_HornW_norm_det_conj_exp
import Theorems.Thm_PI_ET_HornW_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open HornW
namespace PI.ET
theorem _root_.solution (hK : KyFanDet) : Horn := by
  intro n X Y Z U ξ η ζ hX hY hZ hU hE
  obtain ⟨hξ, Wx, hWx, rfl⟩ := hX
  obtain ⟨hη, Wy, hWy, rfl⟩ := hY
  obtain ⟨hζ, Wz, hWz, rfl⟩ := hZ
  rw [exp_conj hWx, exp_conj hWy, exp_conj hWz] at hE
  have hcc : (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) = (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) := by
    have h1 : ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ))ᴴ * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) = (U * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ))ᴴ * (U * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ)) := by rw [hE]
    rw [conjTranspose_mul (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), conjTranspose_mul U (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ), conj_herm, conj_herm, conj_herm] at h1
    calc (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) = (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Uᴴ * U) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) := by rw [unit_star_mul hU, Matrix.mul_one]
      _ = (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) := by simp only [Matrix.mul_assoc]
  refine ⟨fun k hk => key hK hWx hWy hWz hξ hη hcc k hk, ?_⟩
  have hd : ‖((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)).det‖ = ‖(U * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ)).det‖ := by rw [hE]
  have hUd : ‖U.det‖ = 1 := by
    have h2 : ‖star U.det * U.det‖ = 1 := by
      rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, unit_star_mul hU, Matrix.det_one, norm_one]
    rw [norm_mul, norm_star] at h2
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · linarith [norm_nonneg U.det]
  rw [Matrix.det_mul (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), Matrix.det_mul U (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ), norm_mul, norm_mul, norm_det_conj_exp hWx,
    norm_det_conj_exp hWy, norm_det_conj_exp hWz, hUd, one_mul, ← Real.exp_add] at hd
  rw [Finset.sum_add_distrib]
  exact (Real.exp_injective hd).symm
end PI.ET
