-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_isPrimitive_map_eq_C_mul_830b3b67ea86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:09:55.42796+00:00
-- url     : https://prove2.me/submissions/b6729b98-5db0-4363-a758-2d546dcaea9f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIntChowFormExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_coeff_eq_apply_9b6b5e589617

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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {σ : Type*} (g : MvPolynomial σ ℚ) (hg : g ≠ 0) :
    ∃ a : ℚ, a ≠ 0 ∧ ∃ f : MvPolynomial σ ℤ, IndefiniteRowSideFullHecke.ArithBezout.IsPrimitive f ∧
      map (Int.castRingHom ℚ) f = C a * g := by
  classical

  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ∏ m ∈ g.support, (g.coeff m).den := ⟨_, rfl⟩
  have hden : ∀ m, (g.coeff m).den ∣ d := by
    intro m
    by_cases hm : m ∈ g.support
    · rw [hd]; exact Finset.dvd_prod_of_mem _ hm
    · rw [notMem_support_iff.mp hm]; simp
  have hd0 : (d : ℚ) ≠ 0 := by
    rw [hd, Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun m _ => (g.coeff m).den_ne_zero

  let F : ℚ → ℤ := fun q => ((d / q.den : ℕ) : ℤ) * q.num
  have hF0 : F 0 = 0 := by simp [F]
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : MvPolynomial σ ℤ, ∀ m, coeff m f₀ = F (g.coeff m) :=
    exists_coeff_eq_apply F hF0 g
  have hmap₀ : map (Int.castRingHom ℚ) f₀ = C (d : ℚ) * g := by
    ext m
    rw [coeff_map, hf₀, coeff_C_mul]
    obtain ⟨k, hk⟩ := hden m
    simp only [F, eq_intCast, Int.cast_mul, Int.cast_natCast]
    rw [hk, Nat.mul_div_cancel_left _ (g.coeff m).den_pos, ← Rat.mul_den_eq_num (g.coeff m)]
    push_cast
    ring
  have hf₀ne : f₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hmap₀
    exact mul_ne_zero (C_ne_zero.mpr hd0) hg hmap₀.symm

  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℤ, c₀ = f₀.support.gcd (fun m => coeff m f₀) := ⟨_, rfl⟩
  have hc0 : c₀ ≠ 0 := by
    intro h0
    rw [h0, eq_comm, Finset.gcd_eq_zero_iff] at hc₀
    apply hf₀ne
    ext m
    by_cases hm : m ∈ f₀.support
    · simpa using hc₀ m hm
    · simpa using notMem_support_iff.mp hm
  have hdvd : ∀ m, c₀ ∣ coeff m f₀ := by
    intro m
    by_cases hm : m ∈ f₀.support
    · rw [hc₀]; exact Finset.gcd_dvd hm
    · rw [notMem_support_iff.mp hm]; exact dvd_zero _
  obtain ⟨f, hf⟩ : ∃ f : MvPolynomial σ ℤ, ∀ m, coeff m f = coeff m f₀ / c₀ :=
    exists_coeff_eq_apply (fun a => a / c₀) (by simp) f₀
  have hf₀eq : f₀ = C c₀ * f := by
    ext m
    rw [coeff_C_mul, hf, Int.mul_ediv_cancel' (hdvd m)]
  have hc0' : (c₀ : ℚ) ≠ 0 := by exact_mod_cast hc0
  refine ⟨(d : ℚ) / c₀, div_ne_zero hd0 hc0', f, fun c hc => ?_, ?_⟩
  ·
    have h1 : c * c₀ ∣ 1 * c₀ := by
      rw [one_mul]
      conv_rhs => rw [hc₀]
      refine Finset.dvd_gcd fun m _ => ?_
      rw [hf₀eq, coeff_C_mul, mul_comm c₀]
      exact mul_dvd_mul_right (hc m) c₀
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hc0).mp h1)
  · have h2 : C (c₀ : ℚ) * map (Int.castRingHom ℚ) f = C (d : ℚ) * g := by
      rw [← hmap₀, hf₀eq, map_mul, map_C, eq_intCast]
    calc map (Int.castRingHom ℚ) f = C ((c₀ : ℚ)⁻¹) * (C (c₀ : ℚ) * map (Int.castRingHom ℚ) f) := by
          rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc0', C_1, one_mul]
      _ = C ((d : ℚ) / c₀) * g := by
          rw [h2, ← mul_assoc, ← C_mul, div_eq_inv_mul]
end GroundTheory.Heights₂.Heights.ObjectsChow
