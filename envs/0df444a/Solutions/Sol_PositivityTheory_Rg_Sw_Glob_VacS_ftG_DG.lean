-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.Glob.VacS.ftG_DG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:24.351654+00:00
-- url     : https://prove2.me/submissions/6f740585-27a3-462c-bdc4-262ad20def18

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_GaussScalar
import Theorems.Thm_PositivityTheory_Rg_Sw_Glob_VacS_gauss_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS
namespace PositivityTheory.Rg.Sw.Glob.VacS
theorem _root_.solution {m n : ℕ} (σ : Fin m → ℝ) (s : ℝ) (K : ℂ) (γ : Fin m → Fin n → ℂ) (hγ : ∀ a j, 0 < (γ a j).re)
    (u : Fin m → Fin n → ℂ) :
    ftG σ s (DG K γ) u = DG (K * ∏ a, ∏ j, ((Real.pi : ℂ) / γ a j))
      (fun a j => (s : ℂ) ^ 2 * ((σ a : ℂ) ^ 2) / γ a j) u := by
  have hk : ∀ y : Fin m → Fin n → ℂ, DG K γ y *
      cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ)) =
      K * ∏ a, ∏ j, (cexp (-γ a j * ((‖y a j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ))) := by
    intro y
    unfold DG
    have e : cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ)) =
        ∏ a, ∏ j, cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ)) := by
      rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      congr 2
      rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
      all_goals (push_cast; try ring)
    rw [e, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_mul_distrib]
  unfold ftG
  simp_rw [hk]
  rw [integral_const_mul]
  have hI : ∫ y : Fin m → Fin n → ℂ, ∏ a, ∏ j, (cexp (-γ a j * ((‖y a j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ))) =
      ∏ a, ∏ j, (((Real.pi : ℂ) / γ a j) * cexp (-((s : ℂ) ^ 2) * ((‖(σ a : ℂ) * u a j‖ ^ 2 : ℝ) : ℂ) / γ a j)) := by
    rw [integral_fintype_prod_volume_eq_prod (f := fun a (x : Fin n → ℂ) => ∏ j, (cexp (-γ a j * ((‖x j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * x j).re : ℂ))))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [integral_fintype_prod_volume_eq_prod (f := fun j (z : ℂ) => (cexp (-γ a j * ((‖z‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * z).re : ℂ))))]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact gauss_scalar _ (hγ a j) s _
  rw [hI]
  unfold DG
  rw [mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  congr 1
  rw [norm_mul, Complex.norm_real]
  push_cast
  have hg : γ a j ≠ 0 := by
    intro h0; have := hγ a j; rw [h0] at this; simp at this
  field_simp
  rw [Real.norm_eq_abs]
  have hs : ((|σ a| : ℝ) : ℂ) ^ 2 = ((σ a : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  push_cast
  rw [hs]
  ring
end PositivityTheory.Rg.Sw.Glob.VacS
