-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.unfold_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:56.476664+00:00
-- url     : https://prove2.me/submissions/4d9c9474-4da4-43f9-b343-b42303444ea5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_DetMEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_key2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
private theorem paTh_add_lattice {Y : GT ι} {q : ℕ} (hC : Coc Y q) (F : EuclideanSpace ℂ ι → ℂ)
    (x : EuclideanSpace ℂ ι) (g : lat Y.b) :
    paTh Y q F ((g : EuclideanSpace ℂ ι) + x) =
      Y.ka g * cexp (q * Real.pi * Hf x g + q * Real.pi * Hf (g : EuclideanSpace ℂ ι) g / 2) *
        paTh Y q F x := by
  have hH : ∀ v w : EuclideanSpace ℂ ι, Hf v w = inner ℂ w v := fun v w => by
    rw [Hf, PiLp.inner_apply]
    try rfl
  simp only [paTh]
  rw [← tsum_mul_left, ← (Equiv.addLeft g).tsum_eq
    (fun γ : lat Y.b => Y.ka γ * paU q γ F ((g : EuclideanSpace ℂ ι) + x))]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_addLeft, Submodule.coe_add]
  rw [hC g g.2 γ γ.2]
  simp only [paU]
  have harg : (g : EuclideanSpace ℂ ι) + x - ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) =
      x - γ := by abel
  rw [harg]
  have hAB : -((Real.pi : ℂ) * (q : ℂ) * ((Hf (g : EuclideanSpace ℂ ι) (γ : EuclideanSpace ℂ ι)).im : ℂ)) * I +
      ((q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + x) ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) -
        (q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι))
          ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) / 2) =
      ((q : ℂ) * (Real.pi : ℂ) * Hf x g + (q : ℂ) * (Real.pi : ℂ) * Hf (g : EuclideanSpace ℂ ι) g / 2) +
      ((q : ℂ) * (Real.pi : ℂ) * Hf x γ - (q : ℂ) * (Real.pi : ℂ) * Hf (γ : EuclideanSpace ℂ ι) γ / 2) := by
    simp only [hH, inner_add_left, inner_add_right]
    have hc : inner ℂ (g : EuclideanSpace ℂ ι) (γ : EuclideanSpace ℂ ι) =
        (starRingEnd ℂ) (inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι)) :=
      (inner_conj_symm _ _).symm
    have hre : (starRingEnd ℂ) (inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι)) =
        inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι) -
          2 * ((inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι)).im : ℂ) * I := by
      have hs := Complex.sub_conj (inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι))
      push_cast at hs
      linear_combination -hs
    rw [hc, hre]
    ring
  have key : cexp (-((Real.pi : ℂ) * (q : ℂ) * ((Hf (g : EuclideanSpace ℂ ι) (γ : EuclideanSpace ℂ ι)).im : ℂ)) * I) *
      cexp ((q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + x) ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) -
        (q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι))
          ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) / 2) =
      cexp ((q : ℂ) * (Real.pi : ℂ) * Hf x g + (q : ℂ) * (Real.pi : ℂ) * Hf (g : EuclideanSpace ℂ ι) g / 2) *
      cexp ((q : ℂ) * (Real.pi : ℂ) * Hf x γ - (q : ℂ) * (Real.pi : ℂ) * Hf (γ : EuclideanSpace ℂ ι) γ / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hAB]
  linear_combination (Y.ka g * Y.ka γ * F (x - γ)) * key
private theorem ka_neg_eq_conj {Y : GT ι} {q : ℕ} (hC : Coc Y q) (g : lat Y.b) :
    Y.ka (-(g : EuclideanSpace ℂ ι)) = (starRingEnd ℂ) (Y.ka g) := by
  have h0 : Y.ka 0 = 1 := by
    have h00 := hC 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
    have hz : Hf (0 : EuclideanSpace ℂ ι) (0 : EuclideanSpace ℂ ι) = 0 := by simp [Hf]
    rw [add_zero, hz, Complex.zero_im] at h00
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one] at h00
    have hn : Y.ka 0 ≠ 0 := by
      intro h
      have h1 := Y.ka_abs 0 (Submodule.zero_mem _)
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    exact mul_left_cancel₀ hn (h00.symm.trans (mul_one _).symm)
  have hneg : (Hf (g : EuclideanSpace ℂ ι) (-(g : EuclideanSpace ℂ ι))).im = 0 := by
    have e1 : Hf (g : EuclideanSpace ℂ ι) (-(g : EuclideanSpace ℂ ι)) =
        -Hf (g : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι) := by
      simp [Hf, Finset.sum_neg_distrib]
    rw [e1, Complex.neg_im, neg_eq_zero]
    simp [Hf, Complex.mul_conj, Complex.im_sum]
  have hg := hC (g : EuclideanSpace ℂ ι) g.2 (-(g : EuclideanSpace ℂ ι)) (Submodule.neg_mem _ g.2)
  rw [add_neg_cancel, h0, hneg] at hg
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one] at hg
  have hconj : (starRingEnd ℂ) (Y.ka g) * Y.ka g = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Y.ka_abs g g.2]
    norm_num
  calc Y.ka (-(g : EuclideanSpace ℂ ι))
      = ((starRingEnd ℂ) (Y.ka g) * Y.ka g) * Y.ka (-(g : EuclideanSpace ℂ ι)) := by
        rw [hconj, one_mul]
    _ = (starRingEnd ℂ) (Y.ka g) * (Y.ka g * Y.ka (-(g : EuclideanSpace ℂ ι))) := by ring
    _ = (starRingEnd ℂ) (Y.ka g) := by rw [← hg, mul_one]
end
end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution {Y : GT ι} {q : ℕ} (hC : Coc Y q) (F : EuclideanSpace ℂ ι → ℂ) (x : EuclideanSpace ℂ ι) :
    ∑' g : lat Y.b, thF Y q F (g +ᵥ x) = ((‖paTh Y q F x‖ ^ 2 * paW q x : ℝ) : ℂ) := by
  have hpt : ∀ g : lat Y.b, thF Y q F (g +ᵥ x) =
      paTh Y q F x * (paW q x : ℂ) *
        (starRingEnd ℂ) (Y.ka (-(g : EuclideanSpace ℂ ι)) * paU q (-(g : EuclideanSpace ℂ ι)) F x) := by
    intro g
    have hv : (g +ᵥ x : EuclideanSpace ℂ ι) = (g : EuclideanSpace ℂ ι) + x := rfl
    rw [hv]
    unfold thF
    rw [paTh_add_lattice hC F x g, ka_neg_eq_conj hC g]
    have hk := key2 q (g : EuclideanSpace ℂ ι) x
    rw [add_comm x (g : EuclideanSpace ℂ ι)] at hk
    simp only [paU, map_mul, Complex.conj_conj, sub_neg_eq_add]
    rw [add_comm x (g : EuclideanSpace ℂ ι)]
    linear_combination (Y.ka g * paTh Y q F x * (starRingEnd ℂ) (F ((g : EuclideanSpace ℂ ι) + x))) * hk
  rw [tsum_congr hpt, tsum_mul_left]
  have hsum : ∑' g : lat Y.b,
      (starRingEnd ℂ) (Y.ka (-(g : EuclideanSpace ℂ ι)) * paU q (-(g : EuclideanSpace ℂ ι)) F x) =
      (starRingEnd ℂ) (paTh Y q F x) := by
    simp only [paTh]
    rw [starRingEnd_apply, tsum_star]
    rw [← (Equiv.neg (lat Y.b)).tsum_eq (fun g : lat Y.b => star (Y.ka g * paU q g F x))]
    refine tsum_congr fun g => ?_
    simp only [Equiv.neg_apply, Submodule.coe_neg, starRingEnd_apply]
  rw [hsum]
  have hmc : paTh Y q F x * (starRingEnd ℂ) (paTh Y q F x) = ((‖paTh Y q F x‖ ^ 2 : ℝ) : ℂ) := by
    first
    | rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    | (rw [Complex.mul_conj']; push_cast; ring)
  push_cast at hmc ⊢
  linear_combination (paW q x : ℂ) * hmc
end ReciprocityTheory.ChartRestriction.G.I2.FPw
