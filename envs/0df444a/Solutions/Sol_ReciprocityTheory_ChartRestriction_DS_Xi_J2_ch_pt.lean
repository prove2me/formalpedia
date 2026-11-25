-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.ch_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:33:28.246804+00:00
-- url     : https://prove2.me/submissions/39211511-2866-48c7-ab5d-05aed33e6326

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_de_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_de_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_kernel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_one_le_lsq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_one_le_rhoSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_rhoSq_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Module
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace J2
private lemma norm_sq_add_norm_sq_sub_eq_complete_square (w B a : ℂ) :
    ‖w‖ ^ 2 + ‖B - w * star a‖ ^ 2 =
      (1 + ‖a‖ ^ 2) * ‖w - B * a / ((1 + ‖a‖ ^ 2 : ℝ) : ℂ)‖ ^ 2 + ‖B‖ ^ 2 / (1 + ‖a‖ ^ 2) := by
  have key : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hL : (1 + (a.re ^ 2 + a.im ^ 2)) ≠ 0 := by positivity
  simp only [key, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  field_simp
  ring
end J2
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution (p m : ℕ) (ν : Fin (p + 2) → ℝ) (y : TDom p m) :
    ∫⁻ w : ℂ, chF (p + 1) m ν (y.1, Fin.cons w y.2.1, y.2.2) =
      kc (2 + ν 0) * tailF p m (ν 0) (Fin.tail ν) y := by
  rcases y with ⟨a, b, r⟩
  dsimp only
  have hlsq0 : ∀ w : ℂ, Lsq ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 = 1 := by
    intro w; simp [Lsq]
  have hrho : ∀ w : ℂ, rhoSq ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 =
      rhoSq (tailPt ((a, b, r) : TDom p m)) 1 + ‖w‖ ^ 2 := by
    intro w
    simp [rhoSq, Lsq, tailPt, Fin.sum_univ_succ]
    ring
  have hbco : ∀ w : ℂ, bco ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 =
      bco (tailPt ((a, b, r) : TDom p m)) 1 - w * star (a 0) := by
    intro w
    simp [bco, tailPt, Fin.sum_univ_succ]
    ring
  have hL1 : Lsq (tailPt ((a, b, r) : TDom p m)) 1 = 1 + ‖a 0‖ ^ 2 := by
    simp [Lsq, tailPt, Fin.sum_univ_succ]
  have hd1 : de (tailPt ((a, b, r) : TDom p m)) 1 ^ 2 =
      (1 + ‖a 0‖ ^ 2) * rhoSq (tailPt ((a, b, r) : TDom p m)) 1 + ‖bco (tailPt ((a, b, r) : TDom p m)) 1‖ ^ 2 := by
    rw [de, Real.sq_sqrt (add_nonneg (mul_nonneg (by linarith [one_le_lsq (tailPt ((a, b, r) : TDom p m)) 1])
      (rhoSq_nonneg _ _)) (sq_nonneg _)), hL1]
  have hM := one_le_rhoSq (tailPt ((a, b, r) : TDom p m)) 1
  have hd1p := de_pos (tailPt ((a, b, r) : TDom p m)) 1
  set M := rhoSq (tailPt ((a, b, r) : TDom p m)) 1
  set B := bco (tailPt ((a, b, r) : TDom p m)) 1
  set d1 := de (tailPt ((a, b, r) : TDom p m)) 1
  set L := 1 + ‖a 0‖ ^ 2 with hL_def
  have hL : 0 < L := by positivity
  set D := M + ‖B‖ ^ 2 / L with hD_def
  have hD : 0 < D := add_pos_of_pos_of_nonneg (by linarith) (by positivity)
  set c : ℂ := B * a 0 / ((L : ℝ) : ℂ) with hc_def
  have hquad : ∀ w : ℂ, de ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 ^ 2 = L * ‖w - c‖ ^ 2 + D := by
    intro w
    rw [de, Real.sq_sqrt (add_nonneg (mul_nonneg (by linarith [one_le_lsq ((a, Fin.cons w b, r) : Xp (p + 1) m) 0])
      (rhoSq_nonneg _ _)) (sq_nonneg _)), hlsq0, hrho, hbco, one_mul, add_assoc, norm_sq_add_norm_sq_sub_eq_complete_square, hD_def, hc_def, hL_def]
    ring
  have hzero : ∀ w : ℂ, de ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 ^ (-(s0N (p + 1) m 0 + ν 0)) =
      (L * ‖w - c‖ ^ 2 + D) ^ (-(2 + ν 0) / 2) := by
    intro w
    have hs : s0N (p + 1) m 0 = 2 := by simp [s0N]
    rw [hs, ← hquad w, ← Real.rpow_natCast, ← Real.rpow_mul (de_pos _ _).le]
    congr 1
    push_cast
    ring
  have htp : tailPt ((a, b, r) : TDom p m) = (a, Fin.cons 0 b, r) := rfl
  unfold chF tailF
  simp only [Fin.prod_univ_succ, de_cons, hzero]
  rw [lintegral_mul_const _ (by fun_prop), kernel L D hL hD c (2 + ν 0), hL1]
  have hkey : ENNReal.ofReal (L⁻¹ * D ^ (1 - (2 + ν 0) / 2)) =
      ENNReal.ofReal (L ^ ((-2 + ν 0) / 2)) * ENNReal.ofReal (d1 ^ (-ν 0)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e1 : D = d1 ^ 2 / L := by
      rw [hd1, hD_def]
      field_simp
    rw [e1, Real.div_rpow (sq_nonneg _) hL.le, ← Real.rpow_natCast d1 2, ← Real.rpow_mul hd1p.le,
      show (1 - (2 + ν 0) / 2) = -ν 0 / 2 by ring,
      show ((2 : ℕ) : ℝ) * (-ν 0 / 2) = -ν 0 by push_cast; ring,
      show (-2 + ν 0) / 2 = -1 - (-ν 0 / 2) by ring, Real.rpow_sub hL, Real.rpow_neg_one]
    field_simp
  rw [hkey, htp, show de ((a, Fin.cons 0 b, r) : Xp (p + 1) m) 1 = d1 from rfl]
  simp only [Fin.tail]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
