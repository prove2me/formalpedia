-- Prove2me | solution 1 for OracleStateHSP.fact_4_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:22:19.91057+00:00
-- url     : https://prove2.me/submissions/0629bfc6-4eb6-420d-8724-8e4563fc6b50

import Mathlib
import Definitions.Def_OracleStateHSP_relGamma2

open scoped ENNReal
open OracleStateHSP QAlgorithms

namespace AuxFact45

lemma act_smul {ι : Type*} [Fintype ι] (c : ℂ) (M : Matrix ι ι ℂ) (w : EuclideanSpace ℂ ι) :
    act (c • M) w = c • act M w := by
  ext i
  simp [act, Matrix.smul_mulVec]

lemma act_vec_smul {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (c : ℂ) (w : EuclideanSpace ℂ ι) :
    act M (c • w) = c • act M w := by
  ext i
  simp [act, Matrix.mulVec_smul]

lemma relGamma2_smul_le {X Q : Type*} [Fintype X] [Fintype Q] (A : Matrix X X ℂ)
    (Δ : X → X → Matrix Q Q ℂ) {c : ℂ} (hc : c ≠ 0) :
    relGamma2 A (fun x y => c • Δ x y) ≤ relGamma2 A Δ / ENNReal.ofReal ‖c‖ := by
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hd0 : ENNReal.ofReal ‖c‖ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc_pos
  have hdt : ENNReal.ofReal ‖c‖ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdt)]
  refine le_iInf fun k => le_iInf fun u => le_iInf fun v => le_iInf fun h => ?_
  set s : ℝ := Real.sqrt ‖c‖
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hc_pos
  have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs_pos.ne'
  let u' : X → EuclideanSpace ℂ (Q × Fin k) := fun x => ((s : ℂ)⁻¹) • u x
  let v' : X → EuclideanSpace ℂ (Q × Fin k) := fun y => (c⁻¹ * (s : ℂ)) • v y
  have h' : ∀ x y, A x y =
      inner ℂ (u' x) (act (Matrix.kronecker (c • Δ x y) (1 : Matrix (Fin k) (Fin k) ℂ)) (v' y)) := by
    intro x y
    have hkr : Matrix.kronecker (c • Δ x y) (1 : Matrix (Fin k) (Fin k) ℂ) =
        c • Matrix.kronecker (Δ x y) (1 : Matrix (Fin k) (Fin k) ℂ) := by
      ext p q
      simp [Matrix.kroneckerMap_apply, mul_assoc]
    dsimp only [u', v']
    rw [hkr, act_smul, act_vec_smul, inner_smul_left, inner_smul_right, inner_smul_right]
    have hstar : (starRingEnd ℂ) ((s : ℂ)⁻¹) = (s : ℂ)⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    rw [hstar, h x y]
    calc inner ℂ (u x) (act (Matrix.kronecker (Δ x y) (1 : Matrix (Fin k) (Fin k) ℂ)) (v y))
        = (1 : ℂ) * (1 : ℂ) *
            inner ℂ (u x) (act (Matrix.kronecker (Δ x y) (1 : Matrix (Fin k) (Fin k) ℂ)) (v y)) := by ring
      _ = ((s : ℂ)⁻¹ * (s : ℂ)) * (c * c⁻¹) *
            inner ℂ (u x) (act (Matrix.kronecker (Δ x y) (1 : Matrix (Fin k) (Fin k) ℂ)) (v y)) := by
          rw [inv_mul_cancel₀ hs_ne, mul_inv_cancel₀ hc]
      _ = _ := by ring
  have hle_inf : relGamma2 A (fun x y => c • Δ x y) ≤
      max (⨆ x, ENNReal.ofReal (‖u' x‖ ^ 2)) (⨆ y, ENNReal.ofReal (‖v' y‖ ^ 2)) :=
    iInf_le_of_le k (iInf_le_of_le u' (iInf_le_of_le v' (iInf_le _ h')))
  have hu_norm : ∀ x, ENNReal.ofReal (‖u' x‖ ^ 2) ≤
      (⨆ x', ENNReal.ofReal (‖u x'‖ ^ 2)) / ENNReal.ofReal ‖c‖ := by
    intro x
    have h1 : ‖u' x‖ ^ 2 = ‖u x‖ ^ 2 / ‖c‖ := by
      simp only [u', norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos]
      rw [mul_pow, inv_pow, Real.sq_sqrt hc_pos.le, div_eq_inv_mul]
    rw [h1, ENNReal.ofReal_div_of_pos hc_pos]
    exact ENNReal.div_le_div_right (le_iSup (fun x' => ENNReal.ofReal (‖u x'‖ ^ 2)) x) _
  have hv_norm : ∀ y, ENNReal.ofReal (‖v' y‖ ^ 2) ≤
      (⨆ y', ENNReal.ofReal (‖v y'‖ ^ 2)) / ENNReal.ofReal ‖c‖ := by
    intro y
    have h1 : ‖v' y‖ ^ 2 = ‖v y‖ ^ 2 / ‖c‖ := by
      simp only [v', norm_smul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos]
      have hsq : (‖c‖⁻¹ * s) ^ 2 = ‖c‖⁻¹ := by
        rw [mul_pow, Real.sq_sqrt hc_pos.le]
        field_simp [hc_pos.ne']
      rw [mul_pow, hsq, div_eq_inv_mul]
    rw [h1, ENNReal.ofReal_div_of_pos hc_pos]
    exact ENNReal.div_le_div_right (le_iSup (fun y' => ENNReal.ofReal (‖v y'‖ ^ 2)) y) _
  have hmax : max (⨆ x, ENNReal.ofReal (‖u' x‖ ^ 2)) (⨆ y, ENNReal.ofReal (‖v' y‖ ^ 2)) ≤
      max (⨆ x, ENNReal.ofReal (‖u x‖ ^ 2)) (⨆ y, ENNReal.ofReal (‖v y‖ ^ 2)) / ENNReal.ofReal ‖c‖ := by
    refine max_le ?_ ?_
    · exact le_trans (iSup_le hu_norm)
        (ENNReal.div_le_div_right (le_max_left _ _) _)
    · exact le_trans (iSup_le hv_norm)
        (ENNReal.div_le_div_right (le_max_right _ _) _)
  calc relGamma2 A (fun x y => c • Δ x y) * ENNReal.ofReal ‖c‖
      ≤ max (⨆ x, ENNReal.ofReal (‖u' x‖ ^ 2)) (⨆ y, ENNReal.ofReal (‖v' y‖ ^ 2)) * ENNReal.ofReal ‖c‖ := by
          gcongr
    _ ≤ (max (⨆ x, ENNReal.ofReal (‖u x‖ ^ 2)) (⨆ y, ENNReal.ofReal (‖v y‖ ^ 2)) / ENNReal.ofReal ‖c‖) *
          ENNReal.ofReal ‖c‖ := by
          gcongr
    _ = max (⨆ x, ENNReal.ofReal (‖u x‖ ^ 2)) (⨆ y, ENNReal.ofReal (‖v y‖ ^ 2)) :=
          ENNReal.div_mul_cancel hd0 hdt

end AuxFact45

theorem solution {X Q : Type*} [Fintype X] [Fintype Q] (A : Matrix X X ℂ)
    (Δ : X → X → Matrix Q Q ℂ) (c : ℂ) (hc : c ≠ 0) :
    relGamma2 A (fun x y => c • Δ x y) = relGamma2 A Δ / ENNReal.ofReal ‖c‖ := by
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hd0 : ENNReal.ofReal ‖c‖ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc_pos
  have hdt : ENNReal.ofReal ‖c‖ ≠ ⊤ := ENNReal.ofReal_ne_top
  refine le_antisymm (AuxFact45.relGamma2_smul_le A Δ hc) ?_
  have hinv := AuxFact45.relGamma2_smul_le A (fun x y => c • Δ x y) (inv_ne_zero hc)
  have hcancel : (fun x y => c⁻¹ • (c • Δ x y)) = Δ := by
    funext x y
    exact inv_smul_smul₀ hc (Δ x y)
  rw [hcancel, norm_inv] at hinv
  rw [ENNReal.ofReal_inv_of_pos hc_pos, ENNReal.div_eq_inv_mul, inv_inv, mul_comm] at hinv
  exact (ENNReal.div_le_iff_le_mul (Or.inl hd0) (Or.inl hdt)).mpr hinv
