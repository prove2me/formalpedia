-- Prove2me | solution 1 for PenningTrap.invariance_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:44:31.448382+00:00
-- url     : https://prove2.me/submissions/755a680b-08aa-43ab-98e9-264565698ae1

import Mathlib
import Definitions.Def_PenningTrap_model

open Matrix
open PenningTrap

theorem W2m_PenningTrap_det_modeMatrix (K : Matrix (Fin 3) (Fin 3) ℝ) (hK : K.IsSymm)
    (b : Fin 3 → ℝ) (wc w : ℝ) :
    (modeMatrix K b wc w).det = -((charCubic K b wc (w ^ 2) : ℝ) : ℂ) := by
  have h10 : K 1 0 = K 0 1 := hK.apply 0 1
  have h20 : K 2 0 = K 0 2 := hK.apply 0 2
  have h21 : K 2 1 = K 1 2 := hK.apply 1 2
  simp [modeMatrix, charCubic, crossMatrix, Matrix.det_fin_three, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, h10, h20, h21]
  first
    | (linear_combination ((w : ℂ) ^ 2 * (wc : ℂ) ^ 2 *
        ((b 0 : ℂ) * ((K 0 0 : ℂ) * (b 0 : ℂ) + (K 0 1 : ℂ) * (b 1 : ℂ) + (K 0 2 : ℂ) * (b 2 : ℂ))
        + (b 1 : ℂ) * ((K 0 1 : ℂ) * (b 0 : ℂ) + (K 1 1 : ℂ) * (b 1 : ℂ) + (K 1 2 : ℂ) * (b 2 : ℂ))
        + (b 2 : ℂ) * ((K 0 2 : ℂ) * (b 0 : ℂ) + (K 1 2 : ℂ) * (b 1 : ℂ) + (K 2 2 : ℂ) * (b 2 : ℂ))
        - (w : ℂ) ^ 2 * ((b 0 : ℂ) ^ 2 + (b 1 : ℂ) ^ 2 + (b 2 : ℂ) ^ 2))) * Complex.I_sq)
    | (linear_combination (-((w : ℂ) ^ 2 * (wc : ℂ) ^ 2 *
        ((b 0 : ℂ) * ((K 0 0 : ℂ) * (b 0 : ℂ) + (K 0 1 : ℂ) * (b 1 : ℂ) + (K 0 2 : ℂ) * (b 2 : ℂ))
        + (b 1 : ℂ) * ((K 0 1 : ℂ) * (b 0 : ℂ) + (K 1 1 : ℂ) * (b 1 : ℂ) + (K 1 2 : ℂ) * (b 2 : ℂ))
        + (b 2 : ℂ) * ((K 0 2 : ℂ) * (b 0 : ℂ) + (K 1 2 : ℂ) * (b 1 : ℂ) + (K 2 2 : ℂ) * (b 2 : ℂ))
        - (w : ℂ) ^ 2 * ((b 0 : ℂ) ^ 2 + (b 1 : ℂ) ^ 2 + (b 2 : ℂ) ^ 2)))) * Complex.I_sq)
    | (ring_nf; simp only [Complex.I_sq]; ring_nf)

theorem W2m_PenningTrap_det_modeMatrix_ideal (wz wc : ℝ) (h : 2 * wz ^ 2 ≤ wc ^ 2) (w : ℝ) :
    (modeMatrix (Matrix.diagonal ![-(wz ^ 2) / 2, -(wz ^ 2) / 2, wz ^ 2]) ![0, 0, 1] wc w).det
      = -(((w ^ 2 - ((wc + Real.sqrt (wc ^ 2 - 2 * wz ^ 2)) / 2) ^ 2) * (w ^ 2 - wz ^ 2) *
            (w ^ 2 - ((wc - Real.sqrt (wc ^ 2 - 2 * wz ^ 2)) / 2) ^ 2) : ℝ) : ℂ) := by
  rw [W2m_PenningTrap_det_modeMatrix _ (Matrix.isSymm_diagonal _)]
  congr 2
  have hs : Real.sqrt (wc ^ 2 - 2 * wz ^ 2) ^ 2 = wc ^ 2 - 2 * wz ^ 2 :=
    Real.sq_sqrt (by linarith)
  simp [charCubic, Matrix.det_fin_three, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.diagonal_apply]
  first
    | linear_combination (w ^ 2 - wz ^ 2) * (w ^ 2 / 2 + wz ^ 2 / 4
        - (Real.sqrt (wc ^ 2 - 2 * wz ^ 2) ^ 2 - wc ^ 2 + 2 * wz ^ 2) / 16) * hs
    | linear_combination (-((w ^ 2 - wz ^ 2) * (w ^ 2 / 2 + wz ^ 2 / 4
        - (Real.sqrt (wc ^ 2 - 2 * wz ^ 2) ^ 2 - wc ^ 2 + 2 * wz ^ 2) / 16))) * hs

theorem W2m_PenningTrap_invariance_theorem (K : Matrix (Fin 3) (Fin 3) ℝ) (hK : K.IsSymm)
    (hL : K.trace = 0)
    (b : Fin 3 → ℝ) (hb : b ⬝ᵥ b = 1) (wc wbc wbz wbm : ℝ)
    (hfac : ∀ w : ℝ, (modeMatrix K b wc w).det
      = -(((w ^ 2 - wbc ^ 2) * (w ^ 2 - wbz ^ 2) * (w ^ 2 - wbm ^ 2) : ℝ) : ℂ)) :
    wbc ^ 2 + wbz ^ 2 + wbm ^ 2 = wc ^ 2 := by
  have key : ∀ w : ℝ, charCubic K b wc (w ^ 2)
      = (w ^ 2 - wbc ^ 2) * (w ^ 2 - wbz ^ 2) * (w ^ 2 - wbm ^ 2) := by
    intro w
    have H := hfac w
    rw [W2m_PenningTrap_det_modeMatrix K hK b wc w] at H
    exact_mod_cast neg_injective H
  have k0 := key 0
  have k1 := key 1
  have k2 := key (Real.sqrt 2)
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at k2
  have htr : K 0 0 + K 1 1 + K 2 2 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_three] using hL
  have hbb : b 0 * b 0 + b 1 * b 1 + b 2 * b 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three] using hb
  have hbb' : wc ^ 2 * (b 0 * b 0 + b 1 * b 1 + b 2 * b 2) = wc ^ 2 := by rw [hbb, mul_one]
  simp [charCubic, Matrix.det_fin_three, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.one_apply] at k0 k1 k2
  first
    | linear_combination (1 / 2 : ℝ) * k2 - k1 + (1 / 2 : ℝ) * k0 + htr + wc ^ 2 * hbb
    | linarith

theorem W2m_PenningTrap_hd1 (w : ℝ) (c : ℂ) (s : ℝ) :
    HasDerivAt (fun σ : ℝ => c * Complex.exp (-(Complex.I * w * σ)))
      (c * Complex.exp (-(Complex.I * w * s)) * (-(Complex.I * w))) s := by
  have h1 : HasDerivAt (fun σ : ℝ => -(Complex.I * w * (σ : ℂ))) (-(Complex.I * w)) s :=
    ((((hasDerivAt_id' s).ofReal_comp).const_mul (Complex.I * (w : ℂ))).fun_neg).congr_deriv
      (by simp)
  exact ((h1.cexp).const_mul c).congr_deriv (by ring)

theorem W2m_PenningTrap_hd2 (w : ℝ) (c : ℂ) (t : ℝ) :
    deriv (fun s : ℝ => deriv (fun σ : ℝ => c * Complex.exp (-(Complex.I * w * σ))) s) t
      = c * Complex.exp (-(Complex.I * w * t)) * (-(Complex.I * w)) ^ 2 := by
  have e : (fun s : ℝ => deriv (fun σ : ℝ => c * Complex.exp (-(Complex.I * w * σ))) s)
      = fun s : ℝ => (c * (-(Complex.I * w))) * Complex.exp (-(Complex.I * w * s)) := by
    funext s
    rw [(W2m_PenningTrap_hd1 w c s).deriv]
    ring
  rw [e, (W2m_PenningTrap_hd1 w (c * (-(Complex.I * w))) t).deriv]
  ring

theorem W2m_PenningTrap_mode_ansatz_iff_mulVec_eq_zero (K : Matrix (Fin 3) (Fin 3) ℝ)
    (b : Fin 3 → ℝ) (wc w : ℝ) (u : Fin 3 → ℂ) :
    (∀ t : ℝ, ∀ i : Fin 3,
        deriv (fun s : ℝ => deriv (fun σ : ℝ => u i * Complex.exp (-(Complex.I * w * σ))) s) t
          = -((K.map (fun x : ℝ => (x : ℂ))).mulVec
                (fun j => u j * Complex.exp (-(Complex.I * w * t))) i)
            + (wc : ℂ) *
              crossProduct
                (fun j => deriv (fun σ : ℝ => u j * Complex.exp (-(Complex.I * w * σ))) t)
                (fun j => (b j : ℂ)) i)
      ↔ (modeMatrix K b wc w).mulVec u = 0 := by
  have hd1' : ∀ (c : ℂ) (s : ℝ),
      deriv (fun σ : ℝ => c * Complex.exp (-(Complex.I * w * σ))) s
        = c * Complex.exp (-(Complex.I * w * s)) * (-(Complex.I * w)) :=
    fun c s => (W2m_PenningTrap_hd1 w c s).deriv
  have key : ∀ (t : ℝ) (i : Fin 3),
      deriv (fun s : ℝ => deriv (fun σ : ℝ => u i * Complex.exp (-(Complex.I * w * σ))) s) t
        - (-((K.map (fun x : ℝ => (x : ℂ))).mulVec
                (fun j => u j * Complex.exp (-(Complex.I * w * t))) i)
            + (wc : ℂ) *
              crossProduct
                (fun j => deriv (fun σ : ℝ => u j * Complex.exp (-(Complex.I * w * σ))) t)
                (fun j => (b j : ℂ)) i)
        = Complex.exp (-(Complex.I * w * t)) * (modeMatrix K b wc w).mulVec u i := by
    intro t i
    rw [W2m_PenningTrap_hd2]
    simp only [hd1']
    generalize Complex.exp (-(Complex.I * w * t)) = E
    fin_cases i <;>
      simp [modeMatrix, crossMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        cross_apply, Matrix.one_apply] <;>
      first
        | ring1
        | linear_combination (u 0 * E * (w : ℂ) ^ 2) * Complex.I_sq
        | linear_combination (u 1 * E * (w : ℂ) ^ 2) * Complex.I_sq
        | linear_combination (u 2 * E * (w : ℂ) ^ 2) * Complex.I_sq
        | linear_combination (-(u 0 * E * (w : ℂ) ^ 2)) * Complex.I_sq
        | linear_combination (-(u 1 * E * (w : ℂ) ^ 2)) * Complex.I_sq
        | linear_combination (-(u 2 * E * (w : ℂ) ^ 2)) * Complex.I_sq
        | (ring_nf; simp only [Complex.I_sq]; ring_nf)
  constructor
  · intro H
    funext i
    have h1 := key 0 i
    rw [H 0 i, sub_self] at h1
    have h0 : Complex.exp (-(Complex.I * w * ((0 : ℝ) : ℂ))) = 1 := by simp
    rw [h0, one_mul] at h1
    rw [Pi.zero_apply]
    exact h1.symm
  · intro H t i
    have h1 := key t i
    rw [H, Pi.zero_apply, mul_zero] at h1
    exact sub_eq_zero.1 h1

theorem solution (K : Matrix (Fin 3) (Fin 3) ℝ) (hK : K.IsSymm) (hL : K.trace = 0)
    (b : Fin 3 → ℝ) (hb : b ⬝ᵥ b = 1) (wc wbc wbz wbm : ℝ)
    (hfac : ∀ w : ℝ, (modeMatrix K b wc w).det
      = -(((w ^ 2 - wbc ^ 2) * (w ^ 2 - wbz ^ 2) * (w ^ 2 - wbm ^ 2) : ℝ) : ℂ)) :
    wbc ^ 2 + wbz ^ 2 + wbm ^ 2 = wc ^ 2 := by
  apply W2m_PenningTrap_invariance_theorem <;> assumption
