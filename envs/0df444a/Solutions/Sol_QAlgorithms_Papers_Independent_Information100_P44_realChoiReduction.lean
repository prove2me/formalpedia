-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.realChoiReduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:37:01.825404+00:00
-- url     : https://prove2.me/submissions/ceac8e74-4eae-4612-a12d-665e1f076381

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

theorem g52c_re_sum {ι : Type*} [Fintype ι] (f c : ι → ℂ) (hc : ∀ i, (c i).im = 0) :
    ∑ i, ((f i).re : ℂ) * c i = ((∑ i, f i * c i).re : ℂ) := by
  apply Complex.ext
  · simp [Complex.re_sum, Complex.mul_re, hc]
  · simp [Complex.im_sum, Complex.mul_im, hc]

theorem g52c_re_sum2 {ι κ : Type*} [Fintype ι] [Fintype κ] (f c : ι → κ → ℂ)
    (hc : ∀ i j, (c i j).im = 0) :
    ∑ i, ∑ j, ((f i j).re : ℂ) * c i j = ((∑ i, ∑ j, f i j * c i j).re : ℂ) := by
  apply Complex.ext
  · simp [Complex.re_sum, Complex.mul_re, hc]
  · simp [Complex.im_sum, Complex.mul_im, hc]

theorem g52c_fixedRho_im (u v : Fin 4) : (fixedRho u v).im = 0 := by
  fin_cases u <;> fin_cases v <;> simp [fixedRho]

theorem g52c_fromChoi_re (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) (x y : Fin 4) :
    fromChoi (fun a b => ((J a b).re : ℂ)) fixedRho x y = ((fromChoi J fixedRho x y).re : ℂ) := by
  simp only [fromChoi]
  exact g52c_re_sum2 (fun u v => J (x, u) (y, v)) (fun u v => fixedRho u v)
    (fun u v => g52c_fixedRho_im u v)

theorem g52c_ofReal_re_of_eq {z w : ℂ} (h : z = w) (hw : w.im = 0) : ((z.re : ℝ) : ℂ) = w := by
  subst h; exact Complex.ext (by simp) (by simp [hw])

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (hJ : FixedChoiFeasible J) :
    FixedChoiFeasible (fun a b => ((J a b).re : ℂ)) ∧
    ∀ k : Fin 3, channelObjective k (fromChoi (fun a b => ((J a b).re : ℂ))) = channelObjective k (fromChoi J) := by
  obtain ⟨hpsd, h1, h2, h3, h4⟩ := hJ
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- real part of a PSD matrix: (J + Jᵀ)/2
    have heq : (fun a b => ((J a b).re : ℂ)) = (1 / 2 : ℂ) • (J + J.transpose) := by
      ext a b
      have hh : J b a = star (J a b) := by
        have := congrFun (congrFun hpsd.1 a) b
        simp only [Matrix.conjTranspose_apply] at this
        rw [← this, star_star]
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, hh, smul_eq_mul]
      apply Complex.ext <;> (simp; try ring)
    rw [heq]
    exact (hpsd.add hpsd.transpose).smul (by rw [Complex.nonneg_iff]; norm_num)
  · intro u v
    beta_reduce
    have := h1 u v
    have e : ∑ x, ((J (x, u) (x, v)).re : ℂ) = ((∑ x, J (x, u) (x, v)).re : ℂ) := by
      simpa using g52c_re_sum (fun x => J (x, u) (x, v)) (fun _ => 1) (fun _ => by simp)
    rw [e]
    exact g52c_ofReal_re_of_eq this (by split_ifs <;> simp)
  · intro x y
    beta_reduce
    have := h2 x y
    rw [g52c_re_sum (fun u => J (x, u) (y, u)) (fun u => (gibbsWeight fixedEnergy 1 u : ℂ))
      (fun u => by simp)]
    exact g52c_ofReal_re_of_eq this (by split_ifs <;> simp)
  · intro x u y v hne
    simp [h3 x u y v hne]
  · obtain ⟨p1, p2, p3⟩ := h4
    refine ⟨?_, ?_, ?_⟩
    · rw [g52c_fromChoi_re]; exact g52c_ofReal_re_of_eq p1 (by norm_num)
    · rw [g52c_fromChoi_re, g52c_fromChoi_re]
      have := congrArg Complex.re p2
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re] at this ⊢; rw [this]
      · simp
    · rw [g52c_fromChoi_re]; exact g52c_ofReal_re_of_eq p3 (by norm_num)
  · intro k
    simp only [channelObjective]
    rw [g52c_fromChoi_re, Complex.ofReal_re]
