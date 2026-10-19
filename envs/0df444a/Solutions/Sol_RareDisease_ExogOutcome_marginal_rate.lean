-- Prove2me | solution 1 for RareDisease.ExogOutcome.marginal_rate
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T19:22:37.249791+00:00
-- url     : https://prove2.me/submissions/c8c6be5b-d3b5-4b0b-b0bc-af3bb5daf020

import Mathlib

namespace GLMRare

/-- transport a `HasDerivAt` along a provable function equality -/
theorem castH {f g : ℝ → ℝ} {x y : ℝ} (funeq : f = g) (h : HasDerivAt f y x) :
    HasDerivAt g y x := funeq ▸ h

/-- the affine map `x ↦ 1 - (1 - x) * p` has derivative `p` -/
theorem huAff (p : ℝ) (x : ℝ) : HasDerivAt (fun x : ℝ => 1 - (1 - x) * p) p x := by
  have h1 : HasDerivAt (fun y : ℝ => p * y) (p * 1) x := (hasDerivAt_id' x).const_mul p
  have h0 : HasDerivAt (fun y : ℝ => 1 - p) 0 x := hasDerivAt_const x (1 - p)
  have hs := h0.add h1
  simp only [zero_add, mul_one] at hs
  have funeq : ((fun y : ℝ => 1 - p) + (fun y : ℝ => p * y))
      = fun x : ℝ => 1 - (1 - x) * p := by
    funext w
    simp only [Pi.add_apply]
    ring
  exact castH funeq hs

/-- the map `x ↦ 1 - x` has derivative `-1` -/
theorem huNeg (x : ℝ) : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) x := by
  have h1 : HasDerivAt (fun y : ℝ => (-1 : ℝ) * y) (-1 : ℝ) x := hasDerivAt_const_mul (-1)
  have h0 : HasDerivAt (fun y : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
  have hs := h0.add h1
  simp only [zero_add] at hs
  have funeq : ((fun y : ℝ => (1 : ℝ)) + (fun y : ℝ => (-1) * y)) = fun y : ℝ => 1 - y := by
    funext w
    simp only [Pi.add_apply]
    ring
  exact castH funeq hs

end GLMRare

open GLMRare

theorem solution (k p α β : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    let W : ℝ → ℝ → ℝ := fun α β => p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α) * k)
    let M : ℝ → ℝ → ℝ := fun α β =>
      α * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (4 * (1 - α) ^ 2 * k)
        + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α) * k)
    let f₁ : ℝ := (1 - α) * ((5 - α) * p - 2 * (1 - α)) * (1 - (1 - β) * p)
    let f₂ : ℝ := 2 * p * (1 + 2 * β + α - 2 * α * β)
      * (1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p)
    deriv (fun β' => W α β') β / deriv (fun β' => M α β') β
        - deriv (fun α' => W α' β) α / deriv (fun α' => M α' β) α = f₁ / f₂ ∧
      0 < f₂ := by
  obtain ⟨hα0, hα1⟩ := Set.mem_Ico.mp hα
  obtain ⟨hβ0, hβ1⟩ := Set.mem_Ico.mp hβ
  -- elementary positivity
  have h1a : 0 < 1 - α := by linarith
  have h1p : 0 < 1 - p := by linarith
  have hβp : 0 ≤ β * p := mul_nonneg hβ0 hp0.le
  have hqeq : 1 - (1 - β) * p = 1 - p + β * p := by ring
  have hqe : 0 < 1 - (1 - β) * p := by rw [hqeq]; nlinarith
  have hpK1 : 0 < (1 - α) * k := mul_pos h1a hk
  have hK4 : 0 < 4 * (1 - α) * k := by nlinarith [hpK1]
  have hK2 : 0 < 2 * (1 - α) * k := by nlinarith [hpK1]
  have hsq : 0 < (1 - α) * (1 - α) := by nlinarith
  have hKs : 0 < 4 * (1 - α) ^ 2 * k := by nlinarith [mul_pos hsq hk]
  have hKc : 0 < 4 * (1 - α) ^ 3 * k := by
    have h3a : 0 < (1 - α) * (1 - α) * (1 - α) := by nlinarith
    nlinarith [mul_pos h3a hk]
  -- key scalar facts
  have hbb : 0 < 1 + 2 * β + α - 2 * α * β := by
    nlinarith [mul_nonneg hβ0 h1a.le]
  have hA : 0 < (1 - α) * (1 - (1 - β) * p) := mul_pos h1a hqe
  have hB : 0 ≤ (1 - α) * (β * p) := mul_nonneg h1a.le hβp
  have hgb : 0 < α * p + (1 - α) * ((1 - (1 - β) * p) + 2 * β * p) := by nlinarith
  show deriv (fun β' => p * (1 - (1 - β') * p) ^ 3 / (4 * (1 - α) * k)) β /
      deriv (fun β' => α * p ^ 2 * (1 - (1 - β') * p) ^ 2 / (4 * (1 - α) ^ 2 * k)
        + β' * p ^ 2 * (1 - (1 - β') * p) ^ 2 / (2 * (1 - α) * k)) β -
      deriv (fun α' => p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α') * k)) α /
      deriv (fun α' => α' * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (4 * (1 - α') ^ 2 * k)
        + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α') * k)) α
      = (1 - α) * ((5 - α) * p - 2 * (1 - α)) * (1 - (1 - β) * p)
        / (2 * p * (1 + 2 * β + α - 2 * α * β)
          * (1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p))
    ∧ 0 < 2 * p * (1 + 2 * β + α - 2 * α * β)
          * (1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p)
  -- derivative of the β-section of W
  have dWb : deriv (fun β' => p * (1 - (1 - β') * p) ^ 3 / (4 * (1 - α) * k)) β
      = 3 * p * p * (1 - (1 - β) * p) * (1 - (1 - β) * p) / (4 * (1 - α) * k) := by
    have hPow := (huAff p β).fun_pow 3
    have hd := (hPow.const_mul p).div_const (4 * (1 - α) * k)
    rw [hd.deriv]
    ring
  -- derivative of the α-section of W
  have dWa : deriv (fun α' => p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α') * k)) α
      = p * (1 - (1 - β) * p) ^ 3 / (4 * k * (1 - α) * (1 - α)) := by
    have hD : HasDerivAt (fun a' : ℝ => 4 * (1 - a') * k) ((4 * (-1)) * k) α :=
      ((huNeg α).const_mul 4).mul_const k
    have hv := (hasDerivAt_const α (p * (1 - (1 - β) * p) ^ 3)).div hD (ne_of_gt hK4)
    have hvC : HasDerivAt (fun α' : ℝ => p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α') * k)) _ α :=
      hv.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
        simp only [Pi.div_apply]
        skip))
    rw [hvC.deriv]
    have nD : (4 * (1 - α) * k : ℝ) ≠ 0 := ne_of_gt hK4
    have nD2 : (4 * (1 - α) * k) ^ 2 ≠ 0 := pow_ne_zero 2 nD
    have nK : (k : ℝ) ≠ 0 := ne_of_gt hk
    field_simp
    ring
  -- derivative of the β-section of M
  have dMb : deriv (fun β' => α * p ^ 2 * (1 - (1 - β') * p) ^ 2 / (4 * (1 - α) ^ 2 * k)
        + β' * p ^ 2 * (1 - (1 - β') * p) ^ 2 / (2 * (1 - α) * k)) β
      = p * p * (1 - (1 - β) * p)
          * (α * p + (1 - α) * ((1 - (1 - β) * p) + 2 * β * p)) / (2 * (1 - α) ^ 2 * k) := by
    have hPow : HasDerivAt (fun y : ℝ => (1 - (1 - y) * p) ^ 2)
        (2 * (1 - (1 - β) * p) * p) β :=
      ((huAff p β).fun_pow 2).congr_deriv (by norm_num)
    have v1 := (hPow.const_mul (α * p * p)).div_const (4 * (1 - α) ^ 2 * k)
    have v2 := ((hasDerivAt_id' β).mul (hPow.const_mul (p * p))).div_const (2 * (1 - α) * k)
    have hs := v1.add v2
    have hsC : HasDerivAt (fun y : ℝ => α * p ^ 2 * (1 - (1 - y) * p) ^ 2
        / (4 * (1 - α) ^ 2 * k)
        + y * p ^ 2 * (1 - (1 - y) * p) ^ 2 / (2 * (1 - α) * k)) _ β :=
      hs.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
        simp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply]
        ring))
    rw [hsC.deriv]
    have n1 : (4 * (1 - α) ^ 2 * k : ℝ) ≠ 0 := ne_of_gt hKs
    have n2 : (2 * (1 - α) * k : ℝ) ≠ 0 := ne_of_gt hK2
    field_simp
    ring
  -- derivative of the α-section of M
  have dMa : deriv (fun α' => α' * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (4 * (1 - α') ^ 2 * k)
        + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α') * k)) α
      = p * p * (1 - (1 - β) * p) * (1 - (1 - β) * p)
          * (1 + 2 * β + α - 2 * α * β) / (4 * (1 - α) ^ 3 * k) := by
    have hsq' : HasDerivAt (fun a' : ℝ => (1 - a') ^ 2) (2 * (1 - α) * (-1 : ℝ)) α :=
      ((huNeg α).fun_pow 2).congr_deriv (by norm_num)
    have hD1 : HasDerivAt (fun a' : ℝ => 4 * (1 - a') ^ 2 * k) ((4 * ((2 * (1 - α)) * (-1))) * k) α :=
      (hsq'.const_mul 4).mul_const k
    have hD2 : HasDerivAt (fun a' : ℝ => 2 * (1 - a') * k) ((2 * (-1)) * k) α :=
      ((huNeg α).const_mul 2).mul_const k
    have ne1 : (4 * (1 - α) ^ 2 * k : ℝ) ≠ 0 := ne_of_gt hKs
    have ne2 : (2 * (1 - α) * k : ℝ) ≠ 0 := ne_of_gt hK2
    have v1 := (hasDerivAt_mul_const (p * p * ((1 - (1 - β) * p) * (1 - (1 - β) * p)))).div hD1 ne1
    have v2 := (hasDerivAt_const α (β * (p * p * ((1 - (1 - β) * p) * (1 - (1 - β) * p))))).div hD2 ne2
    have hs := v1.add v2
    have hsC : HasDerivAt (fun α'' : ℝ => α'' * p ^ 2 * (1 - (1 - β) * p) ^ 2
        / (4 * (1 - α'') ^ 2 * k)
        + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α'') * k)) _ α :=
      hs.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
        simp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply]
        ring))
    rw [hsC.deriv]
    have n1 : (4 * (1 - α) ^ 2 * k : ℝ) ≠ 0 := ne_of_gt hKs
    have n2 : (2 * (1 - α) * k : ℝ) ≠ 0 := ne_of_gt hK2
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [dWb, dMb, dWa, dMa]
    have h2p : 0 < p * p := mul_pos hp0 hp0
    have hqe2 : 0 < (1 - (1 - β) * p) * (1 - (1 - β) * p) := mul_pos hqe hqe
    have hqeg : 0 < (1 - (1 - β) * p)
        * (α * p + (1 - α) * ((1 - (1 - β) * p) + 2 * β * p)) := mul_pos hqe hgb
    have hnumMb : 0 < p * p * (1 - (1 - β) * p)
        * (α * p + (1 - α) * ((1 - (1 - β) * p) + 2 * β * p)) := by
      have h3 : 0 < p * p * ((1 - (1 - β) * p)
        * (α * p + (1 - α) * ((1 - (1 - β) * p) + 2 * β * p))) := mul_pos h2p hqeg
      rw [show (p * p * (1 - (1 - β) * p)
        * (α * p + (1 - α) * ((1 - (1 - β) * p) + 2 * β * p)))
          = p * p * ((1 - (1 - β) * p)
            * (α * p + (1 - α) * ((1 - (1 - β) * p) + 2 * β * p))) by ring]
      exact h3
    have hdenMb : 0 < 2 * (1 - α) ^ 2 * k := by nlinarith [mul_pos hsq hk]
    have hnumMa : 0 < p * p * (1 - (1 - β) * p) * (1 - (1 - β) * p)
        * (1 + 2 * β + α - 2 * α * β) := by
      have h4 : 0 < p * p * (((1 - (1 - β) * p) * (1 - (1 - β) * p))
          * (1 + 2 * β + α - 2 * α * β)) := mul_pos h2p (mul_pos hqe2 hbb)
      rw [show (p * p * (1 - (1 - β) * p) * (1 - (1 - β) * p)
        * (1 + 2 * β + α - 2 * α * β)) = p * p * (((1 - (1 - β) * p) * (1 - (1 - β) * p))
          * (1 + 2 * β + α - 2 * α * β)) by ring]
      exact h4
    have neMb : (p * p * (1 - (1 - β) * p)
        * (α * p + (1 - α) * ((1 - (1 - β) * p) + 2 * β * p)) / (2 * (1 - α) ^ 2 * k) : ℝ) ≠ 0 := by
      have hden2 : (2 * (1 - α) ^ 2 * k : ℝ) ≠ 0 := ne_of_gt hdenMb
      exact div_ne_zero (ne_of_gt hnumMb) hden2
    have neMa : (p * p * (1 - (1 - β) * p) * (1 - (1 - β) * p)
        * (1 + 2 * β + α - 2 * α * β) / (4 * (1 - α) ^ 3 * k) : ℝ) ≠ 0 := by
      have hden3 : (4 * (1 - α) ^ 3 * k : ℝ) ≠ 0 := ne_of_gt hKc
      exact div_ne_zero (ne_of_gt hnumMa) hden3
    have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk
    have hane : (1 - α : ℝ) ≠ 0 := ne_of_gt h1a
    have hqne : (1 - (1 - β) * p : ℝ) ≠ 0 := ne_of_gt hqe
    have hbne : (1 + 2 * β + α - 2 * α * β : ℝ) ≠ 0 := ne_of_gt hbb
    have hgne : (α * p + (1 - α) * (1 - (1 - β) * p + 2 * β * p) : ℝ) ≠ 0 := ne_of_gt hgb
    have hgval : 1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p
        = α * p + (1 - α) * (1 - (1 - β) * p + 2 * β * p) := by ring
    have hgne2 : (1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p : ℝ) ≠ 0 := by
      rw [hgval]
      exact hgne
    -- nonzero facts restated in the normal forms in which the atoms appear in the goal
    have hbneN : (1 + β * 2 - β * α * 2 + α : ℝ) ≠ 0 := by
      have h0 := hbne
      ring_nf at h0 ⊢
      exact h0
    have hgneN : (1 - p + p * β * 3 - p * β * α * 3 + p * α * 2 - α : ℝ) ≠ 0 := by
      have h0 := hgne2
      ring_nf at h0 ⊢
      exact h0
    -- clear the nested fractions with explicit quotient lemmas instead of field_simp
    rw [div_div_div_eq, div_div_div_eq]
    have hX1 : (4 * (1 - α) * k * (p * p * (1 - (1 - β) * p)
          * (α * p + (1 - α) * (1 - (1 - β) * p + 2 * β * p))) : ℝ) ≠ 0 :=
      ne_of_gt (mul_pos hK4 hnumMb)
    have hB2p : 0 < 4 * k * (1 - α) * (1 - α) :=
      mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hk) h1a) h1a
    have hX2 : (4 * k * (1 - α) * (1 - α) * (p * p * (1 - (1 - β) * p)
          * (1 - (1 - β) * p) * (1 + 2 * β + α - 2 * α * β)) : ℝ) ≠ 0 :=
      ne_of_gt (mul_pos hB2p hnumMa)
    rw [div_sub_div _ _ hX1 hX2]
    have hWne : (4 * (1 - α) * k * (p * p * (1 - (1 - β) * p)
          * (α * p + (1 - α) * (1 - (1 - β) * p + 2 * β * p))) *
        (4 * k * (1 - α) * (1 - α) * (p * p * (1 - (1 - β) * p)
          * (1 - (1 - β) * p) * (1 + 2 * β + α - 2 * α * β))) : ℝ) ≠ 0 :=
      mul_ne_zero hX1 hX2
    have hG'p : 0 < (1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p : ℝ) := by
      rw [hgval]
      exact hgb
    have hFp : 0 < 2 * p * (1 + 2 * β + α - 2 * α * β)
        * (1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p) :=
      mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hp0) hbb) hG'p
    rw [IsUnit.div_eq_div_iff (isUnit_iff_ne_zero.2 hWne) (isUnit_iff_ne_zero.2 (ne_of_gt hFp))]
    ring
  · have hcast : 2 * p * (1 + 2 * β + α - 2 * α * β)
        * (1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p)
        = 2 * p * ((1 + 2 * β + α - 2 * α * β)
          * (1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p)) := by ring
    rw [hcast]
    have hgval : 1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p
        = α * p + (1 - α) * (1 - (1 - β) * p + 2 * β * p) := by ring
    rw [hgval]
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hp0) (mul_pos hbb hgb)
