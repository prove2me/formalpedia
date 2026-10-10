-- Prove2me | solution 1 for ProjReflGrad.Linear.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:57:50.347538+00:00
-- url     : https://prove2.me/submissions/da002f99-493b-422d-8694-5163b17feae5

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

namespace RRAux_ProjReflGrad_Linear_theorem_3_3

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma proj_spec [CompleteSpace H] (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C)
    (hne : C.Nonempty) (w : H) :
    ProjReflGrad.Weak.proj C w ∈ C ∧
      ∀ q ∈ C, inner ℝ (w - ProjReflGrad.Weak.proj C w) (q - ProjReflGrad.Weak.proj C w) ≤ 0 := by
  obtain ⟨v, hvC, hv⟩ := exists_norm_eq_iInf_of_complete_convex hne hCcl.isComplete hCcv w
  have hex : ∃ p, ProjReflGrad.Weak.IsProj C w p := by
    refine ⟨v, hvC, fun q hq => ?_⟩
    rw [hv]
    exact ciInf_le ⟨0, by rintro _ ⟨r, rfl⟩; exact norm_nonneg _⟩ (⟨q, hq⟩ : C)
  have hp : ProjReflGrad.Weak.proj C w = hex.choose := by
    unfold ProjReflGrad.Weak.proj
    rw [dif_pos hex]
  rw [hp]
  obtain ⟨hpC, hpmin⟩ := hex.choose_spec
  refine ⟨hpC, ?_⟩
  have : ‖w - hex.choose‖ = ⨅ q : C, ‖w - q‖ := by
    apply le_antisymm
    · have : Nonempty C := ⟨⟨_, hpC⟩⟩
      exact le_ciInf (fun q => hpmin q q.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨r, rfl⟩; exact norm_nonneg _⟩ (⟨_, hpC⟩ : C)
  exact (norm_eq_iInf_iff_real_inner_le_zero hCcv hpC).mp this

lemma vi_step1 (X X1 Z A : H) (lam : ℝ) (h : inner ℝ ((X - lam • A) - X1) (Z - X1) ≤ 0) :
    ‖X1 - Z‖ ^ 2 ≤ ‖X - Z‖ ^ 2 - ‖X - X1‖ ^ 2 - 2 * lam * inner ℝ A (X1 - Z) := by
  have e : X - Z = (X - X1) + (X1 - Z) := by abel
  have e2 : (X - lam • A) - X1 = (X - X1) - lam • A := by abel
  have e3 : Z - X1 = -(X1 - Z) := by abel
  rw [e, norm_add_sq_real]
  rw [e2, e3, inner_neg_right, inner_sub_left, real_inner_smul_left] at h
  linarith

lemma vi_step2 (Xm Xn X1 Yn B : H) (lam : ℝ) (hy : Yn = (2 : ℝ) • Xn - Xm)
    (h1 : inner ℝ ((Xm - lam • B) - Xn) (X1 - Xn) ≤ 0)
    (h2 : inner ℝ ((Xm - lam • B) - Xn) (Xm - Xn) ≤ 0) :
    2 * lam * inner ℝ B (Yn - X1) ≤ ‖X1 - Xn‖ ^ 2 - ‖Yn - Xn‖ ^ 2 - ‖X1 - Yn‖ ^ 2 := by
  have hs := add_nonpos h1 h2
  rw [← inner_add_right] at hs
  have e1 : (X1 - Xn) + (Xm - Xn) = X1 - Yn := by rw [hy]; module
  have e2 : (Xm - lam • B) - Xn = (Xn - Yn) - lam • B := by rw [hy]; module
  rw [e1, e2, inner_sub_left, real_inner_smul_left] at hs
  have e3 : X1 - Xn = (X1 - Yn) - (Xn - Yn) := by abel
  have e4 : Yn - X1 = -(X1 - Yn) := by abel
  rw [e3, norm_sub_sq_real, e4, inner_neg_right, norm_sub_rev Yn Xn]
  have c1 := real_inner_comm (X1 - Yn) (Xn - Yn)
  have c2 := real_inner_comm B (X1 - Yn)
  nlinarith


lemma amgm (θ a b c s : ℝ) (hs : s * s = 2) (hs1 : 1 ≤ s) (hθ : 0 ≤ θ) :
    2 * θ * (a + b) * c ≤ θ * a ^ 2 + θ * c ^ 2 + θ * (1 + s) * b ^ 2 + θ * (s - 1) * c ^ 2 := by
  have h1 := mul_nonneg hθ (sq_nonneg (a - c))
  have h2 := mul_nonneg (mul_nonneg hθ (sub_nonneg.mpr hs1)) (sq_nonneg ((1 + s) * b - c))
  have e : θ * (s - 1) * ((1 + s) * b - c) ^ 2
      = θ * ((1 + s) * b ^ 2 - 2 * b * c + (s - 1) * c ^ 2) := by
    have : (s - 1) * (1 + s) = 1 := by nlinarith
    linear_combination (θ * b ^ 2 * (1 + s)) * this - θ * 2 * b * c * this + 0 * hs
  nlinarith [e]

lemma one_step [CompleteSpace H] (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C)
    (hne : C.Nonempty) (F : H → H) (L lam m : ℝ)
    (hC2s : ProjReflGrad.Linear.IsStronglyMonotoneMap F m)
    (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L) (hlam0 : 0 < lam)
    (hθ : lam * L * (1 + Real.sqrt 2) ≤ 1)
    (z : H) (Xm Xn X1 Yn Ym : H) (hXm : Xm ∈ C) (hz : z ∈ C) (hy : Yn = (2 : ℝ) • Xn - Xm)
    (hXn : Xn = ProjReflGrad.Weak.proj C (Xm - lam • F Ym))
    (hX1 : X1 = ProjReflGrad.Weak.proj C (Xn - lam • F Yn)) :
    ‖X1 - z‖ ^ 2 + lam * L * ‖X1 - Yn‖ ^ 2 + 2 * lam * inner ℝ (F z) (Xn - z)
      ≤ ‖Xn - z‖ ^ 2 + lam * L * ‖Xn - Ym‖ ^ 2 + 2 * lam * inner ℝ (F z) (Xm - z)
        - (1 - lam * L * (1 + Real.sqrt 2)) * ‖X1 - Yn‖ ^ 2
        - 2 * lam * m * ‖Yn - z‖ ^ 2 - 2 * lam * inner ℝ (F z) (Xn - z) := by
  obtain ⟨hX1C, hX1vi⟩ := proj_spec C hCcl hCcv hne (Xn - lam • F Yn)
  obtain ⟨hXnC, hXnvi⟩ := proj_spec C hCcl hCcv hne (Xm - lam • F Ym)
  rw [← hX1] at hX1C hX1vi
  rw [← hXn] at hXnC hXnvi
  have E1 := vi_step1 Xn X1 z (F Yn) lam (hX1vi z hz)
  have E2 := vi_step2 Xm Xn X1 Yn (F Ym) lam hy (hXnvi X1 hX1C) (hXnvi Xm hXm)
  set s := Real.sqrt 2 with hsdef
  have hs : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr (by norm_num)
  -- Lipschitz/Cauchy–Schwarz
  have E3 : inner ℝ (F Yn - F Ym) (Yn - X1) ≤ L * (‖Yn - Xn‖ + ‖Xn - Ym‖) * ‖X1 - Yn‖ := by
    have h1 := real_inner_le_norm (F Yn - F Ym) (Yn - X1)
    have h2 := hC3 Yn Ym
    have h3 : ‖Yn - Ym‖ ≤ ‖Yn - Xn‖ + ‖Xn - Ym‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev Yn X1] at h1
    have h4 : L * ‖Yn - Ym‖ ≤ L * (‖Yn - Xn‖ + ‖Xn - Ym‖) := mul_le_mul_of_nonneg_left h3 hL.le
    have h5 := mul_le_mul_of_nonneg_right (h2.trans h4) (norm_nonneg (X1 - Yn))
    linarith
  have E4 := hC2s Yn z
  have E5 : inner ℝ (F z) (Yn - z) = 2 * inner ℝ (F z) (Xn - z) - inner ℝ (F z) (Xm - z) := by
    have : Yn - z = (2 : ℝ) • (Xn - z) - (Xm - z) := by rw [hy]; module
    rw [this, inner_sub_right, real_inner_smul_right]
  have E6 : inner ℝ (F Yn) (X1 - z) = inner ℝ (F Yn - F z) (Yn - z) + inner ℝ (F z) (Yn - z)
      - inner ℝ (F Yn - F Ym) (Yn - X1) - inner ℝ (F Ym) (Yn - X1) := by
    have : X1 - z = (Yn - z) - (Yn - X1) := by abel
    rw [this, inner_sub_right, inner_sub_left, inner_sub_left]; ring
  have E7 := amgm (lam * L) ‖Xn - Ym‖ ‖Yn - Xn‖ ‖X1 - Yn‖ s hs hs1 (by positivity)
  have hl2 : 0 ≤ 2 * lam := by positivity
  have F3 := mul_le_mul_of_nonneg_left E3 hl2
  have F4 := mul_le_mul_of_nonneg_left E4 hl2
  have F5 := congrArg (fun t => 2 * lam * t) E5
  have F6 := congrArg (fun t => 2 * lam * t) E6
  rw [norm_sub_rev Xn X1] at E1
  have hb : lam * L * (1 + s) * ‖Yn - Xn‖ ^ 2 ≤ ‖Yn - Xn‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hθ (sq_nonneg ‖Yn - Xn‖)
    linarith
  linarith [E1, E2, F3, F4, F5, F6, E7, hb]


lemma contract (P1 P0 c2 d2 g e θ lm : ℝ) (he : 0 < e) (hθ : 0 ≤ θ) (hlm : 0 < lm)
    (hc : 0 ≤ c2) (hd : 0 ≤ d2) (hg : 0 ≤ g)
    (h1 : P1 ≤ P0 - e * c2 - 2 * lm * d2 - g) (h2 : P1 ≤ (2 + θ) * c2 + 2 * d2 + g) :
    P1 ≤ ((2 + θ) / e + 1 / lm + 1) / ((2 + θ) / e + 1 / lm + 1 + 1) * P0 := by
  set K := (2 + θ) / e + 1 / lm + 1 with hK
  have hK1 : (2 + θ) ≤ K * e := by
    have : (2 + θ) / e * e = 2 + θ := div_mul_cancel₀ _ he.ne'
    have h3 : 0 ≤ (1 / lm + 1) * e := by positivity
    nlinarith
  have hK2 : 1 ≤ K * lm := by
    have : 1 / lm * lm = 1 := div_mul_cancel₀ _ hlm.ne'
    have h3 : 0 ≤ ((2 + θ) / e + 1) * lm := by positivity
    nlinarith
  have hK3 : 1 ≤ K := by have : 0 ≤ (2 + θ) / e + 1 / lm := by positivity
                         linarith
  have a1 : (2 + θ) * c2 ≤ K * e * c2 := mul_le_mul_of_nonneg_right hK1 hc
  have a2 : 2 * d2 ≤ K * (2 * lm * d2) := by nlinarith
  have a3 : g ≤ K * g := by nlinarith
  have key : P1 * (K + 1) ≤ K * P0 := by nlinarith
  have hpos : 0 < K + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

lemma sq_tri (u v w : H) : ‖u - w‖ ^ 2 ≤ 2 * ‖u - v‖ ^ 2 + 2 * ‖v - w‖ ^ 2 := by
  have h := norm_sub_le_norm_sub_add_norm_sub u v w
  have h0 := norm_nonneg (u - w)
  nlinarith [sq_nonneg (‖u - v‖ - ‖v - w‖)]

end RRAux_ProjReflGrad_Linear_theorem_3_3

open ProjReflGrad.Linear in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L lam m : ℝ)
    (hC1 : (ProjReflGrad.Weak.solSet C F).Nonempty) (hm : 0 < m) (hC2s : IsStronglyMonotoneMap F m)
    (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L)
    (hlam0 : 0 < lam) (hlam1 : lam < (Real.sqrt 2 - 1) / L)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) :
    ∀ z ∈ ProjReflGrad.Weak.solSet C F, ∃ γ M : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < M ∧ ∀ n : ℕ, ‖x n - z‖ ≤ M * γ ^ n := by
  intro z hz
  have hzC : z ∈ C := hz.1
  have hne : C.Nonempty := ⟨z, hzC⟩
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hθlt : lam * L < Real.sqrt 2 - 1 := by
    rw [lt_div_iff₀ hL] at hlam1; exact hlam1
  have hs1 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hθ1 : lam * L * (1 + Real.sqrt 2) < 1 := by nlinarith
  have hθ0 : 0 ≤ lam * L := by positivity
  set e := 1 - lam * L * (1 + Real.sqrt 2) with he
  have hepos : 0 < e := by linarith
  have hxC : ∀ k, x (k + 1) ∈ C := by
    intro k
    rw [(hrun.2 k).1]
    exact (RRAux_ProjReflGrad_Linear_theorem_3_3.proj_spec C hCcl hCcv hne _).1
  have hg : ∀ k, 0 ≤ inner ℝ (F z) (x (k + 1) - z) := fun k => hz.2 _ (hxC k)
  let P : ℕ → ℝ := fun k => ‖x (k + 1) - z‖ ^ 2 + lam * L * ‖x (k + 1) - y k‖ ^ 2
    + 2 * lam * inner ℝ (F z) (x k - z)
  set γ := ((2 + lam * L) / e + 1 / (lam * m) + 1) / ((2 + lam * L) / e + 1 / (lam * m) + 1 + 1)
    with hγ
  have hrec : ∀ k, P (k + 2) ≤ γ * P (k + 1) := by
    intro k
    have hstep := RRAux_ProjReflGrad_Linear_theorem_3_3.one_step C hCcl hCcv hne F L lam m hC2s
      hL hC3 hlam0 hθ1.le z (x (k + 1)) (x (k + 2)) (x (k + 3)) (y (k + 2)) (y (k + 1))
      (hxC k) hzC (hrun.2 (k + 1)).2 (hrun.2 (k + 1)).1 (hrun.2 (k + 2)).1
    have htri := RRAux_ProjReflGrad_Linear_theorem_3_3.sq_tri (x (k + 3)) (y (k + 2)) z
    have hgk := hg (k + 1)
    have hlm : 0 < lam * m := by positivity
    have h2 : P (k + 2) ≤ (2 + lam * L) * ‖x (k + 3) - y (k + 2)‖ ^ 2
        + 2 * ‖y (k + 2) - z‖ ^ 2 + 2 * lam * inner ℝ (F z) (x (k + 2) - z) := by
      simp only [P]; nlinarith
    have h1 : P (k + 2) ≤ P (k + 1) - e * ‖x (k + 3) - y (k + 2)‖ ^ 2
        - 2 * (lam * m) * ‖y (k + 2) - z‖ ^ 2 - 2 * lam * inner ℝ (F z) (x (k + 2) - z) := by
      simp only [P]; rw [he]; linarith
    exact RRAux_ProjReflGrad_Linear_theorem_3_3.contract _ _ _ _ _ e (lam * L) (lam * m) hepos
      hθ0 hlm (sq_nonneg _) (sq_nonneg _) (by positivity) h1 h2
  have hγ0 : 0 < γ := by
    have : 0 < 1 / (lam * m) := by positivity
    rw [hγ]; positivity
  have hγ1 : γ < 1 := by
    rw [hγ, div_lt_one (by positivity)]; linarith
  have hiter : ∀ j, P (j + 1) ≤ γ ^ j * P 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc P (j + 1 + 1) ≤ γ * P (j + 1) := hrec j
        _ ≤ γ * (γ ^ j * P 1) := mul_le_mul_of_nonneg_left ih hγ0.le
        _ = γ ^ (j + 1) * P 1 := by ring
  set ρ := Real.sqrt γ with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr hγ0
  have hρ1 : ρ < 1 := by
    rw [hρ, ← Real.sqrt_one]; exact Real.sqrt_lt_sqrt hγ0.le hγ1
  have hρsq : ρ ^ 2 = γ := Real.sq_sqrt hγ0.le
  have hbound : ∀ j, ‖x (j + 2) - z‖ ≤ ρ ^ j * Real.sqrt (P 1) := by
    intro j
    have h1 : ‖x (j + 2) - z‖ ^ 2 ≤ P (j + 1) := by
      have := hg j
      have : 0 ≤ lam * L * ‖x (j + 2) - y (j + 1)‖ ^ 2 := by positivity
      have : 0 ≤ 2 * lam * inner ℝ (F z) (x (j + 1) - z) := by positivity
      simp only [P]; linarith
    have hP1 : 0 ≤ P 1 := by
      have := hg 0
      have : 0 ≤ lam * L * ‖x 2 - y 1‖ ^ 2 := by positivity
      have : 0 ≤ 2 * lam * inner ℝ (F z) (x 1 - z) := by positivity
      simp only [P]; positivity
    have h2 : ‖x (j + 2) - z‖ ^ 2 ≤ (ρ ^ j * Real.sqrt (P 1)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP1, ← pow_mul, mul_comm j 2, pow_mul, hρsq]
      exact h1.trans (hiter j)
    have h3 : 0 ≤ ρ ^ j * Real.sqrt (P 1) := by positivity
    calc ‖x (j + 2) - z‖ = Real.sqrt (‖x (j + 2) - z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((ρ ^ j * Real.sqrt (P 1)) ^ 2) := Real.sqrt_le_sqrt h2
      _ = ρ ^ j * Real.sqrt (P 1) := Real.sqrt_sq h3
  set num := Real.sqrt (P 1) + ‖x 0 - z‖ + ‖x 1 - z‖ + 1 with hnum
  have hnum0 : 0 < num := by positivity
  have hρ2 : 0 < ρ ^ 2 := by positivity
  refine ⟨ρ, num / ρ ^ 2, hρ0, hρ1, by positivity, ?_⟩
  have hMρ : num / ρ ^ 2 * ρ ^ 2 = num := div_mul_cancel₀ _ hρ2.ne'
  have hρ2le : ρ ^ 2 ≤ 1 := by nlinarith
  have hM0 : 0 ≤ num / ρ ^ 2 := by positivity
  intro n
  match n with
  | 0 =>
    have : num / ρ ^ 2 * ρ ^ 2 ≤ num / ρ ^ 2 := by nlinarith
    simp only [pow_zero, mul_one]
    have : ‖x 0 - z‖ ≤ num := by
      have := Real.sqrt_nonneg (P 1); have := norm_nonneg (x 1 - z); linarith
    linarith
  | 1 =>
    have : num / ρ ^ 2 * ρ ^ 2 ≤ num / ρ ^ 2 * ρ := by
      apply mul_le_mul_of_nonneg_left _ hM0
      nlinarith
    simp only [pow_one]
    have : ‖x 1 - z‖ ≤ num := by
      have := Real.sqrt_nonneg (P 1); have := norm_nonneg (x 0 - z); linarith
    linarith
  | j + 2 =>
    have hb := hbound j
    have : num / ρ ^ 2 * ρ ^ (j + 2) = num * ρ ^ j := by
      rw [pow_add, ← mul_assoc, mul_comm _ (ρ ^ j), mul_assoc, hMρ, mul_comm]
    rw [this]
    have hpj : 0 ≤ ρ ^ j := by positivity
    have : Real.sqrt (P 1) ≤ num := by
      have := norm_nonneg (x 0 - z); have := norm_nonneg (x 1 - z); linarith
    calc ‖x (j + 2) - z‖ ≤ ρ ^ j * Real.sqrt (P 1) := hb
      _ ≤ ρ ^ j * num := mul_le_mul_of_nonneg_left this hpj
      _ = num * ρ ^ j := mul_comm _ _

#print axioms solution
