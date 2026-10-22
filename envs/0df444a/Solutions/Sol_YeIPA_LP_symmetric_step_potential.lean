-- Prove2me | solution 1 for YeIPA.LP.symmetric_step_potential
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:18:49.618751+00:00
-- url     : https://prove2.me/submissions/ae4ccf6c-8de3-439d-9ab9-522aef890618

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction

open Matrix
open YeIPA.LP
theorem g70ye_log_term {d r : ℝ} (hd : |d| ≤ r) (hr : r < 1) :
    d - d ^ 2 / (2 * (1 - r)) ≤ Real.log (1 + d) := by
  have hr0 : 0 ≤ r := le_trans (abs_nonneg _) hd
  have h1r : 0 < 1 - r := by linarith
  rcases le_total 0 d with h | h
  · -- x = d/(2+d)
    set x := d / (2 + d) with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
    have key := Real.sum_range_le_log_div hx0 hx1 1
    simp only [Finset.sum_range_one, mul_zero, zero_add, pow_one, Nat.cast_zero] at key
    have he : (1 + x) / (1 - x) = 1 + d := by
      rw [hx]; field_simp; ring
    rw [he] at key
    have hsq : d - d ^ 2 / (2 * (1 - r)) ≤ d - d ^ 2 / 2 := by
      have : d ^ 2 / 2 ≤ d ^ 2 / (2 * (1 - r)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
      linarith
    have h2 : d - d ^ 2 / 2 ≤ 2 * x := by
      rw [hx]; rw [show 2 * (d / (2 + d)) = 2 * d / (2 + d) by ring, le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg d, mul_nonneg h (sq_nonneg d)]
    linarith
  · have hd' : -d ≤ r := by rw [abs_of_nonpos h] at hd; exact hd
    have hu : 0 < 1 + d := by linarith
    set u := 1 + d with hu'
    have hu0 : u ≠ 0 := hu.ne'
    have hu1 : 1 + u ≠ 0 := by linarith
    set x := (1 - u) / (1 + u) with hx
    have hx0 : 0 ≤ x := by apply div_nonneg <;> linarith
    have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
    have key := Real.log_div_le_sum_range_add hx0 hx1 0
    clear_value x u
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, mul_zero, pow_one] at key
    have h1x : 1 - x ≠ 0 := by linarith
    have h1x2 : 1 - x ^ 2 ≠ 0 := by nlinarith
    have he : (1 + x) / (1 - x) = u⁻¹ := by
      rw [div_eq_iff h1x, hx]; field_simp; ring
    have he2 : x / (1 - x ^ 2) = (u⁻¹ - u) / 4 := by
      rw [div_eq_iff h1x2, hx]; field_simp; ring
    rw [he, he2, Real.log_inv] at key
    have h3 : d - d ^ 2 / (2 * (1 - r)) ≤ d - d ^ 2 / (2 * u) := by
      have : d ^ 2 / (2 * u) ≤ d ^ 2 / (2 * (1 - r)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
      linarith
    have h4 : d - d ^ 2 / (2 * u) = - (2 * ((u⁻¹ - u) / 4)) := by
      have : (1 + d) ≠ 0 := by linarith
      rw [hu']; field_simp; ring
    linarith


theorem g70ye_pdcore {n : ℕ} (hn : 0 < n) (x s dx ds : Fin n → ℝ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, 0 < s j) (K β : ℝ) (hK : 0 < K) (hβ : K * β = x ⬝ᵥ s)
    (hdir : ∀ j, s j * dx j + x j * ds j = β - x j * s j) (horth : dx ⬝ᵥ ds = 0)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (θ : ℝ)
    (hθ : θ = α * Real.sqrt (⨅ j, x j * s j) /
      Real.sqrt (∑ j, ((β - x j * s j) / Real.sqrt (x j * s j)) ^ 2)) :
    (∀ j, 0 < x j + θ * dx j) ∧ (∀ j, 0 < s j + θ * ds j) ∧
    (K * Real.log ((x + θ • dx) ⬝ᵥ (s + θ • ds)) -
        ∑ j, Real.log ((x + θ • dx) j * (s + θ • ds) j)) -
      (K * Real.log (x ⬝ᵥ s) - ∑ j, Real.log (x j * s j)) ≤
      -α * Real.sqrt (⨅ j, x j * s j) *
        (Real.sqrt (∑ j, ((β - x j * s j) / Real.sqrt (x j * s j)) ^ 2) / β) +
        α ^ 2 / (2 * (1 - α)) := by
  have hv : ∀ j, 0 < x j * s j := fun j => mul_pos (hx j) (hs j)
  have hxs : 0 < x ⬝ᵥ s := by
    have j : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun i _ => hv i) ⟨j, Finset.mem_univ j⟩
  have hβ0 : 0 < β := by
    by_contra h; push_neg at h; have := mul_nonpos_of_nonneg_of_nonpos hK.le h; linarith
  set mm := ⨅ j, x j * s j with hmm
  have hm_le : ∀ j, mm ≤ x j * s j := fun j => ciInf_le (Finite.bddBelow_range _) j
  have hm_pos : 0 < mm := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun j => x j * s j)
    rw [hmm, ← hj]; exact hv j
  set R := Real.sqrt (∑ j, ((β - x j * s j) / Real.sqrt (x j * s j)) ^ 2) with hR
  have hterm : ∀ j, ((β - x j * s j) / Real.sqrt (x j * s j)) ^ 2 =
      (β - x j * s j) ^ 2 / (x j * s j) := fun j => by
    rw [div_pow, Real.sq_sqrt (hv j).le]
  have hR2 : R ^ 2 = ∑ j, (β - x j * s j) ^ 2 / (x j * s j) := by
    rw [hR, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun j _ => hterm j
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hcrit : 0 ≤ α ^ 2 / (2 * (1 - α)) := by
    have : 0 < 1 - α := by linarith
    positivity
  rcases hR0.eq_or_lt with hRz | hRpos
  · have hθ0 : θ = 0 := by rw [hθ, ← hRz, div_zero]
    subst hθ0
    simp only [zero_smul, add_zero, zero_mul]
    refine ⟨hx, hs, ?_⟩
    rw [← hRz]; simp only [zero_div, mul_zero, sub_self, zero_add]; exact hcrit
  -- R > 0
  set a : Fin n → ℝ := fun j => dx j / x j with ha
  set b' : Fin n → ℝ := fun j => ds j / s j with hb
  have hab : ∀ j, a j + b' j = (β - x j * s j) / (x j * s j) := by
    intro j; simp only [ha, hb]
    have := hx j; have := hs j
    rw [div_add_div _ _ (hx j).ne' (hs j).ne', ← hdir j]; field_simp
  have hT : ∀ j, x j * s j * (a j ^ 2 + b' j ^ 2) =
      (β - x j * s j) ^ 2 / (x j * s j) - 2 * (dx j * ds j) := by
    intro j
    have e : x j * s j * (a j ^ 2 + b' j ^ 2) =
        (s j * dx j + x j * ds j) ^ 2 / (x j * s j) - 2 * (dx j * ds j) := by
      simp only [ha, hb]; have := hx j; have := hs j; field_simp; ring
    rw [e, hdir j]
  have hsumT : ∑ j, x j * s j * (a j ^ 2 + b' j ^ 2) = R ^ 2 := by
    rw [Finset.sum_congr rfl fun j _ => hT j, Finset.sum_sub_distrib, ← Finset.mul_sum, hR2]
    have : ∑ j, dx j * ds j = 0 := horth
    rw [this]; ring
  have hθsq : θ ^ 2 = α ^ 2 * mm / R ^ 2 := by
    rw [hθ, div_pow, mul_pow, Real.sq_sqrt hm_pos.le]
  have hsq : ∑ j, ((θ * a j) ^ 2 + (θ * b' j) ^ 2) ≤ α ^ 2 := by
    have h1 : mm * ∑ j, (a j ^ 2 + b' j ^ 2) ≤ R ^ 2 := by
      rw [← hsumT, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hm_le j) (by positivity)
    have e : ∑ j, ((θ * a j) ^ 2 + (θ * b' j) ^ 2) = θ ^ 2 * ∑ j, (a j ^ 2 + b' j ^ 2) := by
      rw [Finset.mul_sum]; congr 1; funext j; ring
    rw [e, hθsq]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc α ^ 2 * mm * ∑ j, (a j ^ 2 + b' j ^ 2) = α ^ 2 * (mm * ∑ j, (a j ^ 2 + b' j ^ 2)) := by
          ring
      _ ≤ α ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hbd : ∀ j, |θ * a j| ≤ α ∧ |θ * b' j| ≤ α := by
    intro j
    have h := Finset.single_le_sum (f := fun j => (θ * a j) ^ 2 + (θ * b' j) ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ j)
    have h1 : (θ * a j) ^ 2 ≤ α ^ 2 := by nlinarith [sq_nonneg (θ * b' j)]
    have h2 : (θ * b' j) ^ 2 ≤ α ^ 2 := by nlinarith [sq_nonneg (θ * a j)]
    exact ⟨abs_le.2 (abs_le_of_sq_le_sq' h1 hα0.le), abs_le.2 (abs_le_of_sq_le_sq' h2 hα0.le)⟩
  have hpa : ∀ j, 0 < 1 + θ * a j := fun j => by
    have := (abs_le.1 (hbd j).1).1; linarith
  have hpb : ∀ j, 0 < 1 + θ * b' j := fun j => by
    have := (abs_le.1 (hbd j).2).1; linarith
  have hxp : ∀ j, x j + θ * dx j = x j * (1 + θ * a j) := fun j => by
    simp only [ha]; have := hx j; field_simp
  have hsp : ∀ j, s j + θ * ds j = s j * (1 + θ * b' j) := fun j => by
    simp only [hb]; have := hs j; field_simp
  refine ⟨fun j => by rw [hxp j]; exact mul_pos (hx j) (hpa j),
    fun j => by rw [hsp j]; exact mul_pos (hs j) (hpb j), ?_⟩
  have hlogj : ∀ j, Real.log ((x + θ • dx) j * (s + θ • ds) j) =
      Real.log (x j * s j) + (Real.log (1 + θ * a j) + Real.log (1 + θ * b' j)) := by
    intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hxp j, hsp j, show x j * (1 + θ * a j) * (s j * (1 + θ * b' j)) =
      (x j * s j) * ((1 + θ * a j) * (1 + θ * b' j)) by ring,
      Real.log_mul (hv j).ne' (mul_pos (hpa j) (hpb j)).ne',
      Real.log_mul (hpa j).ne' (hpb j).ne']
  have hdot : (x + θ • dx) ⬝ᵥ (s + θ • ds) = x ⬝ᵥ s + θ * (n * β - x ⬝ᵥ s) := by
    have e1 : ∑ j, (s j * dx j + x j * ds j) = n * β - x ⬝ᵥ s := by
      rw [Finset.sum_congr rfl fun j _ => hdir j, Finset.sum_sub_distrib]; simp [dotProduct]
    have e2 : (x + θ • dx) ⬝ᵥ (s + θ • ds) = x ⬝ᵥ s + θ * ∑ j, (s j * dx j + x j * ds j) +
        θ ^ 2 * (dx ⬝ᵥ ds) := by
      simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2, e1, horth]; ring
  have hdotpos : 0 < (x + θ • dx) ⬝ᵥ (s + θ • ds) := by
    have j : Fin n := ⟨0, hn⟩
    refine Finset.sum_pos (fun i _ => ?_) ⟨j, Finset.mem_univ j⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hxp i, hsp i]; exact mul_pos (mul_pos (hx i) (hpa i)) (mul_pos (hs i) (hpb i))
  have hlog1 : Real.log ((x + θ • dx) ⬝ᵥ (s + θ • ds)) - Real.log (x ⬝ᵥ s) ≤
      θ * (n * β - x ⬝ᵥ s) / (x ⬝ᵥ s) := by
    rw [← Real.log_div hdotpos.ne' hxs.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hdotpos hxs)).trans (le_of_eq ?_)
    rw [hdot]; field_simp; ring
  have hlog2 : ∑ j, ((θ * a j + θ * b' j) - ((θ * a j) ^ 2 + (θ * b' j) ^ 2) / (2 * (1 - α))) ≤
      ∑ j, (Real.log (1 + θ * a j) + Real.log (1 + θ * b' j)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := g70ye_log_term (hbd j).1 hα1
    have h2 := g70ye_log_term (hbd j).2 hα1
    rw [add_div]; linarith
  have hsplit : ∑ j, ((θ * a j + θ * b' j) - ((θ * a j) ^ 2 + (θ * b' j) ^ 2) / (2 * (1 - α))) =
      θ * ∑ j, (a j + b' j) - (∑ j, ((θ * a j) ^ 2 + (θ * b' j) ^ 2)) / (2 * (1 - α)) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsq' : (∑ j, ((θ * a j) ^ 2 + (θ * b' j) ^ 2)) / (2 * (1 - α)) ≤ α ^ 2 / (2 * (1 - α)) :=
    div_le_div_of_nonneg_right hsq (by linarith)
  -- the linear identity
  have hL : β * ∑ j, (a j + b' j) = R ^ 2 + n * β - K * β := by
    rw [hR2, Finset.mul_sum, hβ]
    have : ∀ j, β * (a j + b' j) = (β - x j * s j) ^ 2 / (x j * s j) + (β - x j * s j) := by
      intro j; rw [hab j]; have := hx j; have := hs j; field_simp; ring
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [dotProduct]; ring
  have hKlin : K * (θ * (n * β - x ⬝ᵥ s) / (x ⬝ᵥ s)) = θ * (n - K) := by
    rw [← hβ]; field_simp
  have hθR : θ * (R ^ 2 / β) = α * Real.sqrt mm * (R / β) := by
    rw [hθ]; field_simp
  rw [Finset.sum_congr rfl fun j _ => hlogj j, Finset.sum_add_distrib]
  have hK1 := mul_le_mul_of_nonneg_left hlog1 hK.le
  rw [hKlin] at hK1
  have hlin : θ * (n - K) - θ * ∑ j, (a j + b' j) = -(θ * (R ^ 2 / β)) := by
    have : ∑ j, (a j + b' j) = (R ^ 2 + n * β - K * β) / β := by
      rw [← hL]; field_simp
    rw [this]; field_simp; ring
  rw [hθR] at hlin
  nlinarith [hlog2, hsplit, hsq', hK1, hlin]


/-- Lemma 4.11 (Ye 1997, p. 127). Under the standing assumptions (p. 63), let `(x, y, s) ∈ F̊`,
`ρ ≥ 0` (p. 121), let `d = (d_x, d_y, d_s)` solve (4.17) with `γ = n/(n + ρ)`, let `0 < α < 1`
and `θ = α√min(Xs) / ‖(XS)^{-1/2}((xᵀs/(n + ρ))e − Xs)‖` (4.18), and
`x⁺ = x + θd_x`, `y⁺ = y + θd_y`, `s⁺ = s + θd_s`. Then `(x⁺, y⁺, s⁺) ∈ F̊` and
`ψ_{n+ρ}(x⁺, s⁺) − ψ_{n+ρ}(x, s)
  ≤ −α√min(Xs) ‖(XS)^{-1/2}(e − ((n + ρ)/(xᵀs))Xs)‖ + α²/(2(1 − α))`. -/
theorem solution {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hA : StandingAssumptions A b c)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hF : IsInteriorFeasible A b c x y s)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsPDDirection A x s ((n : ℝ) / ((n : ℝ) + ρ)) dx dy ds) :
    IsInteriorFeasible A b c (x + pdStepSize ρ α x s • dx) (y + pdStepSize ρ α x s • dy)
        (s + pdStepSize ρ α x s • ds) ∧
      pdPotential ρ (x + pdStepSize ρ α x s • dx) (s + pdStepSize ρ α x s • ds) -
          pdPotential ρ x s ≤
        -α * Real.sqrt (vmin (fun j => x j * s j)) *
            norm2 (fun j => (1 - ((n : ℝ) + ρ) / (x ⬝ᵥ s) * (x j * s j)) /
              Real.sqrt (x j * s j))
          + α ^ 2 / (2 * (1 - α)) := by
  obtain ⟨hAx, hx, hAy, hs⟩ := hF
  obtain ⟨hdir1, hdir2, hdir3⟩ := hd
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hds : ds = -(Aᵀ *ᵥ dy) := (sub_eq_zero.1 hdir3).symm
  have horth : dx ⬝ᵥ ds = 0 := by
    rw [hds, dotProduct_neg, mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec, hdir2,
      dotProduct_zero, neg_zero]
  have hK : (0 : ℝ) < n + ρ := by linarith
  have hxs : 0 < x ⬝ᵥ s := by
    have j : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) ⟨j, Finset.mem_univ j⟩
  have hβ0 : 0 < x ⬝ᵥ s / ((n : ℝ) + ρ) := div_pos hxs hK
  obtain ⟨h1, h2, h3⟩ := g70ye_pdcore hn x s dx ds hx hs ((n : ℝ) + ρ) (x ⬝ᵥ s / ((n : ℝ) + ρ))
    hK (by field_simp) (fun j => by rw [hdir1 j]; field_simp) horth α hα0 hα1
    (pdStepSize ρ α x s) rfl
  refine ⟨⟨?_, fun j => ?_, ?_, fun j => ?_⟩, ?_⟩
  · rw [mulVec_add, mulVec_smul, hdir2, smul_zero, add_zero, hAx]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact h1 j
  · rw [mulVec_add, mulVec_smul, hds]
    rw [show Aᵀ *ᵥ y + pdStepSize ρ α x s • Aᵀ *ᵥ dy + (s + pdStepSize ρ α x s • -(Aᵀ *ᵥ dy)) =
      Aᵀ *ᵥ y + s by rw [smul_neg]; abel, hAy]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact h2 j
  · have hnorm : norm2 (fun j => (1 - ((n : ℝ) + ρ) / (x ⬝ᵥ s) * (x j * s j)) /
        Real.sqrt (x j * s j)) = Real.sqrt (∑ j, ((x ⬝ᵥ s / ((n : ℝ) + ρ) - x j * s j) /
          Real.sqrt (x j * s j)) ^ 2) / (x ⬝ᵥ s / ((n : ℝ) + ρ)) := by
      unfold norm2
      rw [eq_div_iff hβ0.ne']
      conv_lhs => arg 2; rw [← Real.sqrt_sq hβ0.le]
      rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg _), Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have hv : 0 < x j * s j := mul_pos (hx j) (hs j)
      have hsq : 0 < Real.sqrt (x j * s j) := Real.sqrt_pos.2 hv
      field_simp
    rw [hnorm]
    exact h3



