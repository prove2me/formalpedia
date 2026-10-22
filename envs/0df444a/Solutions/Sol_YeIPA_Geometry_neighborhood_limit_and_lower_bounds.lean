-- Prove2me | solution 1 for YeIPA.Geometry.neighborhood_limit_and_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:11:31.575427+00:00
-- url     : https://prove2.me/submissions/4ef40b37-a3f6-40b7-bf57-0dfbee75b52d

import Mathlib
import Definitions.Def_YeIPA_Geometry_CentralPath

open Matrix Filter Topology
open YeIPA.Geometry

theorem g69c_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hx : A *ᵥ x = b)
    (hs : Aᵀ *ᵥ y + s = c) : c ⬝ᵥ x = b ⬝ᵥ y + x ⬝ᵥ s := by
  rw [← hs, ← hx, add_dotProduct, mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm s x,
    dotProduct_comm (A *ᵥ x) y]

theorem g69c_nonneg_dot {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (hs : ∀ j, 0 ≤ s j)
    (j : Fin n) : x j * s j ≤ x ⬝ᵥ s := by
  unfold dotProduct
  exact Finset.single_le_sum (f := fun i => x i * s i) (fun i _ => mul_nonneg (hx i) (hs i))
    (Finset.mem_univ j)

theorem g69c_neg_lb {n : ℕ} (v : Fin n → ℝ) (j : Fin n) : -negInfNorm v ≤ v j := by
  unfold negInfNorm
  have h1 : (⨅ i, v i) ≤ v j := ciInf_le (Finite.bddBelow_range _) j
  have h2 := min_le_right 0 (⨅ i, v i)
  have h3 := neg_abs_le (min 0 (⨅ i, v i))
  linarith

theorem g69c_tend_dot {n : ℕ} (c : Fin n → ℝ) (xk : ℕ → Fin n → ℝ) (xbar : Fin n → ℝ)
    (h : Tendsto xk atTop (𝓝 xbar)) : Tendsto (fun k => c ⬝ᵥ xk k) atTop (𝓝 (c ⬝ᵥ xbar)) :=
  ((continuous_const.dotProduct continuous_id).tendsto xbar).comp h

/-- Theorem 2.18 (ii) (Ye 1997, p. 74). -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hrank : A.rank = m) (hmn : m < n)
    (hP : ∃ x, PrimalInterior A b x) (hD : ∃ y s, DualInterior A c y s)
    (nrm : (Fin n → ℝ) → ℝ) (hnrm : ∀ v, negInfNorm v ≤ nrm v)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    (∀ (xk : ℕ → Fin n → ℝ) (yk : ℕ → Fin m → ℝ) (sk : ℕ → Fin n → ℝ)
        (xbar : Fin n → ℝ) (ybar : Fin m → ℝ) (sbar : Fin n → ℝ),
        (∀ k, InNeighborhood A b c nrm η (xk k) (yk k) (sk k)) →
        Tendsto (fun k => mu (xk k) (sk k)) atTop (𝓝 0) →
        Tendsto xk atTop (𝓝 xbar) → Tendsto yk atTop (𝓝 ybar) → Tendsto sk atTop (𝓝 sbar) →
        IsPrimalOptimal A b c xbar ∧ IsDualOptimal A b c ybar sbar) ∧
    (∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ), InNeighborhood A b c nrm η x y s →
        (∀ xstar, IsPrimalOptimal A b c xstar → ∀ j ∈ Pstar A b c,
          (1 - η) * xstar j / n ≤ x j) ∧
        (∀ ystar sstar, IsDualOptimal A b c ystar sstar → ∀ j ∈ Zstar A b c,
          (1 - η) * sstar j / n ≤ s j)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le m) hmn)
  constructor
  · intro xk yk sk xbar ybar sbar hN hmu hx hy hs
    have hgap : Tendsto (fun k => xk k ⬝ᵥ sk k) atTop (𝓝 0) := by
      have := hmu.const_mul (n : ℝ)
      rw [mul_zero] at this
      refine this.congr (fun k => ?_)
      unfold mu; field_simp
    have hAx : A *ᵥ xbar = b := by
      have h1 : Tendsto (fun k => A *ᵥ xk k) atTop (𝓝 (A *ᵥ xbar)) :=
        (((continuous_const (y := A)).matrix_mulVec continuous_id).tendsto xbar).comp hx
      have h2 : (fun k => A *ᵥ xk k) = fun _ => b := funext fun k => (hN k).1.1
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    have hys : Aᵀ *ᵥ ybar + sbar = c := by
      have h1 : Tendsto (fun k => Aᵀ *ᵥ yk k + sk k) atTop (𝓝 (Aᵀ *ᵥ ybar + sbar)) :=
        ((((continuous_const (y := Aᵀ)).matrix_mulVec continuous_id).tendsto ybar).comp
          hy).add hs
      have h2 : (fun k => Aᵀ *ᵥ yk k + sk k) = fun _ => c := funext fun k => (hN k).2.1.1
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    have hxnn : ∀ j, 0 ≤ xbar j := fun j =>
      ge_of_tendsto' ((continuous_apply j).continuousAt.tendsto.comp hx)
        (fun k => ((hN k).1.2 j).le)
    have hsnn : ∀ j, 0 ≤ sbar j := fun j =>
      ge_of_tendsto' ((continuous_apply j).continuousAt.tendsto.comp hs)
        (fun k => ((hN k).2.1.2 j).le)
    have hcx := g69c_tend_dot c xk xbar hx
    have hby := g69c_tend_dot b yk ybar hy
    refine ⟨⟨⟨hAx, hxnn⟩, fun x' hx' => ?_⟩, ⟨⟨hys, hsnn⟩, fun y' s' hd' => ?_⟩⟩
    · -- c⬝x_k - x_k⬝s_k = b⬝y_k ≤ c⬝x'
      have hlim := hcx.sub hgap
      rw [sub_zero] at hlim
      refine le_of_tendsto' hlim (fun k => ?_)
      have e1 := g69c_gap A b c (xk k) (yk k) (sk k) (hN k).1.1 (hN k).2.1.1
      have e2 := g69c_gap A b c x' (yk k) (sk k) hx'.1 (hN k).2.1.1
      have : 0 ≤ x' ⬝ᵥ sk k := Finset.sum_nonneg (fun j _ => mul_nonneg (hx'.2 j)
        ((hN k).2.1.2 j).le)
      linarith
    · have hlim := hby.add hgap
      rw [add_zero] at hlim
      refine ge_of_tendsto' hlim (fun k => ?_)
      have e1 := g69c_gap A b c (xk k) (yk k) (sk k) (hN k).1.1 (hN k).2.1.1
      have e2 := g69c_gap A b c (xk k) y' s' (hN k).1.1 hd'.1
      have : 0 ≤ xk k ⬝ᵥ s' := Finset.sum_nonneg (fun j _ => mul_nonneg ((hN k).1.2 j).le
        (hd'.2 j))
      linarith
  · intro x y s hN
    obtain ⟨⟨hAx, hxpos⟩, ⟨hys, hspos⟩, hnb⟩ := hN
    have hmupos : 0 < mu x s := by
      unfold mu
      apply div_pos _ hn
      obtain ⟨j0⟩ : Nonempty (Fin n) := ⟨⟨0, lt_of_le_of_lt (Nat.zero_le m) hmn⟩⟩
      exact lt_of_lt_of_le (mul_pos (hxpos j0) (hspos j0))
        (g69c_nonneg_dot x s (fun j => (hxpos j).le) (fun j => (hspos j).le) j0)
    have hxs : x ⬝ᵥ s = n * mu x s := by unfold mu; field_simp
    have hlow : ∀ j, (1 - η) * mu x s ≤ x j * s j := by
      intro j
      have := g69c_neg_lb (fun j => x j * s j - mu x s) j
      have := hnrm (fun j => x j * s j - mu x s)
      linarith
    constructor
    · intro xstar hopt j _
      have e1 := g69c_gap A b c xstar y s hopt.1.1 hys
      have e2 := g69c_gap A b c x y s hAx hys
      have h3 := hopt.2 x ⟨hAx, fun j => (hxpos j).le⟩
      have h4 := g69c_nonneg_dot xstar s hopt.1.2 (fun j => (hspos j).le) j
      have h5 := hlow j
      have hsj := hspos j
      rw [div_le_iff₀ hn]
      have key : (1 - η) * xstar j * s j ≤ x j * n * s j := by
        nlinarith [mul_le_mul_of_nonneg_left (show xstar j * s j ≤ n * mu x s by linarith)
          (show 0 ≤ 1 - η by linarith)]
      exact le_of_mul_le_mul_right key hsj
    · intro ystar sstar hopt j _
      have e1 := g69c_gap A b c x ystar sstar hAx hopt.1.1
      have e2 := g69c_gap A b c x y s hAx hys
      have h3 := hopt.2 y s ⟨hys, fun j => (hspos j).le⟩
      have h4 := g69c_nonneg_dot x sstar (fun j => (hxpos j).le) hopt.1.2 j
      have h5 := hlow j
      have hxj := hxpos j
      rw [div_le_iff₀ hn]
      have key : (1 - η) * sstar j * x j ≤ s j * n * x j := by
        nlinarith [mul_le_mul_of_nonneg_left (show x j * sstar j ≤ n * mu x s by linarith)
          (show 0 ≤ 1 - η by linarith)]
      exact le_of_mul_le_mul_right key hxj
