-- Prove2me | solution 1 for ShorNonsmooth.Fejer.polyak_inconsistent_best_value_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T11:23:29.038267+00:00
-- url     : https://prove2.me/submissions/f5cbad90-7e86-4388-a4d0-5425f8b65cb2

import Theorems.Thm_subgradients_bounded
import Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod

open Filter Topology
open ShorNonsmooth.Fejer

private theorem best_values_converge (u : ℕ → ℝ) (d : ℝ) (hd : ∀ k, d ≤ u k) :
    ∃ l : ℝ, Tendsto (fun k : ℕ =>
      (Finset.range (k+1)).inf' Finset.nonempty_range_add_one u) atTop (𝓝 l) ∧
      ∀ k, l ≤ u k := by
  let b : ℕ → ℝ := fun k => (Finset.range (k+1)).inf' Finset.nonempty_range_add_one u
  have hb : ∀ k, d ≤ b k := by
    intro k
    exact Finset.le_inf' _ _ (fun i _ => hd i)
  have ha : Antitone b := by
    intro i j hij
    apply Finset.le_inf'
    intro k hk
    exact Finset.inf'_le _ (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.add_le_add_right hij 1)))
  have hbelow : BddBelow (Set.range b) := ⟨d, by rintro _ ⟨k, rfl⟩; exact hb k⟩
  refine ⟨iInf b, tendsto_atTop_ciInf ha hbelow, ?_⟩
  intro k
  exact (ciInf_le hbelow k).trans (Finset.inf'_le _ (Finset.mem_range.mpr (Nat.lt_succ_self k)))

private theorem no_uniform_descent (r : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ k, 0 ≤ r k) (hstep : ∀ k, r (k+1) ≤ r k - ε) : False := by
  have hbound : ∀ k : ℕ, r k ≤ r 0 - k * ε := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := hstep k
      push_cast
      nlinarith
  obtain ⟨k, hk⟩ := exists_nat_gt (r 0 / ε)
  have hlarge : r 0 < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  have := hbound k
  have := hpos k
  linarith


theorem solution {n : ℕ} (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ConvexOn ℝ Set.univ ψ) (d : ℝ) (hd : 0 < d) (hdle : ∀ y, d ≤ ψ y)
    (hdatt : ∃ xm, ψ xm = d) (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient ψ x (g x))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : ∀ k, x (k + 1) = polyakStep ψ g 0 γ (x k)) :
    ∃ ℓ : ℝ, Tendsto (fun k : ℕ =>
        (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one (fun i => ψ (x i)))
        atTop (𝓝 ℓ) ∧ ℓ ≤ 2 * d / (2 - γ) := by
  obtain ⟨l, hlim, hl⟩ := best_values_converge (fun k => ψ (x k)) d (fun k => hdle (x k))
  refine ⟨l, hlim, ?_⟩
  by_contra hnot
  have hlarge : 2*d/(2-γ) < l := lt_of_not_ge hnot
  have htwo : 0 < 2-γ := sub_pos.mpr hγ2
  have hld : d < l := by
    have hh : d < 2*d/(2-γ) := (lt_div_iff₀ htwo).2 (by nlinarith)
    exact hh.trans hlarge
  have hD : 0 < (2-γ)*l-2*d := by
    have := (div_lt_iff₀ htwo).mp hlarge
    nlinarith
  obtain ⟨xm, hxm⟩ := hdatt
  have hgn (k : ℕ) : g (x k) ≠ 0 := by
    intro he
    have hh := hg (x k) xm
    simp only [he, inner_zero_left, hxm] at hh
    have := hl k
    linarith
  have hdescent (k : ℕ) : ‖x (k+1)-xm‖^2 ≤ ‖x k-xm‖^2 -
      γ*ψ (x k)*((2-γ)*ψ (x k)-2*d)/‖g (x k)‖^2 := by
    have hpsi : 0 < ψ (x k) := hd.trans_le (hdle (x k))
    have hnorm : 0 < ‖g (x k)‖ := norm_pos_iff.mpr (hgn k)
    have hinner : ψ (x k)-d ≤ inner ℝ (x k-xm) (g (x k)) := by
      have hh := hg (x k) xm
      rw [hxm, inner_sub_right] at hh
      rw [real_inner_comm, inner_sub_right]
      linarith
    have ht : 0 ≤ 2*(γ*ψ (x k)/‖g (x k)‖^2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hinner ht
    have hstep : x (k+1) = x k - (γ*ψ (x k)/‖g (x k)‖^2) • g (x k) := by
      rw [hx k, polyakStep, if_neg (not_or.mpr ⟨not_le.mpr hpsi, hgn k⟩)]
      simp only [sub_zero]
    rw [hstep, sub_right_comm (x k) _ xm, norm_sub_sq_real, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have heq : ‖x k-xm‖^2 - 2*(γ*ψ (x k)/‖g (x k)‖^2)*(ψ (x k)-d) +
        (γ*ψ (x k)/‖g (x k)‖^2)^2*‖g (x k)‖^2 =
        ‖x k-xm‖^2 - γ*ψ (x k)*((2-γ)*ψ (x k)-2*d)/‖g (x k)‖^2 := by
      field_simp [ne_of_gt hnorm]
      <;> ring
    nlinarith
  have hfactor (k : ℕ) : 0 < (2-γ)*ψ (x k)-2*d := by
    have hh := mul_le_mul_of_nonneg_left (hl k) htwo.le
    linarith
  have hmono (k : ℕ) : ‖x (k+1)-xm‖ ≤ ‖x k-xm‖ := by
    have hh := hdescent k
    have hp : 0 ≤ γ*ψ (x k)*((2-γ)*ψ (x k)-2*d)/‖g (x k)‖^2 := by
      exact div_nonneg (mul_nonneg (mul_nonneg hγ0.le (hd.trans_le (hdle (x k))).le)
        (hfactor k).le) (sq_nonneg _)
    nlinarith [norm_nonneg (x (k+1)-xm), norm_nonneg (x k-xm)]
  have hball (k : ℕ) : x k ∈ Metric.closedBall xm ‖x 0-xm‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hmono k).trans ih
  obtain ⟨B, hB, hBbound⟩ := subgradients_bounded hψ
    (Metric.isBounded_closedBall (x := xm) (r := ‖x 0-xm‖))
  let ε : ℝ := γ*d*((2-γ)*l-2*d)/B^2
  have hε : 0 < ε := by dsimp [ε]; positivity
  apply no_uniform_descent (fun k => ‖x k-xm‖^2) ε hε (fun k => sq_nonneg _)
  intro k
  have hnorm : 0 < ‖g (x k)‖ := norm_pos_iff.mpr (hgn k)
  have hpsi : 0 < ψ (x k) := hd.trans_le (hdle (x k))
  have hfac := hfactor k
  have hbound : ‖g (x k)‖ ≤ B := hBbound (x k) (hball k) (g (x k)) (hg (x k))
  have hn2 : ‖g (x k)‖^2 ≤ B^2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hprod : d*((2-γ)*l-2*d) ≤ ψ (x k)*((2-γ)*ψ (x k)-2*d) := by
    apply mul_le_mul (hdle (x k))
    · exact sub_le_sub_right (mul_le_mul_of_nonneg_left (hl k) htwo.le) _
    · exact hD.le
    · exact (hd.trans_le (hdle (x k))).le
  have hnum := mul_le_mul_of_nonneg_left hprod hγ0.le
  have hεle : ε ≤ γ*ψ (x k)*((2-γ)*ψ (x k)-2*d)/‖g (x k)‖^2 := by
    calc
      ε ≤ (γ*ψ (x k)*((2-γ)*ψ (x k)-2*d))/B^2 := by
        dsimp [ε]
        apply div_le_div_of_nonneg_right _ (sq_nonneg B)
        nlinarith [hnum]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hnorm) hn2
  exact (hdescent k).trans (sub_le_sub_left hεle _)

