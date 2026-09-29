-- Prove2me | solution 1 for OnlineConvexOpt.BanditConvex.bandit_to_full_information_regret
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:06:49.630488+00:00
-- url     : https://prove2.me/submissions/75a89338-d1ce-4fe8-93d2-9b76a9e4a0a1

import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_FirstOrderAlgorithm
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory

namespace OnlineConvexOpt.BanditConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Gradient of a linear functional. -/
lemma aux_bfi_lin_grad (G z : E) : HasGradientAt (fun y => inner ℝ G y) G z := by
  rw [hasGradientAt_iff_isLittleO]
  refine (Asymptotics.isLittleO_zero _ _).congr_left (fun y => ?_)
  rw [inner_sub_right]; ring

open Classical in
/-- The modified cost function. -/
noncomputable def aux_bfi_h (x u g : E) (a b : ℝ) : E → ℝ :=
  fun y => if y = u then b else if dist y x < 1 then a + inner ℝ g (y - x) else a - ‖g‖

lemma aux_bfi_h_x (x u g : E) (a b : ℝ) (hab : x = u → a = b) :
    aux_bfi_h x u g a b x = a := by
  unfold aux_bfi_h
  by_cases hxu : x = u
  · rw [if_pos hxu, hab hxu]
  · rw [if_neg hxu, if_pos (by simp)]; simp

lemma aux_bfi_h_u (x u g : E) (a b : ℝ) : aux_bfi_h x u g a b u = b := by
  unfold aux_bfi_h; rw [if_pos rfl]

lemma aux_bfi_h_lb (x u g : E) (a b : ℝ) (y : E) :
    min b (a - ‖g‖) ≤ aux_bfi_h x u g a b y := by
  unfold aux_bfi_h
  split_ifs with h1 h2
  · exact min_le_left _ _
  · have h3 : dist y x = ‖y - x‖ := dist_eq_norm y x
    have h4 := real_inner_le_norm g (y - x)
    have h5 : -(inner ℝ g (y - x)) ≤ ‖g‖ * ‖y - x‖ := by
      have := abs_real_inner_le_norm g (y - x)
      have := neg_abs_le (inner ℝ g (y - x))
      linarith
    have h6 : ‖g‖ * ‖y - x‖ ≤ ‖g‖ := by
      have := norm_nonneg g
      nlinarith
    exact (min_le_right _ _).trans (by linarith)
  · exact min_le_right _ _

lemma aux_bfi_h_grad (x u g : E) (a b : ℝ) (hab : x = u → a = b) :
    HasGradientAt (aux_bfi_h x u g a b) g x := by
  rw [hasGradientAt_iff_isLittleO]
  refine (Asymptotics.isLittleO_zero _ _).congr' ?_ Filter.EventuallyEq.rfl
  have hball : Metric.ball x 1 ∈ nhds x := Metric.ball_mem_nhds x one_pos
  have hS : {y : E | y = u → y = x} ∈ nhds x := by
    by_cases hxu : x = u
    · subst hxu; exact Filter.mem_of_superset Filter.univ_mem (fun y _ => id)
    · refine Filter.mem_of_superset (isOpen_compl_singleton.mem_nhds hxu) ?_
      intro y hy hyu; exact absurd hyu hy
  filter_upwards [hball, hS] with y hy1 hy2
  rw [aux_bfi_h_x x u g a b hab]
  by_cases hyu : y = u
  · have hyx := hy2 hyu
    have hxu : x = u := hyx ▸ hyu
    unfold aux_bfi_h
    rw [if_pos hyu, ← hab hxu, hyx]
    simp
  · unfold aux_bfi_h
    rw [if_neg hyu, if_pos (by simpa [Metric.mem_ball] using hy1)]
    ring

/-- A first-order algorithm reproduces the bandit play on any cost sequence whose gradients at
the played points are the bandit gradient estimates. -/
lemma aux_bfi_play (A : (ℕ → E → ℝ) → ℕ → E) (hA : IsFirstOrderOnlineAlgorithm A)
    (h : ℕ → E → ℝ) (G : ℕ → E) (xs : ℕ → E)
    (hx0 : xs 0 = A (fun _ _ => (0 : ℝ)) 0)
    (hxs : ∀ t : ℕ, xs (t + 1) = A (fun τ y => if τ ≤ t then inner ℝ (G τ) y else 0) (t + 1))
    (hgrad : ∀ τ, HasGradientAt (h τ) (G τ) (xs τ)) : ∀ t, A h t = xs t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    let h' : ℕ → E → ℝ := fun τ => if τ < t then h τ else fun y => inner ℝ (G τ) y
    let ℓ : ℕ → E → ℝ := fun τ y => inner ℝ (G τ) y
    have e1 : A h t = A h' t := hA.1 h h' t (fun s hs => by simp [h', hs])
    have e2 : A h' t = A ℓ t := by
      refine hA.2 h' ℓ (fun τ => ⟨G τ, ?_, fun y => rfl⟩) t
      by_cases hτ : τ < t
      · have hA' : A h' τ = A h τ :=
          hA.1 h' h τ (fun s hs => by simp [h', lt_trans hs hτ])
        have hh' : h' τ = h τ := by simp [h', hτ]
        rw [hA', ih τ hτ, hh']
        exact hgrad τ
      · have hh' : h' τ = fun y => inner ℝ (G τ) y := by simp [h', hτ]
        rw [hh']
        exact aux_bfi_lin_grad (G τ) _
    have e3 : A ℓ t = xs t := by
      cases t with
      | zero =>
        rw [hx0]; exact hA.1 ℓ _ 0 (fun s hs => absurd hs (Nat.not_lt_zero _))
      | succ n =>
        rw [hxs n]
        exact hA.1 ℓ _ (n + 1) (fun s hs => by
          have : s ≤ n := Nat.lt_succ_iff.mp hs
          funext y; simp [ℓ, this])
    rw [e1, e2, e3]

lemma aux_bfi_inf (K : Set E) (F : E → ℝ) (u : E) (hu : u ∈ K) (m : ℝ) (hm : ∀ y, m ≤ F y) :
    ⨅ y ∈ K, F y ≤ F u := by
  have hbdd : BddBelow (Set.range fun y => ⨅ (_ : y ∈ K), F y) := by
    refine ⟨min m 0, ?_⟩
    rintro _ ⟨y, rfl⟩
    by_cases hy : y ∈ K
    · simp only
      rw [ciInf_pos hy]; exact min_le_of_left_le (hm y)
    · haveI : IsEmpty (y ∈ K) := ⟨hy⟩
      simp only
      rw [Real.iInf_of_isEmpty]; exact min_le_right _ _
  calc ⨅ y ∈ K, F y ≤ ⨅ (_ : u ∈ K), F u := ciInf_le hbdd u
    _ = F u := ciInf_pos hu

end OnlineConvexOpt.BanditConvex

open OnlineConvexOpt.BanditConvex

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [m0 : MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (K : Set E) (T : ℕ) (u : E) (hu : u ∈ K)
    (f : ℕ → E → ℝ) (gradf : ℕ → E → E) (hf : ∀ t y, HasGradientAt (f t) (gradf t y) y)
    (A : (ℕ → E → ℝ) → ℕ → E) (hA : IsFirstOrderOnlineAlgorithm A)
    (B : (ℕ → E) → ℝ)
    (hB : ∀ (h : ℕ → E → ℝ) (grad' : ℕ → E),
      (∀ t, HasGradientAt (h t) (grad' t) (A h t)) →
      OnlineConvexOpt.FirstOrder.RegretT K h (fun t => A h t) T ≤ B grad')
    (𝓕 : ℕ → MeasurableSpace Ω) (hFmono : Monotone 𝓕) (hFle : ∀ t, 𝓕 t ≤ m0)
    (x g : ℕ → Ω → E)
    (hx0 : x 0 = fun _ => A (fun _ _ => (0 : ℝ)) 0)
    (hxstep : ∀ t : ℕ, x (t + 1) =
      fun ω => A (fun τ y => if τ ≤ t then inner ℝ (g τ ω) y else 0) (t + 1))
    (hxmeas : ∀ t, Measurable[𝓕 t] (x t))
    (hgmeas : ∀ t, Measurable[𝓕 (t + 1)] (g t))
    (hunbiased : ∀ t, condExp (𝓕 t) Prob (g t) =ᵐ[Prob] fun ω => gradf t (x t ω))
    (hfintegrable : ∀ t, Integrable (fun ω => f t (x t ω)) Prob)
    (hBintegrable : Integrable (fun ω => B (fun t => g t ω)) Prob) :
    (∫ ω, ∑ t ∈ Finset.range T, f t (x t ω) ∂Prob) - ∑ t ∈ Finset.range T, f t u ≤
      ∫ ω, B (fun t => g t ω) ∂Prob := by
  -- pathwise bound
  have path : ∀ ω, ∑ t ∈ Finset.range T, f t (x t ω) ≤
      B (fun t => g t ω) + ∑ t ∈ Finset.range T, f t u := by
    intro ω
    let h : ℕ → E → ℝ := fun τ => aux_bfi_h (x τ ω) u (g τ ω) (f τ (x τ ω)) (f τ u)
    have hab : ∀ τ, x τ ω = u → f τ (x τ ω) = f τ u := fun τ e => by rw [e]
    have hgrad : ∀ τ, HasGradientAt (h τ) (g τ ω) (x τ ω) := fun τ =>
      aux_bfi_h_grad _ _ _ _ _ (hab τ)
    have hplay : ∀ t, A h t = x t ω :=
      aux_bfi_play A hA h (fun τ => g τ ω) (fun t => x t ω)
        (by rw [hx0]) (fun t => by rw [hxstep t]) hgrad
    have hreg := hB h (fun t => g t ω) (fun t => by rw [hplay t]; exact hgrad t)
    unfold OnlineConvexOpt.FirstOrder.RegretT at hreg
    have hsum1 : ∑ t ∈ Finset.range T, h t (A h t) = ∑ t ∈ Finset.range T, f t (x t ω) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [hplay t]; exact aux_bfi_h_x _ _ _ _ _ (hab t)
    have hsumu : ∑ t ∈ Finset.range T, h t u = ∑ t ∈ Finset.range T, f t u := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      exact aux_bfi_h_u _ _ _ _ _
    have hinf : ⨅ y ∈ K, ∑ t ∈ Finset.range T, h t y ≤ ∑ t ∈ Finset.range T, h t u :=
      aux_bfi_inf K _ u hu
        (∑ t ∈ Finset.range T, min (f t u) (f t (x t ω) - ‖g t ω‖))
        (fun y => Finset.sum_le_sum (fun t _ => aux_bfi_h_lb _ _ _ _ _ y))
    rw [hsum1] at hreg
    linarith
  have hint : Integrable (fun ω => ∑ t ∈ Finset.range T, f t (x t ω)) Prob :=
    integrable_finsetSum _ (fun t _ => hfintegrable t)
  have h1 : (∫ ω, ∑ t ∈ Finset.range T, f t (x t ω) ∂Prob) ≤
      ∫ ω, (B (fun t => g t ω) + ∑ t ∈ Finset.range T, f t u) ∂Prob :=
    integral_mono hint (hBintegrable.add (integrable_const _)) path
  have h2 : (∫ ω, (B (fun t => g t ω) + ∑ t ∈ Finset.range T, f t u) ∂Prob) =
      (∫ ω, B (fun t => g t ω) ∂Prob) + ∑ t ∈ Finset.range T, f t u := by
    rw [integral_add hBintegrable (integrable_const _), integral_const]
    simp
  linarith
