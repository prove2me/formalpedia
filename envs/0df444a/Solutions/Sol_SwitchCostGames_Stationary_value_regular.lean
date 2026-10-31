-- Prove2me | solution 1 for SwitchCostGames.Stationary.value_regular
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:17:29.366354+00:00
-- url     : https://prove2.me/submissions/7f33513d-cd0f-4045-8adf-ebbd6f7005ed

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model
import Theorems.Thm_SwitchCostGames_Stationary_filar_raghavan
import Theorems.Thm_SwitchCostGames_Stationary_lemma_1
import Theorems.Thm_AGT_zero_sum_minimax

open SwitchCostGames.Stationary

/-- Uniqueness of the saddle value of a one-shot zero-sum game. -/
theorem SCG_saddleValue_unique {ι κ : Type*} [Fintype ι] [Fintype κ] (M : ι → κ → ℝ)
    (v w : ℝ) (hv : IsSaddleValue M v) (hw : IsSaddleValue M w) : v = w := by
  obtain ⟨p, q, ⟨hp, hq, hp1, hq1⟩, rfl⟩ := hv
  obtain ⟨p', q', ⟨hp', hq', hp1', hq1'⟩, rfl⟩ := hw
  have h1 := hq1 q' hq'
  have h2 := hp1' p hp
  have h3 := hq1' q hq
  have h4 := hp1 p' hp'
  linarith

theorem SCG_mixed_of {α : Type*} [Fintype α] {k : ℕ} (g : α ≃ Fin k) (z : Fin k → ℝ)
    (hz : z ∈ stdSimplex ℝ (Fin k)) : BlottoLP.Flow.IsMixed (z ∘ g) := by
  refine ⟨fun x => hz.1 _, ?_⟩
  rw [← hz.2]
  exact g.sum_comp z

theorem SCG_simplex_of {α : Type*} [Fintype α] {k : ℕ} (g : α ≃ Fin k) (z : α → ℝ)
    (hz : BlottoLP.Flow.IsMixed z) : z ∘ g.symm ∈ stdSimplex ℝ (Fin k) := by
  refine ⟨fun x => hz.1 _, ?_⟩
  rw [← hz.2]
  exact g.symm.sum_comp z

/-- Existence of a saddle value for any finite nonempty zero-sum game (von Neumann's minimax
theorem, transported from `AGT.zero_sum_minimax`). -/
theorem SCG_saddleValue_exists {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (M : ι → κ → ℝ) : ∃ v, IsSaddleValue M v := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, Fintype.card ι = a + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  obtain ⟨b, hb⟩ : ∃ b, Fintype.card κ = b + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  let e : ι ≃ Fin (a + 1) := Fintype.equivFinOfCardEq ha
  let f : κ ≃ Fin (b + 1) := Fintype.equivFinOfCardEq hb
  let A : Matrix (Fin (a + 1)) (Fin (b + 1)) ℝ := fun i j => M (e.symm i) (f.symm j)
  obtain ⟨p, hp, q, hq, hpmax, hqmin, -⟩ := AGT.zero_sum_minimax A
  -- the payoff in coordinates
  have key : ∀ (x : ι → ℝ) (y : κ → ℝ),
      BlottoLP.Flow.expPay M x y = (x ∘ e.symm) ⬝ᵥ A.mulVec (y ∘ f.symm) := by
    intro x y
    simp only [BlottoLP.Flow.expPay, dotProduct, Matrix.mulVec, Function.comp, A,
      Finset.mul_sum]
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← f.symm.sum_comp]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have ce : ∀ z : Fin (a + 1) → ℝ, (z ∘ e) ∘ e.symm = z := by
    intro z; funext i; simp
  have cf : ∀ z : Fin (b + 1) → ℝ, (z ∘ f) ∘ f.symm = z := by
    intro z; funext i; simp
  refine ⟨BlottoLP.Flow.expPay M (p ∘ e) (q ∘ f), p ∘ e, q ∘ f,
    ⟨SCG_mixed_of e p hp, SCG_mixed_of f q hq, ?_, ?_⟩, rfl⟩
  · intro σ' hσ'
    rw [key, key, cf, ce]
    exact hpmax _ (SCG_simplex_of e σ' hσ')
  · intro τ' hτ'
    rw [key, key, cf, ce]
    exact hqmin _ (SCG_simplex_of f τ' hτ')

theorem solution {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) (v : ℝ → ℝ)
    (hv : ∀ c : ℝ, 0 ≤ c → IsValue G c (v c)) :
    ContinuousOn v (Set.Ici 0) ∧ MonotoneOn v (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) v ∧
      IsPiecewiseAffineOn v (Set.Ici 0) := by
  classical
  obtain ⟨a, b, hb, -, hval⟩ := filar_raghavan G
  let V : ((Fin n → Fin n) → ℝ) → ℝ := fun x =>
    Classical.choose (SCG_saddleValue_exists (paramGame a b x))
  have hV : ∀ x, IsSaddleValue (paramGame a b x) (V x) := fun x =>
    Classical.choose_spec (SCG_saddleValue_exists (paramGame a b x))
  obtain ⟨hVc, hVm, hVconc, hVpw⟩ := lemma_1 a b hb V hV
  let k : ℝ → ((Fin n → Fin n) → ℝ) := fun t => fun _ => t
  have hvV : ∀ c : ℝ, 0 ≤ c → v c = V (k c) := by
    intro c hc
    exact SCG_saddleValue_unique _ _ _ ((hval c hc (v c)).1 (hv c hc)) (hV _)
  have hk : Continuous k := continuous_pi (fun _ => continuous_id)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ContinuousOn.congr (hVc.comp hk).continuousOn ?_
    intro c hc
    exact hvV c hc
  · intro x hx y hy hxy
    rw [hvV x hx, hvV y hy]
    exact hVm (fun _ => hxy)
  · refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy s t hs ht hst
    have hxy : 0 ≤ s • x + t • y := by
      simp only [smul_eq_mul]
      have : (0:ℝ) ≤ s * x := mul_nonneg hs hx
      have : (0:ℝ) ≤ t * y := mul_nonneg ht hy
      linarith
    rw [hvV x hx, hvV y hy, hvV _ hxy]
    have := hVconc.2 (Set.mem_univ (k x)) (Set.mem_univ (k y)) hs ht hst
    have e : s • k x + t • k y = k (s • x + t • y) := by
      funext i; simp [k]
    rw [e] at this
    exact this
  · obtain ⟨B, hB⟩ := hVpw 0 (fun _ => 1)
    refine ⟨B, ?_⟩
    intro p q hpq hsub hBn
    obtain ⟨α, β, hab⟩ := hB p q hpq (Set.subset_univ _) hBn
    refine ⟨α, β, ?_⟩
    intro x hx
    have hx0 : 0 ≤ x := hsub hx
    rw [hvV x hx0, ← hab x hx]
    congr 1
    funext i
    simp [k]
