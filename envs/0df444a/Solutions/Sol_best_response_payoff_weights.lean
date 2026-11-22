-- Prove2me | solution 1 for best_response_payoff_weights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:55.342311+00:00
-- url     : https://prove2.me/submissions/e42e09a1-e5c9-46c5-a5ad-6dd348ad0129

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Theorems.Thm_MWUConfig_potential_pos

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {R C : Type*} [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (cfg : MWUConfig C) :
    v * cfg.potential ≤
    ∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0) := by
  have hr := (hrow cfg.toPMF).choose_spec
  have hΦ_pos := cfg.potential_pos
  -- hr says: v ≤ Σ_c (w(c)/Φ) · M(r,c) = (Σ_c w(c)·M(r,c)) / Φ
  -- So v · Φ ≤ Σ_c w(c) · M(r,c)
  have key : (∑ c : C, cfg.toPMF.prob c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0)) =
    (∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0)) / cfg.potential := by
    simp only [MWUConfig.toPMF, normalizeToPMF, MWUConfig.potential]
    rw [Finset.sum_div]; congr 1; ext c; field_simp
  rw [key] at hr
  rwa [le_div_iff₀ hΦ_pos] at hr
