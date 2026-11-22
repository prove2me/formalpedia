-- Prove2me | solution 1 for boolTestExpectation_empirical_eq_avg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:32:35.018147+00:00
-- url     : https://prove2.me/submissions/bf021e7c-2cbd-49e6-9728-299aa795545a

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution
    {H : Type*} [Fintype H] [DecidableEq H]
    {T : ℕ} (hT : 0 < T) (hs : Fin T → H) (f : H → Bool) :
    boolTestExpectation (empiricalPMF hT hs) f =
    (∑ t : Fin T, if f (hs t) then (1 : ℝ) else 0) / T := by
  simp only [boolTestExpectation, trueExpectation, empiricalPMF]
  conv_lhs => arg 2; ext h; rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  symm
  have := Finset.card_eq_sum_card_fiberwise (f := hs)
    (s := univ) (t := univ) (fun _ _ => Finset.mem_univ _)
  conv_lhs => rw [show (∑ t : Fin T, if f (hs t) then (1 : ℝ) else 0) =
    ∑ h : H, ∑ t ∈ univ.filter (fun t => hs t = h),
      (if f (hs t) then (1 : ℝ) else 0) from by
    rw [← Finset.sum_biUnion (s := univ)]
    · congr 1; ext t; simp
    · intro h₁ _ h₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro t _ ht1 ht2; exact hne (ht1.symm.trans ht2)]
  congr 1; ext h
  rw [Finset.sum_congr rfl (fun t ht => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht])]
  rw [Finset.sum_const, nsmul_eq_mul]
