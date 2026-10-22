-- Prove2me | solution 1 for TsengBCD.Hemivariate.argmin_attained
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:22:35.449641+00:00
-- url     : https://prove2.me/submissions/87fb4b46-78bc-42ad-91b9-0736255318e3

import Mathlib
import Definitions.Def_TsengBCD_Hemivariate_Setting

set_option autoImplicit false
open Filter Topology

theorem solution {N : ℕ} {n : Fin N → ℕ} (f : TsengBCD.Stationary.X n → EReal) (x0 : TsengBCD.Stationary.X n)
    (hbdd : Bornology.IsBounded (TsengBCD.Stationary.levelSet f x0)) (hlsc : LowerSemicontinuous f) :
    IsCompact (TsengBCD.Stationary.levelSet f x0) ∧
      ∀ y ∈ TsengBCD.Stationary.levelSet f x0, ∀ k : Fin N, ∃ a : EuclideanSpace ℝ (Fin (n k)),
        ∀ b : EuclideanSpace ℝ (Fin (n k)),
          f (Function.update y k a) ≤ f (Function.update y k b) := by
  have hcl : IsClosed (TsengBCD.Stationary.levelSet f x0) := hlsc.isClosed_preimage (f x0)
  have hcomp : IsCompact (TsengBCD.Stationary.levelSet f x0) :=
    Metric.isCompact_of_isClosed_isBounded hcl hbdd
  refine ⟨hcomp, fun y hy k => ?_⟩
  have hy' : f y ≤ f x0 := hy
  have hcont : Continuous (fun a : EuclideanSpace ℝ (Fin (n k)) => Function.update y k a) :=
    continuous_const.update k continuous_id
  have hS : IsClosed {a : EuclideanSpace ℝ (Fin (n k)) | f (Function.update y k a) ≤ f y} :=
    (hlsc.isClosed_preimage (f y)).preimage hcont
  have hSsub : {a : EuclideanSpace ℝ (Fin (n k)) | f (Function.update y k a) ≤ f y} ⊆
      (fun x : TsengBCD.Stationary.X n => x k) '' TsengBCD.Stationary.levelSet f x0 := by
    intro a ha
    exact ⟨Function.update y k a, le_trans ha hy', by simp⟩
  have hSb : Bornology.IsBounded {a : EuclideanSpace ℝ (Fin (n k)) | f (Function.update y k a) ≤ f y} :=
    (hcomp.image (continuous_apply k)).isBounded.subset hSsub
  have hScomp := Metric.isCompact_of_isClosed_isBounded hS hSb
  have hne : {a : EuclideanSpace ℝ (Fin (n k)) | f (Function.update y k a) ≤ f y}.Nonempty :=
    ⟨y k, by simp⟩
  have hlscg : LowerSemicontinuous (fun a : EuclideanSpace ℝ (Fin (n k)) => f (Function.update y k a)) :=
    lowerSemicontinuous_iff_isClosed_preimage.2 fun c => (hlsc.isClosed_preimage c).preimage hcont
  obtain ⟨a, haS, hmin⟩ := hlscg.lowerSemicontinuousOn _ |>.exists_isMinOn hne hScomp
  refine ⟨a, fun b => ?_⟩
  by_cases hb : f (Function.update y k b) ≤ f y
  · exact isMinOn_iff.mp hmin b hb
  · exact haS.trans (le_of_lt (not_le.mp hb))
