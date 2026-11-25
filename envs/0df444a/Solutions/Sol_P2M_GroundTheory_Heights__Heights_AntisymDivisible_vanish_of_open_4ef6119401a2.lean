-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_open_4ef6119401a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:50.991281+00:00
-- url     : https://prove2.me/submissions/43021aa1-cb58-495f-8a0e-c40d7406d786

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_comp_collapse_49ec2e4b76fe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution [Fintype σ] (u v : σ) (P : MvPolynomial σ ℝ) (O : Set (σ → ℝ))
    (hO : IsOpen O) (hne : (O ∩ {x | x u = x v}).Nonempty)
    (h : ∀ x ∈ O ∩ {x | x u = x v}, eval x P = 0) :
    ∀ x : σ → ℝ, x u = x v → eval x P = 0 := by
  obtain ⟨x0, hx0O, hx0H⟩ := hne
  have hx0H' : x0 u = x0 v := hx0H
  have hQ : rename (collapse u v) P = 0 := by
    have hO' : IsOpen {y : σ → ℝ | y ∘ collapse u v ∈ O} :=
      hO.preimage (continuous_pi fun w => continuous_apply (collapse u v w))
    have hx0 : x0 ∈ {y : σ → ℝ | y ∘ collapse u v ∈ O} := by
      show x0 ∘ collapse u v ∈ O
      rwa [comp_collapse x0 hx0H']
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO' x0 hx0
    rw [ball_pi x0 hε] at hball
    refine MvPolynomial.funext_set (fun w => Metric.ball (x0 w) ε) (fun w => ?_) fun y hy => ?_
    · rw [Real.ball_eq_Ioo]
      exact Set.Ioo_infinite (by linarith)
    · rw [eval_rename, map_zero]
      apply h
      refine ⟨hball hy, ?_⟩
      show (y ∘ collapse u v) u = (y ∘ collapse u v) v
      simp only [Function.comp, collapse, if_pos rfl]
      split_ifs <;> rfl
  intro x hx
  have := congrArg (eval x) hQ
  rwa [eval_rename, comp_collapse x hx, map_zero] at this
end GroundTheory.Heights₂.Heights.AntisymDivisible
