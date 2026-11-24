-- Prove2me | solution 1 for TrigPolyLinComb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T14:41:30.57357+00:00
-- url     : https://prove2.me/submissions/4e7ace5a-df0b-43a6-a8f5-8475447f9079

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolyLinComb

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {m : ℕ} {S T : ℝ → ℝ} (hS : TrigPolyLe m S)
    (hT : TrigPolyLe m T) (c d : ℝ) :
    TrigPolyLe m (fun t => c * S t + d * T t) := by
  obtain ⟨a₁, b₁, h₁⟩ := hS
  obtain ⟨a₂, b₂, h₂⟩ := hT
  refine ⟨fun k => c * a₁ k + d * a₂ k, fun k => c * b₁ k + d * b₂ k, fun t => ?_⟩
  simp only [h₁ t, h₂ t, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)
