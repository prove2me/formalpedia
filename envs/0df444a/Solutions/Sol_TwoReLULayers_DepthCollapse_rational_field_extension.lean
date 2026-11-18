-- Prove2me | solution 1 for TwoReLULayers.DepthCollapse.rational_field_extension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:05:34.565011+00:00
-- url     : https://prove2.me/submissions/7ddc96a0-cd1c-4a76-850d-ebb2b32d072a

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

open TwoReLULayers.DepthCollapse
noncomputable section

private def liftAffine {n : ℕ} (R : Subfield ℝ)
    (a : AffineScalar (⊥ : Subfield ℝ) n) : AffineScalar R n where
  bias := ⟨a.bias, (show (⊥ : Subfield ℝ) ≤ R from bot_le) a.bias.property⟩
  weight := fun i => ⟨a.weight i, (show (⊥ : Subfield ℝ) ≤ R from bot_le) (a.weight i).property⟩

private theorem liftAffine_eval {n : ℕ} (R : Subfield ℝ)
    (a : AffineScalar (⊥ : Subfield ℝ) n) (x : E n) :
    (liftAffine R a).eval x = a.eval x := rfl

theorem solution {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (f : E n → ℝ) (hf : f ∈ ReLU2 (⊥ : Subfield ℝ) n) :
    f ∈ ReLU2 R n := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨⟨N.width₁, N.width₂, (fun i => liftAffine R (N.first i)),
    (fun i => liftAffine R (N.second i)), liftAffine R N.output⟩, fun x => ?_⟩
  exact hN x
