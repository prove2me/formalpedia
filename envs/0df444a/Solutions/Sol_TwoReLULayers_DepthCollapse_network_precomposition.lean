-- Prove2me | solution 1 for TwoReLULayers.DepthCollapse.network_precomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:06:17.878698+00:00
-- url     : https://prove2.me/submissions/9ffc07cb-88f9-4147-95ca-f54b6cb753e4

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

open Finset
open TwoReLULayers.DepthCollapse

noncomputable section

private def composeAffine {R : Subfield ℝ} {n m : ℕ}
    (a : AffineScalar R m) (A : AffineR R n m) : AffineScalar R n where
  bias := a.bias + ∑ i, a.weight i * (A i).bias
  weight := fun j => ∑ i, a.weight i * (A i).weight j

private theorem composeAffine_eval {R : Subfield ℝ} {n m : ℕ}
    (a : AffineScalar R m) (A : AffineR R n m) (x : E n) :
    (composeAffine a A).eval x = a.eval (affineEval A x) := by
  simp [composeAffine, AffineScalar.eval, affineEval, Finset.sum_mul,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc]
  rw [Finset.sum_comm]
  ring


theorem solution {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (R : Subfield ℝ) (A : AffineR R n m) (f : E m → ℝ) (hf : f ∈ ReLU2 R m) :
    (fun x => f (affineEval A x)) ∈ ReLU2 R n := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨⟨N.width₁, N.width₂, (fun i => composeAffine (N.first i) A),
    N.second, N.output⟩, fun x => ?_⟩
  change f (affineEval A x) = _
  rw [hN]
  unfold Network2.eval
  congr 3
  ext i
  change max 0 ((N.first i).eval (affineEval A x)) =
    max 0 ((composeAffine (N.first i) A).eval x)
  rw [composeAffine_eval]
