-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Det2.v_det_scaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:12.373035+00:00
-- url     : https://prove2.me/submissions/6dc56c8a-10b1-4c33-9110-4533c6859b67

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FrobEqOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Filter Topology
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Det2
namespace ReciprocityTheory.PGsh.Up.Det2
theorem _root_.solution {C : Type} [Field C] (v : Valuation C NNReal) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c : Matrix ι ι C) (y z : ι → C) :
    v (Matrix.of fun j k => c j k * (y j / z k)).det =
      v c.det * (∏ j, v (y j)) / ∏ k, v (z k) := by
  have hM : (Matrix.of fun j k => c j k * (y j / z k)) =
      Matrix.diagonal y * c * Matrix.diagonal fun k => (z k)⁻¹ := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, div_eq_mul_inv]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, map_mul, map_mul,
    map_prod, map_prod]
  simp only [map_inv₀, Finset.prod_inv_distrib, div_eq_mul_inv]
  ring
end ReciprocityTheory.PGsh.Up.Det2
