-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.det_monF_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:34:53.6388+00:00
-- url     : https://prove2.me/submissions/252903ac-8a2c-443a-8724-82692c76108e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Theorems.Thm_ReciprocityTheory_PGsh_Up_span_monF_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (Cm : Matrix ι ι k) (hC : IsUnit Cm.det) :
    (Matrix.of fun (x α : ι → ZMod p) => monF Cm α x).det ≠ 0 := by
  have hspan := span_monF_eq_top (p := p) Cm Cm⁻¹ (Matrix.nonsing_inv_mul Cm hC)
  have hli : LinearIndependent k
      (fun α => Matrix.transpose (Matrix.of fun (x α : ι → ZMod p) => monF Cm α x) α) := by
    have hcols : (fun α => Matrix.transpose (Matrix.of fun (x α : ι → ZMod p) => monF Cm α x) α) =
        monF (p := p) Cm := by
      funext α x
      simp [Matrix.transpose_apply]
    rw [hcols]
    apply linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
    simp
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
end ReciprocityTheory.PGsh.Up
