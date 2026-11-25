-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.vdet_vandermonde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:31:16.456093+00:00
-- url     : https://prove2.me/submissions/1ee027d4-bb6f-4a8f-9b7e-51c38fe2e5f1

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_VdetLeOfSpanLe
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_finZ_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution [NeZero p] (ω : ZMod p → C)
    (hω : ∀ a b, a ≠ b → v (ω a - ω b) = 1) :
    v (Matrix.of fun a j : ZMod p => ω a ^ j.val).det = 1 := by
  rw [← Matrix.det_submatrix_equiv_self (finZ p)]
  have e : (Matrix.of fun a j : ZMod p => ω a ^ j.val).submatrix (finZ p) (finZ p) =
      Matrix.vandermonde (ω ∘ finZ p) := by
    ext i j
    simp [Matrix.vandermonde, finZ_val]
  rw [e, Matrix.det_vandermonde, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_eq_one fun j hj => ?_
  exact hω _ _ fun h => (ne_of_gt (Finset.mem_Ioi.1 hj)) ((finZ p).injective h)
end ReciprocityTheory.PGsh.Up.U3
