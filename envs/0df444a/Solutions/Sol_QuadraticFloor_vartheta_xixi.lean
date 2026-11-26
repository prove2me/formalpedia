-- Prove2me | solution 1 for QuadraticFloor.vartheta_xixi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:16.713406+00:00
-- url     : https://prove2.me/submissions/33db0783-3d39-4d40-9458-1ee0bf7b45cc

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_xi_four
public import Theorems.Thm_QuadraticFloor_xi_sq_nat
public import Theorems.Thm_QuadraticFloor_eta_mul_chi4_sq
public import Theorems.Thm_QuadraticFloor_ite_of_neg


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace QuadraticFloor
theorem _root_.solution : vartheta p (xi * xi) = fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ) := by
  funext x
  unfold vartheta
  have h1 : (xi * xi) (-1) ≠ -1 := by
    rw [MulChar.mul_apply, show (-1 : ZMod 5) = 4 by decide, xi_four]; norm_num
  rw [ite_of_neg h1, eta_mul_chi4_sq, MulChar.mul_apply, ← pow_two, xi_sq_nat]
end QuadraticFloor
