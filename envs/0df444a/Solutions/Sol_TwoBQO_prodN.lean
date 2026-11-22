-- Prove2me | solution 1 for TwoBQO.prodN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:46:02.454168+00:00
-- url     : https://prove2.me/submissions/85e6929b-8a6a-4b76-976d-76ec391f6e4d

module
public import Mathlib.SetTheory.Ordinal.Basic
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
public import Theorems.Thm_TwoBQO_of_wellFoundedLT
public import Theorems.Thm_TwoBQO_pi

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace TwoBQO
theorem _root_.solution : ∀ n : ℕ, TwoBQO fun f g : Fin n → ℕ => ∀ i, f i ≤ g i := fun n =>
  TwoBQO.pi n (fun _ => ℕ) (fun _ => (· ≤ ·)) fun _ => TwoBQO.of_wellFoundedLT
end TwoBQO
