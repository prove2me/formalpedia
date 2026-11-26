-- Prove2me | solution 1 for PascalExtremes.targetA_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:10.281933+00:00
-- url     : https://prove2.me/submissions/4fba251d-7731-407c-8d0e-1d10b2ab639d

module
public import Definitions.Def_PascalExtremes_Basic
public import Definitions.Def_PascalExtremes_Powers
public import Definitions.Def_PascalExtremes_CarryBounds
public import Mathlib.Tactic
public import Definitions.Def_PascalExtremes_TargetA
public import Theorems.Thm_PascalExtremes_targetA_upper_witness
public import Theorems.Thm_PascalExtremes_padicVal_G_le_choose


set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p m N : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m)
    (hrow : AdmissibleRow m N) :
    padicValNat p (G N m) ≤ rP p m := by
  obtain ⟨k, hk, hkval⟩ := targetA_upper_witness hp hm2 hpm hrow
  exact (padicVal_G_le_choose (by omega) hrow.1 hp hk).trans hkval
end PascalExtremes
