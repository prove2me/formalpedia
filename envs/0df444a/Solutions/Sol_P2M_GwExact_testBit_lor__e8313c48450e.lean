-- Prove2me | solution 1 for P2M_GwExact_testBit_lor__e8313c48450e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:20:32.036069+00:00
-- url     : https://prove2.me/submissions/23b4ace9-5975-4a2e-ac8b-9f2984678bdf

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (a b u : Nat) : (Nat.lor a b).testBit u = (a.testBit u || b.testBit u) :=
  Nat.testBit_or a b u
end GwExact
