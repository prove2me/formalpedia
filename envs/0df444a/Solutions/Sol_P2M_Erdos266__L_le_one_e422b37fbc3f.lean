-- Prove2me | solution 1 for P2M_Erdos266__L_le_one_e422b37fbc3f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:50:09.171803+00:00
-- url     : https://prove2.me/submissions/0393cf6d-63bf-4974-bca6-4a0aa0372db2

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_lattice_lemma


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (d : ℕ) : εL d ≤ 1 := (lattice_lemma d).choose_spec.choose_spec.2.1
end Erdos266
