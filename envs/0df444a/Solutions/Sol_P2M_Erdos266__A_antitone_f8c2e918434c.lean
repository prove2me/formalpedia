-- Prove2me | solution 1 for P2M_Erdos266__A_antitone_f8c2e918434c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:51:00.553919+00:00
-- url     : https://prove2.me/submissions/78cb5fd7-c686-4c36-868e-d965b8e8025b

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_P2M_Erdos266__A_succ_le_342abca4b5cd

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution : Antitone εA :=
  antitone_nat_of_succ_le εA_succ_le
end Erdos266
