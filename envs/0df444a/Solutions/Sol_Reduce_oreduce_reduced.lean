-- Prove2me | solution 1 for Reduce.oreduce_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:15:34.730462+00:00
-- url     : https://prove2.me/submissions/892ff88f-c229-471e-b68a-da99239a4c32

import Definitions.Def_Bdd_Reduce_Process
import Definitions.Def_Bdd_Reduce_Discover
import Definitions.Def_Bdd_Reduce_Main

set_option autoImplicit true
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {O : OBdd n m} : OBdd.Reduced (oreduce O).1.2 := (oreduce O).2.1
end Reduce
