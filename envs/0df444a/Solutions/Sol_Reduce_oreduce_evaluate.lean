-- Prove2me | solution 1 for Reduce.oreduce_evaluate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:15:45.739003+00:00
-- url     : https://prove2.me/submissions/3ba3286b-0c04-4280-9410-45b7ed4616cd

import Definitions.Def_Bdd_Reduce_Process
import Definitions.Def_Bdd_Reduce_Discover
import Definitions.Def_Bdd_Reduce_Main

set_option autoImplicit true
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {O : OBdd n m} : (oreduce O).1.2.evaluate = O.evaluate :=
  (oreduce O).2.2
end Reduce
