-- Prove2me | solution 1 for Relabel.orelabel_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:01:18.585399+00:00
-- url     : https://prove2.me/submissions/3ebb5010-f596-4718-817d-fe008887ecb1

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Relabel
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Bdd.RelevantMayPrecede
open Relabel
attribute [local implicit_reducible] relabel relabel_heap relabel_node
attribute [local implicit_reducible] orelabel
namespace Relabel
theorem _root_.solution {O : OBdd n m} : orelabel O (f := id) (by simp) (fun _ _ _ _ _ ↦ by simpa) = O := by simp +instances [orelabel]
end Relabel
