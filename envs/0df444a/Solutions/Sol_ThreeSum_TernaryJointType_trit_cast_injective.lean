-- Prove2me | solution 1 for ThreeSum.TernaryJointType.trit_cast_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:12.489191+00:00
-- url     : https://prove2.me/submissions/a05294c0-6a56-41d8-8e0c-bb81ae9fc253

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset
namespace ThreeSum.TernaryJointType
theorem _root_.solution {p : ℕ} (hp : 2 < p) :
    Function.Injective (fun x : Fin 3 => (x.val : ZMod p)) := by
  intro a b hab
  apply Fin.ext
  have ha : a.val < p := lt_of_lt_of_le a.isLt (by omega)
  have hb : b.val < p := lt_of_lt_of_le b.isLt (by omega)
  have hv := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hv
end ThreeSum.TernaryJointType
