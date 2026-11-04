-- Prove2me | solution 1 for ThreeSum.TernaryCoverRankFibers.affineFiber_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:47.473761+00:00
-- url     : https://prove2.me/submissions/8922716e-74ab-4628-85f0-23cbecdc5916

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRankFibers
open Finset
variable {K : Type*} [Field K]
variable {E ι : Type*} [Fintype E] [Fintype ι] [DecidableEq K]
namespace ThreeSum.TernaryCoverRankFibers
theorem _root_.solution (left right : E → ι → K)
    (hinj : Function.Injective (fun e => (left e, right e))) (offset : ι → K × K) :
    (affineFiber left right (⊥ : Submodule K (K × K)) offset).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro e he f hf
  apply hinj
  have hpair (i : ι) : (left e i, right e i) = (left f i, right f i) := by
    have ha := (mem_filter.mp he).2 i
    have hb := (mem_filter.mp hf).2 i
    have ha' : (left e i, right e i) = offset i := sub_eq_zero.mp ha
    have hb' : (left f i, right f i) = offset i := sub_eq_zero.mp hb
    exact ha'.trans hb'.symm
  exact Prod.ext (funext fun i => congrArg Prod.fst (hpair i))
    (funext fun i => congrArg Prod.snd (hpair i))
end ThreeSum.TernaryCoverRankFibers
