-- Prove2me | solution 1 for SoficGroups.SourceCommonComponentComparisonBad.cast_card_sdiff_eq_sub_card_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/9b801b7d-d209-46f5-a526-6e4f587adc96

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonComponentComparisonBad
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCommonComponentComparisonBad
theorem _root_.solution
    {V : Type*} [DecidableEq V] (C D : Finset V) :
    ((C \ D).card : ℝ) =
      (C.card : ℝ) - ((C ∩ D).card : ℝ) := by
  have hnat := Finset.card_sdiff_add_card_inter C D
  have hreal : ((C \ D).card : ℝ) +
      ((C ∩ D).card : ℝ) = (C.card : ℝ) := by
    exact_mod_cast hnat
  linarith
end SoficGroups.SourceCommonComponentComparisonBad
