-- Prove2me | solution 1 for SizeRamsey.Plan.wheel5Pres_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:20.407911+00:00
-- url     : https://prove2.me/submissions/1ef18325-1215-4bc1-8d23-6460516fc327

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
namespace SizeRamsey.Plan
theorem _root_.solution : ∀ v, v ∈ wheel5Pres v ∧ (wheel5Pres v).card = 2 ∧
    QTrans wheel5 (wheel5Pres v) := by
  decide
end SizeRamsey.Plan
