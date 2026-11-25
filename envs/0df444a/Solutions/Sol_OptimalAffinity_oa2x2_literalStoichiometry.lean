-- Prove2me | solution 1 for OptimalAffinity.oa2x2_literalStoichiometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:53:50.521094+00:00
-- url     : https://prove2.me/submissions/0250d605-00cb-4977-867b-eb78609c5a7c

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution :
    oa2x2.xReactant = ![1, 0] ∧ oa2x2.yReactant = ![0, 2] ∧
    oa2x2.xProduct = ![0, 2] ∧ oa2x2.yProduct = ![1, 1] := by
  simp [oa2x2]
end OptimalAffinity
