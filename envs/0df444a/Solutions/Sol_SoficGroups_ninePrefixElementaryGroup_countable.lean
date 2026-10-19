-- Prove2me | solution 1 for SoficGroups.ninePrefixElementaryGroup_countable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/19c4984a-fb8e-425a-bcf2-9a74de1c7227

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution :
    Countable (prefixElementaryGroup ninePrefixCode) :=
  ninePrefixElementaryGroupEquiv.symm.injective.countable
end SoficGroups
