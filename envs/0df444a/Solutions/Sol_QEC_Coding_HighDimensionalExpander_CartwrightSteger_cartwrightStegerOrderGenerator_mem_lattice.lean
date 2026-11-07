-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderGenerator_mem_lattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:17.216772+00:00
-- url     : https://prove2.me/submissions/16987f1a-5795-4da5-b1c9-0a9dfc9dbe98

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    (QuotientGroup.mk
        (cartwrightStegerOrderGenerator P r
          (constantClassRepresentative P r u)) :
      CartwrightStegerOrderProjectiveGroup P r) ∈
        CartwrightStegerOrderLattice P r :=
  Subgroup.subset_closure ⟨u, rfl⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
