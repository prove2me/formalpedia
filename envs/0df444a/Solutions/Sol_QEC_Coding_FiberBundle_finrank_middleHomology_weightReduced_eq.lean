-- Prove2me | solution 1 for QEC.Coding.FiberBundle.finrank_middleHomology_weightReduced_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:30:43.542198+00:00
-- url     : https://prove2.me/submissions/72e96906-3e2e-4139-ac83-1a66f67085ba

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_ChainComplexData_finrank_middleHomology_eq
import Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_finrank_middleHomology_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    Module.finrank (ZMod 2)
        (chainComplex (weightReducedData D)).middleHomology =
      Module.finrank (ZMod 2) (chainComplex D).middleHomology :=
  (weightReductionHomotopyEquiv D h).finrank_middleHomology_eq
end QEC.Coding.FiberBundle
