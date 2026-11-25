-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.torusLex_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:27:11.258918+00:00
-- url     : https://prove2.me/submissions/5e7fb601-3f30-4187-95c4-6ecf25684de4

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexC
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLex
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_torusLex_of
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_torus_l2_cauchy_of_basic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hBasic : TorusMeanBasicStatement) (hCoeff : TorusCoeffStatement) :
    TorusLexStatement ∧ TorusL2Cauchy :=
  ⟨TorusLexOrder.torusLex_of hBasic hCoeff, TorusLexOrder.torus_l2_cauchy_of_basic hBasic⟩
end ReciprocityTheory.MultiplicativeHeights
