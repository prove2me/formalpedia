-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__conjAt_6819ae325d9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:05.369108+00:00
-- url     : https://prove2.me/submissions/7ede424a-e659-42f7-849e-d8ecb4e2c7bd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Examples₂
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open NumberField.IsCMField
namespace Formalism.L2.Indef.Examples₂
theorem _root_.solution (v0 : InfinitePlace K3) : IsConjAt v0 := by
  intro a
  exact IsCMField.complexEmbedding_complexConj K3 v0.embedding a
end Formalism.L2.Indef.Examples₂
