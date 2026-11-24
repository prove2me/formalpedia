-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__one_quot_de26657ef017
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:06.922285+00:00
-- url     : https://prove2.me/submissions/5df3a445-a5d9-4fd0-8466-c213c225f88d

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
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef.Examples₂
theorem _root_.solution (n : ℕ) : IsQuotMetric (1 : Matrix (Fin n) (Fin n) K) 1 (fr K n) := by
  intro v
  simp [fr]
end Formalism.L2.Indef.Examples₂
