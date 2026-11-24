-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__indep_unit_5db93c2a0b31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:28:00.90638+00:00
-- url     : https://prove2.me/submissions/02adc3ce-6d53-4e02-842e-4a54136142d3

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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] (A : Unit → Submodule K V) : iSupIndep A := by
  intro i
  have h : (⨆ (j : Unit) (_ : j ≠ i), A j) = ⊥ := by simp
  rw [h]
  exact disjoint_bot_right
end Formalism.L2.Indef.Examples₂
