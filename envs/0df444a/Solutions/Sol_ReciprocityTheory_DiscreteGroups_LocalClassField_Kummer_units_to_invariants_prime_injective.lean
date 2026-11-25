-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.units_to_invariants_prime_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:11:56.573884+00:00
-- url     : https://prove2.me/submissions/30b77c71-6100-4d16-8c26-b157c27bf2cf

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Kummer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
open ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
theorem _root_.solution : Function.Injective (unitsToInvariants' p K) := by
  intro a b hab
  have h1 : Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul =
      Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b.toMul := congrArg Subtype.val hab
  exact Units.map_injective (algebraMap K (PadicAlgCl p)).injective h1
end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
