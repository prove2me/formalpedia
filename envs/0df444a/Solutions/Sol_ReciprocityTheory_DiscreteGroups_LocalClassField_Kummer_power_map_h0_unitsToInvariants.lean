-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.power_map_h0_unitsToInvariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:04.023807+00:00
-- url     : https://prove2.me/submissions/2a92208a-e583-4224-9c92-f17f6f6069dd

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Kummer
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_powMap_apply


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
theorem _root_.solution (b : Kˣ) :
    (pP p K n).h0 (unitsToInvariants' p K (Additive.ofMul b)) = unitsToInvariants' p K (Additive.ofMul (b ^ n)) := by
  refine Subtype.ext ?_
  show powMap p n (Additive.ofMul (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b) : KbarMult p) = _
  rw [powMap_apply, ← map_pow]
  rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
