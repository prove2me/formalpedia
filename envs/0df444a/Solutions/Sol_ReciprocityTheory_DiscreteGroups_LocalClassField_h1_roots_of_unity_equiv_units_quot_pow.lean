-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.h1_roots_of_unity_equiv_units_quot_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:03:11.5655+00:00
-- url     : https://prove2.me/submissions/45b6d622-1512-4346-970d-93b1c41ebfb8

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Kummer
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_h1_roots_of_unity_equiv_of_h1_subsingleton
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_h1_kbarRep_subsingleton


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
open Kummer
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n] :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) :=
  h1_roots_of_unity_equiv_of_h1_subsingleton p K n (h1_kbarRep_subsingleton p K)
end ReciprocityTheory.DiscreteGroups.LocalClassField
