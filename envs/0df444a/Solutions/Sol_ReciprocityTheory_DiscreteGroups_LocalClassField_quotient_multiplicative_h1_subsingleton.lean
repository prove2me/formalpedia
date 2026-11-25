-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.quotient_multiplicative_h1_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:23:54.387715+00:00
-- url     : https://prove2.me/submissions/ea056f48-9250-454e-adce-d670e7761b36

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiveTerm
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KbarRepContAction
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_multiplicative_cochain_h1_subsingleton
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_inf_inj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (N : Subgroup (GK p K)) [N.Normal] (Q : TRep ℤ (GK p K ⧸ N))
    (P : Pair Q (kbarT p K)) (hP : IsInvRep (kbarT p K) N Q P) : Subsingleton (Q.H 1) :=
  have := multiplicative_cochain_h1_subsingleton p K
  (inf_inj (kbarT p K) N Q P hP).subsingleton
end ReciprocityTheory.DiscreteGroups.LocalClassField
