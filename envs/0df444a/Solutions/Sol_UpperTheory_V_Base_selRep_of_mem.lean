-- Prove2me | solution 1 for UpperTheory.V.Base.selRep_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:30.141521+00:00
-- url     : https://prove2.me/submissions/0c6830f7-6de8-4bfc-a750-d202b3c8799b

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
import Theorems.Thm_UpperTheory_V_Base_conjRep_of_mem
import Theorems.Thm_UpperTheory_V_Base_coe_selRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.Gal
open UpperTheory UpperTheory.V UpperTheory.V.Base
variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable [IsTopologicalGroup G] [DiscreteTopology M]
namespace UpperTheory.V.Base
theorem _root_.solution (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)}
    (h𝒟 : ConjStable 𝒟) {g : G} (hg : g ∈ U) (x : LocSel ρ U 𝒟) : selRep ρ U h𝒟 g x = x := by
  apply Subtype.ext
  rw [coe_selRep, conjRep_of_mem ρ U hg]
end UpperTheory.V.Base
