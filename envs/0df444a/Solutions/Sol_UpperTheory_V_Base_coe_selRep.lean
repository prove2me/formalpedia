-- Prove2me | solution 1 for UpperTheory.V.Base.coe_selRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:56:47.89158+00:00
-- url     : https://prove2.me/submissions/b631b485-f21e-42cd-870e-315aab9c14fa

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1

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
theorem _root_.solution (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟)
    (g : G) (x : LocSel ρ U 𝒟) : (selRep ρ U h𝒟 g x : H1U ρ U) = conjRep ρ U g x := rfl
end UpperTheory.V.Base
