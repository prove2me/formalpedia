-- Prove2me | solution 1 for UpperTheory.V.Base.selRes_selRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:35.221689+00:00
-- url     : https://prove2.me/submissions/b6b99e0f-9c2c-402c-bb3b-f88066a1cd3b

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
import Theorems.Thm_UpperTheory_V_Base_resU_conjRep

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
theorem _root_.solution (ρ : Representation R G M) {U' U : Subgroup G} [U.Normal] [U'.Normal] (h : U' ≤ U)
    {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟) (g : G) (x : LocSel ρ U 𝒟) :
    selRes ρ h 𝒟 (selRep ρ U h𝒟 g x) = selRep ρ U' h𝒟 g (selRes ρ h 𝒟 x) := by
  apply Subtype.ext
  show resU ρ h (conjRep ρ U g x) = conjRep ρ U' g (resU ρ h x)
  exact resU_conjRep ρ h g x
end UpperTheory.V.Base
