-- Prove2me | solution 1 for ReciprocityTheory.Coh.LowDeg.h1Equiv_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:48:37.400056+00:00
-- url     : https://prove2.me/submissions/1daf909e-97ef-469f-97e8-9ca211a91e70

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
import Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
open ReciprocityTheory.Coh.LowDeg
variable (M : TRep R G)
variable {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {M' : TRep R G'}
namespace ReciprocityTheory.Coh.LowDeg
theorem _root_.solution (P : Pair M M') (x : M.H 1) :
    h1EquivOfOrderTwo M' (P.hom.H 1 x) =
      pairH1DecompositionMap M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv (h1EquivOfOrderTwo M x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have key : (oneCocyclesEquivFunctions M' (P.hom.Z 1 z) : Z1 M'.rho) =
      compatiblePairCocycles1 M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv (oneCocyclesEquivFunctions M z) := by
    refine Subtype.ext (funext fun g => ?_)
    have hv : (fun i : Fin 1 => P.φ (![g] i)) = ![P.φ g] := by funext i; fin_cases i; rfl
    show P.u (z.1.1 fun i => P.φ (![g] i)) = P.u (z.1.1 ![P.φ g])
    rw [hv]
  exact congrArg Submodule.Quotient.mk key
end ReciprocityTheory.Coh.LowDeg
