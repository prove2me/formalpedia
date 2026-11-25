-- Prove2me | solution 1 for ReciprocityTheory.Coh.LowDeg.h2Equiv_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:55:10.318996+00:00
-- url     : https://prove2.me/submissions/5600821f-12e8-4357-aaba-1c0c85103742

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
theorem _root_.solution (P : Pair M M') (x : M.H 2) :
    h2EquivOfOrderTwo M' (P.hom.H 2 x) =
      compatiblePairH2 M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv (h2EquivOfOrderTwo M x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have key : (twoCocyclesEquivFunctions M' (P.hom.Z 2 z) : Z2 M'.rho) =
      compatiblePairCocycles2 M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv (twoCocyclesEquivFunctions M z) := by
    refine Subtype.ext (funext fun p => ?_)
    have hv : (fun i : Fin 2 => P.φ (![p.1, p.2] i)) = ![P.φ p.1, P.φ p.2] := by
      funext i; fin_cases i <;> rfl
    show P.u (z.1.1 fun i => P.φ (![p.1, p.2] i)) = P.u (z.1.1 ![P.φ p.1, P.φ p.2])
    rw [hv]
  exact congrArg Submodule.Quotient.mk key
end ReciprocityTheory.Coh.LowDeg
