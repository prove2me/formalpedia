-- Prove2me | solution 1 for ReciprocityTheory.Gal.mem_Sel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:56.235698+00:00
-- url     : https://prove2.me/submissions/f21933c0-c095-4e4c-8f23-69f34f5d3aee

import Definitions.Def_ReciprocityTheory_GaloisValuations_SeparatedDvrSecondCohomologyMem
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Gal
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
variable {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (phi : ∀ i, D i →* G) (hphi : ∀ i, Continuous (phi i))
namespace ReciprocityTheory.Gal
theorem _root_.solution (L : LocCond rho phi) (x : H1 rho) :
    x ∈ Sel rho phi hphi L ↔ ∀ i, resH1 rho (phi i) (hphi i) x ∈ L i := by
  simp only [Sel, Submodule.mem_iInf, Submodule.mem_comap]
end ReciprocityTheory.Gal
