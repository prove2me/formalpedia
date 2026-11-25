-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.normF_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:45:47.35513+00:00
-- url     : https://prove2.me/submissions/e7b1f392-e617-4601-913e-2b64adaa6a21

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
variable [U.FiniteIndex]
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {M : TRep R G} (n : ℕ) (F F' : (Fin (n + 1) → G) → M.V) :
    normF M U n (F - F') = normF M U n F - normF M U n F' := by
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  funext x
  simp only [normF, Pi.sub_apply, map_sub, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib]
end ReciprocityTheory.Coh.CCA
