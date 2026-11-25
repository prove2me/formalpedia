-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__inclCx_spec_0473f0a012a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:58.807651+00:00
-- url     : https://prove2.me/submissions/9b6c5404-54a6-42d9-8fa4-0a5078e9c0c0

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Coh.CohomologyFunctoriality₂
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : TRep R G} {U : Subgroup G}
namespace ReciprocityTheory.Coh.CohomologyFunctoriality₂
theorem _root_.solution (A : Cx R) (eA : ∀ n, A.X n ≃ₗ[R] hcoch (M.resSub U) G n)
    (hA : IsHomog (M.resSub U) G A eA) (eG : ∀ n, M.coch.X n ≃ₗ[R] hcoch M G n) (hG : IsHomog M G M.coch eG)
    (n : ℕ) (F : M.coch.X n) : (eA n ((inclCx A eA hA eG hG).f n F)).1 = (eG n F).1 := by
  show (eA n ((eA n).symm (inclL n (eG n F)))).1 = _
  rw [LinearEquiv.apply_symm_apply]
  rfl
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
