-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__normCx_spec_5a505131bda6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:04.944635+00:00
-- url     : https://prove2.me/submissions/19755ee7-8207-4f82-93e4-d30a770fd39a

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
  (M : TRep R G) (U : Subgroup G) [U.FiniteIndex]
variable {M U}
namespace ReciprocityTheory.Coh.CohomologyFunctoriality₂
theorem _root_.solution (A : Cx R) (eA : ∀ n, A.X n ≃ₗ[R] hcoch (M.resSub U) G n)
    (hA : IsHomog (M.resSub U) G A eA) (eG : ∀ n, M.coch.X n ≃ₗ[R] hcoch M G n) (hG : IsHomog M G M.coch eG)
    (n : ℕ) (F : A.X n) : (eG n ((normCx A eA hA eG hG).f n F)).1 = normF M U n (eA n F).1 := by
  show (eG n ((eG n).symm (normL M U n (eA n F)))).1 = _
  rw [LinearEquiv.apply_symm_apply]
  rfl
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
