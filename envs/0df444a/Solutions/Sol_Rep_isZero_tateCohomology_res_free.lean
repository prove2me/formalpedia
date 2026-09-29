-- Prove2me | solution 1 for Rep.isZero_tateCohomology_res_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3254356d-e831-57f7-88cc-938804ab913b

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Definitions.Def_GroupCohomology_RelationModule
import Theorems.Thm_Rep_nonempty_res_free_iso_free
import Theorems.Thm_Rep_isZero_tateCohomology_free_tensor
import Theorems.Thm_Rep_isZero_tateCohomology_of_retract
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_isZero_tateCohomology_res_free

set_option autoImplicit false
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

theorem solution {k G : Type} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] (α : Type) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.res S.subtype (Rep.free k G α)).tateCohomology q) := by
  obtain ⟨β, ⟨e⟩⟩ := Rep.nonempty_res_free_iso_free (k := k) S α
  have hB := Rep.isZero_tateCohomology_free_tensor (G := ↥S) β (𝟙_ (Rep k ↥S)) q
  exact Rep.isZero_tateCohomology_of_retract (e.hom ≫ (ρ_ _).inv) ((ρ_ _).hom ≫ e.inv) (by simp) q hB

end S_Rep_isZero_tateCohomology_res_free
end P2MW
export P2MW.S_Rep_isZero_tateCohomology_res_free (solution)
