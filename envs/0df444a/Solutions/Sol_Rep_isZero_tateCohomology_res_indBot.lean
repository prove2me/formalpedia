-- Prove2me | solution 1 for Rep.isZero_tateCohomology_res_indBot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e927595a-e44f-536a-8c73-2396f5374cfb

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_of_iso
import Theorems.Thm_Rep_nonempty_res_indBot_iso
import Theorems.Thm_Rep_isZero_tateCohomology_indBot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_isZero_tateCohomology_res_indBot
p2m_attr_erase "simp" "Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply"

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [Fintype S] (A : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.res S.subtype A.indBot).tateCohomology q) := by
  obtain ⟨e⟩ := Rep.nonempty_res_indBot_iso S A
  obtain ⟨e'⟩ := Rep.nonempty_tateCohomology_iso_of_iso e q
  exact (Rep.isZero_tateCohomology_indBot (Rep.trivial k S ((G ⧸ S) →₀ A)) q).of_iso e'

end S_Rep_isZero_tateCohomology_res_indBot
end P2MW
export P2MW.S_Rep_isZero_tateCohomology_res_indBot (solution)
