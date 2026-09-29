-- Prove2me | solution 1 for Rep.dimShiftDown_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/68062dc5-9ebf-519d-b576-a388692d780d

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_indBotPi_indBotSigma
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_dimShiftDown_shortExact

set_option autoImplicit false
universe u
open CategoryTheory Rep
set_option maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) :
    (A.dimShiftDown).ShortExact := by
  exact
    { exact := (forget₂ (Rep.{u} k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
        (ShortComplex.moduleCat_exact_iff _).2 fun x hx =>
          ⟨(⟨x, hx⟩ : LinearMap.ker (Rep.indBotπ A).hom.toLinearMap), rfl⟩
      mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
      epi_g := (Rep.epi_iff_surjective _).2 fun a => ⟨A.indBotσ a, Rep.indBotPi_indBotSigma A a⟩ }

end S_Rep_dimShiftDown_shortExact
end P2MW
export P2MW.S_Rep_dimShiftDown_shortExact (solution)
