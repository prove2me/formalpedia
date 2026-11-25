-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.dvd_prod_shift_sub_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:35.742082+00:00
-- url     : https://prove2.me/submissions/cd0ff059-3843-4720-9da6-ea061441cec9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}
namespace PositivityTheory.Rg.Cz.SpecA
theorem _root_.solution {R : Type*} [CommRing R] (Y : R) (Z : List R) : Y ∣ (Z.map (Y + ·)).prod - Z.prod := by
  induction Z with
  | nil => simp
  | cons z Z ih =>
    simp only [List.map_cons, List.prod_cons]
    have he : (Y + z) * (Z.map (Y + ·)).prod - z * Z.prod =
        Y * (Z.map (Y + ·)).prod + z * ((Z.map (Y + ·)).prod - Z.prod) := by ring
    rw [he]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right ih _)
end PositivityTheory.Rg.Cz.SpecA
