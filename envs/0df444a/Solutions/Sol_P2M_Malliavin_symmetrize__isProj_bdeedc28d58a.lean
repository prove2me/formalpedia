-- Prove2me | solution 1 for P2M_Malliavin_symmetrize__isProj_bdeedc28d58a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:04.422963+00:00
-- url     : https://prove2.me/submissions/ad04fc40-133b-4075-a5db-50435455e0dd

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_isSymmetric_symmetrize
import Theorems.Thm_Malliavin_symmetrize_of_isSymmetric

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [AddCommGroup E] [Module ℝ E]
namespace Malliavin
theorem _root_.solution (n : ℕ) :
    LinearMap.IsProj (symmetricSubmodule T E n) (symmetrizeₗ n) where
  map_mem f := isSymmetric_symmetrize n f
  map_id _ hf := symmetrize_of_isSymmetric hf
end Malliavin
