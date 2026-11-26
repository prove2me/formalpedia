-- Prove2me | solution 1 for P2M_Malliavin_symmetrize__comp_symmetrize__14ce21f0a046
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:01.586286+00:00
-- url     : https://prove2.me/submissions/67295a5b-3320-4610-86ca-f3922479a950

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrize_symmetrize

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [AddCommGroup E] [Module ℝ E]
namespace Malliavin
theorem _root_.solution (n : ℕ) :
    (symmetrizeₗ n : ((Fin n → T) → E) →ₗ[ℝ] ((Fin n → T) → E)).comp (symmetrizeₗ n) =
      symmetrizeₗ n :=
  LinearMap.ext fun f => symmetrize_symmetrize n f
end Malliavin
