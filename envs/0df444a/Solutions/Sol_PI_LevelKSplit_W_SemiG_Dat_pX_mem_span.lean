-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.pX_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:56.116087+00:00
-- url     : https://prove2.me/submissions/cee00a78-5bb1-471c-8a7e-2fc0501415df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (u : n → A) : D.pX u ∈ Submodule.span A (Set.range D.e) := by
  simp only [pX, LinearMap.sum_apply, LinearMap.smulRight_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
end PI.LevelKSplit.W.SemiG.Dat
