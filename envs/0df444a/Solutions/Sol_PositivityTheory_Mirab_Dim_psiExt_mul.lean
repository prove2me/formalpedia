-- Prove2me | solution 1 for PositivityTheory.Mirab.Dim.psiExt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:59.263736+00:00
-- url     : https://prove2.me/submissions/eee81880-d579-4131-afb9-c4f1ec14e767

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndDim
import Theorems.Thm_PositivityTheory_Mirab_Dim_psiExt_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open PositivityTheory PositivityTheory.Mirab PositivityTheory.Mirab.Dim
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
variable (ψ₀ : AddChar k ℂ)
namespace PositivityTheory.Mirab.Dim
theorem _root_.solution (u : uniSub k n) (y : mirabSub k n) (hy : y ∈ uniSub k n) :
    psiExt n ψ₀ ((u : mirabSub k n) * y) = genericChar n ψ₀ u * psiExt n ψ₀ y := by
  have h := psiExt_of_mem n ψ₀ (u * ⟨y, hy⟩)
  rw [map_mul, ← psiExt_of_mem n ψ₀ ⟨y, hy⟩] at h
  exact h
end PositivityTheory.Mirab.Dim
