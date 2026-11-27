-- Prove2me | solution 1 for PositivityTheory.Mirab.Irr.mackey_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:36.29144+00:00
-- url     : https://prove2.me/submissions/2931b3a3-3502-4978-8d83-b8bc6ce45b5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_mirabolicIsMackey


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
open PositivityTheory PositivityTheory.Mirab PositivityTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace PositivityTheory.Mirab.Irr
theorem _root_.solution (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) (h : mirabSub k n) (hh : h ∉ uniSub k n) :
    ∃ u c : uniSub k n, (c : mirabSub k n) = h⁻¹ * u * h ∧ genericChar n ψ₀ c ≠ genericChar n ψ₀ u := by
  obtain ⟨u, hu, hc, hne⟩ := (mirabolicIsMackey k ℂ n ψ₀ hψ (mirabSub k n) (uniSub k n)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)).2.2 h hh
  exact ⟨⟨u, hu⟩, ⟨_, hc⟩, rfl, hne⟩
end PositivityTheory.Mirab.Irr
