-- Prove2me | solution 1 for PositivityTheory.Mirab.Irr.deltaU_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:28.083934+00:00
-- url     : https://prove2.me/submissions/c3de244f-4134-403b-accb-e1187f54e275

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr
import Theorems.Thm_GlobalTheory_FiniteGL_mem_mirabInducedSpace


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
theorem _root_.solution (ψ₀ : AddChar k ℂ) : deltaU n ψ₀ ∈ MirabInducedSpace n ψ₀ := by
  rw [mem_mirabInducedSpace]
  intro u x
  by_cases hx : x ∈ uniSub k n
  · have hux : (u : mirabSub k n) * x ∈ uniSub k n := mul_mem u.2 hx
    unfold deltaU
    rw [dif_pos hx, dif_pos hux, ← map_mul]
    exact congrArg (genericChar n ψ₀) (Subtype.ext rfl)
  · have hux : (u : mirabSub k n) * x ∉ uniSub k n := by
      intro hm
      have := mul_mem (inv_mem u.2) hm
      rw [← mul_assoc, inv_mul_cancel, one_mul] at this
      exact hx this
    unfold deltaU
    rw [dif_neg hx, dif_neg hux, mul_zero]
end PositivityTheory.Mirab.Irr
