-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.rowForm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:25.944362+00:00
-- url     : https://prove2.me/submissions/11effdef-1312-42de-9f9a-820d3780906a

import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmRowForm
namespace PI.UnitaryGroupMassFormula.QmRowForm
theorem _root_.solution (h1 : DblDec) (h2 : DblInc) (h3 : DblPerm) : PI.RowForm := by
  intro A _ _ n t E hE a b u
  have hx : (fun k : Fin t => u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) ∘ (Fin.revPerm : Equiv.Perm (Fin t)) =
      fun k : Fin t => u - (k : ℂ) := by
    funext k
    have hk : (k : ℕ) + 1 ≤ t := k.isLt
    simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub hk, Nat.cast_add,
      Nat.cast_one]
    ring
  have e1 := h1 A n t E hE a b u
  have e2 := h2 A n t E hE a b u
  have e3 := h3 A n t E hE a b (fun k : Fin t => u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) Fin.revPerm
  rw [hx, e1, e2] at e3
  have hf : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  have e4 := congrArg (fun y : A => ((t.factorial : ℂ)⁻¹) • y) e3
  simp only [smul_smul, inv_mul_cancel₀ hf, one_smul] at e4
  exact e4
end PI.UnitaryGroupMassFormula.QmRowForm
