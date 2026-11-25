-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.det_column_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:41.625037+00:00
-- url     : https://prove2.me/submissions/41d72982-63dd-420f-832f-3a1b60fcedf9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetDFin
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetColumnPerturbation
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_det_first_row_expansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.phiL_apply
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.piL_apply

set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) (c : Fin N) :
    (1 + phiF X + s • Matrix.single 0 c.succ 1).det = (1 + piF X - s • colQ X c).det := by
  set A := 1 + phiF X + s • Matrix.single 0 c.succ (1 : ℂ) with hA
  have hne : c.succ ≠ (0 : Fin (N + 1)) := Fin.succ_ne_zero c
  have hz : ∀ k : Fin N, ((0 : Fin (N + 1)) = k.succ) ↔ False :=
    fun k => ⟨fun h => Fin.succ_ne_zero k h.symm, False.elim⟩
  rw [← Matrix.det_updateCol_add_smul_self A hne (-s)]
  rw [det_first_row_expansion _ 1]
  · rw [one_mul]
    congr 1
    ext k l
    by_cases hl : l = c
    · subst hl
      simp [A, Matrix.updateCol_apply, piF, colQ, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj,
        Fin.succ_ne_zero, hz]
      ring
    · have hl' : l.succ ≠ c.succ := fun h => hl (Fin.succ_inj.mp h)
      simp [A, Matrix.updateCol_apply, piF, colQ, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj,
        hl, hl', Fin.succ_ne_zero, hz]
  · intro j
    by_cases hj : j = c.succ
    · subst hj
      simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, Fin.succ_ne_zero, hz]
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨m, rfl⟩
      · simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, hne.symm, hz]
      · have hm : m ≠ c := fun h => hj (by rw [h])
        simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, hm, Fin.succ_ne_zero, hz,
          Fin.succ_inj, Ne.symm hm]
end PositivityTheory.Rg.Sw.LVs.CK
