-- Prove2me | solution 1 for PI.IsoDualPair.UnitaryGroupMassFormula.conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:50:24.070335+00:00
-- url     : https://prove2.me/submissions/22eb56a8-fa4e-4cdb-b8cb-bd74fb81a711

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_hvC_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.IsoDualPair PI.IsoDualPair.UnitaryGroupMassFormula
open PI.IsoDualPair
variable {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoDualPair.UnitaryGroupMassFormula
theorem _root_.solution {φ : LaC N nu} (h : φ ∈ Vnu N nu) : (fun J => conj (φ J)) ∈ Vnu N nu := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    rw [hvC_conj]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero =>
    have : (fun J => conj ((0 : LaC N nu) J)) = 0 := by funext J; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun J => conj ((x + y) J)) = (fun J => conj (x J)) + (fun J => conj (y J)) := by
      funext J; simp
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (fun J => conj ((a • x) J)) = conj a • (fun J => conj (x J)) := by
      funext J; simp
    rw [this]; exact Submodule.smul_mem _ _ hx
end PI.IsoDualPair.UnitaryGroupMassFormula
