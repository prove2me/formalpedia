-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.mem_spanLt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:16.422841+00:00
-- url     : https://prove2.me/submissions/2ef60150-62ee-4d3b-8998-42696532e4fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_pm_mulVec_eq_sum
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_pm_mul_qm
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_qm_mulVec_fcol
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_fcol_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula PI.NUnimodLoc.UnitaryGroupMassFormula.FC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW Formalism.REAL
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}
variable (hF : IsFrameJ ε e f wf z0)
include hF
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.FC
theorem _root_.solution {a : ℕ} (ha : a ≤ r) (v : Fin (2 * r + k + 1) → ℂ) :
    v ∈ spanLt e a ↔ ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qm k r ε e f wf z0 *ᵥ v) i = 0 := by
  constructor
  · intro hv
    let W : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
      { carrier := {v | ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qm k r ε e f wf z0 *ᵥ v) i = 0}
        add_mem' := fun {x y} hx hy i hi => by
          rw [Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
        zero_mem' := fun i _ => by simp
        smul_mem' := fun c x hx i hi => by
          rw [Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero] }
    have hle : spanLt e a ≤ W := by
      unfold spanLt
      rw [Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩ i hi
      have hb' : b.val < a := hb
      have hfb : e b = fcol k r e f wf z0 ⟨b.val, by omega⟩ := by simp [fcol, b.isLt]
      show (Qm k r ε e f wf z0 *ᵥ e b) i = 0
      rw [hfb, qm_mulVec_fcol hF, Pi.single_apply, if_neg]
      intro h
      rw [Fin.ext_iff] at h
      simp only at h
      omega
    exact hle hv
  · intro hv
    have hv' : v = Pm k r e f wf z0 *ᵥ (Qm k r ε e f wf z0 *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, pm_mul_qm hF, Matrix.one_mulVec]
    rw [hv', pm_mulVec_eq_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : a ≤ j.val
    · rw [hv j hj, zero_smul]; exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j.val, by omega⟩, ?_, ?_⟩)
      · simp only [Set.mem_ofPred_eq]; omega
      · rw [fcol_lt j (by omega)]
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
