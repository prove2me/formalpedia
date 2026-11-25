-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.frame_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:10:52.490114+00:00
-- url     : https://prove2.me/submissions/ada4e072-bf36-42a3-ae5b-71cb362976de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_pm_mulVec_eq_sum
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_pm_mul_qm
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_qm_mulVec_apply
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_fcol_eI
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_fcol_lt
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_fcol_mid_orth
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_mem_spanLt_iff
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_colm
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_inUJ_iff_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_val


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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} (hc : c ≠ 0) (hz : z0 = c • z)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (inUJ ε g ∧ InN ε e z g) ↔ Qm k r ε e f wf z0 * g * Pm k r e f wf z0 ∈ Nset k r := by
  have hPQ := pm_mul_qm hF
  have hE : (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ↔
      (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) i (eI k r a) = if i = eI k r a then 1 else 0) := by
    refine forall_congr' fun a => ?_
    rw [mem_spanLt_iff hF a.isLt.le]
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    rw [← fcol_eI (k := k) (e := e) (f := f) (wf := wf) (z0 := z0) a, colm hF, sub_eq_zero, Matrix.one_apply]
  have hM : (∀ j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k →
        (g - 1) *ᵥ fcol k r e f wf z0 j ∈ spanLt e r) ↔
      (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
        (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) i j = if i = j then 1 else 0) := by
    constructor
    · intro h i j hj1 hj2 hi
      have := (mem_spanLt_iff hF le_rfl _).1 (h j hj1 hj2) i hi
      rwa [colm hF, sub_eq_zero, Matrix.one_apply] at this
    · intro h j hj1 hj2
      rw [mem_spanLt_iff hF le_rfl]
      intro i hi
      rw [colm hF, sub_eq_zero, Matrix.one_apply]
      exact h i j hj1 hj2 hi
  simp only [Nset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hu, ⟨hS1, _⟩, hN⟩
    exact ⟨(inUJ_iff_UH hF g).1 hu, hE.1 hS1, hM.1 fun j hj1 hj2 => hN _ (fcol_mid_orth hF hj1 hj2)⟩
  · rintro ⟨hu, h2, h3⟩
    have hmid := hM.2 h3
    have hE2 := hE.2 h2
    have hzr : (g - 1) *ᵥ z0 ∈ spanLt e r := by
      have := hmid ⟨r + k, by omega⟩ (by simp) (by simp)
      have hf : fcol k r e f wf z0 ⟨r + k, by omega⟩ = z0 := by simp [fcol]
      rwa [hf] at this
    refine ⟨(inUJ_iff_UH hF g).2 hu, ⟨hE2, ?_⟩, ?_⟩
    · have hzz : z = c⁻¹ • z0 := by rw [hz, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hzz, Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ hzr
    · intro y hy
      have hy' : y = Pm k r e f wf z0 *ᵥ (Qm k r ε e f wf z0 *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
      rw [hy', pm_mulVec_eq_sum, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Matrix.mulVec_smul]
      by_cases hj : j.val < r
      · refine Submodule.smul_mem _ _ ?_
        have := hE2 ⟨j.val, hj⟩
        rw [fcol_lt j hj]
        refine Submodule.span_mono ?_ this
        exact Set.image_mono fun b hb => lt_trans hb hj
      by_cases hj' : j.val ≤ r + k
      · exact Submodule.smul_mem _ _ (hmid j (by omega) hj')
      · have hv := piI_val (k := k) (r := r) j
        have hpl : (piI k r j).val < r := by rw [hv]; split_ifs <;> omega
        rw [qm_mulVec_apply hF, fcol_lt _ hpl, hy, mul_zero, zero_smul]
        exact Submodule.zero_mem _
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
