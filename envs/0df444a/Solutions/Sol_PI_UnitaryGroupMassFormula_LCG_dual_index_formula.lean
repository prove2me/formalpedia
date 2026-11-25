-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.dual_index_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:39:42.270547+00:00
-- url     : https://prove2.me/submissions/27125845-02ef-4936-8804-b1986ebefd62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DIdx_dualL_anti
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DIdx_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open DIdx
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution : DualIdx := by
  intro K _ _ k X Y hXY hne
  suffices H : ∀ m : ℕ, ∀ X Y : Submodule (𝓞 K) (Fin k → K), X ≤ Y →
      X.toAddSubgroup.relIndex Y.toAddSubgroup = m → m ≠ 0 →
      (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
        (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤ X.toAddSubgroup.relIndex Y.toAddSubgroup from
    H _ X Y hXY rfl hne
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X Y hXY hm hm0
  by_cases hYX : Y ≤ X
  · have e : X = Y := le_antisymm hXY hYX
    subst e
    rw [AddSubgroup.relIndex_self, AddSubgroup.relIndex_self]
    exact ⟨one_ne_zero, le_rfl⟩
  · obtain ⟨x, hxY, hxX⟩ := Set.not_subset.mp hYX
    have hX1Y : X ⊔ Submodule.span (𝓞 K) {x} ≤ Y :=
      sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hxY)
    have hXX1 : X ≤ X ⊔ Submodule.span (𝓞 K) {x} := le_sup_left
    have hxX1 : x ∈ X ⊔ Submodule.span (𝓞 K) {x} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    obtain ⟨h0, hle⟩ := step K k X Y hXY (by rw [hm]; exact hm0) x hxY
    have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXX1)
      ((Submodule.toAddSubgroup_le _ _).mpr hX1Y)
    rw [hm] at hmul
    have hb0 : (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 := by
      intro h; rw [h, mul_zero] at hmul; exact hm0 hmul.symm
    have ha0 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0 := by
      intro h; rw [h, zero_mul] at hmul; exact hm0 hmul.symm
    have ha1 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 1 := by
      intro h
      rw [AddSubgroup.relIndex_eq_one] at h
      exact hxX (h hxX1)
    have hlt : (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup.relIndex Y.toAddSubgroup < m := by
      rw [← hmul]
      have h2 : 2 ≤ X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by omega
      have hbpos := Nat.pos_of_ne_zero hb0
      nlinarith
    obtain ⟨ih0, ihle⟩ := ih _ hlt (X ⊔ Submodule.span (𝓞 K) {x}) Y hX1Y rfl hb0
    have hdmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr (DIdx.dualL_anti hX1Y))
      ((Submodule.toAddSubgroup_le _ _).mpr (DIdx.dualL_anti hXX1))
    rw [← hdmul, hm, ← hmul]
    refine ⟨mul_ne_zero ih0 h0, ?_⟩
    rw [mul_comm (X.toAddSubgroup.relIndex _)]
    exact Nat.mul_le_mul ihle hle
end PI.UnitaryGroupMassFormula.LCG
