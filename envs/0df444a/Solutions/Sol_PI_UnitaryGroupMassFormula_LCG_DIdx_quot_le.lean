-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.DIdx.quot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:44.410582+00:00
-- url     : https://prove2.me/submissions/76b3f1ce-5b96-4954-9375-03f081c1a2bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DIdx_absNorm_eq_index

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
open PI.UnitaryGroupMassFormula.LCG.DIdx
namespace PI.UnitaryGroupMassFormula.LCG.DIdx
theorem _root_.solution (K : Type) [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (a : 𝓞 K)
    (ha0 : a ≠ 0) :
    Ideal.span {a} ≤ qI 𝔞 a ∧
    (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≠ 0 ∧
    (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≤ Ideal.absNorm 𝔞 := by
  have hle : Ideal.span {a} ≤ qI 𝔞 a := by
    intro y hy c _
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [Ideal.mem_span_singleton']
    exact ⟨c * z, by ring⟩
  have hmul : 𝔞 * qI 𝔞 a ≤ Ideal.span {a} := Ideal.mul_le.mpr fun r hr s hs => hs r hr
  have hq0 : qI 𝔞 a ≠ ⊥ := by
    intro h
    have : a ∈ qI 𝔞 a := hle (Ideal.mem_span_singleton_self a)
    rw [h, Ideal.mem_bot] at this
    exact ha0 this
  have hNq : Ideal.absNorm (qI 𝔞 a) ≠ 0 := fun h => hq0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hNa : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
    exact ha0 h
  have hN𝔞 : Ideal.absNorm 𝔞 ≠ 0 := fun h => h𝔞 (Ideal.absNorm_eq_zero_iff.mp h)
  have hrel : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup * Ideal.absNorm (qI 𝔞 a) =
      Ideal.absNorm (Ideal.span {a}) := by
    rw [absNorm_eq_index, absNorm_eq_index]
    exact AddSubgroup.relIndex_mul_index ((Submodule.toAddSubgroup_le _ _).mpr hle)
  have hdvd : Ideal.absNorm (Ideal.span {a}) ∣ Ideal.absNorm 𝔞 * Ideal.absNorm (qI 𝔞 a) := by
    have := Ideal.absNorm_dvd_absNorm_of_le hmul
    rwa [map_mul] at this
  have hr0 : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrel
    exact hNa hrel.symm
  refine ⟨hle, hr0, ?_⟩
  have h1 : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup * Ideal.absNorm (qI 𝔞 a) ≤
      Ideal.absNorm 𝔞 * Ideal.absNorm (qI 𝔞 a) := by
    rw [hrel]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hN𝔞 hNq)) hdvd
  exact Nat.le_of_mul_le_mul_right h1 (Nat.pos_of_ne_zero hNq)
end PI.UnitaryGroupMassFormula.LCG.DIdx
