-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BModbound.ratio_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:41.242004+00:00
-- url     : https://prove2.me/submissions/53da554c-b743-4ccb-8a13-6cfdccc22ed4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_HaarMeasureGL
import Theorems.Thm_P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_measure_eq_relIndex_mul__a8f443d766a4
import Theorems.Thm_P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_relIndex_ne_zero_of_isCompact_of_isOpen__ed8b7a4764f5
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_pi_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module ValuativeRel MeasureTheory
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound
theorem _root_.solution {d : ℕ} (X' Y' : AddSubgroup (Fin d → k)) (hXc : IsCompact (X' : Set (Fin d → k)))
    (hXo : IsOpen (X' : Set (Fin d → k))) (L : (Fin d → k) ≃ₗ[k] (Fin d → k))
    (hY : (Y' : Set (Fin d → k)) = L '' (X' : Set (Fin d → k))) :
    (X' ⊓ Y').relIndex X' ≠ 0 ∧ (X' ⊓ Y').relIndex Y' ≠ 0 ∧
      ((X' ⊓ Y').relIndex Y' : ℝ) / ((X' ⊓ Y').relIndex X' : ℝ) =
        (distribHaarChar k (LinearEquiv.det L) : ℝ) := by
  have hLc : Continuous L := L.toLinearMap.continuous_on_pi
  have hLsc : Continuous L.symm := L.symm.toLinearMap.continuous_on_pi
  have hYeq : (Y' : Set (Fin d → k)) = L.symm ⁻¹' (X' : Set (Fin d → k)) := by
    rw [hY]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      exact ⟨L.symm y, h, by simp⟩
  have hYo : IsOpen (Y' : Set (Fin d → k)) := hYeq ▸ hXo.preimage hLsc
  have hYc : IsCompact (Y' : Set (Fin d → k)) := hY ▸ hXc.image hLc
  have hJo : IsOpen ((X' ⊓ Y' : AddSubgroup (Fin d → k)) : Set (Fin d → k)) := by
    rw [AddSubgroup.coe_inf]; exact hXo.inter hYo
  have n1 := relIndex_ne_zero_of_isCompact_of_isOpen' X' (X' ⊓ Y') hXc hJo inf_le_left
  have n2 := relIndex_ne_zero_of_isCompact_of_isOpen' Y' (X' ⊓ Y') hYc hJo inf_le_right
  refine ⟨n1, n2, ?_⟩
  borelize (Fin d → k)
  let μ : Measure (Fin d → k) := Measure.addHaar
  have e1 := measure_eq_relIndex_mul' _ μ (X' ⊓ Y') X' inf_le_left hJo.measurableSet n1
  have e2 := measure_eq_relIndex_mul' _ μ (X' ⊓ Y') Y' inf_le_right hJo.measurableSet n2
  have e3 : μ (Y' : Set (Fin d → k)) = distribHaarChar (Fin d → k) L * μ (X' : Set (Fin d → k)) := by
    rw [distribHaarChar_mul μ L, hY]
    rfl
  rw [GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq] at e3
  have hJ0 : μ ((X' ⊓ Y' : AddSubgroup (Fin d → k)) : Set (Fin d → k)) ≠ 0 :=
    hJo.measure_ne_zero μ ⟨0, (X' ⊓ Y').zero_mem⟩
  have hJt : μ ((X' ⊓ Y' : AddSubgroup (Fin d → k)) : Set (Fin d → k)) ≠ ⊤ :=
    ne_top_of_le_ne_top hXc.measure_lt_top.ne (measure_mono (by simp [AddSubgroup.coe_inf]))
  have key : ((X' ⊓ Y').relIndex Y' : ENNReal) =
      (distribHaarChar k (LinearEquiv.det L) : ENNReal) * ((X' ⊓ Y').relIndex X' : ENNReal) := by
    have h := e3
    rw [e1, e2, ← mul_assoc] at h
    exact (ENNReal.mul_left_inj hJ0 hJt).1 h
  have key' := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_mul] at key'
  simp only [ENNReal.toReal_natCast, ENNReal.coe_toReal] at key'
  rw [key', mul_div_assoc, div_self (by exact_mod_cast n1), mul_one]
end PositivityTheory.RgUd.T.Nil.Orb.BModbound
