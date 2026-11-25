-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.tau_pow_le_ht
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:58.638247+00:00
-- url     : https://prove2.me/submissions/7e92f17c-bf99-4db0-bffc-29e5b89383d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatticeIsDiscreteGroup
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_gram_nonneg
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ht_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (hz : 0 < tau1 I z) (s : Sub I z) :
    tau1 I z ^ (2 * I.f * s.j) ≤ ht I s ∧ idx I s.B s.b ≠ 0 := by
  have hf : 0 < I.f := Module.finrank_pos
  have hj : 0 < s.j := s.j_pos
  have hN : (0 : ℝ) < 2 * (I.f : ℝ) * (s.j : ℝ) := by
    have : (0 : ℝ) < I.f := by exact_mod_cast hf
    have : (0 : ℝ) < s.j := by exact_mod_cast hj
    positivity
  have hht : ∀ t : Sub I z, 0 ≤ ht I t := by
    intro t
    rw [ht_eq]
    exact div_nonneg (Finset.prod_nonneg fun v _ => gram_nonneg hDM I z v t.b) (Nat.cast_nonneg _)
  have hsize : ∀ t : Sub I z, 0 ≤ size I t := fun t => Real.rpow_nonneg (hht t) _
  have hle : tau1 I z ≤ size I s :=
    (min_le_right _ _).trans (ciInf_le ⟨0, by rintro _ ⟨t, rfl⟩; exact hsize t⟩ s)
  have hpow : size I s ^ (2 * I.f * s.j) = ht I s := by
    unfold size
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hht s)]
    push_cast
    rw [one_div_mul_cancel hN.ne', Real.rpow_one]
  refine ⟨?_, ?_⟩
  · calc tau1 I z ^ (2 * I.f * s.j) ≤ size I s ^ (2 * I.f * s.j) := pow_le_pow_left₀ hz.le hle _
      _ = ht I s := hpow
  · intro h0
    have h1 : ht I s = 0 := by
      rw [ht_eq, h0]
      simp
    have hs0 : size I s = 0 := by
      unfold size
      rw [h1, Real.zero_rpow (one_div_pos.2 hN).ne']
    linarith
end PI.UnitaryGroupMassFormula.LCG
