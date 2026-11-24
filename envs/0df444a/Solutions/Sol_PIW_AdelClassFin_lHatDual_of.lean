-- Prove2me | solution 1 for PIW.AdelClassFin.lHatDual_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:11:08.32389+00:00
-- url     : https://prove2.me/submissions/607347a8-353e-495c-8fb6-03e0657a4b94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
import Theorems.Thm_PIW_AdelClassFin_DictLat_hhat_iv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (h₁ : DInter) (h₂ : LDenom) (h₃ : LDense) (h₄ : LHatInt) : LHatDual := by
  intro I z hz
  obtain ⟨m, hm, hmz⟩ := h₂ I z
  obtain ⟨l, hl, y', hy', he⟩ := h₃ I m hm _ hmz
  have hmE : (m : I.E) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hiv : iv I ((m : I.E)⁻¹ • l) = z - y' := by
    rw [DictLat.iv_smulE]
    have e1 : iv I l = (m : I.E ⊗[I.F] Af I.F) • (z - y') := by
      rw [smul_sub, he]
      abel
    rw [e1, smul_smul]
    have e2 : Formalism.UG.inclE (F := I.F) (Af I.F) (m : I.E)⁻¹ * (m : I.E ⊗[I.F] Af I.F) = 1 := by
      rw [← map_natCast (Formalism.UG.inclE (F := I.F) (Af I.F)) m, ← map_mul, inv_mul_cancel₀ hmE,
        map_one]
    rw [e2, one_smul]
  have hv : (m : I.E)⁻¹ • l ∈ I.L := by
    rw [I.L_dual]
    intro y hy
    apply h₁ I.F I.E
    have e3 : z - y' = z + (-1 : I.E ⊗[I.F] Af I.F) • y' := by rw [neg_one_smul, sub_eq_add_neg]
    rw [← DictLat.hhat_iv, hiv, e3, DictLat.hhat_add_right, DictLat.hhat_smul_right]
    exact add_mem (hz _ (DictLat.iv_mem I hy))
      (mul_mem (neg_mem (one_mem _)) (h₄ I _ (DictLat.iv_mem I hy) _ hy'))
  have hz' : z = iv I ((m : I.E)⁻¹ • l) + y' := by rw [hiv, sub_add_cancel]
  rw [hz']
  exact I.Lf.add_mem (DictLat.iv_mem I hv) hy'
end PIW.AdelClassFin
