-- Prove2me | solution 1 for PI.SerBridgeGLW.trace_inv_of_monoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:17.231278+00:00
-- url     : https://prove2.me/submissions/20663a92-08b9-4a9f-b6e0-8f226189cfe1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Matrix ComplexOrder
open PI PI.SerBridgeGLW
namespace PI.SerBridgeGLW
theorem _root_.solution {G : Type} [Group G] [Fintype G] {n : Type} [Fintype n] [DecidableEq n]
    (M : G →* Matrix n n ℂ) (x : G) : star (trace (M x)) = trace (M x⁻¹) := by
  classical
  set P : Matrix n n ℂ := ∑ g, (M g)ᴴ * M g with hPdef
  have hinv : ∀ y : G, M y * M y⁻¹ = 1 := fun y => by rw [← map_mul, mul_inv_cancel, map_one]
  have hP : (M x)ᴴ * P * M x = P := by
    rw [hPdef, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight x) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulRight, map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hPpd : P.PosDef := by
    rw [hPdef, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]
    simp only [map_one, Matrix.conjTranspose_one, Matrix.mul_one]
    exact Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_sum _ fun g _ => Matrix.posSemidef_conjTranspose_mul_self _)
  have hPu : IsUnit P := hPpd.isUnit
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hPu)
  have hct : (M x)ᴴ = P * M x⁻¹ * P⁻¹ := by
    calc (M x)ᴴ = (M x)ᴴ * P * (M x * M x⁻¹) * P⁻¹ := by
          rw [hinv, Matrix.mul_one, Matrix.mul_assoc, hPP, Matrix.mul_one]
      _ = ((M x)ᴴ * P * M x) * M x⁻¹ * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * M x⁻¹ * P⁻¹ := by rw [hP]
  rw [← Matrix.trace_conjTranspose, hct, Matrix.trace_mul_cycle,
    Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).1 hPu), Matrix.one_mul]
end PI.SerBridgeGLW
