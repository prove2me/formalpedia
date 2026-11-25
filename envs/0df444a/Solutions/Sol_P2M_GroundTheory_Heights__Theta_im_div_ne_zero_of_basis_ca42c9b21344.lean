-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_im_div_ne_zero_of_basis_ca42c9b21344
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:47.483801+00:00
-- url     : https://prove2.me/submissions/3e223732-c0c9-480e-9fec-888d2f72461d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassReducedParamsNonemptyPf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_IsLatticeParam_smul_fdb7c318695f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    {ι : Type*} (b : Module.Basis ι ℚ K) (e : ι ≃ Fin 2) :
    (σ (b (e.symm 1)) / σ (b (e.symm 0))).im ≠ 0 := by
  set w : ℂ := (σ (b (e.symm 0)))⁻¹ with hw
  intro h0
  have hall : ∀ x : K, (σ x * w).im = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨j, rfl⟩ := e.symm.surjective i
      fin_cases j
      · simp only [Fin.zero_eta, w]
        rw [mul_inv_cancel₀]
        · simp
        · exact (map_ne_zero σ).mpr (b.ne_zero _)
      · simpa [div_eq_mul_inv, w] using h0
    | zero => simp
    | add y z _ _ hy hz => simp [add_mul, hy, hz]
    | smul q y _ hy =>
      rw [Rat.smul_def, map_mul, map_ratCast, mul_assoc]
      simp [hy]
  have hw0 : w ≠ 0 := inv_ne_zero ((map_ne_zero σ).mpr (b.ne_zero _))
  have hwim : w.im = 0 := by simpa using hall 1
  obtain ⟨x, hx⟩ := hσ
  apply hx
  have hxr : σ x = (σ x * w) * w⁻¹ := by field_simp
  have hwinv : (w⁻¹).im = 0 := by simp [Complex.inv_im, hwim]
  rw [hxr, Complex.mul_im, hall x, hwinv]
  ring
end GroundTheory.Heights₂.Theta
