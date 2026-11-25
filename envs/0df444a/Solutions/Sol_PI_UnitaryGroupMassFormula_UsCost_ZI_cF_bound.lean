-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.cF_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:49.966699+00:00
-- url     : https://prove2.me/submissions/85108c86-8895-4e91-b891-204d624c3810

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_isUnit_eA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_isOpen_det
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_contDiffOn_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_quad_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
theorem _root_.solution (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : Fin s → Fin s → ℂ, (Matrix.of Z).det ≠ 0 → ∀ i, ∀ a ≤ n,
    ‖iteratedFDeriv ℝ a (cF s i) Z‖ ≤ K * (max 1 ‖eA s‖ * max 1 ‖Ring.inverse (eA s Z)‖) ^ (a + 1) := by
  set U := {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} with hU_def
  have hUo : IsOpen U := isOpen_det s
  let φ : (Fin s → Fin s → ℂ) → En s := fun Z => Ring.inverse (eA s Z)
  let P : (En s →L[ℝ] En s) →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] En s) :=
    (ContinuousLinearMap.compL ℝ (Fin s → Fin s → ℂ) (En s) (En s)).flip (eA s)
  let Bi : En s →L[ℝ] En s →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] En s) :=
    (ContinuousLinearMap.compL ℝ (En s) (En s →L[ℝ] En s) _ (-P)).comp
      (ContinuousLinearMap.mulLeftRight ℝ (En s))
  have hφ : ∀ m : ℕ, ContDiffOn ℝ m φ U := fun m =>
    (contDiffOn_inv s m).comp (eA s).contDiff.contDiffOn (fun Z hZ => isUnit_eA s hZ)
  have hd : ∀ Z ∈ U, fderiv ℝ φ Z = Bi (φ Z) (φ Z) := by
    intro Z hZ
    obtain ⟨u, hu⟩ := isUnit_eA s hZ
    have h0 := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu] at h0
    have h1 := h0.comp Z (eA s).hasFDerivAt
    have hinv : ((u⁻¹ : (En s)ˣ) : En s) = φ Z := by
      show _ = Ring.inverse (eA s Z)
      rw [← hu, Ring.inverse_unit u]
    rw [show φ = Ring.inverse ∘ (eA s) from rfl, h1.fderiv, hinv]
    ext W : 1
    simp [Bi, P, φ]
  obtain ⟨K0, hK0, hb⟩ := quad_bound Bi hUo hφ hd n
  refine ⟨(∑ j, ‖lamF s j‖) * K0,
    mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hK0, ?_⟩
  intro Z hZ i a ha
  have hZU : Z ∈ U := hZ
  have hcf : cF s i = (lamF s i) ∘ φ := rfl
  have e1 : iteratedFDeriv ℝ a (cF s i) Z = iteratedFDerivWithin ℝ a (cF s i) U Z :=
    (iteratedFDerivWithin_of_isOpen a hUo hZU).symm
  have e2 : iteratedFDeriv ℝ a φ Z = iteratedFDerivWithin ℝ a φ U Z :=
    (iteratedFDerivWithin_of_isOpen a hUo hZU).symm
  have h3 : ‖iteratedFDerivWithin ℝ a (cF s i) U Z‖
      ≤ ‖lamF s i‖ * ‖iteratedFDerivWithin ℝ a φ U Z‖ := by
    rw [hcf]
    exact (lamF s i).norm_iteratedFDerivWithin_comp_left (hφ a Z hZU) hUo.uniqueDiffOn hZU le_rfl
  have hLi : ‖lamF s i‖ ≤ ∑ j, ‖lamF s j‖ :=
    Finset.single_le_sum (f := fun j => ‖lamF s j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hM0 : 0 ≤ max 1 ‖φ Z‖ := le_trans zero_le_one (le_max_left _ _)
  have hM : max 1 ‖φ Z‖ ≤ max 1 ‖eA s‖ * max 1 ‖φ Z‖ :=
    le_mul_of_one_le_left hM0 (le_max_left _ _)
  have hL0 : 0 ≤ ∑ j, ‖lamF s j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [e1]
  calc _ ≤ ‖lamF s i‖ * ‖iteratedFDerivWithin ℝ a φ U Z‖ := h3
    _ ≤ (∑ j, ‖lamF s j‖) * (K0 * max 1 ‖φ Z‖ ^ (a + 1)) := by
        rw [← e2]
        exact mul_le_mul hLi (hb Z hZU a ha) (norm_nonneg _) hL0
    _ ≤ (∑ j, ‖lamF s j‖) * (K0 * (max 1 ‖eA s‖ * max 1 ‖φ Z‖) ^ (a + 1)) := by
        gcongr
    _ = (∑ j, ‖lamF s j‖) * K0 * (max 1 ‖eA s‖ * max 1 ‖Ring.inverse (eA s Z)‖) ^ (a + 1) := by
        ring
end PI.UnitaryGroupMassFormula.UsCost.ZI
