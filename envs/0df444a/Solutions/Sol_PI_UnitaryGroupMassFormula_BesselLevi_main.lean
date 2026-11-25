-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:05.009954+00:00
-- url     : https://prove2.me/submissions/9ff96bcc-2a6c-4a52-88c5-763c73911051

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_inv_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_in
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_row_out
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_uh
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_mulVec_bvec_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_bvec_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_fix
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_n_col
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_of_left_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
namespace PI.UnitaryGroupMassFormula.BesselLevi
variable {k r : ℕ}
private theorem inv_mul_eq_one_of_mem_UH_Hpk {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) : s⁻¹ * s = 1 := by
  rw [inv_eq hs]
  have e : Hpk k r * sᴴ * Hpk k r * s = Hpk k r * (sᴴ * Hpk k r * s) := by simp only [Matrix.mul_assoc]
  rw [e, show sᴴ * Hpk k r * s = Hpk k r from hs, hpk_sq]
private theorem mul_inv_eq_one_of_mem_UH_Hpk {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) : s * s⁻¹ = 1 :=
  Matrix.mul_nonsing_inv s (Matrix.isUnit_det_of_left_inverse (inv_mul_eq_one_of_mem_UH_Hpk hs))
end PI.UnitaryGroupMassFormula.BesselLevi
end
end

set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselLevi
variable {k r : ℕ}
namespace PI.UnitaryGroupMassFormula.BesselLevi
theorem _root_.solution : _root_.PI.BesselLevi.BesselLevi := by
  intro k r T hT s hs hE hz
  have hX : colX k r s := fun i j hj hji => by
    have e := hE ⟨j.val, hj⟩ i hji
    have hj' : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
    rw [hj'] at e
    convert e
  have hWu := hW_uh hs hX
  have hc0 : ((Real.sqrt T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
  refine ⟨hW k r s, ⟨hWu, fun a => ⟨hW_fix _ (Or.inl (by simp [eI])), hW_fix _ (Or.inr (by
      simp only [esI]
      have := a.isLt
      omega))⟩, ?_⟩, (hW k r s)⁻¹ * s,
    (nset_iff _).2 ⟨uh_mul (uh_inv hWu) hs, col_of_left_inv (n_col hs hX) ?_⟩, ?_⟩
  · rw [Matrix.mulVec_smul]
    congr 1
    ext i
    rw [mulVec_bvec_apply, bvec_apply]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [hW_in hi (by simp [wI])]
      have e := hz i hi.1
      rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mulVec_bvec_apply,
        bvec_apply] at e
      exact mul_left_cancel₀ hc0 e
    · rw [hW_row_out i _ (by omega)]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc s, mul_inv_eq_one_of_mem_UH_Hpk hs, Matrix.one_mul, inv_mul_eq_one_of_mem_UH_Hpk hWu]
  · rw [← Matrix.mul_assoc, mul_inv_eq_one_of_mem_UH_Hpk hWu, Matrix.one_mul]
end PI.UnitaryGroupMassFormula.BesselLevi
