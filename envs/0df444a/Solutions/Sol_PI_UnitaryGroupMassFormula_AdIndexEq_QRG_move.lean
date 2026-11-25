-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:23.099153+00:00
-- url     : https://prove2.me/submissions/b336a81a-7914-4708-9dac-b39d326f2858

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_sub_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_sub_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (u y : Fin n → K)
    (huy : H σ J u u = H σ J y y) (ha : H σ J (u - y) (u - y) ≠ 0) :
    ∃ α : K, σ α * α = 1 ∧ Rm σ J (u - y) α *ᵥ u = y ∧
      ∀ z, H σ J (u - y) z = 0 → Rm σ J (u - y) α *ᵥ z = z := by
  have hD : H σ J (u - y) u = H σ J u u - H σ J y u := H_sub_left σ J u y u
  have hsD : σ (H σ J (u - y) u) = H σ J u u - H σ J u y := by
    rw [hD, map_sub, ← H_symm σ J hσ hJ u u, ← H_symm σ J hσ hJ y u]
  have hc : H σ J (u - y) (u - y) = H σ J (u - y) u + σ (H σ J (u - y) u) := by
    rw [hsD, hD, H_sub_right, H_sub_left, H_sub_left, huy]
    ring
  have hD0 : H σ J (u - y) u ≠ 0 := by
    intro h0
    apply ha
    rw [hc, h0, map_zero, add_zero]
  have hsD0 : σ (H σ J (u - y) u) ≠ 0 := (map_ne_zero σ).mpr hD0
  refine ⟨-(σ (H σ J (u - y) u)) / H σ J (u - y) u, ?_, ?_, ?_⟩
  · rw [map_div₀, map_neg, hσ]
    field_simp
  · rw [Rm_mulVec]
    have hcoef : (-(σ (H σ J (u - y) u)) / H σ J (u - y) u - 1) *
        ((H σ J (u - y) (u - y))⁻¹ * H σ J (u - y) u) = -1 := by
      rw [hc]
      have hsum : H σ J (u - y) u + σ (H σ J (u - y) u) ≠ 0 := by rw [← hc]; exact ha
      field_simp
      ring
    rw [hcoef, neg_one_smul]
    abel
  · intro z hz
    rw [Rm_mulVec, hz, mul_zero, mul_zero, zero_smul, add_zero]
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
