-- Prove2me | solution 1 for P2M_GlobalTheory_HasRationalTorsion_exists_pow_twelve_eq___43dcc7f916ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:58.348243+00:00
-- url     : https://prove2.me/submissions/1ddbadfb-7d3e-41f0-be32-5e816443b7a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_HasRationalTorsion_of_dvd
import Theorems.Thm_P2M_GlobalTheory_splitCurve___21d0522b5d77
import Theorems.Thm_P2M_GlobalTheory_deuringCurve___056d131758c7
import Theorems.Thm_GlobalTheory_HasRationalTorsion_exists_deuringCurve
import Theorems.Thm_GlobalTheory_HasRationalTorsion_exists_splitCurve_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {K : Type*} [Field K] [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
namespace GlobalTheory
namespace HasRationalTorsion
theorem _root_.solution (h : HasRationalTorsion W L 12) :
    ∃ δ : K, δ ^ 12 = W.Δ := by
  obtain ⟨C, A, B, -, c, hu, e, -, hc⟩ := (h.of_dvd (by norm_num : 4 ∣ 12)).exists_splitCurve_sq
  obtain ⟨C', a, b, d, hu', e', hd⟩ := (h.of_dvd (by norm_num : 3 ∣ 12)).exists_deuringCurve
  have h4 : (2 * c) ^ 4 = W.Δ := by
    have := congrArg WeierstrassCurve.Δ e
    rw [variableChange_Δ, hu, splitCurve_Δ] at this
    simp only [inv_one, Units.val_one, one_pow, one_mul] at this
    rw [this]
    linear_combination 16 * (c ^ 2 + A * B * (A - B)) * hc
  have h3 : (b * d) ^ 3 = W.Δ := by
    have := congrArg WeierstrassCurve.Δ e'
    rw [variableChange_Δ, hu', deuringCurve_Δ] at this
    simp only [inv_one, Units.val_one, one_pow, one_mul] at this
    rw [this, mul_pow, hd]
  refine ⟨b * d / (2 * c), ?_⟩
  have hΔ := W.isUnit_Δ.ne_zero
  rw [div_pow, show 12 = 3 * 4 by rfl, pow_mul, h3, mul_comm 3 4, pow_mul, h4]
  field_simp
end HasRationalTorsion
end GlobalTheory
