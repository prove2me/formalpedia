-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_abs_degree_sub_le_caf889cc4611
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:20.472901+00:00
-- url     : https://prove2.me/submissions/458bb356-65cf-4971-99b4-6fe0462381f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_mul_inv_eecafab33dac

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {L : Type} [Field L] [NumberField L] {Ψ : Type} [Fintype Ψ]
    (P : SmallBlockLattices L Ψ) (lat₁ lat₂ : Ψ → FractionalIdeal (𝓞 L)⁰ L) (h₁ : ∀ τ, lat₁ τ ≠ 0)
    (h₂ : ∀ τ, lat₂ τ ≠ 0) (K : ℝ)
    (hx : ∀ τ, |Real.log (FractionalIdeal.absNorm (lat₁ τ * (lat₂ τ)⁻¹) : ℝ)| ≤ Module.finrank ℚ L * K) :
    |P.degree lat₁ - P.degree lat₂| ≤ Fintype.card Ψ * K := by
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  set x := fun τ => Real.log (FractionalIdeal.absNorm (lat₁ τ * (lat₂ τ)⁻¹) : ℝ) with hxdef
  have hτ : ∀ τ, lineDeg (lat₁ τ) (P.arch τ) - lineDeg (lat₂ τ) (P.arch τ) = -x τ / Module.finrank ℚ L := by
    intro τ
    rw [lineDeg, lineDeg, hxdef]
    simp only
    rw [log_absNorm_mul_inv (h₁ τ) (h₂ τ)]
    ring
  rw [SmallBlockLattices.degree, SmallBlockLattices.degree, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun τ _ => hτ τ), ← Finset.sum_div, Finset.sum_neg_distrib, abs_div, abs_neg,
    abs_of_pos hd, div_le_iff₀ hd]
  calc |∑ τ, x τ| ≤ ∑ τ, |x τ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _τ : Ψ, Module.finrank ℚ L * K := Finset.sum_le_sum fun τ _ => hx τ
    _ = Fintype.card Ψ * K * Module.finrank ℚ L := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end GroundTheory.Heights₂.Heights.NineStatements
