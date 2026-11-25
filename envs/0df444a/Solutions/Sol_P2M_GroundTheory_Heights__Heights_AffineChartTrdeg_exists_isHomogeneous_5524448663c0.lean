-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_exists_isHomogeneous_5524448663c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:10:34.738809+00:00
-- url     : https://prove2.me/submissions/2979a7bb-2f3d-485d-95f4-578fcd96a920

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AffineChartTrdeg
variable {F : Type} [Field F] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.AffineChartTrdeg
theorem _root_.solution (j : Fin n) (hj : genPt P j ≠ 0)
    {a : FractionRing (MvPolynomial (Fin n) F ⧸ P)}
    (ha : a ∈ Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)) :
    ∃ D : ℕ, ∀ D' ≥ D, ∃ h : MvPolynomial (Fin n) F,
      h.IsHomogeneous D' ∧ aeval (genPt P) h = a * genPt P j ^ D' := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    refine ⟨1, fun D' hD' => ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e, D' = 1 + e := ⟨D' - 1, by omega⟩
    refine ⟨X m * X j ^ e, (isHomogeneous_X F m).mul (isHomogeneous_X_pow j e), ?_⟩
    simp only [map_mul, map_pow, aeval_X]
    rw [pow_add, pow_one]
    field_simp
  | algebraMap r =>
    exact ⟨0, fun D' _ => ⟨C r * X j ^ D', isHomogeneous_C_mul_X_pow r j D', by simp⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    refine ⟨max D₁ D₂, fun D' hD' => ?_⟩
    obtain ⟨f, hf, ef⟩ := h₁ D' (le_of_max_le_left hD')
    obtain ⟨g, hg, eg⟩ := h₂ D' (le_of_max_le_right hD')
    exact ⟨f + g, hf.add hg, by rw [map_add, ef, eg, add_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    refine ⟨D₁ + D₂, fun D' hD' => ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e, D' = D₁ + e := ⟨D' - D₁, by omega⟩
    obtain ⟨f, hf, ef⟩ := h₁ D₁ le_rfl
    obtain ⟨g, hg, eg⟩ := h₂ e (by omega)
    exact ⟨f * g, hf.mul hg, by rw [map_mul, ef, eg, pow_add]; ring⟩
end GroundTheory.Heights₂.Heights.AffineChartTrdeg
