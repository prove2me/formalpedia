-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_norm_sq_heights_eq_sine_sq_example_1e100f7a2fe3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:19:06.550998+00:00
-- url     : https://prove2.me/submissions/34adefcc-57cd-41a6-8b3a-8b5b18445138

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exXi_h_bce7dc8fca97
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_lagrange_identity_complex_two_51ae89be2e4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_hermG_one_469a158ecd3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_hermG_one_re_c3c1dc8ca6a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_eval_exg_fbc9ade089ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_eval_exh_fa7de0d52714

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (z : (Σ k, ExW k) → ℂ) (hblk : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ‖eval z (map (Int.castRingHom ℂ) exg)‖ ^ 2 * exXi.h (fun p => z (T.yyEmb 0 p)) *
        exXi.h (fun p => z (T.yyEmb 1 p)) =
      ‖eval z (map (Int.castRingHom ℂ) exh)‖ ^ 2 *
        sinSqG (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) (fun k : Unit ⊕ Unit => z ⟨.line0, k⟩)
          (fun k : Unit ⊕ Unit => z ⟨.line1, k⟩) := by
  have hd : z ⟨.det, ()⟩ ≠ 0 := by
    obtain ⟨i, hi⟩ := hblk .det
    exact hi
  have hU : 0 < ‖z ⟨.line0, Sum.inl ()⟩‖ ^ 2 + ‖z ⟨.line0, Sum.inr ()⟩‖ ^ 2 := by
    obtain ⟨i, hi⟩ := hblk .line0
    rcases i with ⟨⟩ | ⟨⟩
    · have := pow_pos (norm_pos_iff.2 hi) 2
      positivity
    · have := pow_pos (norm_pos_iff.2 hi) 2
      positivity
  have hW : 0 < ‖z ⟨.line1, Sum.inl ()⟩‖ ^ 2 + ‖z ⟨.line1, Sum.inr ()⟩‖ ^ 2 := by
    obtain ⟨i, hi⟩ := hblk .line1
    rcases i with ⟨⟩ | ⟨⟩
    · have := pow_pos (norm_pos_iff.2 hi) 2
      positivity
    · have := pow_pos (norm_pos_iff.2 hi) 2
      positivity
  have hdn : 0 < ‖z ⟨.det, ()⟩‖ := norm_pos_iff.2 hd
  have hL := lagrange_identity_complex_two (z ⟨.line0, Sum.inl ()⟩) (z ⟨.line0, Sum.inr ()⟩) (z ⟨.line1, Sum.inl ()⟩)
    (z ⟨.line1, Sum.inr ()⟩)
  have key : ‖z ⟨.line0, Sum.inl ()⟩ * z ⟨.line1, Sum.inr ()⟩ - z ⟨.line0, Sum.inr ()⟩ * z ⟨.line1, Sum.inl ()⟩‖ ^ 2 =
      (‖z ⟨.line0, Sum.inl ()⟩‖ ^ 2 + ‖z ⟨.line0, Sum.inr ()⟩‖ ^ 2) *
        (‖z ⟨.line1, Sum.inl ()⟩‖ ^ 2 + ‖z ⟨.line1, Sum.inr ()⟩‖ ^ 2) -
      ‖star (z ⟨.line0, Sum.inl ()⟩) * z ⟨.line1, Sum.inl ()⟩ +
        star (z ⟨.line0, Sum.inr ()⟩) * z ⟨.line1, Sum.inr ()⟩‖ ^ 2 := by
    linarith
  rw [eval_exg, eval_exh, exXi_h, exXi_h, sinSqG, hermG_one, hermG_one_re, hermG_one_re]
  simp only [T.yyEmb, if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false]
  rw [norm_mul, mul_pow, key, norm_pow]
  field_simp
end GroundTheory.Heights₂.Heights.Inter
