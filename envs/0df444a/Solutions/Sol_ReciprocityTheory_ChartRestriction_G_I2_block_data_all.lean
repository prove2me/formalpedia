-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.block_data_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:44:28.427721+00:00
-- url     : https://prove2.me/submissions/109893a2-4e8b-4755-8d7f-361816e122d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IteratedDerivListBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OneAddPowSubOneLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardChoiceLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_c_le_DF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_block_data


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}
variable [IsCMField E] (X : PT E) (bs : Fin nb → Block E n X.dim)
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (hx : Ext.All) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) (P : Par X (DF bs)) (I : Submodule ℤ (Vsp X.dim)) (hI : IsSplit P I)
    (j : Fin nb) :
    ∃ (y : Fin (bs j).i → Vsp X.dim) (s : Fin (bs j).i → (Fin 1 → Vsp X.dim) → ℂ)
      (μ : Fin (bs j).i → ℂ),
      (∀ b, s b ∈ X.Sec P.q 1) ∧
      (∀ b (xs : Fin (bs j).c → Vsp X.dim), (∀ k, InPart (bs j).τ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 (s b) (bs j).c xs - μ b * ∏ k, Hf (xs k) (y b)‖ ≤ P.eps1 * ‖μ b‖) ∧
      (∀ b, P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (s b) ≤
        ‖μ b‖ ^ 2) ∧
      (∀ b, ‖y b‖ ≤ 2) ∧
      (2 : ℝ) ^ (-(X.r : ℝ) / 2) / 2 ≤
        ‖(Matrix.of fun a b => Hf (EuclideanSpace.single
          (⟨(bs j).τ, Fin.castLE (bs j).hi a⟩ : Idx X.dim) (1 : ℂ)) (y b)).det‖ ∧
      (∀ b, μ b ≠ 0) := by
  rcases Nat.eq_zero_or_pos (bs j).i with h0 | hpos
  · haveI : IsEmpty (Fin (bs j).i) := by rw [h0]; infer_instance
    refine ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, fun b => isEmptyElim b,
      isEmptyElim, isEmptyElim, ?_, isEmptyElim⟩
    rw [Matrix.det_isEmpty, norm_one]
    have h1 : (2 : ℝ) ^ (-(X.r : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have := Nat.cast_nonneg (α := ℝ) X.r; linarith)
    linarith
  · exact block_data hx hc ht ha X P I hI (bs j).τ (bs j).i (bs j).hi (bs j).c (c_le_DF bs j hpos)
end ReciprocityTheory.ChartRestriction.G.I2
