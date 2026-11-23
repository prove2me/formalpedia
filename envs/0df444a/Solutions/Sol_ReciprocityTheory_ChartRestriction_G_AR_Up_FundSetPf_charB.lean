-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.charB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:35.66751+00:00
-- url     : https://prove2.me/submissions/2d9dbedb-65f6-4969-84cf-1a5f32282349

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) {y y' : Frame Ψ r}
    (hy : ∀ τ, (mat y τ).det ≠ 0) (hy' : ∀ τ, (mat y' τ).det ≠ 0) :
    (∃ b ∈ Bor Ψ r, lact δ y = rmul y' b) ↔ ∀ τ : Ψ, ∀ a c : Fin r, c < a →
      ((mat y' τ).adjugate * (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ) a c = 0 := by
  constructor
  · rintro ⟨b, hb, h⟩ τ a c hca
    have h1 : (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y' τ * mat b τ := congrFun h τ
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul]
    rw [show mat b τ a c = b τ a c from rfl, (hb τ).2 a c hca, mul_zero]
  · intro h
    refine ⟨fun τ => (mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ), fun τ => ⟨?_, ?_⟩, ?_⟩
    · have hd : ((δ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
        rw [show ((δ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (δ : Matrix (Fin r) (Fin r) E).det from
          (RingHom.map_det τ.1 _).symm]
        exact (map_ne_zero τ.1).mpr (Matrix.isUnits_det_units δ).ne_zero
      show ((mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (inv_ne_zero (hy' τ)) (mul_ne_zero hd (hy τ))
    · intro a c hca
      show ((mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)) a c = 0
      rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, ← Matrix.mul_assoc, h τ a c hca, smul_zero]
    · funext τ
      show ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) =
        mat y' τ * ((mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ))
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hy' τ))]
end ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
