-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.PT.card_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:53:02.923646+00:00
-- url     : https://prove2.me/submissions/ba6604f8-ea77-4247-9a95-cbe36f3aa891

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.PT
variable (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2.PT
theorem _root_.solution [IsCMField E] : Fintype.card (Idx X.dim) = X.gA := by
  have hinv : Function.Involutive
      (NumberField.ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    fun φ => RingHom.ext fun x => by simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hsum : ∑ τ, X.dim (NumberField.ComplexEmbedding.conjugate τ) = ∑ τ, X.dim τ :=
    Equiv.sum_comp (Function.Involutive.toPerm _ hinv) X.dim
  have h2 : 2 * ∑ τ, X.dim τ = Fintype.card (E →+* ℂ) * X.r := by
    rw [two_mul]
    nth_rewrite 2 [← hsum]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun τ _ => X.dim_conj τ), Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  haveI : NumberField.IsTotallyComplex E := NumberField.IsCMField.to_isTotallyComplex
  rw [NumberField.Embeddings.card, NumberField.IsTotallyComplex.finrank] at h2
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  unfold PT.gA PT.f
  rw [NumberField.IsTotallyComplex.finrank, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  linarith
end ReciprocityTheory.ChartRestriction.G.I2.PT
