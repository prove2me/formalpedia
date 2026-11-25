-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OFC.S1_mem_OmF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:17.019244+00:00
-- url     : https://prove2.me/submissions/6e526ec4-9584-4ccf-986a-b11658500558

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OmFConnPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OFC_scaledZt_linear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OFC
open NumberField Complex Matrix Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OFC
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : S1 X t z ∈ OmF X x0 := by
  rw [ExF.mem_OmF_iff X x0 ho] at hz ⊢
  intro τ
  have hA := hz τ
  have heq : ExF.Am X (S1 X t z) τ =
      ((1 - t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) + ((t ^ 2 : ℝ) : ℂ) • ExF.Am X z τ := by
    simp only [ExF.Am, scaledZt_linear, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.star_def, Complex.conj_ofReal]
    have e1 : ((1 - t ^ 2 : ℝ) : ℂ) = 1 - (t : ℂ) * t := by
      push_cast
      ring
    have e2 : ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) * t := by
      push_cast
      ring
    rw [e1, e2, sub_smul, one_smul, smul_sub]
    abel
  rw [heq]
  rcases ht0.lt_or_eq with htpos | rfl
  · have h2 : (0 : ℂ) < ((t ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast pow_pos htpos 2
    have h1 : (0 : ℂ) ≤ ((1 - t ^ 2 : ℝ) : ℂ) := by
      have : t ^ 2 ≤ 1 := by nlinarith
      exact_mod_cast sub_nonneg.2 this
    exact (hA.smul h2).posSemidef_add ((Matrix.PosSemidef.one).smul h1)
  · simpa using Matrix.PosDef.one
end ReciprocityTheory.ChartRestriction.G.AR.Up.OFC
