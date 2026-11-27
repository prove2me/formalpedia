-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.integral_le_of_ae_le_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:39:43.687743+00:00
-- url     : https://prove2.me/submissions/ddd1a6c1-5c8a-428c-9477-dcb67a6b63fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntNsg
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntegralLeOfAeLeAffine
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (F1 F2 F3 : X → ℝ) (C r : ℝ) (I1 : Integrable F1 μ) (I2 : Integrable F2 μ) (I3 : Integrable F3 μ)
    (hle : ∀ᵐ x ∂μ, F1 x ≤ F2 x + C + r * F3 x) :
    ∫ x, F1 x ∂μ ≤ ∫ x, F2 x ∂μ + C + r * ∫ x, F3 x ∂μ := by
  have hC : Integrable (fun _ : X => C) μ := integrable_const C
  have h2C : Integrable (fun x => F2 x + C) μ := I2.add hC
  have hI : Integrable (fun x => F2 x + C + r * F3 x) μ := h2C.add (I3.const_mul r)
  calc ∫ x, F1 x ∂μ ≤ ∫ x, (F2 x + C + r * F3 x) ∂μ := integral_mono_ae I1 hI hle
    _ = ∫ x, F2 x ∂μ + C + r * ∫ x, F3 x ∂μ := by
      rw [integral_add h2C (I3.const_mul r), integral_const_mul, integral_add I2 hC]
      simp
end ReciprocityTheory.ChartRestriction.G.T0.Data
