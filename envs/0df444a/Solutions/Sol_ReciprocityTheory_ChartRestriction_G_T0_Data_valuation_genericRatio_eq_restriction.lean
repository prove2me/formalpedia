-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.valuation_genericRatio_eq_restriction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:50:06.311914+00:00
-- url     : https://prove2.me/submissions/470df207-c01a-4e94-9788-91838f36a638

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntNsg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrdEqValuationRatioBaseAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpecialFibreFactorization
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationGenericRatioEqRestriction
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_SpecialFibreFactorization
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_x4v4_eq_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_x4v4_ratio_spec
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
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hunit : w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0) :
    w (d.rationalBaseRow c) = d.Wres c w (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) := by
  have hg : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have e0 : d.w j0 c = ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
    d.x4v4_eq_smul hd c (hd.w_mem j0 c)
  have hr00 : ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) ≠ 0 := by
    intro h0
    apply hj0
    rw [e0, h0, zero_smul]
  have key : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) =
      ratio (Ω := Ω c) (d.w j c) (d.w j0 c) * ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
    intro j
    have ej : d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
      d.x4v4_eq_smul hd c (hd.w_mem j c)
    have hrj : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
        ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
      apply x4v4_ratio_spec hj0
      calc d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c := ej
        _ = (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) *
              ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) • d.w (d.jc c) c := by
            rw [div_mul_cancel₀ _ hr00]
        _ = (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) •
              (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) • d.w (d.jc c) c) := by
            rw [smul_smul]
        _ = _ := by rw [← e0]
    rw [hrj, div_mul_cancel₀ _ hr00]
  have hsum : d.rationalBaseRow c = (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) := by
    unfold Data.rationalBaseRow
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [key j, map_mul, mul_assoc]
  rw [hsum, AddValuation.map_mul, hunit, zero_add]
  first
    | rfl
    | simp [Data.Wres, AddValuation.comap_apply]
end ReciprocityTheory.ChartRestriction.G.T0.Data
