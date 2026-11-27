-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.ordMinMax_eq_ratio_untop_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:24:23.000297+00:00
-- url     : https://prove2.me/submissions/00d1c381-10f1-4c01-ae01-36b3179848d1

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ratio_base_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ord_eq_valuation_ratio_base_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ratio_ne_zero_of_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ord_eq_valuation_ratio_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_coe_untopD_of_ne_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hint : ∀ j, 0 ≤ v (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c v f = (v (ratio (Ω := Ω c) f (d.w (d.jc c) c))).untopD 0 -
      (v (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))).untopD 0 := by
  have key : ∀ {g : A c}, g ∈ 𝒜 c d.wL → g ≠ 0 → d.ord c v d.wL g =
      (v (ratio (Ω := Ω c) g (d.w (d.jc c) c))).untopD 0 + d.ord c v d.wL (d.w (d.jc c) c) := by
    intro g hg hg0
    have h := d.ord_eq_valuation_ratio_base_add hd c v hv hg hg0
    have hne : v (ratio (Ω := Ω c) g (d.w (d.jc c) c)) ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff]
      exact d.ratio_base_ne_zero hd c hg hg0
    rw [← coe_untopD_of_ne_top hne, ← WithTop.coe_add] at h
    exact WithTop.coe_inj.1 h
  have hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) = d.ord c v d.wL (d.w j0 c) := by
    apply le_antisymm
    · exact ciInf_le (Set.finite_range _).bddBelow (⟨j0, hj0⟩ : {j // d.w j c ≠ 0})
    · haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨j0, hj0⟩⟩
      refine le_ciInf fun j => ?_
      have h := d.ord_eq_valuation_ratio_add hd c v hv (hd.w_mem j.1 c) (hd.w_mem j0 c) hj0 j.2
      have hnn := hint j.1
      have hne : v (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c)) ≠ ⊤ := by
        rw [Ne, AddValuation.top_iff]
        exact d.ratio_ne_zero_of_ne_zero hd c (hd.w_mem j.1 c) (hd.w_mem j0 c) hj0 j.2
      rw [← coe_untopD_of_ne_top hne, ← WithTop.coe_add] at h
      have h' := WithTop.coe_inj.1 h
      rw [← coe_untopD_of_ne_top hne] at hnn
      have h0 : 0 ≤ (v (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c))).untopD 0 := by exact_mod_cast hnn
      omega
  unfold ordMM
  rw [hinf, key hf hf0, key (hd.w_mem j0 c) hj0]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.Data
