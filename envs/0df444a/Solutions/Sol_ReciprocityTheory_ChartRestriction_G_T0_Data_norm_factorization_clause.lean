-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.norm_factorization_clause
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:35:33.357023+00:00
-- url     : https://prove2.me/submissions/bd12f58d-6c27-4bda-b454-f3353f17a19b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_finsum_liesOver_eq_finsum_good
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_by_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (g : Ω c) (hg : g ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
              (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
                (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w g)) := by
  obtain ⟨-, hy⟩ := d.norm_by_places hd h c
  have hne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) g ≠ 0 := by
    intro h0
    exact hg ((map_eq_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mp h0)
  obtain ⟨-, κ, hκ, hN⟩ := hy _ hne
  refine ⟨κ, hκ, ?_⟩
  rw [hN]
  congr 1
  refine finprod_congr fun p => finprod_congr fun _ => ?_
  congr 1
  exact d.finsum_liesOver_eq_finsum_good c p g hg (fun w t => (d.fze h c w : ℤ) * WithTop.untopD 0 t)
    (fun w => by simp)
end ReciprocityTheory.ChartRestriction.G.T0.Data
