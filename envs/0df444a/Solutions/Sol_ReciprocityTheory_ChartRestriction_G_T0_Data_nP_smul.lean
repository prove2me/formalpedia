-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.nP_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:47:55.89126+00:00
-- url     : https://prove2.me/submissions/230b3e6b-4751-4a62-8306-2371e63ae51c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_adm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_goodP_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_untopD_eq

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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {G : WT} {f : A c} (hf : f ∈ 𝒜 c G)
    (hf0 : f ≠ 0) {a : Ω c} (ha : a ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    d.nP h c G (a • f) p = d.nP h c G f p +
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a) := by
  unfold nP
  rw [← finsum_mem_add_distrib (d.goodP_finite hd h c hp)]
  refine finsum_mem_congr rfl fun w hw => ?_
  have key := hd.ord_smul c _ (d.good_adm hd h c hp hw) (G := G) (f := f) a hf hf0 ha
  have hva : (d.Wres c w) a ≠ ⊤ := by
    intro htop
    exact ha ((AddValuation.top_iff _).mp htop)
  rw [← untopD_eq hva, ← WithTop.coe_add] at key
  rw [WithTop.coe_inj.mp key]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.Data
