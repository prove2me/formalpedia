-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.norm_factorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:08.487527+00:00
-- url     : https://prove2.me/submissions/4dc2ae1d-8fd0-47c0-9dc9-be9fec30bea8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_factorization_clause
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_arithDegree_additive

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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) :
    (∀ c (g : Ω c), g ≠ 0 → ∃ κ : K, κ ≠ 0 ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
              (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
                (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w g))) ∧
    (∀ (G : WT) (ta ta' : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0) → d.aG h G ta = d.aG h G ta') ∧
    (∀ (G G' : WT) (ta ta' : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c G' ∧ ta' c ≠ 0) → d.aG h (G + G') (ta * ta') = d.aG h G ta + d.aG h G' ta') := by
  exact ⟨fun c g hg => d.norm_factorization_clause hd h c g hg, (d.arithDegree_additive hd h).1, (d.arithDegree_additive hd h).2⟩
end ReciprocityTheory.ChartRestriction.G.T0.Data
