-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.val_algebraMap_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:29:31.422801+00:00
-- url     : https://prove2.me/submissions/22359a5a-8861-4731-b1ae-e8b046198f39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (c : ι) (p : Ideal (KTp K d.D d.N))
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p) (a : K)
    (ha : a ≠ 0) : w (algebraMap K (OmS (Ω c) d.D d.N) a) = 0 := by
  have h1 := (hw.2 (MvPolynomial.C a)).1
  have h2 := (hw.2 (MvPolynomial.C a⁻¹)).1
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes] at h1 h2
  have h3 : w (algebraMap K (OmS (Ω c) d.D d.N) a) + w (algebraMap K (OmS (Ω c) d.D d.N) a⁻¹) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, AddValuation.map_one]
  exact ((add_eq_zero_iff_of_nonneg h1 h2).mp h3).1
end ReciprocityTheory.ChartRestriction.G.T0.Data
