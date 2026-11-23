-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.w_eq_scalarRatio_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:51.481108+00:00
-- url     : https://prove2.me/submissions/715a082d-b6da-42ee-8c62-313f76f8460e

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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (j : Fin (d.N + 1)) :
    d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hmem := hd.w_mem
  have hne : (⟨d.w (d.jc c) c, hmem _ c⟩ : 𝒜 c d.wL) ≠ 0 := fun h => hd.w_base c (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp (hd.finrank_one c d.wL) ⟨d.w j c, hmem j c⟩
  have hex : ∃ a : Ω c, d.w j c = a • d.w (d.jc c) c := by
    refine ⟨a, ?_⟩
    have h2 := congrArg Subtype.val ha
    simpa using h2.symm
  unfold ratio
  rw [dif_pos hex]
  exact hex.choose_spec
end ReciprocityTheory.ChartRestriction.G.T0.Data
