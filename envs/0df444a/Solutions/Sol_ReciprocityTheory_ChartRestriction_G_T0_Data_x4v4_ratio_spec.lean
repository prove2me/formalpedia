-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.x4v4_ratio_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:05.022091+00:00
-- url     : https://prove2.me/submissions/379d7bf3-05a8-425e-9a5e-75183ef9f8e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_X4v4RatioSpec

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
theorem _root_.solution {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V}
    (hg : g ≠ 0) {a : Ω'} (hf : f = a • g) : ratio (Ω := Ω') f g = a := by
  have hex : ∃ b : Ω', f = b • g := ⟨a, hf⟩
  unfold ratio
  rw [dif_pos hex]
  have h2 : hex.choose • g = a • g := hex.choose_spec.symm.trans hf
  exact smul_left_injective Ω' hg h2
end ReciprocityTheory.ChartRestriction.G.T0.Data
