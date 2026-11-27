-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.w_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:17:17.200652+00:00
-- url     : https://prove2.me/submissions/f6932c16-be35-4398-b81b-17cf6576428b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow

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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (j : Fin (d.N + 1)) :
    d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hex : ∃ a : Ω c, d.w j c = a • d.w (d.jc c) c := by
    have h1 := hd.finrank_one c d.wL
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨d.w (d.jc c) c, hd.w_mem _ _⟩ : 𝒜 c d.wL)
      (fun h => hd.w_base c (congrArg Subtype.val h))).mp h1 ⟨d.w j c, hd.w_mem _ _⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  unfold ratio
  rw [dif_pos hex]
  exact hex.choose_spec
end ReciprocityTheory.ChartRestriction.G.T0.Data
