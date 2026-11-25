-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.KT_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:07.702931+00:00
-- url     : https://prove2.me/submissions/3cf5ae9e-f91c-497e-a6e5-05bd1e95fb58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_fieldOfS


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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) :
    FiniteDimensional (d.KT c) (OmS (Ω c) d.D d.N) := by
  have hfs := ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) (hd.fg c) (hd.trdeg c) (hd.a1 c)
  let e : TVar d.D d.N ≃ TVar d.D d.N :=
    Equiv.prodCongr (Equiv.refl _) (Fin.cycleRange (d.jc c)).symm
  have key : (ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) = (sImg (D := d.D) (d.jc c) (d.x c)) ∘ e := by
    funext p
    obtain ⟨i, j⟩ := p
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]
  have hrange : Set.range (ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) =
      Set.range (sImg (D := d.D) (d.jc c) (d.x c)) := by
    rw [key, EquivLike.range_comp]
  have h2 := hfs.2
  rw [hrange] at h2
  exact h2
end ReciprocityTheory.ChartRestriction.G.T0.Data
