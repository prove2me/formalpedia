-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.height_one_prime_eq_span_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:55.207177+00:00
-- url     : https://prove2.me/submissions/5d6ab1fe-dab7-4026-9b05-040a796a1b67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_heightOne_principal


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
theorem _root_.solution (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne) :
    p = Ideal.span {d.gen p} := by
  haveI := hp.1
  have hpr : p.IsPrincipal := by
    obtain ⟨g, _, hg⟩ := ValUFD.heightOne_principal p hp.2
    exact ⟨⟨g, hg⟩⟩
  unfold Data.gen
  rw [dif_pos hpr]
  exact (Ideal.span_singleton_generator p).symm
end ReciprocityTheory.ChartRestriction.G.T0.Data
