-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.x4v4_gen_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:19.890784+00:00
-- url     : https://prove2.me/submissions/20ff896c-faa4-4137-8c2e-aafa1db57923

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
theorem _root_.solution {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := by
  refine (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ?_
  obtain ⟨hprime, hh⟩ := hp
  have hpr := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh
  unfold gen
  rw [dif_pos hpr]
  intro h0
  exact p.ne_bot_of_height_eq_one hh ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)
end ReciprocityTheory.ChartRestriction.G.T0.Data
