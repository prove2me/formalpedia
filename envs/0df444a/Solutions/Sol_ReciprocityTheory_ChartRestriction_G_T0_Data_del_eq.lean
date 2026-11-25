-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.del_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:37:04.559826+00:00
-- url     : https://prove2.me/submissions/3d9d3fef-8f9b-4acf-b504-ac2ab1cfeb20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_omS_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
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
    letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
    d.del = ∑ c, Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
  Finset.sum_congr rfl fun c _ => (d.omS_finite hd h c).2.symm
end ReciprocityTheory.ChartRestriction.G.T0.Data
