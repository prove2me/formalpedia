-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.HgtMM_eq_AH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:07.221168+00:00
-- url     : https://prove2.me/submissions/5a282291-9676-4e59-9b46-3248acf29b21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (h : d.S1) (f : ∀ c, A c) :
    d.HgtMM h f = d.AH h (fun c v g => d.ordMM c v g) (fun c g P => d.nrm c d.wL g P / d.be c P) f :=
  rfl
end ReciprocityTheory.ChartRestriction.G.T0.Data
