-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sigP_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:27:25.801091+00:00
-- url     : https://prove2.me/submissions/f0bbfa6c-5641-4793-8516-61406d57b49f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sigF_algebraMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_algebraMap_K_KTf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sigF_fZ

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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) (b : Fin (d.D + 1)) (u : Kˣ) :
    sigP b u F = C ((u : K) ^ (if b = 0 then (d.delc c : ℤ) else d.aMM h c)) * F := by
  apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  rw [← sigF_algebraMap d b u F, hF, sigF_fZ d hd h c b u, map_mul, ← hF, algebraMap_K_KTf d]
end ReciprocityTheory.ChartRestriction.G.T0.Data
