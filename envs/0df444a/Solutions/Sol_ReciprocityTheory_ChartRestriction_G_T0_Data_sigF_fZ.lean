-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sigF_fZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:08:04.263556+00:00
-- url     : https://prove2.me/submissions/74af4bb6-f810-47a7-97a2-0c733e8c08c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sigF_norm_w0rat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sigF_cMM
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) :
    sigF b u (d.fZ h c) = algebraMap K (KTf K d.D d.N)
      ((u : K) ^ (if b = 0 then (d.delc c : ℤ) else d.aMM h c)) * d.fZ h c := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  show sigF b u (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * d.cMM h c) = _
  rw [map_mul, sigF_norm_w0rat d hd h c b u, sigF_cMM d hd h c b u]
  show _ = _ * (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * d.cMM h c)
  split_ifs with hb
  · simp only [zpow_zero, map_one, mul_one, zpow_natCast]
    ring
  · simp only [one_pow, map_one, one_mul]
    ring
end ReciprocityTheory.ChartRestriction.G.T0.Data
