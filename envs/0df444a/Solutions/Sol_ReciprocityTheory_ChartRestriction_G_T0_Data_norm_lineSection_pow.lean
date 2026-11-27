-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.norm_lineSection_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:52:38.884895+00:00
-- url     : https://prove2.me/submissions/fe047ae2-4407-4b46-a2b9-904199bee68f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineSection_pow_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineSection_pow_ne

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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) (k : ℕ) (hk : 1 ≤ k) :
    d.nrm c (k • d.wL) (d.w (d.jc c) c ^ k) P = d.nrm c d.wL (d.w (d.jc c) c) P ^ k := by
  induction k, hk using Nat.le_induction with
  | base => rw [one_smul, pow_one, pow_one]
  | succ k hk ih =>
    rw [succ_nsmul, pow_succ, pow_succ, hd.nrm_mul c P (lineSection_pow_mem d hd c k) (hd.w_mem _ _)
      (lineSection_pow_ne d hd c k) (hd.w_base c), ih]
end ReciprocityTheory.ChartRestriction.G.T0.Data
