-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.upB_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:21:19.703979+00:00
-- url     : https://prove2.me/submissions/cf05c8fb-adb7-4723-b6fa-fafe151cc943

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SumLogHeightUpperBound

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
theorem _root_.solution (hd : d.AxH 𝒜) : 0 ≤ d.upB := by
  have h1 := hd.P_ge.2.2.2.1
  have h2 := hd.size_L
  have h3 : 0 ≤ Real.log (d.N + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos _)
  have h4 : 0 ≤ max 0 d.laW := le_max_left _ _
  unfold upB
  nlinarith
end ReciprocityTheory.ChartRestriction.G.T0.Data
