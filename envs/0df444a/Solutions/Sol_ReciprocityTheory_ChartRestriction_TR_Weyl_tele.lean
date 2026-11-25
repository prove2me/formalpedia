-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:48:03.061901+00:00
-- url     : https://prove2.me/submissions/4c08ccdc-c7fe-412f-a259-7a906798504c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_tele_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {K : Type*} [Field K] {t y : K} (ht : t ≠ 0) (hy : y ≠ 0) (c b e : ℤ) (h : c ≤ b + 1) :
    (t - y) * ∑ m ∈ Icc c b, t ^ (m + e) * y ^ (b - m) = t ^ (b + 1 + e) - y ^ (b - c + 1) * t ^ (c + e) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b = c - 1 + k := ⟨(b - c + 1).toNat, by omega⟩
  subst hk
  exact tele_nat ht hy c e k
end ReciprocityTheory.ChartRestriction.TR.Weyl
