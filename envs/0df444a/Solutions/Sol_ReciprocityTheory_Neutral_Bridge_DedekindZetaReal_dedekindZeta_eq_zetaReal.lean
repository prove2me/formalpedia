-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.dedekindZeta_eq_zetaReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:31:59.678887+00:00
-- url     : https://prove2.me/submissions/94442eb2-f794-4fe1-a82b-bc540a15c683

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_zetaReal_term_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable (K : Type*) [Field K] [NumberField K]
open ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
namespace ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
theorem _root_.solution {s : ℝ} (hs : 1 < s) :
    dedekindZeta K (s : ℂ) = ((zetaReal K s : ℝ) : ℂ) := by
  unfold dedekindZeta LSeries zetaReal
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n ↦ zetaReal_term_eq K (zero_lt_one.trans hs) n
end ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
