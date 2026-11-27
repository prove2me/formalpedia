-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.exists_int_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:31:51.937318+00:00
-- url     : https://prove2.me/submissions/385e17f4-cab5-417e-b6b1-332a9bb6d6f6

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactBisAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open NumberField
namespace ReciprocityTheory.MultiplicativeHeights.DegAdd
theorem _root_.solution {K : Type} [Field K] [NumberField K] (a : K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ α : 𝓞 K, (α : K) = d * a := by
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ (L := K) {a}
  exact ⟨d, hd, ⟨d • a, h a (Finset.mem_singleton_self a)⟩, zsmul_eq_mul a d⟩
end ReciprocityTheory.MultiplicativeHeights.DegAdd
