-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_qExpansion_E__eq_23abd34fd0e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:13.228244+00:00
-- url     : https://prove2.me/submissions/6db58f92-31f4-4db5-9744-7a2b90a7e8d4

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open ModularForm EisensteinSeries ArithmeticFunction PowerSeries UpperHalfPlane
open scoped ArithmeticFunction.sigma
namespace ReciprocityTheory.PGsh
theorem _root_.solution : qExpansion 1 E₄ = PowerSeries.map (Int.castRingHom ℂ) e4Z := by
  ext n
  rw [coeff_map, e4Z, coeff_mk]
  by_cases hn : n = 0
  · subst hn; norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩]
  · norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, hn, show bernoulli 4 = -1 / 30 by decide +kernel]
end ReciprocityTheory.PGsh
