-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_qExpansion_E__eq_3ba1083836b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:17.970357+00:00
-- url     : https://prove2.me/submissions/4cf97d24-1c40-4bab-bbdc-4a725cb8eaed

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
theorem _root_.solution : qExpansion 1 E₆ = PowerSeries.map (Int.castRingHom ℂ) e6Z := by
  ext n
  rw [coeff_map, e6Z, coeff_mk]
  by_cases hn : n = 0
  · subst hn; norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩]
  · norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, hn, show bernoulli 6 = 1 / 42 by decide +kernel]
end ReciprocityTheory.PGsh
