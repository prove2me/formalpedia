-- Prove2me | solution 1 for QEC.Distillation.BK15.l2_l1_pairing_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:00:51.23577+00:00
-- url     : https://prove2.me/submissions/851bd898-3713-4336-827c-b23ec3a48801

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ (b : Sum (Fin 4) QuadraticIndex → Bit) (a : Fin 4 → Bit),
      wordPairing (l2CoefficientMap b) (l1CoefficientMap a) = 0 := by
  intro b a
  have hrows : ∀ (g : Sum (Fin 4) QuadraticIndex) (j : Fin 4),
      wordPairing (l2Generator g) (linearGenerator j) = 0 := by decide +kernel
  have hb : l2CoefficientMap b = ∑ g, b g • l2Generator g := by
    funext i
    change (∑ g, b g * l2Generator g i) = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have ha : l1CoefficientMap a = ∑ j, a j • linearGenerator j := by
    funext i
    change (∑ j, a j * linearGenerator j i) = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hb, ha]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hrows,
    smul_zero, Finset.sum_const_zero]
end QEC.Distillation.BK15