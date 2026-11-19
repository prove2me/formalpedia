-- Prove2me | solution 1 for QEC.Distillation.BK15.l1DualModel_l1_pairing_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:01:30.398408+00:00
-- url     : https://prove2.me/submissions/36ed4052-bacf-4958-8105-b21ef91eecc1

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ (bc : (Sum (Fin 4) QuadraticIndex → Bit) × Bit) (a : Fin 4 → Bit),
      wordPairing (l1DualCoefficientMap bc) (l1CoefficientMap a) = 0 := by
  intro bc a
  have hpair : ∀ (b : Sum (Fin 4) QuadraticIndex → Bit) (a : Fin 4 → Bit),
      wordPairing (l2CoefficientMap b) (l1CoefficientMap a) = 0 := by
    have hrows : ∀ (g : Sum (Fin 4) QuadraticIndex) (j : Fin 4),
        wordPairing (l2Generator g) (linearGenerator j) = 0 := by decide +kernel
    intro b a
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
  have hones : ∀ a : Fin 4 → Bit, wordPairing allOnes (l1CoefficientMap a) = 0 := by decide +kernel
  change wordPairing (l2CoefficientMap bc.1 + bc.2 • allOnes) (l1CoefficientMap a) = 0
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hpair,
    hones, smul_zero, add_zero]
end QEC.Distillation.BK15