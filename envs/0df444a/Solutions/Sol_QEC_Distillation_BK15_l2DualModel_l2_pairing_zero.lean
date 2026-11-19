-- Prove2me | solution 1 for QEC.Distillation.BK15.l2DualModel_l2_pairing_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:01:34.000824+00:00
-- url     : https://prove2.me/submissions/da5357b1-d0c9-4f44-b674-01bdab1c67f2

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ (ac : (Fin 4 → Bit) × Bit) (b : Sum (Fin 4) QuadraticIndex → Bit),
      wordPairing (l2DualCoefficientMap ac) (l2CoefficientMap b) = 0 := by
  intro ac b
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
  have hones : ∀ g : Sum (Fin 4) QuadraticIndex, wordPairing allOnes (l2Generator g) = 0 := by decide +kernel
  have hb : l2CoefficientMap b = ∑ g, b g • l2Generator g := by
    funext i
    change (∑ g, b g * l2Generator g i) = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hz : wordPairing allOnes (l2CoefficientMap b) = 0 := by
    rw [hb]
    simp only [map_sum, map_smul, hones, smul_zero, Finset.sum_const_zero]
  have hswap : wordPairing (l1CoefficientMap ac.1) (l2CoefficientMap b) = 0 := by
    rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply]
    exact hpair b ac.1
  change wordPairing (l1CoefficientMap ac.1 + ac.2 • allOnes) (l2CoefficientMap b) = 0
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hswap,
    hz, smul_zero, add_zero]
end QEC.Distillation.BK15