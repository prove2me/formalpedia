-- Prove2me | solution 1 for P2M_O3_Stage2RouteB_pairing_add_left__aa498a6aacda
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:56.223964+00:00
-- url     : https://prove2.me/submissions/bcf7d75b-2291-4b53-a0cd-161af4aaed59

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {d : ℕ} (a b c : Point d) :
    pairing (a + b) c = pairing a c + pairing b c := by
  simp only [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]
end O3.Stage2RouteB
