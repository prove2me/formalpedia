-- Prove2me | solution 1 for Sqrt6KissingBound.kissingConfiguration_root_le_sqrt6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:35:45.314053+00:00
-- url     : https://prove2.me/submissions/f0a1d58e-3ec2-4214-886b-42649a9111a7

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_kissingConfiguration_card_le_sqrt6_pow


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hX : IsKissingConfiguration X) :
    (X.card : ℝ) ^ ((n : ℝ)⁻¹) ≤ Real.sqrt 6 := by
  have hbound := kissingConfiguration_card_le_sqrt6_pow hn X hX
  have hn0 : n ≠ 0 := by omega
  have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ (X.card : ℝ))
    hbound (by positivity : 0 ≤ (n : ℝ)⁻¹)
  rwa [Real.pow_rpow_inv_natCast (Real.sqrt_nonneg _) hn0] at hroot
end Sqrt6KissingBound
