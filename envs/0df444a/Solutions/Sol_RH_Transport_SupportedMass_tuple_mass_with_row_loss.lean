-- Prove2me | solution 1 for RH.Transport.SupportedMass.tuple_mass_with_row_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:30.616107+00:00
-- url     : https://prove2.me/submissions/e377a8c8-d21f-4c4d-86e0-42968ade4517

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
import Theorems.Thm_RH_Transport_SupportedMass_tuple_mass_decay
import Theorems.Thm_RH_Transport_SupportedMass_support_decay_absorbs_row_loss

set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (q w : ∀ i, α i → ℝ) (a C ell : ι → ℝ) {p Z : ℝ}
    (hp : p < 1 / 30) (hZ : 1 ≤ Z)
    (ha : ∀ i, 0 < a i) (hC : ∀ i, 0 ≤ C i)
    (hell : ∀ i, 0 ≤ ell i)
    (hq : ∀ i j, 0 ≤ q i j) (hw : ∀ i j, 0 ≤ w i j)
    (hsupport : ∀ i j, w i j ≠ 0 → a i * Z ^ ell i ≤ q i j)
    (hmass : ∀ i, (∑ j, w i j * q i j ^ (-(3 / 2 : ℝ))) ≤ C i) :
    (∑ t : ∀ i, α i, ∏ i, w i (t i) * q i (t i) ^ (-2 : ℝ)) *
        Z ^ (max 0 (5 * Geometry.ell p - 1 + (∑ i, ell i)) / 8) ≤
      ∏ i, C i * a i ^ (-(1 / 2 : ℝ)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  exact support_decay_absorbs_row_loss hp
    (Finset.sum_nonneg (fun i _ => hell i)) hZ
    (Finset.prod_nonneg (fun i _ =>
      mul_nonneg (hC i) (Real.rpow_nonneg (ha i).le _)))
    (tuple_mass_decay q w a C ell hZ0 ha hq hw hsupport hmass)
end RH.Transport.SupportedMass
