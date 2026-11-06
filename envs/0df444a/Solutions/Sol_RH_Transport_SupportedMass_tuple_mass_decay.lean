-- Prove2me | solution 1 for RH.Transport.SupportedMass.tuple_mass_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:27.084437+00:00
-- url     : https://prove2.me/submissions/9e235fe1-c97b-4a0e-be2e-bc9d46c9d631

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
import Theorems.Thm_RH_Transport_SupportedMass_weighted_mass_decay
import Theorems.Thm_RH_Transport_SupportedMass_product_decay

set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (q w : ∀ i, α i → ℝ) (a C ell : ι → ℝ) {Z : ℝ}
    (hZ : 0 < Z) (ha : ∀ i, 0 < a i)
    (hq : ∀ i j, 0 ≤ q i j) (hw : ∀ i j, 0 ≤ w i j)
    (hsupport : ∀ i j, w i j ≠ 0 → a i * Z ^ ell i ≤ q i j)
    (hmass : ∀ i, (∑ j, w i j * q i j ^ (-(3 / 2 : ℝ))) ≤ C i) :
    (∑ t : ∀ i, α i, ∏ i, w i (t i) * q i (t i) ^ (-2 : ℝ)) ≤
      (∏ i, C i * a i ^ (-(1 / 2 : ℝ))) *
        Z ^ (-(∑ i, ell i) / 2) := by
  rw [← Fintype.prod_sum
    (fun (i : ι) (j : α i) => w i j * q i j ^ (-2 : ℝ))]
  apply product_decay Finset.univ _ _ ell hZ
  · intro i hi
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hw i j) (Real.rpow_nonneg (hq i j) _))
  · intro i hi
    exact weighted_mass_decay Finset.univ (q i) (w i) (ha i) hZ
      (fun j _ => hw i j) (fun j _ => hsupport i j) (hmass i)
end RH.Transport.SupportedMass
