-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.v_eq_one_of_residue_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:59:45.343647+00:00
-- url     : https://prove2.me/submissions/0d67f438-987c-444f-8f28-e3447ef03431

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
theorem _root_.solution {x : v.valuationSubring}
    (hx : IsLocalRing.residue v.valuationSubring x ≠ 0) : v (x : C) = 1 := by
  have hu : IsUnit x := (IsLocalRing.residue_ne_zero_iff_isUnit x).mp hx
  obtain ⟨u, rfl⟩ := hu
  have h1 : v ((u : v.valuationSubring) : C) ≤ 1 := (u : v.valuationSubring).2
  have h2 : v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) ≤ 1 :=
    ((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring).2
  have hmul : ((u : v.valuationSubring) : C) *
      (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) = 1 := by
    have h := congrArg (fun z : v.valuationSubring => (z : C)) (Units.mul_inv u)
    exact_mod_cast h
  have hv : v ((u : v.valuationSubring) : C) *
      v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) = 1 := by
    rw [← map_mul, hmul, map_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  have : v ((u : v.valuationSubring) : C) *
      v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) ≤
      v ((u : v.valuationSubring) : C) := mul_le_of_le_one_right zero_le h2
  rw [hv] at this
  exact absurd (lt_of_le_of_lt this hlt) (lt_irrefl _)
end ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
