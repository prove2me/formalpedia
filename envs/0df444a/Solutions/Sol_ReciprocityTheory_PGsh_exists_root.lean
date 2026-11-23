-- Prove2me | solution 1 for ReciprocityTheory.PGsh.exists_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:18.744671+00:00
-- url     : https://prove2.me/submissions/38e261b7-d062-43e0-b3df-d1d68d75c741

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Ideal
namespace ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime]
section Untilt
variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
end Untilt
section Roots
variable (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C]
private lemma le_one_of_pow (hv : v.Integers O) {z : C} {w : O} (h : z ^ p = algebraMap O C w) :
    v z ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have h1 : 1 < v z ^ p := one_lt_pow₀ hlt hp.out.ne_zero
  rw [← map_pow, h] at h1
  exact absurd (hv.map_le_one w) (not_le.2 h1)
variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
end Roots
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime]
variable (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (hv : v.Integers O) (x : O) : ∃ y : O, y ^ p = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C x) hp.out.pos
  obtain ⟨y, rfl⟩ := hv.exists_of_le_one (le_one_of_pow C v O hv hz)
  exact ⟨y, hv.hom_inj (by rw [map_pow, hz])⟩
end ReciprocityTheory.PGsh
