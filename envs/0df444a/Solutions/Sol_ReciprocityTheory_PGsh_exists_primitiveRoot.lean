-- Prove2me | solution 1 for ReciprocityTheory.PGsh.exists_primitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:07.721943+00:00
-- url     : https://prove2.me/submissions/4d5dc9fd-516e-4ef3-88a1-6193f4a2f662

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Theorems.Thm_ReciprocityTheory_PGsh_exists_root
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
theorem _root_.solution [CharZero C] (hv : v.Integers O) :
    ∃ ζ : O, IsPrimitiveRoot ζ p := by
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p C)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos p C hp.out.pos))
  have hzp : IsPrimitiveRoot z p := Polynomial.isRoot_cyclotomic_iff.1 hz
  have hz1 : z ^ p = algebraMap O C 1 := by rw [hzp.pow_eq_one, map_one]
  obtain ⟨y, rfl⟩ := hv.exists_of_le_one (le_one_of_pow C v O hv hz1)
  exact ⟨y, (IsPrimitiveRoot.map_iff_of_injective hv.hom_inj).1 hzp⟩
end ReciprocityTheory.PGsh
