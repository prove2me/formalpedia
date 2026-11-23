-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.conv_mem_dualLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:59.301016+00:00
-- url     : https://prove2.me/submissions/44682810-91be-4cdd-9bcc-32b86666baf2

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
private theorem mem_dualLat_iff_sum_mul_integral {X : Type} [Fintype X] (M : Submodule R (X → C)) (u : X → C) :
    u ∈ dualLat M ↔ ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a := Iff.rfl
private theorem mem_pairInt_iff {X : Type} [Fintype X] (U F : X → C) :
    F ∈ pairInt (R := R) U ↔ ∃ r : R, algebraMap R C r = ∑ x, U x * F x :=
  Iff.rfl
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (AA : HopfOrder (C := C) R N) {u w : N → C}
    (hu : u ∈ dualLat AA.carrier) (hw : w ∈ dualLat AA.carrier) :
    conv u w ∈ dualLat AA.carrier := by
  have key : tensorSpan R AA.carrier ≤
      pairInt (R := R) (fun p : N × N => u p.1 * w p.2) := by
    rw [tensorSpan, Submodule.span_le]
    rintro F ⟨g, hg, k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_pairInt_iff]
    obtain ⟨r, hr⟩ := (mem_dualLat_iff_sum_mul_integral _ _).1 hu g hg
    obtain ⟨s, hs⟩ := (mem_dualLat_iff_sum_mul_integral _ _).1 hw k hk
    refine ⟨r * s, ?_⟩
    rw [map_mul, hr, hs, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [mem_dualLat_iff_sum_mul_integral]
  intro f hf
  obtain ⟨r, hr⟩ := (mem_pairInt_iff _ _).1 (key (AA.comul f hf))
  refine ⟨r, hr.trans ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [addPull, LinearMap.funLeft_apply, conv, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Fintype.sum_equiv (Equiv.addLeft a) _ _ fun b => ?_
  simp
end ReciprocityTheory.PGsh.L2
