-- Prove2me | solution 1 for ReciprocityTheory.PGsh.mem_span_p_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:47.569854+00:00
-- url     : https://prove2.me/submissions/c80d4b4b-5360-4676-8421-749ea54945a1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MulIterateRootEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open WittVector Ideal TensorProduct
namespace ReciprocityTheory.PGsh
section Witt
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
private lemma frob_bij : Function.Bijective (WittVector.frobenius : WittVector p R → WittVector p R) := by
  constructor
  · intro x y h
    ext n
    have h' := congrArg (fun z => WittVector.coeff z n) h
    simp only [WittVector.coeff_frobenius_charP] at h'
    apply (frobeniusEquiv R p).injective
    rw [_root_.frobeniusEquiv_apply, _root_.frobeniusEquiv_apply, frobenius_def, frobenius_def]
    exact h'
  · intro x
    refine ⟨WittVector.mk p (fun n => (frobeniusEquiv R p).symm (x.coeff n)), ?_⟩
    ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.coeff_mk]
    have h := (frobeniusEquiv R p).apply_symm_apply (x.coeff n)
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h
end Witt
section Tilt
variable {p : ℕ} [hp : Fact p.Prime] {O : Type*} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
end Tilt
section Main
variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
end Main
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open WittVector Ideal TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (x : WittVector p R) : x ∈ span {(p : WittVector p R)} ↔ x.coeff 0 = 0 := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← WittVector.verschiebung_frobenius, WittVector.verschiebung_coeff_zero]
  · intro hx
    obtain ⟨y, hy⟩ := (frob_bij (p := p) (R := R)).2 (WittVector.mk p (fun n => x.coeff (n + 1)))
    refine Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩
    rw [← WittVector.verschiebung_frobenius, hy]
    ext n
    cases n with
    | zero => rw [WittVector.verschiebung_coeff_zero, hx]
    | succ n => exact WittVector.verschiebung_coeff_succ _ n
end ReciprocityTheory.PGsh
