-- Prove2me | solution 1 for RingTheory.Sequence.isWeaklyRegular_of_free_aux
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f9161605-7ee2-535e-a148-034d4cf64345

import Mathlib
import Theorems.Thm_isSMulRegular_iff_of_free
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingTheory_Sequence_isWeaklyRegular_of_free_aux

open scoped Pointwise TensorProduct

theorem solution.{u, v} {R : Type u} {M : Type max u v} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {s : List R} :
    RingTheory.Sequence.IsWeaklyRegular M s ↔ RingTheory.Sequence.IsWeaklyRegular R s := by
  generalize hn : s.length = n
  induction n generalizing R M with
  | zero => simp_all
  | succ n IH =>
    cases s with
    | nil => simp at hn
    | cons x xs =>
    let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} := Submodule.quotEquivOfEq _ _
      (by rw [← Submodule.ideal_span_singleton_smul]; simp)
    let e' := QuotSMulTop.equivQuotTensor x M
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff,
      e.isWeaklyRegular_congr, e'.isWeaklyRegular_congr,
      ← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x}),
      ← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R := R) (R ⧸ Ideal.span {x})]
    refine and_congr isSMulRegular_iff_of_free ?_
    cases subsingleton_or_nontrivial (R ⧸ Ideal.span {x})
    · haveI : Subsingleton ((R ⧸ Ideal.span {x}) ⊗[R] M) := Module.subsingleton (R ⧸ Ideal.span {x}) _
      exact iff_of_true
        ((RingTheory.Sequence.isWeaklyRegular_iff_Fin ..).mpr fun _ _ _ _ ↦ Subsingleton.elim _ _)
        ((RingTheory.Sequence.isWeaklyRegular_iff_Fin ..).mpr fun _ _ _ _ ↦ Subsingleton.elim _ _)
    exact IH (by simp_all)

end S_RingTheory_Sequence_isWeaklyRegular_of_free_aux
end P2MW
export P2MW.S_RingTheory_Sequence_isWeaklyRegular_of_free_aux (solution)
