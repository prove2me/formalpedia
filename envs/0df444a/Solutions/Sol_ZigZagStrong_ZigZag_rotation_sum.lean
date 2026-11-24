-- Prove2me | solution 1 for ZigZagStrong.ZigZag.rotation_sum
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T22:58:14.642371+00:00
-- url     : https://prove2.me/submissions/dc906659-3b5f-44aa-aec7-0f4c35e5f54a

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem tensorOp_apply_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    (StrongConv.tensorOp A T x).ofLp a = ∑ b, A a b • T (x.ofLp b) := by
  simp only [StrongConv.tensorOp, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  simp [Finset.sum_apply, Pi.single_apply]

end ZigZagStrong.ZigZag

open ZigZagStrong.ZigZag in
theorem solution {Γ V : Type*} [Group Γ] {d : ℕ} (S : Generators Γ d)
  (π : Γ →* Equiv.Perm V) :
  rotation S.flip (fun i => permL2 (π (S.gen i))) =
    ∑ i : Fin d, StrongConv.tensorOp (elementary i (S.flip i)) (permL2 (π (S.gen i))) := by
  ext x a : 2
  have h : ∀ (i : Fin d), (StrongConv.tensorOp (elementary i (S.flip i)) (permL2 (π (S.gen i))) x).ofLp a
      = if a = S.flip i then permL2 (π (S.gen i)) (x.ofLp i) else 0 := by
    intro i
    rw [tensorOp_apply_aux]
    rw [Finset.sum_eq_single i]
    · by_cases ha : a = S.flip i <;> simp [elementary, ha]
    · intro b _ hb; simp [elementary, hb]
    · simp
  have h2 : (∑ i : Fin d, StrongConv.tensorOp (elementary i (S.flip i)) (permL2 (π (S.gen i)))) x
      = ∑ i : Fin d, StrongConv.tensorOp (elementary i (S.flip i)) (permL2 (π (S.gen i))) x := by
    simp
  rw [h2]
  have h3 : ((∑ i : Fin d, StrongConv.tensorOp (elementary i (S.flip i)) (permL2 (π (S.gen i))) x)).ofLp a
      = ∑ i : Fin d, (StrongConv.tensorOp (elementary i (S.flip i)) (permL2 (π (S.gen i))) x).ofLp a := by
    simp
  rw [h3]
  simp only [h]
  rw [Finset.sum_eq_single (S.flip a)]
  · have hs : S.flip.symm a = S.flip a := (Equiv.symm_apply_eq _).2 (S.flip_sq a).symm
    simp [ZigZagStrong.ZigZag.rotation, hs, S.flip_sq a]
  · intro b _ hb
    rw [if_neg]
    intro h'; apply hb; rw [h', S.flip_sq b]
  · simp
