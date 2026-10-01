-- Prove2me | solution 1 for RobustMDP.FiniteHorizon.lemma_one
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:37:00.758829+00:00
-- url     : https://prove2.me/submissions/91a5e2f4-9dda-47d8-a739-0035eee8454b

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace CRobust

noncomputable def backward {X : Type*} {N : ℕ} (g : Fin N → X → X) (vN : X) : Fin (N+1) → X :=
  Fin.reverseInduction vN (fun i v => g i v)

theorem backward_last {X : Type*} {N : ℕ} (g : Fin N → X → X) (vN : X) :
    backward g vN (Fin.last N)=vN := Fin.reverseInduction_last

theorem backward_step {X : Type*} {N : ℕ} (g : Fin N → X → X) (vN : X) (t : Fin N) :
    backward g vN t.castSucc=g t (backward g vN t.succ) := Fin.reverseInduction_castSucc t

theorem backward_unique {X : Type*} {N : ℕ} (g : Fin N → X → X) (vN : X)
    (v : Fin (N+1) → X) (hlast : v (Fin.last N)=vN)
    (hstep : ∀ t : Fin N, v t.castSucc=g t (v t.succ)) : v=backward g vN := by
  funext t
  induction t using Fin.reverseInduction with
  | last => exact hlast.trans (backward_last g vN).symm
  | cast t ih => rw [hstep,backward_step,ih]

theorem backward_upper {X : Type*} [Preorder X] {N : ℕ} (g : Fin N → X → X)
    (hg : ∀ t, Monotone (g t)) (v vstar : Fin (N+1) → X)
    (hlast : v (Fin.last N) ≤ vstar (Fin.last N))
    (hv : ∀ t : Fin N, v t.castSucc ≤ g t (v t.succ))
    (hs : ∀ t : Fin N, vstar t.castSucc=g t (vstar t.succ)) : v ≤ vstar := by
  intro t
  induction t using Fin.reverseInduction with
  | last => exact hlast
  | cast t ih => exact (hv t).trans ((hg t ih).trans_eq (hs t).symm)

theorem initial_eq_fold {X : Type*} {N : ℕ} (g : Fin N → X → X) (vN : X)
    (v : Fin (N+1) → X) (hlast : v (Fin.last N)=vN)
    (hstep : ∀ t : Fin N, v t.castSucc=g t (v t.succ)) :
    v 0=(List.ofFn g).foldr (fun f x => f x) vN := by
  induction N with
  | zero => simpa using hlast
  | succ N ih =>
    rw [List.ofFn_succ,List.foldr_cons]
    have h0 := hstep 0
    rw [Fin.castSucc_zero] at h0
    rw [h0]
    congr 1
    apply ih (fun i => g i.succ) (fun i => v i.succ)
    · simpa using hlast
    · intro t
      simpa only [Fin.castSucc_succ] using hstep t.succ
end CRobust

theorem solution {n N : ℕ} (g : Fin N → (Fin n → ℝ) → (Fin n → ℝ))
    (hg : ∀ t, Monotone (g t)) (q : Fin n → ℝ) (hq : 0 ≤ q) (vN : Fin n → ℝ) :
    (∃! vstar : Fin (N+1) → Fin n → ℝ,
        vstar (Fin.last N)=vN ∧ ∀ t : Fin N, vstar t.castSucc=g t (vstar t.succ)) ∧
    ∀ vstar : Fin (N+1) → Fin n → ℝ,
      vstar (Fin.last N)=vN → (∀ t : Fin N, vstar t.castSucc=g t (vstar t.succ)) →
        vstar 0=(List.ofFn g).foldr (fun f x => f x) vN ∧
        IsGreatest
          ((fun v : Fin (N+1) → Fin n → ℝ => ∑ i, q i*v 0 i) ''
            {v | v (Fin.last N)=vN ∧ ∀ t : Fin N, v t.castSucc ≤ g t (v t.succ)})
          (∑ i, q i*vstar 0 i) := by
  constructor
  · refine ⟨CRobust.backward g vN,⟨CRobust.backward_last g vN,CRobust.backward_step g vN⟩,?_⟩
    intro v hv
    exact CRobust.backward_unique g vN v hv.1 hv.2
  · intro vstar hl hs
    refine ⟨CRobust.initial_eq_fold g vN vstar hl hs,?_,?_⟩
    · exact ⟨vstar,⟨hl,fun t => (hs t).le⟩,rfl⟩
    · rintro z ⟨v,⟨hv,hstep⟩,rfl⟩
      have hh := CRobust.backward_upper g hg v vstar (by rw [hv,hl]) hstep hs
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hh 0 i) (hq i))

