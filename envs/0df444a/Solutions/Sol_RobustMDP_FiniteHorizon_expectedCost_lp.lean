-- Prove2me | solution 1 for RobustMDP.FiniteHorizon.expectedCost_lp
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:39:22.804285+00:00
-- url     : https://prove2.me/submissions/0094c557-af67-47ea-898e-494458ce7c16

import Definitions.Def_RobustMDP_FiniteHorizon_expectedCost
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

open RobustMDP.FiniteHorizon

private theorem cost_eq_initial {n N : ℕ} {A : Type} (M : Model n N A) (i₀ : Fin n)
    (π : ControlPolicy n N A) (P : Fin N → A → Fin n → Fin n → ℝ)
    (v : Fin (N+1) → Fin n → ℝ) (hlast : v (Fin.last N)=M.terminalCost)
    (hstep : ∀ t : Fin N, ∀ i, v t.castSucc i=M.cost t i (π t i)+∑ j, P t (π t i) i j*v t.succ j) :
    M.expectedCost i₀ π P=v 0 i₀ := by
  classical
  let Q : Fin (N+1) → ℝ := fun t => ∑ i, stateDist π P i₀ t i*v t i
  have hQ0 : Q 0=v 0 i₀ := by simp [Q,stateDist]
  have hQlast : Q (Fin.last N)=∑ i, stateDist π P i₀ N i*M.terminalCost i := by simp [Q,hlast]
  have hQs : ∀ t : Fin N, Q t.castSucc=(∑ i, stateDist π P i₀ t i*M.cost t i (π t i))+Q t.succ := by
    intro t
    dsimp [Q]
    simp only [hstep,mul_add,Finset.sum_add_distrib]
    congr 1
    simp only [Fin.val_succ,stateDist, t.isLt, dite_true,Fin.eta]
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    exact Finset.sum_comm.trans (by congr 1; ext i; congr 1; ext j; ring)
  have htel : (∑ t : Fin N, (Q t.castSucc - Q t.succ))=Q 0-Q (Fin.last N) := by
    rw [Finset.sum_sub_distrib]
    have h1 := Fin.sum_univ_succ Q
    have h2 := Fin.sum_univ_castSucc Q
    linarith
  have hsum : (∑ t : Fin N, ∑ i, stateDist π P i₀ t i*M.cost t i (π t i))=Q 0-Q (Fin.last N) := by
    rw [← htel]
    apply Finset.sum_congr rfl
    intro t _
    linarith [hQs t]
  unfold Model.expectedCost
  rw [hsum,hQ0,hQlast]
  ring

theorem solution {n N : ℕ} {A : Type} (M : Model n N A) (i₀ : Fin n)
    (π : ControlPolicy n N A) (P : Fin N → A → Fin n → Fin n → ℝ)
    (hP : ∀ t a i, P t a i ∈ stdSimplex ℝ (Fin n)) :
    IsGreatest
      {x : ℝ | ∃ v : Fin (N+1) → Fin n → ℝ,
        v (Fin.last N)=M.terminalCost ∧
        (∀ t : Fin N, ∀ i, v t.castSucc i ≤
          M.cost t i (π t i)+∑ j, P t (π t i) i j*v t.succ j) ∧
        x=v 0 i₀}
      (M.expectedCost i₀ π P) := by
  let g : Fin N → (Fin n → ℝ) → (Fin n → ℝ) := fun t w i =>
    M.cost t i (π t i)+∑ j, P t (π t i) i j*w j
  let vstar := CRobust.backward g M.terminalCost
  have hs : ∀ t : Fin N, vstar t.castSucc=g t (vstar t.succ) := CRobust.backward_step g M.terminalCost
  have hl : vstar (Fin.last N)=M.terminalCost := CRobust.backward_last g M.terminalCost
  have heq : M.expectedCost i₀ π P=vstar 0 i₀ := cost_eq_initial M i₀ π P vstar hl (fun t i => congrFun (hs t) i)
  have hg : ∀ t, Monotone (g t) := by
    intro t v w hvw i
    exact add_le_add_right (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hvw j) ((hP t (π t i) i).1 j))) _
  constructor
  · exact ⟨vstar,hl,fun t i => (congrFun (hs t) i).le,heq⟩
  · rintro x ⟨v,hlv,hsv,rfl⟩
    rw [heq]
    exact CRobust.backward_upper g hg v vstar (by rw [hlv,hl]) hsv hs 0 i₀

