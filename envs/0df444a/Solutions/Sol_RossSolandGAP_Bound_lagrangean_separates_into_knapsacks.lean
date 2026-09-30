-- Prove2me | solution 1 for RossSolandGAP.Bound.lagrangean_separates_into_knapsacks
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:59:22.705314+00:00
-- url     : https://prove2.me/submissions/c2fdb09d-6a98-4dcb-98d1-d43fa9eab540

import Definitions.Def_RossSolandGAP_Bound_Model
import Mathlib.Tactic
set_option autoImplicit false
open Finset RossSolandGAP.Bound

private theorem lag_identity {m n : ℕ} (c : Fin m → Fin n → ℝ) (lam : Fin n → ℝ)
    (x : Fin m → Fin n → ℝ) : lagObj c lam x = ∑ j, lam j-∑ i, knapObj c lam i (x i) := by
  have hs : (∑ j, lam j*∑ i, x i j) = ∑ i, ∑ j, lam j*x i j := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [lagObj,cost,knapObj,sub_mul,mul_sub,mul_one,Finset.sum_sub_distrib]
  rw [hs]
  ring

theorem solution {m n : ℕ} (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (lam : Fin n → ℝ) :
    (∀ x, lagObj c lam x = ∑ j, lam j - ∑ i, knapObj c lam i (x i)) ∧
    ∀ x, FeasibleLag r b x →
      ((∀ x', FeasibleLag r b x' → lagObj c lam x ≤ lagObj c lam x') ↔
        ∀ i v, KnapFeasible r b i v → knapObj c lam i v ≤ knapObj c lam i (x i)) := by
  classical
  refine ⟨lag_identity c lam,?_⟩
  intro x hx
  constructor
  · intro hmin i v hv
    let y : Fin m → Fin n → ℝ := Function.update x i v
    have hy : FeasibleLag r b y := by
      constructor
      · intro k j
        by_cases hki : k=i
        · subst k; simpa [y] using hv.1 j
        · simpa [y,Function.update_of_ne hki] using hx.1 k j
      · intro k
        by_cases hki : k=i
        · subst k; simpa [y] using hv.2
        · simpa [y,Function.update_of_ne hki] using hx.2 k
    have hh := hmin y hy
    rw [lag_identity,lag_identity] at hh
    have hyi : knapObj c lam i (y i) = knapObj c lam i v := by simp [y]
    have he : ∑ k ∈ univ.erase i, knapObj c lam k (y k) =
        ∑ k ∈ univ.erase i, knapObj c lam k (x k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k≠i := (Finset.mem_erase.mp hk).1
      simp [y,Function.update_of_ne hki]
    have hySum := Finset.sum_erase_add univ (fun k => knapObj c lam k (y k)) (Finset.mem_univ i)
    have hxSum := Finset.sum_erase_add univ (fun k => knapObj c lam k (x k)) (Finset.mem_univ i)
    rw [hyi,he] at hySum
    linarith
  · intro hrow y hy
    rw [lag_identity,lag_identity]
    have hs : ∑ i, knapObj c lam i (y i) ≤ ∑ i, knapObj c lam i (x i) :=
      Finset.sum_le_sum (fun i _ => hrow i (y i) ⟨hy.1 i,hy.2 i⟩)
    linarith
