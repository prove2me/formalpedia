-- Prove2me | solution 1 for TPG.integral_indicator_Z_mul
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:04:18.31161+00:00
-- url     : https://prove2.me/submissions/ec05a5a7-c9b9-48f9-b281-50ac63b280de

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov
import Theorems.Thm_TPG_integral_trajLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

/-- Conditioning the path weight on the action at time `u`: the weight on `{z' u = z}` is the
probability of that action times the weight for the sequence `q` updated to a point mass at `u`. -/
lemma TPG_FB_pathWeight_update {S : Type} [Fintype S] (E : Env S) (T : ℕ) (q : ℕ → ℝ)
    (u : Fin T) (z : Bool) (x : Fin T → S) (z' : Fin T → Bool) :
    (if z' u = z then E.pathWeight T q x z' else 0)
      = (if z then q (u : ℕ) else 1 - q (u : ℕ))
        * E.pathWeight T (Function.update q (u : ℕ) (if z then 1 else 0)) x z' := by
  classical
  have key : (if z' u = z then (∏ t : Fin T, if z' t then q (t : ℕ) else 1 - q (t : ℕ)) else 0)
      = (if z then q (u : ℕ) else 1 - q (u : ℕ)) *
        ∏ t : Fin T, (if z' t then Function.update q (u : ℕ) (if z then 1 else 0) (t : ℕ)
            else 1 - Function.update q (u : ℕ) (if z then 1 else 0) (t : ℕ)) := by
    rw [← Finset.mul_prod_erase Finset.univ
        (fun t : Fin T => if z' t then q (t : ℕ) else 1 - q (t : ℕ)) (Finset.mem_univ u),
      ← Finset.mul_prod_erase Finset.univ
        (fun t : Fin T => if z' t then Function.update q (u : ℕ) (if z then 1 else 0) (t : ℕ)
            else 1 - Function.update q (u : ℕ) (if z then 1 else 0) (t : ℕ)) (Finset.mem_univ u)]
    have h2 : ∀ t ∈ Finset.univ.erase u,
        (if z' t then Function.update q (u : ℕ) (if z then 1 else 0) (t : ℕ)
            else 1 - Function.update q (u : ℕ) (if z then 1 else 0) (t : ℕ))
          = (if z' t then q (t : ℕ) else 1 - q (t : ℕ)) := by
      intro t ht
      have hne : (t : ℕ) ≠ (u : ℕ) := fun h => (Finset.ne_of_mem_erase ht) (Fin.ext h)
      rw [Function.update_of_ne hne]
    rw [Finset.prod_congr rfl h2]
    simp only [Function.update_self]
    cases z <;> cases h : z' u <;> simp
  unfold Env.pathWeight
  calc (if z' u = z then
          (∏ t : Fin T, if (t : ℕ) = 0 then E.ρ (x t) else 1)
          * (∏ s : Fin T, ∏ t : Fin T,
              if (s : ℕ) + 1 = (t : ℕ) then E.P (s : ℕ) (z' s) (x s) (x t) else 1)
          * (∏ t : Fin T, if z' t then q (t : ℕ) else 1 - q (t : ℕ)) else 0)
      = (∏ t : Fin T, if (t : ℕ) = 0 then E.ρ (x t) else 1)
          * (∏ s : Fin T, ∏ t : Fin T,
              if (s : ℕ) + 1 = (t : ℕ) then E.P (s : ℕ) (z' s) (x s) (x t) else 1)
          * (if z' u = z then (∏ t : Fin T, if z' t then q (t : ℕ) else 1 - q (t : ℕ))
              else 0) := by
        split_ifs <;> simp
    _ = _ := by rw [key]; ring

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (u : Fin T) (z : Bool) (F : Traj S T → ℝ) (hF : Measurable F)
    (hint : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ => F (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2)) :
    ∫ ω, (if Z u ω = z then F ω else 0) ∂(E.trajLaw T q)
      = (if z then q (u : ℕ) else 1 - q (u : ℕ))
          * ∫ ω, F ω ∂(E.trajLaw T (Function.update q (u : ℕ) (if z then 1 else 0))) := by
  classical
  have hq' : ∀ t : ℕ, 0 ≤ Function.update q (u : ℕ) (if z then 1 else 0) t ∧
      Function.update q (u : ℕ) (if z then 1 else 0) t ≤ 1 := by
    intro t
    by_cases h : t = (u : ℕ)
    · subst h
      cases z <;> simp
    · rw [Function.update_of_ne h]
      exact hq t
  have hZ : Measurable (Z u : Traj S T → Bool) := by
    show Measurable (fun ω : Traj S T => (ω u).2.1)
    exact measurable_fst.comp (measurable_snd.comp (measurable_pi_apply u))
  have hF' : Measurable (fun ω : Traj S T => if Z u ω = z then F ω else 0) :=
    Measurable.ite (hZ (measurableSet_singleton z)) hF measurable_const
  have hval : ∀ (p : (Fin T → S) × (Fin T → Bool)) (y : Fin T → ℝ),
      Z u (embedPath p.1 p.2 y) = p.2 u := fun p y => rfl
  have hint' : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ =>
        (fun ω : Traj S T => if Z u ω = z then F ω else 0) (embedPath p.1 p.2 y))
        (E.rewardLaw p.1 p.2) := by
    intro p
    by_cases h : p.2 u = z
    · simpa only [hval, h, if_true] using hint p
    · simp only [hval, h, if_false]
      exact integrable_zero _ _ _
  rw [(integral_trajLaw E T q hq _ hF' hint').2, (integral_trajLaw E T _ hq' F hF hint).2,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : ∫ y, (fun ω : Traj S T => if Z u ω = z then F ω else 0) (embedPath p.1 p.2 y)
        ∂(E.rewardLaw p.1 p.2)
      = if p.2 u = z then ∫ y, F (embedPath p.1 p.2 y) ∂(E.rewardLaw p.1 p.2) else 0 := by
    by_cases h : p.2 u = z
    · simp only [hval, h, if_true]
    · simp only [hval, h, if_false, integral_zero]
  rw [h1, ← mul_assoc, ← TPG_FB_pathWeight_update]
  split_ifs <;> simp
