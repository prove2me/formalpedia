-- Prove2me | solution 1 for PicardFO.Fulfill.Supplement.theorem_B_1_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:31.8788+00:00
-- url     : https://prove2.me/submissions/beaf9446-8327-4d38-a059-1c43f3817447

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Supplement_Witness

open PicardFO
open PicardFO.Fulfill
open PicardFO.Fulfill.Supplement

/-- The printed 2R bound fails for numerical Algorithm 1 even with R=1 and x₁,₀=S.
The theorem certifies assumptions, count and a wrong full action after 2R sweeps. -/
theorem solution :
    witnessPolicy.Admissible witnessModel ∧ witnessModel.Valid witnessStock ∧
    witnessModel.replenishments witnessPolicy witnessStock witnessOrders 4 = 1 ∧
    witnessModel.sequential witnessPolicy witnessStock witnessOrders 2 = (0, 0) ∧
    witnessModel.cached witnessPolicy witnessStock witnessOrders (id : Fin 3 → Fin 3) 2 2 = (4, 0) := by
      have hA : ∀ (a : ℝ) (r : Fin 3 → ℝ) (w : Fin 3),
          witnessPolicy.action witnessModel ⟨a, r⟩ w =
            (if a - max (2 - max (r w) 0) 0 ≤ 2 then
              5 - max (a - max (2 - max (r w) 0) 0) 0 else 0, max (2 - max (r w) 0) 0) := by
        intro a r w
        rfl
      have hT : ∀ (a : ℝ) (r : Fin 3 → ℝ) (p q : ℝ) (w : Fin 3),
          witnessModel.system.f ⟨a, r⟩ (p, q) w =
            ⟨max (a - q) 0 + p, fun n => if n = w then max (r n - 0) 0 + min q a else r n⟩ := by
        intro a r p q w
        rfl
      have o0 : witnessOrders 0 = 0 := by simp [witnessOrders]
      have o1 : witnessOrders 1 = 1 := by simp [witnessOrders]
      have o2 : witnessOrders 2 = 0 := by simp [witnessOrders]
      have o3 : witnessOrders 3 = 2 := by simp [witnessOrders]
      -- policy actions and transitions at the concrete states visited
      have a0 : ∀ w, witnessPolicy.action witnessModel ⟨5, fun _ => 0⟩ w = (0, 2) := by
        intro w
        rw [hA]; norm_num
      have a1 : witnessPolicy.action witnessModel ⟨3, ![2, 0, 0]⟩ 1 = (4, 2) := by
        rw [hA]; norm_num
      have a2 : witnessPolicy.action witnessModel ⟨5, ![2, 2, 0]⟩ 0 = (0, 0) := by
        rw [hA]; norm_num
      have a3 : witnessPolicy.action witnessModel ⟨5, ![2, 2, 0]⟩ 2 = (0, 2) := by
        have e : (![2, 2, 0] : Fin 3 → ℝ) 2 = 0 := rfl
        rw [hA, e]; norm_num
      have a4 : witnessPolicy.action witnessModel ⟨1, ![2, 2, 0]⟩ 0 = (4, 0) := by
        rw [hA]; norm_num
      have f0 : witnessModel.system.f ⟨5, fun _ => 0⟩ (0, 2) 0 = ⟨3, ![2, 0, 0]⟩ := by
        rw [hT, Stock.mk.injEq]
        refine ⟨by norm_num, ?_⟩
        funext n; fin_cases n <;> norm_num
      have f0' : witnessModel.system.f ⟨5, fun _ => 0⟩ (0, 0) 0 = ⟨5, fun _ => 0⟩ := by
        rw [hT, Stock.mk.injEq]
        refine ⟨by norm_num, ?_⟩
        funext n; fin_cases n <;> norm_num
      have f1 : witnessModel.system.f ⟨3, ![2, 0, 0]⟩ (4, 2) 1 = ⟨5, ![2, 2, 0]⟩ := by
        rw [hT, Stock.mk.injEq]
        refine ⟨by norm_num, ?_⟩
        funext n; fin_cases n <;> norm_num
      have f1' : witnessModel.system.f ⟨3, ![2, 0, 0]⟩ (0, 2) 1 = ⟨1, ![2, 2, 0]⟩ := by
        rw [hT, Stock.mk.injEq]
        refine ⟨by norm_num, ?_⟩
        funext n; fin_cases n <;> norm_num
      have f2 : witnessModel.system.f ⟨5, ![2, 2, 0]⟩ (0, 0) 0 = ⟨5, ![2, 2, 0]⟩ := by
        rw [hT, Stock.mk.injEq]
        refine ⟨by norm_num, ?_⟩
        funext n; fin_cases n <;> norm_num
      -- sequential states
      have s0 : witnessModel.system.seqState (witnessPolicy.action witnessModel) witnessStock
          witnessOrders 0 = ⟨5, fun _ => 0⟩ := rfl
      have s1 : witnessModel.system.seqState (witnessPolicy.action witnessModel) witnessStock
          witnessOrders 1 = ⟨3, ![2, 0, 0]⟩ := by
        rw [System.seqState, s0, o0, a0, f0]
      have s2 : witnessModel.system.seqState (witnessPolicy.action witnessModel) witnessStock
          witnessOrders 2 = ⟨5, ![2, 2, 0]⟩ := by
        rw [System.seqState, s1, o1, a1, f1]
      have s3 : witnessModel.system.seqState (witnessPolicy.action witnessModel) witnessStock
          witnessOrders 3 = ⟨5, ![2, 2, 0]⟩ := by
        rw [System.seqState, s2, o2, a2, f2]
      have q0 : witnessModel.sequential witnessPolicy witnessStock witnessOrders 0 = (0, 2) := by
        rw [Model.sequential, System.seqAct, s0, a0]
      have q1 : witnessModel.sequential witnessPolicy witnessStock witnessOrders 1 = (4, 2) := by
        rw [Model.sequential, System.seqAct, s1, o1, a1]
      have q2 : witnessModel.sequential witnessPolicy witnessStock witnessOrders 2 = (0, 0) := by
        rw [Model.sequential, System.seqAct, s2, o2, a2]
      have q3 : witnessModel.sequential witnessPolicy witnessStock witnessOrders 3 = (0, 2) := by
        rw [Model.sequential, System.seqAct, s3, o3, a3]
      -- one process step, by ownership
      have pown : ∀ (α : ℕ → Action) (s : Stock 3) (t : ℕ),
          witnessModel.system.procAct (witnessPolicy.action witnessModel) witnessOrders
            (fun t => (id : Fin 3 → Fin 3) (witnessModel.retailer (witnessOrders t))) α
            (witnessOrders t) s t = witnessPolicy.action witnessModel s (witnessOrders t) := by
        intro α s t
        exact if_pos rfl
      have pother : ∀ (α : ℕ → Action) (m : Fin 3) (s : Stock 3) (t : ℕ),
          witnessOrders t ≠ m → witnessModel.Feasible s (witnessOrders t) (α t) →
          witnessModel.system.procAct (witnessPolicy.action witnessModel) witnessOrders
            (fun t => (id : Fin 3 → Fin 3) (witnessModel.retailer (witnessOrders t))) α
            m s t = α t := by
        intro α m s t h1 h2
        exact (if_neg h1).trans (if_pos h2)
      -- process states
      have p00 : ∀ (α : ℕ → Action) (m : Fin 3),
          witnessModel.system.procState (witnessPolicy.action witnessModel) witnessStock witnessOrders
            (fun t => (id : Fin 3 → Fin 3) (witnessModel.retailer (witnessOrders t))) α m 0
            = ⟨5, fun _ => 0⟩ := fun _ _ => rfl
      have p01 : ∀ (α : ℕ → Action),
          witnessModel.system.procState (witnessPolicy.action witnessModel) witnessStock witnessOrders
            (fun t => (id : Fin 3 → Fin 3) (witnessModel.retailer (witnessOrders t))) α 0 1
            = ⟨3, ![2, 0, 0]⟩ := by
        intro α
        have h := pown α ⟨5, fun _ => 0⟩ 0
        rw [a0] at h
        rw [o0] at h
        rw [System.procState, p00, h, o0, f0]
      have c1 : ∀ t, t = 0 ∨ t = 1 →
          witnessModel.cached witnessPolicy witnessStock witnessOrders (id : Fin 3 → Fin 3) 1 t
            = (0, 2) := by
        intro t ht
        have h : ∀ s, witnessModel.system.procState (witnessPolicy.action witnessModel) witnessStock
            witnessOrders (fun t => (id : Fin 3 → Fin 3) (witnessModel.retailer (witnessOrders t)))
            (fun _ => (0, 0)) (witnessOrders t) t = s →
            witnessModel.cached witnessPolicy witnessStock witnessOrders (id : Fin 3 → Fin 3) 1 t
            = witnessPolicy.action witnessModel s (witnessOrders t) := by
          rintro s rfl
          exact pown _ _ t
        rcases ht with rfl | rfl
        · rw [h _ (p00 _ _), a0]
        · rw [h ⟨5, fun _ => 0⟩ ?_, a0]
          rw [System.procState, p00, pother _ _ _ _ (by rw [o0, o1]; decide) (Or.inl rfl), o0, f0']
      have p02 : ∀ (α : ℕ → Action), α 1 = (0, 2) →
          witnessModel.system.procState (witnessPolicy.action witnessModel) witnessStock witnessOrders
            (fun t => (id : Fin 3 → Fin 3) (witnessModel.retailer (witnessOrders t))) α 0 2
            = ⟨1, ![2, 2, 0]⟩ := by
        intro α hα
        rw [System.procState, p01, pother _ _ _ _ (by rw [o1]; decide) ?_, hα, o1, f1']
        rw [hα, o1]
        right
        refine ⟨by norm_num, by norm_num, ?_, ?_⟩
        · change max ((0:ℝ) - 0) 0 + 2 ≤ 2
          norm_num
        · change max ((3:ℝ) - 2) 0 + 0 ≤ 5
          norm_num
      refine ⟨?_, ?_, ?_, q2, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · norm_num [witnessPolicy]
        · norm_num [witnessPolicy]
        · norm_num [witnessPolicy, witnessModel]
        · intro n
          norm_num [witnessPolicy, witnessModel]
        · intro w
          norm_num [witnessModel]
        · intro n x w _ hx
          change x ≤ 2 at hx
          change 0 ≤ max (2 - max x 0) 0 ∧ max (x - 0) 0 + max (2 - max x 0) 0 ≤ 2
          refine ⟨le_max_right _ _, ?_⟩
          have h2 : max x 0 ≤ 2 := max_le hx (by norm_num)
          rw [sub_zero, max_eq_left (by linarith : (0:ℝ) ≤ 2 - max x 0)]
          linarith
      · refine ⟨le_refl (5:ℝ), fun n => ?_⟩
        change (0:ℝ) ≤ 2
        norm_num
      · have hf : ((Finset.range (4 + 1)).filter fun t => 0 < (Model.sourceAction
            (witnessModel.sequential witnessPolicy witnessStock witnessOrders) t).1) = {2} := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩
            interval_cases t
            · simp [Model.sourceAction] at h2
            · simp [Model.sourceAction, q0] at h2
            · rfl
            · simp [Model.sourceAction, q2] at h2
            · simp [Model.sourceAction, q3] at h2
          · rintro rfl
            refine ⟨by norm_num, ?_⟩
            simp [Model.sourceAction, q1]
        unfold Model.replenishments
        convert Finset.card_singleton 2
      · have h := pown (witnessModel.cached witnessPolicy witnessStock witnessOrders
          (id : Fin 3 → Fin 3) 1) (witnessModel.system.procState (witnessPolicy.action witnessModel)
            witnessStock witnessOrders
            (fun t => (id : Fin 3 → Fin 3) (witnessModel.retailer (witnessOrders t)))
            (witnessModel.cached witnessPolicy witnessStock witnessOrders (id : Fin 3 → Fin 3) 1)
            (witnessOrders 2) 2) 2
        refine Eq.trans h ?_
        rw [o2, p02 _ (c1 1 (Or.inr rfl)), a4]
