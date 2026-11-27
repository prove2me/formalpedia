-- Prove2me | solution 1 for UnsplitCVRP.Combinatorial.Supplement.lp_le_opt
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:13.523302+00:00
-- url     : https://prove2.me/submissions/73343ec1-60dc-458c-8760-b885ecfc25f7

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting
import Definitions.Def_UnsplitCVRP_Combinatorial_Supplement_ConfigLP

open UnsplitCVRP
open UnsplitCVRP.Combinatorial
open UnsplitCVRP.Combinatorial.Supplement

/-- §4, p. 9: the optimum value of the Configuration-LP is a lower bound on the cost of
every feasible solution ("the optimum LP value provides a lower bound on opt"). -/
theorem solution {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (δ : ℝ)
    (xstar : List (Fin (n + 1)) → ℝ) (hx : IsConfigOptimal c d δ xstar)
    (R : List (List (Fin (n + 1)))) (hR : IsSolution d R) :
    configCost c d δ xstar ≤ SupplyChainTheory.solutionCost c R := by
      classical
      let Q : Fin (n + 1) → List (Fin (n + 1)) → ℝ := fun a L =>
        (List.zipWith c (a :: L) (L ++ [0])).sum
      have Qnil : ∀ a, Q a [] = c a 0 := by intro a; simp [Q]
      have Qcons : ∀ a x L, Q a (x :: L) = c a x + Q x L := by
        intro a x L; simp [Q]
      have Qnn : ∀ L a, 0 ≤ Q a L := by
        intro L
        induction L with
        | nil => intro a; rw [Qnil]; exact hc.nonneg _ _
        | cons x L ih => intro a; rw [Qcons]; linarith [hc.nonneg a x, ih x]
      have key1 : ∀ L a b, Q a L ≤ c a b + Q b L := by
        intro L a b
        cases L with
        | nil => rw [Qnil, Qnil]; linarith [hc.triangle a 0 b]
        | cons y M => rw [Qcons, Qcons]; linarith [hc.triangle a y b]
      have key2 : ∀ (p : Fin (n + 1) → Bool) L a, Q a (L.filter p) ≤ Q a L := by
        intro p L
        induction L with
        | nil => intro a; simp
        | cons x L ih =>
          intro a
          by_cases hp : p x = true
          · rw [List.filter_cons_of_pos hp, Qcons, Qcons]; linarith [ih x]
          · rw [List.filter_cons_of_neg hp, Qcons]; linarith [ih a, key1 L a x]
      have route : ∀ L, SupplyChainTheory.routeCost c L = Q 0 L := by
        intro L
        simp [SupplyChainTheory.routeCost, SupplyChainTheory.closedLength, Q]
      let f : List (Fin (n + 1)) → List (Fin (n + 1)) := fun L => L.filter (fun v => decide (δ < d v))
      let M := R.map f
      let y : List (Fin (n + 1)) → ℝ := fun T => (M.count T : ℝ)
      obtain ⟨hR1, hR2, hR3⟩ := hR
      have memJ : ∀ L ∈ R, f L ≠ [] → f L ∈ configTours d δ := by
        intro L hL hne
        have hnd : L.Nodup := (List.nodup_flatten.mp hR2).1 L hL
        have hmemcl : ∀ v ∈ L, v ∈ clients n := fun v hv =>
          (hR3 v).mp (List.mem_flatten.mpr ⟨L, hL, hv⟩)
        have hload : load d (f L) ≤ 1 := by
          have hsub : ((f L).map d).Sublist (L.map d) := (List.filter_sublist).map d
          have : load d (f L) ≤ load d L := by
            unfold load
            apply hsub.sum_le_sum
            intro a ha
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
            have h0 : v ≠ 0 := fun h => (hR1 L hL).2.1 (h ▸ hv)
            exact (hd v h0).1.le
          linarith [(hR1 L hL).2.2]
        unfold configTours
        rw [Finset.mem_filter]
        refine ⟨?_, hne, ?_, hload⟩
        · rw [Finset.mem_map]
          exact ⟨⟨f L, hnd.filter _⟩, Finset.mem_univ _, rfl⟩
        · intro v hv
          have hv' := List.mem_filter.mp hv
          exact Finset.mem_filter.mpr ⟨hmemcl v hv'.1, by simpa using hv'.2⟩
      have feas : IsConfigFeasible d δ y := by
        refine ⟨fun T _ => by positivity, ?_⟩
        intro v hv
        have hvc : v ∈ clients n := (Finset.mem_filter.mp hv).1
        have hvb : δ < d v := (Finset.mem_filter.mp hv).2
        obtain ⟨L, hL, hvL⟩ := List.mem_flatten.mp ((hR3 v).mpr hvc)
        have hvf : v ∈ f L := by simp [f, hvL, hvb]
        have hfne : f L ≠ [] := List.ne_nil_of_mem hvf
        have hT : f L ∈ (configTours d δ).filter (fun T => v ∈ T) :=
          Finset.mem_filter.mpr ⟨memJ L hL hfne, hvf⟩
        have h1 : (1 : ℝ) ≤ y (f L) := by
          have : 0 < M.count (f L) := List.count_pos_iff.mpr (List.mem_map_of_mem hL)
          simp only [y]; exact_mod_cast this
        calc (1 : ℝ) ≤ y (f L) := h1
          _ ≤ _ := Finset.single_le_sum (f := y) (fun T _ => by positivity) hT
      have hcost := hx.2 y feas
      refine hcost.trans ?_
      have rnn : ∀ T, 0 ≤ SupplyChainTheory.routeCost c T := fun T => by rw [route]; exact Qnn _ _
      let g : List (Fin (n + 1)) → ℝ := fun T => SupplyChainTheory.routeCost c T * y T
      have step1 : configCost c d δ y ≤ ∑ T ∈ configTours d δ ∪ M.toFinset, g T :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun T _ _ => mul_nonneg (rnn T) (by positivity))
      have step2 : ∑ T ∈ configTours d δ ∪ M.toFinset, g T = ∑ T ∈ M.toFinset, g T := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro T _ hT
        have : M.count T = 0 := List.count_eq_zero.mpr (by simpa using hT)
        simp [g, y, this]
      have step3 : ∑ T ∈ M.toFinset, g T = (M.map (SupplyChainTheory.routeCost c)).sum := by
        rw [Finset.sum_list_map_count]
        apply Finset.sum_congr rfl
        intro T _
        simp only [g, y, nsmul_eq_mul]; rw [mul_comm]; congr 2
        simp only [List.count, List.countP_eq_length_filter]
        congr 1
        apply List.filter_congr
        intro a _
        by_cases h : a = T
        · subst h
          rw [@beq_self_eq_true _ instBEqOfDecidableEq _ a, @beq_self_eq_true _ List.instBEq _ a]
        · rw [@beq_false_of_ne _ instBEqOfDecidableEq _ _ _ h, @beq_false_of_ne _ List.instBEq _ _ _ h]
      have step4 : (M.map (SupplyChainTheory.routeCost c)).sum ≤ SupplyChainTheory.solutionCost c R := by
        simp only [M, List.map_map, SupplyChainTheory.solutionCost]
        apply List.sum_le_sum
        intro L _
        simp only [Function.comp, route, f]
        exact key2 _ L 0
      linarith
