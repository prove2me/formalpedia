-- Prove2me | solution 1 for PolylogKServer.Fractional.frac_competitive_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T09:32:18.6152+00:00
-- url     : https://prove2.me/submissions/b950a0f0-1d7e-4fdc-bbd4-0ed014e9fdf5

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PolylogKServer_Fractional_KServer

set_option autoImplicit false

namespace B5077a04K8

open PolylogKServer.HST PolylogKServer.Fractional

/-- K8 statement (verbatim from Assembly.lean). -/
def K8 : Prop :=
  ∀ {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (T : WTree V) (T' : WTree V') (k : ℕ)
    (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf), T.IsLeafMetric M e →
    ∀ (M' : Type) [MetricSpace M'] [Fintype M'] (e' : M' ≃ T'.Leaf), T'.IsLeafMetric M' e' →
    ∀ (g : M ≃ M') (c₁ c₂ : ℝ), 0 ≤ c₁ →
    (∀ x y : M, dist (g x) (g y) ≤ dist x y) →
    (∀ x y : M, dist x y ≤ c₁ * dist (g x) (g y)) →
    ∀ (C₀ : KServer.Config k M) (F : FracKServerAlg k M'),
    F.IsCompetitiveFrom T' e' (fun j => g (C₀ j)) c₂ → 0 ≤ c₂ →
    ∃ F' : FracKServerAlg k M, F'.IsCompetitiveFrom T e C₀ (c₁ * c₂)

section Tree

variable {V : Type} [Fintype V] [DecidableEq V]

theorem anc_of_anc_parent (T : WTree V) {x v : V} (h : T.IsAnc x (T.parent v)) : T.IsAnc x v := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i + 1, by rw [Function.iterate_succ_apply]; exact hi⟩

theorem anc_cases (T : WTree V) {x v : V} (h : T.IsAnc x v) : x = v ∨ T.IsAnc x (T.parent v) := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | zero => exact Or.inl hi.symm
  | succ i => exact Or.inr ⟨i, by rw [Function.iterate_succ_apply] at hi; exact hi⟩

theorem depth_parent_le (T : WTree V) (v : V) : T.depth (T.parent v) ≤ T.depth v := by
  by_cases hv : v = T.root
  · rw [hv, T.parent_root]
  · have := T.depth_parent v hv; omega

theorem depth_iter_le (T : WTree V) (v : V) (i : ℕ) : T.depth (T.parent^[i] v) ≤ T.depth v := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => rw [Function.iterate_succ_apply']; exact (depth_parent_le T _).trans ih

theorem not_anc_parent (T : WTree V) {v : V} (hv : v ≠ T.root) : ¬ T.IsAnc v (T.parent v) := by
  rintro ⟨i, hi⟩
  have h1 := depth_iter_le T (T.parent v) i
  rw [hi] at h1
  have := T.depth_parent v hv
  omega

theorem not_anc_root (T : WTree V) {v : V} (hv : v ≠ T.root) : ¬ T.IsAnc v T.root := by
  rintro ⟨i, hi⟩
  rw [Function.iterate_fixed T.parent_root] at hi
  exact hv hi.symm

theorem treeDist_eq' (T : WTree V) (u v : V) :
    T.treeDist u v = ∑ x ∈ Finset.univ.filter (fun x => x ≠ T.root),
      (open Classical in if (T.IsAnc x u ↔ T.IsAnc x v) then 0 else T.W x) := by
  unfold WTree.treeDist
  congr 1

theorem treeDist_self' (T : WTree V) (u : V) : T.treeDist u u = 0 := by
  rw [treeDist_eq']; simp

theorem treeDist_comm' (T : WTree V) (u v : V) : T.treeDist u v = T.treeDist v u := by
  rw [treeDist_eq', treeDist_eq']
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases a : T.IsAnc x u <;> by_cases b : T.IsAnc x v <;> simp [a, b]

theorem treeDist_triangle' (T : WTree V) (u v w : V) :
    T.treeDist u w ≤ T.treeDist u v + T.treeDist v w := by
  rw [treeDist_eq', treeDist_eq', treeDist_eq', ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  have hW : 0 ≤ T.W x := (T.W_pos x (Finset.mem_filter.1 hx).2).le
  by_cases a : T.IsAnc x u <;> by_cases b : T.IsAnc x v <;> by_cases c : T.IsAnc x w <;>
    simp [a, b, c, hW]

theorem dist_parent_le (T : WTree V) {v : V} (hv : v ≠ T.root) :
    T.treeDist v (T.parent v) ≤ T.W v := by
  classical
  rw [treeDist_eq']
  have hmem : v ∈ Finset.univ.filter (fun x => x ≠ T.root) := by simp [hv]
  calc _ ≤ ∑ x ∈ Finset.univ.filter (fun x => x ≠ T.root), (if x = v then T.W x else 0) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hW : 0 < T.W x := T.W_pos x (Finset.mem_filter.1 hx).2
        by_cases hxv : x = v
        · rw [if_pos hxv, hxv]; split_ifs <;> linarith [T.W_pos v hv]
        · simp only [hxv, if_false]
          have : (T.IsAnc x v ↔ T.IsAnc x (T.parent v)) :=
            ⟨fun h => (anc_cases T h).resolve_left hxv, anc_of_anc_parent T⟩
          simp [this]
    _ = T.W v := by rw [Finset.sum_ite_eq' _ v]; simp [hmem]

open Classical in
theorem telescope (T : WTree V) (H : V → ℝ) (u : V) :
    H u = H T.root + ∑ v ∈ Finset.univ.filter (fun x => x ≠ T.root),
      (if T.IsAnc v u then H v - H (T.parent v) else 0) := by
  induction hd : T.depth u using Nat.strong_induction_on generalizing u with
  | _ d ih =>
    by_cases hu : u = T.root
    · subst hu
      rw [Finset.sum_eq_zero, add_zero]
      intro v hv
      rw [if_neg (not_anc_root T (Finset.mem_filter.1 hv).2)]
    · have hdp := T.depth_parent u hu
      have ihp := ih (T.depth (T.parent u)) (by omega) (T.parent u) rfl
      have hmem : u ∈ Finset.univ.filter (fun x => x ≠ T.root) := by simp [hu]
      have hsplit : ∀ v ∈ Finset.univ.filter (fun x => x ≠ T.root),
          (if T.IsAnc v u then H v - H (T.parent v) else 0) =
          (if v = u then H u - H (T.parent u) else 0) +
          (if T.IsAnc v (T.parent u) then H v - H (T.parent v) else 0) := by
        intro v _
        by_cases hvu : v = u
        · subst hvu
          simp [not_anc_parent T hu, show T.IsAnc v v from ⟨0, rfl⟩]
        · simp only [hvu, if_false, zero_add]
          have : (T.IsAnc v u ↔ T.IsAnc v (T.parent u)) :=
            ⟨fun h => (anc_cases T h).resolve_left hvu, anc_of_anc_parent T⟩
          simp only [this]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' _ u,
        if_pos hmem]
      linarith

/-- Weak duality on a tree: a `c`-Lipschitz potential against a balanced signed measure. -/
theorem dual_le (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (c : ℝ) (hc : 0 ≤ c)
    (h : M → ℝ) (hh : ∀ a b, h a - h b ≤ c * T.treeDist (e a) (e b))
    (δ : M → ℝ) (hδ : ∑ m, δ m = 0) :
    ∑ m, δ m * h m ≤ c * ∑ v ∈ Finset.univ.filter (fun x => x ≠ T.root),
      T.W v * |∑ m, (open Classical in if T.IsAnc v (e m) then δ m else 0)| := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, abs_zero, mul_zero, Finset.sum_const_zero,
      le_refl]
  have hne : (Finset.univ : Finset M).Nonempty := Finset.univ_nonempty
  set H : V → ℝ := fun v => Finset.univ.inf' hne (fun m => h m + c * T.treeDist v (e m)) with hHdef
  have hHe : ∀ m, H (e m) = h m := by
    intro m
    apply le_antisymm
    · have := Finset.inf'_le (fun m' => h m' + c * T.treeDist (e m : V) (e m')) (Finset.mem_univ m)
      simpa [treeDist_self'] using this
    · refine Finset.le_inf' _ _ fun m' _ => ?_
      have := hh m m'
      linarith
  have hlip : ∀ u w, H u - H w ≤ c * T.treeDist u w := by
    intro u w
    obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_inf' hne (fun m => h m + c * T.treeDist w (e m))
    have h1 := Finset.inf'_le (fun m' => h m' + c * T.treeDist u (e m')) (Finset.mem_univ m)
    have h2 := treeDist_triangle' T u w (e m)
    have h3 : H w = h m + c * T.treeDist w (e m) := hm
    have h4 : H u ≤ h m + c * T.treeDist u (e m) := h1
    nlinarith
  have hstep : ∀ v, v ≠ T.root → |H v - H (T.parent v)| ≤ c * T.W v := by
    intro v hv
    have hd := dist_parent_le T hv
    rw [abs_le]
    constructor
    · have := hlip (T.parent v) v
      rw [treeDist_comm'] at this
      nlinarith
    · have := hlip v (T.parent v)
      nlinarith
  calc ∑ m, δ m * h m
      = ∑ m, δ m * (H T.root + ∑ v ∈ Finset.univ.filter (fun x => x ≠ T.root),
          (if T.IsAnc v (e m) then H v - H (T.parent v) else 0)) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← telescope T H, hHe]
    _ = ∑ v ∈ Finset.univ.filter (fun x => x ≠ T.root),
          (H v - H (T.parent v)) * ∑ m, (if T.IsAnc v (e m) then δ m else 0) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hδ, zero_mul, zero_add,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun m _ => ?_
        split_ifs <;> ring
    _ ≤ ∑ v ∈ Finset.univ.filter (fun x => x ≠ T.root),
          c * T.W v * |∑ m, (if T.IsAnc v (e m) then δ m else 0)| := by
        refine Finset.sum_le_sum fun v hv => ?_
        have := hstep v (Finset.mem_filter.1 hv).2
        calc _ ≤ |(H v - H (T.parent v)) * ∑ m, (if T.IsAnc v (e m) then δ m else 0)| :=
              le_abs_self _
          _ = |H v - H (T.parent v)| * |∑ m, (if T.IsAnc v (e m) then δ m else 0)| := abs_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => by ring

theorem subtreeMass_eq (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (x : M → ℝ) (v : V) :
    subtreeMass T e x v = ∑ m, (open Classical in if T.IsAnc v (e m : V) then x m else 0) := by
  unfold subtreeMass
  congr 1

theorem delta_eq (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (x x' : M → ℝ) (v : V) :
    subtreeMass T e x' v - subtreeMass T e x v =
      ∑ m, (open Classical in if T.IsAnc v (e m : V) then x' m - x m else 0) := by
  classical
  rw [subtreeMass_eq, subtreeMass_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> ring

/-- K2: the fractional movement cost on a tree is monotone in the leaf metric. -/
theorem fracMoveCost_le {V' : Type} [Fintype V'] [DecidableEq V'] (T : WTree V) (T' : WTree V')
    {M : Type} [Fintype M] (e : M ≃ T.Leaf) (e' : M ≃ T'.Leaf) (c : ℝ) (hc : 0 ≤ c)
    (hd : ∀ a b : M, T.treeDist (e a) (e b) ≤ c * T'.treeDist (e' a) (e' b))
    (x x' : M → ℝ) (hsum : ∑ m, x m = ∑ m, x' m) :
    fracMoveCost T e x x' ≤ c * fracMoveCost T' e' x x' := by
  classical
  set δ : M → ℝ := fun m => x' m - x m with hδdef
  have hδ : ∑ m, δ m = 0 := by simp only [hδdef, Finset.sum_sub_distrib, hsum, sub_self]
  set Δ : V → ℝ := fun v => ∑ m, (if T.IsAnc v (e m : V) then δ m else 0) with hΔ
  set s : V → ℝ := fun v => if 0 ≤ Δ v then 1 else -1 with hs
  set f : M → ℝ := fun m => ∑ v ∈ Finset.univ.filter (fun x => x ≠ T.root),
    (if T.IsAnc v (e m : V) then T.W v * s v else 0) with hf
  have hlhs : fracMoveCost T e x x' = ∑ m, δ m * f m := by
    unfold fracMoveCost
    simp only [hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [delta_eq]
    have habs : |Δ v| = s v * Δ v := by
      simp only [hs]
      split_ifs with h0
      · rw [abs_of_nonneg h0]; ring
      · rw [abs_of_neg (lt_of_not_ge h0)]; ring
    change T.W v * |Δ v| = _
    rw [habs, hΔ]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  have hlip : ∀ a b, f a - f b ≤ c * T'.treeDist (e' a) (e' b) := by
    intro a b
    refine le_trans ?_ (hd a b)
    rw [treeDist_eq', hf]
    simp only
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun v hv => ?_
    have hW : 0 < T.W v := T.W_pos v (Finset.mem_filter.1 hv).2
    have hs1 : s v = 1 ∨ s v = -1 := by simp only [hs]; split_ifs <;> simp
    by_cases ha : T.IsAnc v (e a : V) <;> by_cases hb : T.IsAnc v (e b : V) <;>
      simp only [ha, hb, if_true, if_false, iff_self, iff_true, true_iff, iff_false, false_iff,
        not_true_eq_false, not_false_eq_true] <;>
      rcases hs1 with h1 | h1 <;> (try rw [h1]) <;> nlinarith
  rw [hlhs]
  have := dual_le T' e' c hc f hlip δ hδ
  refine this.trans (le_of_eq ?_)
  unfold fracMoveCost
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [delta_eq]

theorem fracMoveCost_comp {V' : Type} [Fintype V'] [DecidableEq V'] (T' : WTree V')
    {M M' : Type} [Fintype M] [Fintype M'] (g : M ≃ M') (e' : M' ≃ T'.Leaf) (y y' : M' → ℝ) :
    fracMoveCost T' (g.trans e') (fun m => y (g m)) (fun m => y' (g m)) =
      fracMoveCost T' e' y y' := by
  unfold fracMoveCost
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [subtreeMass_eq, subtreeMass_eq, subtreeMass_eq, subtreeMass_eq]
  congr 3
  · exact Equiv.sum_comp g (fun m' => (open Classical in if T'.IsAnc v (e' m' : V') then y' m' else 0))
  · exact Equiv.sum_comp g (fun m' => (open Classical in if T'.IsAnc v (e' m' : V') then y m' else 0))

end Tree

section Opt

open KServer

theorem opt_map {k : ℕ} {M M' : Type} [MetricSpace M] [MetricSpace M'] (g : M ≃ M')
    (hle : ∀ x y : M, dist (g x) (g y) ≤ dist x y) (C₀ : Config k M) (σ : List M) :
    offlineCost (fun j => g (C₀ j)) (σ.map g) ≤ offlineCost C₀ σ := by
  unfold offlineCost
  have hbdd : BddBelow {c : ℝ | ∃ S : ℕ → Config k M', ServesFrom (fun j => g (C₀ j)) (σ.map g) S ∧
      c = ∑ j ∈ Finset.range (σ.map g).length, moveCost (S j) (S (j + 1))} := by
    refine ⟨0, ?_⟩
    rintro c ⟨S, -, rfl⟩
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => dist_nonneg
  have fwd : ∀ S : ℕ → Config k M, ServesFrom C₀ σ S →
      ServesFrom (fun j => g (C₀ j)) (σ.map g) (fun n s => g (S n s)) := by
    intro S hS
    refine ⟨by funext s; simp [hS.1], fun j => ?_⟩
    obtain ⟨s, hs⟩ := hS.2 ⟨j, by simpa using j.2⟩
    refine ⟨s, ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map] at hs ⊢
    rw [hs]
  rcases Set.eq_empty_or_nonempty {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} with hA | hA
  · have hB : {c : ℝ | ∃ S : ℕ → Config k M', ServesFrom (fun j => g (C₀ j)) (σ.map g) S ∧
        c = ∑ j ∈ Finset.range (σ.map g).length, moveCost (S j) (S (j + 1))} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem] at hA ⊢
      rintro c ⟨S, hS, -⟩
      refine hA _ ⟨fun n s => g.symm (S n s), ⟨?_, fun j => ?_⟩, rfl⟩
      · funext s; simp [hS.1]
      · obtain ⟨s, hs⟩ := hS.2 ⟨j, by simp⟩
        refine ⟨s, ?_⟩
        simp only [List.get_eq_getElem, List.getElem_map] at hs ⊢
        rw [hs]; simp
    rw [hA, hB]
  · refine le_csInf hA ?_
    rintro c ⟨S, hS, rfl⟩
    refine (csInf_le hbdd ⟨_, fwd S hS, rfl⟩).trans ?_
    rw [List.length_map]
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun s _ => hle _ _

end Opt

theorem k8_proof : K8 := by
  intro V V' _ _ _ _ T T' k M _ _ e hM M' _ _ e' hM' g c₁ c₂ hc₁ hle hge C₀ F hF hc₂
  obtain ⟨h0, hst, hsv, a, ha⟩ := hF
  refine ⟨⟨fun l m => F.state (l.map g) (g m)⟩, ?_, ?_, ?_, c₁ * a, ?_⟩
  · funext m
    show F.state ([].map g) (g m) = _
    rw [List.map_nil, h0]
    have hiff : g m ∈ Set.range (fun j => g (C₀ j)) ↔ m ∈ Set.range C₀ := by
      constructor
      · rintro ⟨j, hj⟩; exact ⟨j, g.injective hj⟩
      · rintro ⟨j, hj⟩; exact ⟨j, by show g (C₀ j) = g m; rw [hj]⟩
    unfold indicatorState
    by_cases hm : m ∈ Set.range C₀
    · rw [if_pos (hiff.2 hm), if_pos hm]
    · rw [if_neg (fun h => hm (hiff.1 h)), if_neg hm]
  · intro l
    obtain ⟨hb, hs⟩ := hst (l.map g)
    refine ⟨fun m => hb (g m), ?_⟩
    rw [← hs]
    exact Equiv.sum_comp g (F.state (l.map g))
  · intro l r
    show F.state ((l ++ [r]).map g) (g r) = 1
    rw [List.map_append, List.map_singleton]
    exact hsv _ _
  · intro ρ
    have hopt := opt_map g hle C₀ ρ
    have hcost : FracKServerAlg.cost (k := k) ⟨fun l m => F.state (l.map g) (g m)⟩ T e ρ ≤
        c₁ * F.cost T' e' (ρ.map g) := by
      unfold FracKServerAlg.cost
      rw [List.length_map, Finset.mul_sum]
      refine Finset.sum_le_sum fun t _ => ?_
      simp only [← List.map_take]
      rw [← fracMoveCost_comp T' g e']
      refine fracMoveCost_le T T' e (g.trans e') c₁ hc₁ ?_ _ _ ?_
      · intro x y
        rw [← hM x y]
        have := hM' (g x) (g y)
        simp only [Equiv.trans_apply]
        rw [← this]
        exact hge x y
      · rw [Equiv.sum_comp g (F.state (List.map g (List.take t ρ))),
          Equiv.sum_comp g (F.state (List.map g (List.take (t + 1) ρ))),
          (hst _).2, (hst _).2]
    have h1 := mul_le_mul_of_nonneg_left (ha (ρ.map g)) hc₁
    have h2 := mul_le_mul_of_nonneg_left hopt (mul_nonneg hc₁ hc₂)
    nlinarith

end B5077a04K8

open PolylogKServer.HST PolylogKServer.Fractional in
theorem solution :
  ∀ {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (T : WTree V) (T' : WTree V') (k : ℕ)
    (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf), T.IsLeafMetric M e →
    ∀ (M' : Type) [MetricSpace M'] [Fintype M'] (e' : M' ≃ T'.Leaf), T'.IsLeafMetric M' e' →
    ∀ (g : M ≃ M') (c₁ c₂ : ℝ), 0 ≤ c₁ →
    (∀ x y : M, dist (g x) (g y) ≤ dist x y) →
    (∀ x y : M, dist x y ≤ c₁ * dist (g x) (g y)) →
    ∀ (C₀ : KServer.Config k M) (F : FracKServerAlg k M'),
    F.IsCompetitiveFrom T' e' (fun j => g (C₀ j)) c₂ → 0 ≤ c₂ →
    ∃ F' : FracKServerAlg k M, F'.IsCompetitiveFrom T e C₀ (c₁ * c₂) := by
  exact B5077a04K8.k8_proof
