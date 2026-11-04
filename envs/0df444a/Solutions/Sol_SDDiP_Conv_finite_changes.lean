-- Prove2me | solution 1 for SDDiP.Conv.finite_changes
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:36:45.437917+00:00
-- url     : https://prove2.me/submissions/3b222ce3-7709-4425-868f-bdad751c71fa

import Mathlib
import Definitions.Def_SDDiP_Conv_SND

namespace SDDiP1Aux

open SDDiP.Conv StochasticProg.Multistage MeasureTheory Filter ProbabilityTheory

variable {H d ℓ : ℕ} (D : Model H d ℓ)

lemma mem_children {n m : D.T.Node} :
    m ∈ D.T.children n ↔ (D.T.stage m).val = (D.T.stage n).val + 1 ∧ D.T.anc m = n := by
  simp [Tree.children]

lemma child_ne_root {n m : D.T.Node} (h : m ∈ D.T.children n) : m ≠ D.T.root := by
  intro hm
  rw [mem_children] at h
  have := D.T.root_stage
  rw [hm] at h
  omega

lemma mem_children_iff_anc {n m : D.T.Node} (hm : m ≠ D.T.root) :
    m ∈ D.T.children n ↔ D.T.anc m = n := by
  rw [mem_children]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have h1 : (D.T.stage m).val ≠ 0 := fun h0 => hm (D.T.root_unique m h0)
    have := D.T.anc_stage m h1
    rw [h] at this
    omega

lemma leaf_children {n : D.T.Node} (hn : D.IsLeaf n) : D.T.children n = ∅ := by
  ext m
  simp only [Finset.notMem_empty, iff_false]
  intro h
  rw [mem_children] at h
  have := (D.T.stage m).isLt
  unfold Model.IsLeaf at hn
  omega

lemma Qcal_leaf {n : D.T.Node} (hn : D.IsLeaf n) (x : Fin d → Bool) : D.Qcal n x = 0 := by
  simp [Model.Qcal, leaf_children D hn]

lemma q_nonneg (n m : D.T.Node) : 0 ≤ D.q n m :=
  div_nonneg (D.p_pos m).le (D.p_pos n).le

/-- Induction from the leaves upward. -/
lemma tree_induction (P : D.T.Node → Prop) (h : ∀ n, (∀ m ∈ D.T.children n, P m) → P n) :
    ∀ n, P n := by
  suffices ∀ k, ∀ n, H - (D.T.stage n).val = k → P n from fun n => this _ n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk
    apply h
    intro m hm
    rw [mem_children] at hm
    have := (D.T.stage m).isLt
    exact ih _ (by omega) m rfl

/-! ### foldr max -/

lemma foldr_ge_init {α : Type*} (g : α → ℝ) (l : List α) (b : ℝ) :
    b ≤ l.foldr (fun κ acc => max (g κ) acc) b := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons]; exact le_trans ih (le_max_right _ _)

lemma foldr_mono_init {α : Type*} (g : α → ℝ) (l : List α) {b c : ℝ} (h : b ≤ c) :
    l.foldr (fun κ acc => max (g κ) acc) b ≤ l.foldr (fun κ acc => max (g κ) acc) c := by
  induction l with
  | nil => simpa
  | cons a l ih => simp only [List.foldr_cons]; exact max_le_max le_rfl ih

lemma foldr_le {α : Type*} (g : α → ℝ) (l : List α) {b c : ℝ} (hb : b ≤ c)
    (hl : ∀ κ ∈ l, g κ ≤ c) : l.foldr (fun κ acc => max (g κ) acc) b ≤ c := by
  induction l with
  | nil => simpa
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (hl a (by simp)) (ih (fun κ hκ => hl κ (by simp [hκ])))

lemma foldr_mem {α : Type*} (g : α → ℝ) (l : List α) (b : ℝ) :
    l.foldr (fun κ acc => max (g κ) acc) b = b ∨
      ∃ κ ∈ l, l.foldr (fun κ acc => max (g κ) acc) b = g κ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons]
    rcases max_choice (g a) (l.foldr (fun κ acc => max (g κ) acc) b) with h | h
    · exact Or.inr ⟨a, Or.inl rfl, h⟩
    · rw [h]
      rcases ih with h' | ⟨κ, hκ, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨κ, Or.inr hκ, h'⟩

/-! ### cut lists -/

lemma cutLists_pos {M : ℕ} (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) (i : ℕ)
    (n : D.T.Node) (h : D.Sampled (s i) n ∧ ¬ D.IsLeaf n) :
    D.cutLists s κ (i + 1) n = D.cutLists s κ i n ++ [κ i] := by
  rw [Model.cutLists]
  exact if_pos h

lemma cutLists_neg {M : ℕ} (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) (i : ℕ)
    (n : D.T.Node) (h : ¬ (D.Sampled (s i) n ∧ ¬ D.IsLeaf n)) :
    D.cutLists s κ (i + 1) n = D.cutLists s κ i n := by
  rw [Model.cutLists]
  exact if_neg h

lemma mem_cutLists {M : ℕ} (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) :
    ∀ (i : ℕ) (n : D.T.Node) (c : D.T.Node → Cut d), c ∈ D.cutLists s κ i n →
      ∃ i' < i, D.Sampled (s i') n ∧ c = κ i' := by
  intro i
  induction i with
  | zero => intro n c hc; simp [Model.cutLists] at hc
  | succ i ih =>
    intro n c hc
    by_cases h : D.Sampled (s i) n ∧ ¬ D.IsLeaf n
    · rw [cutLists_pos D s κ i n h, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨i', hi', h1, h2⟩ := ih n c hc
        exact ⟨i', by omega, h1, h2⟩
      · simp only [List.mem_singleton] at hc
        exact ⟨i, by omega, h.1, hc⟩
    · rw [cutLists_neg D s κ i n h] at hc
      obtain ⟨i', hi', h1, h2⟩ := ih n c hc
      exact ⟨i', by omega, h1, h2⟩

lemma approx_leaf (L : D.T.Node → ℝ) {M : ℕ} (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d)
    (i : ℕ) {n : D.T.Node} (hn : D.IsLeaf n) (x : Fin d → Bool) : D.approx L s κ i n x = 0 := by
  simp [Model.approx, Model.psi, hn]

lemma approx_nonleaf (L : D.T.Node → ℝ) {M : ℕ} (s : ℕ → Fin M → D.Leaf)
    (κ : ℕ → D.T.Node → Cut d) (i : ℕ) {n : D.T.Node} (hn : ¬ D.IsLeaf n) (x : Fin d → Bool) :
    D.approx L s κ i n x =
      (D.cutLists s κ i n).foldr (fun c acc => max (D.agg n c x) acc) (L n) := by
  simp [Model.approx, Model.psi, hn]

lemma approx_succ_ge (L : D.T.Node → ℝ) {M : ℕ} (s : ℕ → Fin M → D.Leaf)
    (κ : ℕ → D.T.Node → Cut d) (i : ℕ) (n : D.T.Node) (x : Fin d → Bool) :
    D.approx L s κ i n x ≤ D.approx L s κ (i + 1) n x := by
  by_cases hl : D.IsLeaf n
  · rw [approx_leaf D L s κ i hl, approx_leaf D L s κ (i + 1) hl]
  · rw [approx_nonleaf D L s κ i hl, approx_nonleaf D L s κ (i + 1) hl]
    by_cases h : D.Sampled (s i) n ∧ ¬ D.IsLeaf n
    · rw [cutLists_pos D s κ i n h, List.foldr_append]
      exact foldr_mono_init _ _ (by simp)
    · rw [cutLists_neg D s κ i n h]

lemma approx_succ_ge_agg (L : D.T.Node → ℝ) {M : ℕ} (s : ℕ → Fin M → D.Leaf)
    (κ : ℕ → D.T.Node → Cut d) (i : ℕ) (n : D.T.Node) (h : D.Sampled (s i) n ∧ ¬ D.IsLeaf n)
    (x : Fin d → Bool) : D.agg n (κ i) x ≤ D.approx L s κ (i + 1) n x := by
  rw [approx_nonleaf D L s κ (i + 1) h.2, cutLists_pos D s κ i n h, List.foldr_append]
  refine le_trans ?_ (foldr_ge_init _ _ _)
  simp

/-- Part 1 of the under-approximation property: `ψ^i_n ≤ 𝒬_n`. -/
lemma approx_le_Qcal (L : D.T.Node → ℝ) (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    {M : ℕ} (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) (hvalid : D.ValidCuts s κ)
    (i : ℕ) (n : D.T.Node) (x : Fin d → Bool) : D.approx L s κ i n x ≤ D.Qcal n x := by
  by_cases hl : D.IsLeaf n
  · rw [approx_leaf D L s κ i hl, Qcal_leaf D hl]
  · rw [approx_nonleaf D L s κ i hl]
    refine foldr_le _ _ (hL n x hl) ?_
    intro c hc
    obtain ⟨i', -, hs, rfl⟩ := mem_cutLists D s κ i n c hc
    unfold Model.agg Model.Qcal
    apply Finset.sum_le_sum
    intro m hm
    exact mul_le_mul_of_nonneg_left (hvalid i' n m hs hm x) (q_nonneg D n m)

/-! ### nodal problems and the forward solution -/

lemma nodalValue_eq_of_opt {n : D.T.Node} {xa : Fin d → ℝ} {ψ : (Fin d → Bool) → ℝ}
    {w : (Fin d → Bool) × (Fin ℓ → ℝ)} (h : D.IsNodalOptimal n xa ψ w) :
    D.nodalValue n xa ψ = D.f n w.1 w.2 + ψ w.1 := by
  unfold Model.nodalValue
  apply IsLeast.csInf_eq
  refine ⟨⟨w, h.1, rfl⟩, ?_⟩
  rintro _ ⟨w', hw', rfl⟩
  exact h.2 w' hw'

lemma feas_nonempty {n : D.T.Node} (hn : n ≠ D.T.root) (xa : Fin d → Bool) :
    (D.feasibleSet n (toReal xa)).Nonempty := by
  obtain ⟨x, y, h⟩ := D.feasible n hn xa
  exact ⟨(x, y), h⟩

lemma feas_nonempty_root : (D.feasibleSet D.T.root D.x0).Nonempty := by
  obtain ⟨x, y, h⟩ := D.feasible_root
  exact ⟨(x, y), h⟩

lemma fwdOf_root (sol : D.Solver) (Ψ : D.T.Node → (Fin d → Bool) → ℝ) :
    D.fwdOf sol Ψ D.T.root = sol D.T.root D.x0 (Ψ D.T.root) := by
  rw [Model.fwdOf, dif_pos rfl]

lemma fwdOf_nonroot (sol : D.Solver) (Ψ : D.T.Node → (Fin d → Bool) → ℝ) {n : D.T.Node}
    (hn : n ≠ D.T.root) :
    D.fwdOf sol Ψ n = sol n (toReal (D.fwdOf sol Ψ (D.T.anc n)).1) (Ψ n) := by
  rw [Model.fwdOf, dif_neg hn]

lemma parentState_root (w : D.TreeSol) : D.parentState w D.T.root = D.x0 := by
  unfold Model.parentState; simp

lemma parentState_nonroot (w : D.TreeSol) {n : D.T.Node} (hn : n ≠ D.T.root) :
    D.parentState w n = toReal (w (D.T.anc n)).1 := by
  unfold Model.parentState; simp [hn]

lemma fwd_opt (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    (Ψ : D.T.Node → (Fin d → Bool) → ℝ) (n : D.T.Node) :
    D.IsNodalOptimal n (D.parentState (D.fwdOf sol Ψ) n) (Ψ n) (D.fwdOf sol Ψ n) := by
  by_cases hn : n = D.T.root
  · subst hn
    rw [parentState_root, fwdOf_root]
    exact hsol _ _ _ (feas_nonempty_root D)
  · rw [parentState_nonroot D _ hn, fwdOf_nonroot D sol Ψ hn]
    exact hsol _ _ _ (feas_nonempty D hn _)

/-! ### Claim 1 -/

lemma sum_p_Qcal (w : D.TreeSol) :
    ∑ n, D.p n * D.Qcal n (w n).1 =
      ∑ n, (if n = D.T.root then 0 else
        D.p n * D.nodalValue n (D.parentState w n) (D.Qcal n)) := by
  have step1 : ∀ n, D.p n * D.Qcal n (w n).1 =
      ∑ m ∈ D.T.children n, D.p m * D.nodalValue m (D.parentState w m) (D.Qcal m) := by
    intro n
    rw [show D.Qcal n (w n).1 = ∑ m ∈ D.T.children n, D.q n m * D.Q m (w n).1 from rfl,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmr := child_ne_root D hm
    have hanc := (mem_children_iff_anc D hmr).1 hm
    rw [parentState_nonroot D w hmr, hanc, ← D.Q_eq, ← mul_assoc]
    congr 1
    unfold Model.q
    field_simp [(D.p_pos n).ne']
  simp_rw [step1]
  rw [Finset.sum_comm' (t' := Finset.univ.filter (fun m => m ≠ D.T.root))
    (s' := fun m => {D.T.anc m})]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : m = D.T.root
    · simp [hm]
    · simp [hm]
  · intro n m
    simp only [Finset.mem_univ, true_and, Finset.mem_singleton, Finset.mem_filter]
    constructor
    · intro h
      have hmr := child_ne_root D h
      exact ⟨((mem_children_iff_anc D hmr).1 h).symm, hmr⟩
    · rintro ⟨h1, h2⟩
      exact (mem_children_iff_anc D h2).2 h1.symm

theorem claim1 {M : ℕ} (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) (hvalid : D.ValidCuts s κ) (i : ℕ)
    (hexact : ∀ n, D.approx L s κ i n (D.forwardSol L sol s κ i n).1 =
      D.Qcal n (D.forwardSol L sol s κ i n).1) :
    D.IsOptimal (D.forwardSol L sol s κ i) := by
  have hopt : ∀ n, D.IsNodalOptimal n (D.parentState (D.forwardSol L sol s κ i) n)
      (D.approx L s κ i n) (D.forwardSol L sol s κ i n) :=
    fwd_opt D sol hsol (D.approx L s κ i)
  set w := D.forwardSol L sol s κ i with hw
  have hfeas : D.IsFeasible w := fun n => (hopt n).1
  have key_le : ∀ w', D.IsFeasible w' → ∀ n,
      D.nodalValue n (D.parentState w' n) (D.Qcal n) ≤
        D.f n (w' n).1 (w' n).2 + D.Qcal n (w' n).1 := by
    intro w' hw' n
    have o := hsol n (D.parentState w' n) (D.Qcal n) ⟨w' n, hw' n⟩
    rw [nodalValue_eq_of_opt D o]
    exact o.2 _ (hw' n)
  have key_eq : ∀ n, D.f n (w n).1 (w n).2 + D.Qcal n (w n).1 =
      D.nodalValue n (D.parentState w n) (D.Qcal n) := by
    intro n
    refine le_antisymm ?_ (key_le w hfeas n)
    have o := hsol n (D.parentState w n) (D.Qcal n) ⟨w n, hfeas n⟩
    rw [nodalValue_eq_of_opt D o, ← hexact n]
    calc D.f n (w n).1 (w n).2 + D.approx L s κ i n (w n).1
        ≤ D.f n (sol n (D.parentState w n) (D.Qcal n)).1 (sol n (D.parentState w n) (D.Qcal n)).2
          + D.approx L s κ i n (sol n (D.parentState w n) (D.Qcal n)).1 := (hopt n).2 _ o.1
      _ ≤ _ := add_le_add_right (approx_le_Qcal D L hL s κ hvalid i n _) _
  have total : ∀ w' : D.TreeSol, D.cost w' - D.nodalValue D.T.root D.x0 (D.Qcal D.T.root) =
      ∑ n, D.p n * (D.f n (w' n).1 (w' n).2 + D.Qcal n (w' n).1 -
        D.nodalValue n (D.parentState w' n) (D.Qcal n)) := by
    intro w'
    have hsplit : ∑ n, D.p n * D.nodalValue n (D.parentState w' n) (D.Qcal n) =
        D.p D.T.root * D.nodalValue D.T.root (D.parentState w' D.T.root) (D.Qcal D.T.root) +
        ∑ n, (if n = D.T.root then 0 else
          D.p n * D.nodalValue n (D.parentState w' n) (D.Qcal n)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ D.T.root)]
      congr 1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ D.T.root), if_pos rfl, zero_add]
      apply Finset.sum_congr rfl
      intro n hn
      rw [if_neg (Finset.ne_of_mem_erase hn)]
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hsplit, sum_p_Qcal D w', D.p_root, parentState_root]
    unfold Model.cost
    ring
  refine ⟨hfeas, fun w' hw' => ?_⟩
  have h1 := total w
  have h2 := total w'
  have h3 : ∑ n, D.p n * (D.f n (w n).1 (w n).2 + D.Qcal n (w n).1 -
      D.nodalValue n (D.parentState w n) (D.Qcal n)) = 0 :=
    Finset.sum_eq_zero (fun n _ => by rw [key_eq n]; ring)
  have h4 : 0 ≤ ∑ n, D.p n * (D.f n (w' n).1 (w' n).2 + D.Qcal n (w' n).1 -
      D.nodalValue n (D.parentState w' n) (D.Qcal n)) :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (D.p_pos n).le (by linarith [key_le w' hw' n]))
  linarith

/-! ### (3.8) -/

theorem eq38 {M : ℕ} (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d)
    (hvalid : D.ValidCuts s κ) (htight : D.TightCuts L sol s κ)
    (i : ℕ) (n : D.T.Node) (hn : D.Sampled (s i) n) (hnl : ¬ D.IsLeaf n)
    (hchild : ∀ m ∈ D.T.children n, D.approx L s κ i m (D.forwardSol L sol s κ i m).1 =
      D.Qcal m (D.forwardSol L sol s κ i m).1) :
    D.approx L s κ (i + 1) n (D.forwardSol L sol s κ i n).1 =
      D.Qcal n (D.forwardSol L sol s κ i n).1 := by
  apply le_antisymm (approx_le_Qcal D L hL s κ hvalid (i + 1) n _)
  refine le_trans ?_ (approx_succ_ge_agg D L s κ i n ⟨hn, hnl⟩ _)
  unfold Model.agg Model.Qcal
  apply Finset.sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_left _ (q_nonneg D n m)
  rw [← htight i n m hn hm]
  have hmr := child_ne_root D hm
  have hanc : D.T.anc m = n := (mem_children_iff_anc D hmr).1 hm
  set x := (D.forwardSol L sol s κ i n).1 with hx
  have hwm : D.forwardSol L sol s κ i m = sol m (toReal x) (D.approx L s κ i m) := by
    show D.fwdOf sol _ m = _
    rw [fwdOf_nonroot D sol _ hmr, hanc]
    rfl
  have hne := feas_nonempty D hmr x
  have o1 := hsol m (toReal x) (D.approx L s κ i m) hne
  have o2 := hsol m (toReal x) (D.approx L s κ (i + 1) m) hne
  have o3 := hsol m (toReal x) (D.Qcal m) hne
  have hc := hchild m hm
  rw [hwm] at hc
  rw [D.Q_eq, nodalValue_eq_of_opt D o2, nodalValue_eq_of_opt D o3]
  calc _ ≤ D.f m (sol m (toReal x) (D.approx L s κ i m)).1
          (sol m (toReal x) (D.approx L s κ i m)).2 +
          D.Qcal m (sol m (toReal x) (D.approx L s κ i m)).1 := o3.2 _ o1.1
    _ = D.f m (sol m (toReal x) (D.approx L s κ i m)).1
          (sol m (toReal x) (D.approx L s κ i m)).2 +
          D.approx L s κ i m (sol m (toReal x) (D.approx L s κ i m)).1 := by rw [hc]
    _ ≤ _ := o1.2 _ o2.1
    _ ≤ _ := add_le_add_right (approx_succ_ge D L s κ i m _) _

/-! ### finitely many changes -/

lemma eventually_const_of_mono_finite (a : ℕ → ℝ) (ha : Monotone a) (V : Finset ℝ)
    (hV : ∀ i, a i ∈ V) : ∃ N, ∀ i ≥ N, a i = a N := by
  classical
  have hne : (V.filter (fun v => ∃ i, a i = v)).Nonempty := ⟨a 0, by simp [hV 0]⟩
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image _ id hne
  obtain ⟨N, hN⟩ := (Finset.mem_filter.1 hv).2
  refine ⟨N, fun i hi => le_antisymm ?_ (ha hi)⟩
  rw [hN]
  exact hmax (a i) (Finset.mem_filter.2 ⟨hV i, i, rfl⟩)

theorem finiteChanges {M : ℕ} (L : D.T.Node → ℝ)
    (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) (hfin : D.FiniteCuts s κ) :
    ∃ i₁, ∀ i ≥ i₁, D.approx L s κ i = D.approx L s κ i₁ := by
  obtain ⟨C, hC⟩ := hfin
  have hpt : ∀ (nx : D.T.Node × (Fin d → Bool)), ∃ N, ∀ i ≥ N,
      D.approx L s κ i nx.1 nx.2 = D.approx L s κ N nx.1 nx.2 := by
    rintro ⟨n, x⟩
    apply eventually_const_of_mono_finite (fun i => D.approx L s κ i n x)
      (monotone_nat_of_le_succ (fun i => approx_succ_ge D L s κ i n x))
      (insert (L n) (insert 0 ((Fintype.piFinset
        (fun m => if m ∈ D.T.children n then C else {0})).image (fun g => D.agg n g x))))
    intro i
    by_cases hl : D.IsLeaf n
    · rw [approx_leaf D L s κ i hl]
      simp
    · rw [approx_nonleaf D L s κ i hl]
      rcases foldr_mem (fun c => D.agg n c x) (D.cutLists s κ i n) (L n) with h | ⟨c, hc, h⟩
      · rw [h]; simp
      · rw [h]
        obtain ⟨i', -, hs, rfl⟩ := mem_cutLists D s κ i n c hc
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_image]
        refine ⟨fun m => if m ∈ D.T.children n then κ i' m else 0, ?_, ?_⟩
        · rw [Fintype.mem_piFinset]
          intro m
          by_cases hm : m ∈ D.T.children n
          · simp only [hm, if_true]; exact hC i' n m hs hm
          · simp [hm]
        · unfold Model.agg
          apply Finset.sum_congr rfl
          intro m hm
          simp [hm]
  choose N hN using hpt
  refine ⟨Finset.univ.sup N, fun i hi => ?_⟩
  funext n x
  have hle : N (n, x) ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ _)
  rw [hN (n, x) i (le_trans hle hi), hN (n, x) _ hle]

/-! ### sampling -/

theorem samplingIO {M : ℕ} (hM : 0 < M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → Fin M → D.Leaf) (hS : D.IsSampling P S) :
    ∀ᵐ ω ∂P, ∀ n : D.Leaf, ∀ j : ℕ, ∃ i ≥ j, ∃ k, S i ω k = n := by
  obtain ⟨hmeas, hind, hdist⟩ := hS
  rw [ae_all_iff]
  intro n
  let k0 : Fin M := ⟨0, hM⟩
  let A : ℕ → Set Ω := fun i => {ω | S i ω k0 = n}
  have hsing : MeasurableSet ({n} : Set D.Leaf) := MeasurableSpace.measurableSet_top
  have hAm : ∀ i, MeasurableSet (A i) := fun i => hmeas i k0 hsing
  have hinj : Function.Injective (fun i : ℕ => (i, k0)) := fun a b h => (Prod.mk.inj h).1
  have hind0 := hind.precomp hinj
  have hind' : iIndepSet A P := by
    rw [iIndepSet_iff_meas_biInter hAm]
    intro t
    exact (iIndepFun_iff_measure_inter_preimage_eq_mul.1 hind0) t
      (sets := fun _ => ({n} : Set D.Leaf)) (fun _ _ => hsing)
  have hsum : ∑' i, P (A i) = ⊤ := by
    have : ∀ i, P (A i) = ENNReal.ofReal (D.p n.1) := fun i => hdist i k0 n
    simp only [this]
    apply ENNReal.tsum_const_eq_top_of_ne_zero
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact D.p_pos n.1
  have h1 := measure_limsup_eq_one hAm hind' hsum
  have hae : ∀ᵐ ω ∂P, ω ∈ limsup A atTop := by
    rw [ae_mem_iff_measure_eq (MeasurableSet.measurableSet_limsup hAm).nullMeasurableSet, h1, measure_univ]
  filter_upwards [hae] with ω hω
  rw [Filter.mem_limsup_iff_frequently_mem, frequently_atTop] at hω
  intro j
  obtain ⟨i, hi, h⟩ := hω j
  exact ⟨i, hi, k0, h⟩

/-! ### Claim 2 and Theorem 2 -/

lemma stage_iter (x : D.T.Node) : ∀ j ≤ (D.T.stage x).val,
    (D.T.stage ((D.T.anc)^[j] x)).val + j = (D.T.stage x).val := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    rw [Function.iterate_succ_apply']
    have h2 := D.T.anc_stage ((D.T.anc)^[j] x) (by omega)
    omega

lemma exists_leaf_below : ∀ n : D.T.Node, ∃ ℓ' : D.Leaf, D.OnPath ℓ' n := by
  apply tree_induction D
  intro n ih
  by_cases hl : D.IsLeaf n
  · exact ⟨⟨n, hl⟩, 0, Nat.zero_le _, rfl⟩
  · have hlt : (D.T.stage n).val + 1 < H := by
      have := (D.T.stage n).isLt; unfold Model.IsLeaf at hl; omega
    have hsum := D.p_children n hlt
    have hne : (D.T.children n).Nonempty := by
      apply Finset.nonempty_of_sum_ne_zero (f := D.p)
      rw [← hsum]; exact (D.p_pos n).ne'
    obtain ⟨m, hm⟩ := hne
    obtain ⟨ℓ', j, hj, hjm⟩ := ih m hm
    have hst := stage_iter D ℓ'.1 j hj
    rw [hjm] at hst
    have hm' := (mem_children D).1 hm
    refine ⟨ℓ', j + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply', hjm, hm'.2]

theorem claim2 {M : ℕ} (hM : 0 < M) (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → Fin M → D.Leaf) (hS : D.IsSampling P S)
    (κ : Ω → ℕ → D.T.Node → Cut d)
    (hvalid : ∀ ω, D.ValidCuts (fun i => S i ω) (κ ω))
    (htight : ∀ ω, D.TightCuts L sol (fun i => S i ω) (κ ω))
    (hfin : ∀ ω, D.FiniteCuts (fun i => S i ω) (κ ω)) :
    ∀ᵐ ω ∂P, ∀ j : ℕ,
      (∀ i ≥ j, D.approx L (fun i => S i ω) (κ ω) i = D.approx L (fun i => S i ω) (κ ω) j) →
        D.IsOptimal (D.forwardSol L sol (fun i => S i ω) (κ ω) j) := by
  filter_upwards [samplingIO D hM P S hS] with ω hω
  intro j hconst
  have hfwd : ∀ i ≥ j, D.forwardSol L sol (fun i => S i ω) (κ ω) i =
      D.forwardSol L sol (fun i => S i ω) (κ ω) j := by
    intro i hi
    unfold Model.forwardSol
    rw [hconst i hi]
  apply claim1 D L hL sol hsol (fun i => S i ω) (κ ω) (hvalid ω) j
  apply tree_induction D
  intro n ih
  by_cases hl : D.IsLeaf n
  · rw [approx_leaf D L _ _ j hl, Qcal_leaf D hl]
  · obtain ⟨ℓ', hpath⟩ := exists_leaf_below D n
    obtain ⟨i, hi, k, hk⟩ := hω ℓ' j
    have hsamp : D.Sampled ((fun i => S i ω) i) n := ⟨k, by simp only; rw [hk]; exact hpath⟩
    have h := eq38 D L hL sol hsol (fun i => S i ω) (κ ω) (hvalid ω) (htight ω) i n hsamp hl
      (by intro m hm; rw [hconst i hi, hfwd i hi]; exact ih m hm)
    rw [hconst (i + 1) (by omega), hfwd i hi] at h
    exact h

theorem theorem2 {M : ℕ} (hM : 0 < M) (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → Fin M → D.Leaf) (hS : D.IsSampling P S)
    (κ : Ω → ℕ → D.T.Node → Cut d)
    (hvalid : ∀ ω, D.ValidCuts (fun i => S i ω) (κ ω))
    (htight : ∀ ω, D.TightCuts L sol (fun i => S i ω) (κ ω))
    (hfin : ∀ ω, D.FiniteCuts (fun i => S i ω) (κ ω)) :
    ∀ᵐ ω ∂P, ∀ᶠ i in atTop, D.IsOptimal (D.forwardSol L sol (fun i => S i ω) (κ ω) i) := by
  filter_upwards [claim2 D hM L hL sol hsol P S hS κ hvalid htight hfin] with ω hω
  obtain ⟨i₁, hi₁⟩ := finiteChanges D L (fun i => S i ω) (κ ω) (hfin ω)
  rw [eventually_atTop]
  refine ⟨i₁, fun i hi => hω i (fun k hk => ?_)⟩
  rw [hi₁ k (le_trans hi hk), hi₁ i hi]

/-! ### Under-approximation, part 2 -/

theorem underApprox {M : ℕ} (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) (hvalid : D.ValidCuts s κ)
    (i : ℕ) (n : D.T.Node) :
    (∀ x, D.approx L s κ i n x ≤ D.Qcal n x) ∧
      ∀ xa : Fin d → Bool, D.nodalValue n (toReal xa) (D.approx L s κ i n) ≤ D.Q n xa := by
  refine ⟨approx_le_Qcal D L hL s κ hvalid i n, fun xa => ?_⟩
  rw [D.Q_eq]
  by_cases hne : (D.feasibleSet n (toReal xa)).Nonempty
  · have hbdd : BddBelow ((fun w => D.f n w.1 w.2 + D.approx L s κ i n w.1) ''
        D.feasibleSet n (toReal xa)) := by
      obtain ⟨b, hb⟩ := (Set.finite_range (D.approx L s κ i n)).bddBelow
      let g : (Fin d → ℝ) × (Fin d → ℝ) × (Fin ℓ → ℝ) → ℝ :=
        fun z => ∑ j, D.c n j * z.2.1 j + ∑ j, D.e n j * z.2.2 j
      have hg : Continuous g := by fun_prop
      obtain ⟨a, ha⟩ := (D.X_compact n).bddBelow_image hg.continuousOn
      refine ⟨a + b, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      have h1 : a ≤ g (toReal xa, toReal w.1, w.2) := ha ⟨_, hw, rfl⟩
      have h2 : b ≤ D.approx L s κ i n w.1 := hb ⟨w.1, rfl⟩
      have h3 : g (toReal xa, toReal w.1, w.2) = D.f n w.1 w.2 := rfl
      simp only
      linarith
    unfold Model.nodalValue
    apply le_csInf (hne.image _)
    rintro _ ⟨w, hw, rfl⟩
    refine le_trans (csInf_le hbdd ⟨w, hw, rfl⟩) ?_
    exact add_le_add_right (approx_le_Qcal D L hL s κ hvalid i n w.1) _
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [Model.nodalValue, hne]

end SDDiP1Aux

open SDDiP.Conv StochasticProg.Multistage MeasureTheory Filter

theorem solution {H d ℓ M : ℕ} (D : Model H d ℓ) (L : D.T.Node → ℝ)
    (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) (hfin : D.FiniteCuts s κ) :
    ∃ i₁, ∀ i ≥ i₁, D.approx L s κ i = D.approx L s κ i₁ := by
  exact SDDiP1Aux.finiteChanges D L s κ hfin
