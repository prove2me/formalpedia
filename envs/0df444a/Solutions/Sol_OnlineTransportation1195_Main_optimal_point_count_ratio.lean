-- Prove2me | solution 1 for OnlineTransportation1195.Main.optimal_point_count_ratio
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T18:12:19.392852+00:00
-- url     : https://prove2.me/submissions/e53399ee-579e-4534-865d-951d9bee4db3

import Theorems.Thm_OnlineTransportation1195_Main_normalized_downward_deadlines
import Definitions.Def_OnlineTransportation1195_Main_OnlinePolicy

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
/-!
Blueprint for Theorem 1.2 (`optimal_point_count_ratio`), q419.
Every `sorry` below is a stub proved in a Part file.
-/
/-! ## Walk lengths and threshold connectivity -/
/-- Metric length of the first `j` steps of the list `L` (default vertex `x`). -/
noncomputable def wlen (D : Fin n → Fin n → ℝ) (L : List (Fin n)) (x : Fin n) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, D (L.getD i x) (L.getD (i + 1) x)

/-- `a` and `b` are joined by a chain of hops of length at most `h`. -/
def Conn (D : Fin n → Fin n → ℝ) (h : ℝ) (a b : Fin n) : Prop :=
  Relation.ReflTransGen (fun x y => D x y ≤ h) a b

/-- Metric axioms for a distance function on `Fin n`. -/
structure IsMetric (D : Fin n → Fin n → ℝ) : Prop where
  nonneg : ∀ a b, 0 ≤ D a b
  self : ∀ a, D a a = 0
  pos : ∀ a b, a ≠ b → 0 < D a b
  symm : ∀ a b, D a b = D b a
  tri : ∀ a b c, D a c ≤ D a b + D b c

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartW
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
theorem conn_mono {D : Fin n → Fin n → ℝ} {h h' : ℝ} (hh : h ≤ h') {a b : Fin n}
    (H : Conn D h a b) : Conn D h' a b :=
  Relation.ReflTransGen.mono (fun _ _ hxy => le_trans hxy hh) _ _ H

/-- The minimax (bottleneck) distance. -/
theorem exists_pr (D : Fin n → Fin n → ℝ) (hD : IsMetric D) :
    ∃ pr : Fin n → Fin n → ℝ, ∀ a b (h : ℝ), 0 ≤ h → (Conn D h a b ↔ pr a b ≤ h) := by
  let S : Finset ℝ := insert 0 (Finset.univ.image (fun p : Fin n × Fin n => D p.1 p.2))
  have hS0 : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have hSD : ∀ x y, D x y ∈ S := fun x y =>
    Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(x, y), Finset.mem_univ _, rfl⟩)
  have hSne : S.Nonempty := ⟨0, hS0⟩
  have hC : ∀ a b, (S.filter (fun h => Conn D h a b)).Nonempty := by
    intro a b
    refine ⟨S.max' hSne, Finset.mem_filter.2 ⟨S.max'_mem hSne, ?_⟩⟩
    exact Relation.ReflTransGen.single (S.le_max' _ (hSD a b))
  refine ⟨fun a b => (S.filter (fun h => Conn D h a b)).min' (hC a b), ?_⟩
  intro a b h hh
  constructor
  · intro H
    have hT : (S.filter (· ≤ h)).Nonempty := ⟨0, Finset.mem_filter.2 ⟨hS0, hh⟩⟩
    set h' := (S.filter (· ≤ h)).max' hT with hh'
    have hmem := Finset.mem_filter.1 ((S.filter (· ≤ h)).max'_mem hT)
    have H' : Conn D h' a b := by
      refine Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ H
      exact (S.filter (· ≤ h)).le_max' _ (Finset.mem_filter.2 ⟨hSD x y, hxy⟩)
    exact le_trans (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hmem.1, H'⟩)) hmem.2
  · intro hle
    have := Finset.mem_filter.1 ((S.filter (fun h => Conn D h a b)).min'_mem (hC a b))
    exact conn_mono hle this.2

end OnlineTransportation1195.Dev.T12.PartW
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartW
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
variable (T : Tree n)
/-! ## Generic tree accounting -/
noncomputable def phi (v : Fin n) : ℝ :=
  ∑ i ∈ Finset.range (T.depth v), T.W (T.parent^[i] v)

theorem phi_root : phi T T.root = 0 := by
  simp [phi, T.depth_root]

theorem phi_parent (v : Fin n) (hv : v ≠ T.root) : phi T v = T.W v + phi T (T.parent v) := by
  unfold phi
  rw [← T.depth_parent v hv, Finset.sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id]
  ring

theorem phi_nonneg (hW0 : ∀ v, 0 ≤ T.W v) (v : Fin n) : 0 ≤ phi T v :=
  Finset.sum_nonneg (fun _ _ => hW0 _)

theorem step_identity (a c : Fin n) (hac : T.Adj a c) :
    T.totalStep a c = 2 * T.downStep a c - (phi T c - phi T a) := by
  unfold Tree.totalStep Tree.downStep
  by_cases h1 : c ≠ T.root ∧ T.parent c = a
  · rw [if_pos h1, if_pos h1, phi_parent T c h1.1, h1.2]; ring
  · have h2 : a ≠ T.root ∧ T.parent a = c := by
      rcases hac with h | h
      · exact absurd h h1
      · exact h
    rw [if_neg h1, if_neg h1, if_pos h2, phi_parent T a h2.1, h2.2]; ring

theorem vertexAt_zero (L : List (Fin n)) (hL : L.head? = some T.root) :
    T.vertexAt L 0 = T.root := by
  unfold Tree.vertexAt
  cases L with
  | nil => simp at hL
  | cons x xs => simp at hL; simp [hL]

theorem totalPrefix_eq (L : List (Fin n)) (hL : T.Walk L) (i : ℕ) (hi : i + 1 < L.length) :
    T.totalPrefix L i = 2 * T.downPrefix L i - phi T (T.vertexAt L (i + 1)) := by
  induction i with
  | zero =>
    simp only [Tree.totalPrefix, Tree.downPrefix, zero_add, Finset.sum_range_one]
    rw [step_identity T _ _ (hL.2 0 hi), vertexAt_zero T L hL.1, phi_root]
    simp only [zero_add, sub_zero]
  | succ i ih =>
    have hi' : i + 1 < L.length := by omega
    have e1 : T.totalPrefix L (i + 1) = T.totalPrefix L i +
        T.totalStep (T.vertexAt L (i + 1)) (T.vertexAt L (i + 1 + 1)) :=
      Finset.sum_range_succ _ _
    have e2 : T.downPrefix L (i + 1) = T.downPrefix L i +
        T.downStep (T.vertexAt L (i + 1)) (T.vertexAt L (i + 1 + 1)) :=
      Finset.sum_range_succ _ _
    rw [e1, e2, ih hi', step_identity T _ _ (hL.2 (i + 1) hi)]
    ring

theorem isAnc_iff (x v : Fin n) :
    T.IsAnc x v ↔ x = v ∨ T.IsAnc x (T.parent v) := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | zero => left; simpa using hi.symm
    | succ i => right; exact ⟨i, by rwa [Function.iterate_succ_apply] at hi⟩
  · rintro (h | ⟨i, hi⟩)
    · exact ⟨0, by simp [h]⟩
    · exact ⟨i + 1, by rwa [Function.iterate_succ_apply]⟩

theorem isAnc_of_parent (x v : Fin n) (h : T.IsAnc x (T.parent v)) : T.IsAnc x v := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i + 1, by rwa [Function.iterate_succ_apply]⟩

theorem not_isAnc_root (u : Fin n) (hu : u ≠ T.root) : ¬ T.IsAnc u T.root := by
  rintro ⟨i, hi⟩
  have key : ∀ k : ℕ, T.parent^[k] T.root = T.root := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, T.parent_root]
  exact hu (hi ▸ key i)

/-- Before the first crossing of edge `u`, the walk stays outside the subtree of `u`. -/
theorem outside_subtree (L : List (Fin n)) (hL : T.Walk L) (u : Fin n) (hu : u ≠ T.root)
    (i : ℕ) (hfirst : ∀ j, j < i → ¬ T.CrossAt L u j) (hi : i < L.length) :
    ¬ T.IsAnc u (T.vertexAt L i) := by
  induction i with
  | zero => rw [vertexAt_zero T L hL.1]; exact not_isAnc_root T u hu
  | succ m ih =>
    have ihm := ih (fun j hj => hfirst j (by omega)) (by omega)
    have hadj := hL.2 m hi
    intro hA
    rcases hadj with ⟨hc, hp⟩ | ⟨ha, hp⟩
    · rcases (isAnc_iff T u _).1 hA with h | h
      · exact hfirst m (by omega) (Or.inl ⟨hu, hi, by rw [← hp, ← h], h.symm⟩)
      · rw [hp] at h; exact ihm h
    · rw [← hp] at hA
      exact ihm (isAnc_of_parent T _ _ hA)

/-- The walk bound for a tree walk with deadlines `c · W`. -/
theorem walk_bound (D : Fin n → Fin n → ℝ) (hsymm : ∀ a b, D a b = D b a)
    (hWD : ∀ v, v ≠ T.root → D (T.parent v) v ≤ T.W v) (hW0 : ∀ v, 0 ≤ T.W v)
    (L : List (Fin n)) (c : ℝ) (hL : T.DownDeadlines L (fun e => c * T.W e))
    (u : Fin n) (hu : u ≠ T.root) :
    ∃ j < L.length, L.getD j T.root = u ∧
      wlen D L T.root j ≤ (2 * c - 1) * T.W u := by
  have hue : u ∈ T.edges := Finset.mem_erase.2 ⟨hu, Finset.mem_univ _⟩
  obtain ⟨i, ⟨hcross, hfirst⟩, hdl⟩ := hL.2.2 u hue
  have hdown : T.DownAt L u i := by
    rcases hcross with h | h
    · exact h
    · exfalso
      have := outside_subtree T L hL.1 u hu i hfirst (by have := h.2.1; omega)
      exact this (by rw [h.2.2.1]; exact ⟨0, rfl⟩)
  obtain ⟨-, hi, -, hv⟩ := hdown
  refine ⟨i + 1, hi, hv, ?_⟩
  have hw : wlen D L T.root (i + 1) ≤ T.totalPrefix L i := by
    unfold wlen Tree.totalPrefix
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm' : m + 1 < L.length := by have := Finset.mem_range.1 hm; omega
    have hadj := hL.1.2 m hm'
    change D (T.vertexAt L m) (T.vertexAt L (m + 1)) ≤ _
    unfold Tree.totalStep
    by_cases h1 : T.vertexAt L (m + 1) ≠ T.root ∧ T.parent (T.vertexAt L (m + 1)) = T.vertexAt L m
    · rw [if_pos h1]
      have := hWD _ h1.1; rw [h1.2] at this; exact this
    · have h2 : T.vertexAt L m ≠ T.root ∧ T.parent (T.vertexAt L m) = T.vertexAt L (m + 1) := by
        rcases hadj with h | h
        · exact absurd h h1
        · exact h
      rw [if_neg h1, if_pos h2, hsymm]
      have := hWD _ h2.1; rw [h2.2] at this; exact this
  rw [totalPrefix_eq T L hL.1 i hi] at hw
  change T.vertexAt L (i + 1) = u at hv
  rw [hv, phi_parent T u hu] at hw
  have := phi_nonneg T hW0 (T.parent u)
  linarith

end OnlineTransportation1195.Dev.T12.PartW
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartW
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
/-! ## The bottleneck tree -/
/-- Hypotheses on a bottleneck-distance function `b` from the root `r`. -/
structure Bot (D : Fin n → Fin n → ℝ) (r : Fin n) (b : Fin n → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ b v
  conn : ∀ v, Conn D (b v) r v
  least : ∀ v (h : ℝ), 0 ≤ h → Conn D h r v → b v ≤ h
  pos : ∀ v, v ≠ r → 0 < b v

/-- Chains of exactly `m` hops of length at most `h`. -/
def chainN (D : Fin n → Fin n → ℝ) (h : ℝ) : ℕ → Fin n → Fin n → Prop
  | 0, a, c => a = c
  | m + 1, a, c => ∃ p, chainN D h m a p ∧ D p c ≤ h

theorem chainN_of_conn (D : Fin n → Fin n → ℝ) (h : ℝ) (a c : Fin n) (H : Conn D h a c) :
    ∃ m, chainN D h m a c := by
  induction H with
  | refl => exact ⟨0, rfl⟩
  | tail _ hyz ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + 1, _, hm, hyz⟩

theorem conn_of_chainN (D : Fin n → Fin n → ℝ) (h : ℝ) (a : Fin n) :
    ∀ m c, chainN D h m a c → Conn D h a c := by
  intro m
  induction m with
  | zero => intro c hc; cases hc; exact Relation.ReflTransGen.refl
  | succ m ih =>
    rintro c ⟨p, hp, hpc⟩
    exact Relation.ReflTransGen.tail (ih p hp) hpc

end OnlineTransportation1195.Dev.T12.PartW
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartW
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
variable {D : Fin n → Fin n → ℝ} {r : Fin n} {b : Fin n → ℝ}
noncomputable def kOf (hB : Bot D r b) (v : Fin n) : ℕ :=
  Nat.find (chainN_of_conn D (b v) r v (hB.conn v))

def Rel (hB : Bot D r b) (u v : Fin n) : Prop :=
  b u < b v ∨ (b u = b v ∧ kOf hB u < kOf hB v)

theorem exists_par (hB : Bot D r b) (v : Fin n) (hv : v ≠ r) :
    ∃ p, D p v ≤ b v ∧ Rel hB p v := by
  have hspec := Nat.find_spec (chainN_of_conn D (b v) r v (hB.conn v))
  have hk : kOf hB v ≠ 0 := by
    intro h0
    unfold kOf at h0
    rw [h0] at hspec
    exact hv hspec.symm
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk
  unfold kOf at hm
  rw [hm] at hspec
  obtain ⟨p, hp, hpv⟩ := hspec
  refine ⟨p, hpv, ?_⟩
  have hbp : b p ≤ b v := hB.least p (b v) (hB.nonneg v) (conn_of_chainN D _ r m p hp)
  rcases lt_or_eq_of_le hbp with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    have : kOf hB p ≤ m := by
      unfold kOf
      exact Nat.find_min' _ (by rw [heq]; exact hp)
    unfold kOf at this ⊢
    omega

noncomputable def par (hB : Bot D r b) (v : Fin n) : Fin n :=
  if hv : v = r then r else Classical.choose (exists_par hB v hv)

theorem par_spec (hB : Bot D r b) (v : Fin n) (hv : v ≠ r) :
    D (par hB v) v ≤ b v ∧ Rel hB (par hB v) v := by
  unfold par
  rw [dif_neg hv]
  exact Classical.choose_spec (exists_par hB v hv)

theorem par_le (hB : Bot D r b) (v : Fin n) : b (par hB v) ≤ b v := by
  by_cases hv : v = r
  · unfold par; rw [dif_pos hv, hv]
  · rcases (par_spec hB v hv).2 with h | h
    · exact h.le
    · exact h.1.le

theorem rel_wf (hB : Bot D r b) : WellFounded (Rel hB) := by
  have : IsTrans (Fin n) (Rel hB) := ⟨fun x y z hxy hyz => by
    unfold Rel at *
    rcases hxy with h1 | ⟨h1, h1'⟩ <;> rcases hyz with h2 | ⟨h2, h2'⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (h2 ▸ h1)
    · exact Or.inl (h1 ▸ h2)
    · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩⟩
  have : Std.Irrefl (Rel hB) := ⟨fun x hx => by
    unfold Rel at hx
    rcases hx with h | ⟨_, h⟩
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

theorem reach (hB : Bot D r b) (v : Fin n) : ∃ i, (par hB)^[i] v = r := by
  induction v using (rel_wf hB).induction with
  | _ v ih =>
    by_cases hv : v = r
    · exact ⟨0, hv⟩
    · obtain ⟨i, hi⟩ := ih (par hB v) (par_spec hB v hv).2
      exact ⟨i + 1, by rwa [Function.iterate_succ_apply]⟩

noncomputable def dep (hB : Bot D r b) (v : Fin n) : ℕ := Nat.find (reach hB v)

theorem dep_parent (hB : Bot D r b) (v : Fin n) (hv : v ≠ r) :
    dep hB (par hB v) + 1 = dep hB v := by
  apply le_antisymm
  · have hs := Nat.find_spec (reach hB v)
    change (par hB)^[dep hB v] v = r at hs
    obtain ⟨j, hj⟩ : ∃ j, dep hB v = j + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero (fun h0 => hv ?_)
      rw [h0] at hs; exact hs
    rw [hj] at hs ⊢
    rw [Function.iterate_succ_apply] at hs
    have : dep hB (par hB v) ≤ j := Nat.find_min' _ hs
    omega
  · have hs := Nat.find_spec (reach hB (par hB v))
    change (par hB)^[dep hB (par hB v)] (par hB v) = r at hs
    exact Nat.find_min' _ (by rw [Function.iterate_succ_apply]; exact hs)

/-- The bottleneck tree with path-maximum (= bottleneck) weights. -/
noncomputable def botTree (hB : Bot D r b) : Tree n where
  root := r
  parent := par hB
  depth := dep hB
  parent_root := by unfold par; simp
  depth_root := by
    unfold dep
    rw [Nat.find_eq_zero]
    rfl
  depth_parent := dep_parent hB
  W := b
  W_pos := hB.pos

theorem botTree_anc (hB : Bot D r b) (a c : Fin n) (h : (botTree hB).IsAnc a c) : b a ≤ b c := by
  obtain ⟨i, rfl⟩ := h
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (par_le hB _).trans ih

end OnlineTransportation1195.Dev.T12.PartW
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartW
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
theorem conn_zero (D : Fin n → Fin n → ℝ) (hD : IsMetric D) (a c : Fin n) (H : Conn D 0 a c) :
    a = c := by
  induction H with
  | refl => rfl
  | tail _ hyz ih =>
    rw [ih]
    by_contra hne
    exact absurd hyz (not_le.2 (hD.pos _ _ hne))

/-- For every root `r` there is a walk from `r` reaching every `u` that is `h`-connected to `r`
within metric length `(2n-3) h`. (Prim tree rooted at `r` with path-maximum weights, Theorem 3.1
with deadlines `(n-1) w`, and the down/up accounting of the paper's proof of Theorem 1.3.) -/
theorem walks_exist (hn : 2 ≤ n) (D : Fin n → Fin n → ℝ) (hD : IsMetric D) (r : Fin n) :
    ∃ L : List (Fin n), L.head? = some r ∧
      ∀ (u : Fin n) (h : ℝ), 0 ≤ h → Conn D h r u →
        ∃ j < L.length, L.getD j r = u ∧ wlen D L r j ≤ (2 * (n : ℝ) - 3) * h := by
  obtain ⟨pr, hpr⟩ := exists_pr D hD
  set b : Fin n → ℝ := fun v => max (pr r v) 0 with hb
  have hB : Bot D r b := by
    refine ⟨fun v => le_max_right _ _, fun v => ?_, fun v h hh H => ?_, fun v hv => ?_⟩
    · exact (hpr r v _ (le_max_right _ _)).2 (le_max_left _ _)
    · exact max_le ((hpr r v h hh).1 H) hh
    · rcases lt_or_eq_of_le (le_max_right (pr r v) 0) with h | h
      · exact h
      · exfalso
        have H := (hpr r v (b v) (le_max_right _ _)).2 (le_max_left _ _)
        change Conn D (max (pr r v) 0) r v at H
        rw [← h] at H
        exact hv (conn_zero D hD r v H).symm
  set T := botTree hB with hT
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnorm : T.Normalized (fun e => ((n : ℝ) - 1) * T.W e) := by
    refine ⟨fun e he => mul_pos hn1 (T.W_pos e (Finset.mem_erase.1 he).1), ?_, ?_⟩
    · intro a _ c _ hac
      exact mul_le_mul_of_nonneg_left (botTree_anc hB a c hac) hn1.le
    · have hcard : (T.edges.card : ℝ) = (n : ℝ) - 1 := by
        unfold Tree.edges
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
          Nat.cast_sub (by omega)]
        simp
      have : ∀ e ∈ T.edges, T.W e / (((n : ℝ) - 1) * T.W e) = 1 / ((n : ℝ) - 1) := by
        intro e he
        have := T.W_pos e (Finset.mem_erase.1 he).1
        field_simp
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard]
      field_simp
  obtain ⟨L, hL⟩ := normalized_downward_deadlines T _ hnorm
  refine ⟨L, hL.1.1, ?_⟩
  intro u h hh H
  by_cases hu : u = r
  · subst hu
    have hlen : 0 < L.length := by
      cases L with
      | nil => exact absurd hL.1.1 (by simp)
      | cons _ _ => simp
    refine ⟨0, hlen, vertexAt_zero T L hL.1.1, ?_⟩
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [wlen, Finset.range_zero, Finset.sum_empty]
    nlinarith
  · obtain ⟨j, hj, hjv, hjw⟩ := walk_bound T D hD.symm
      (fun v hv => (par_spec hB v hv).1) hB.nonneg L _ hL u hu
    refine ⟨j, hj, hjv, hjw.trans ?_⟩
    have hbu : T.W u ≤ h := hB.least u h hh H
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have e : 2 * ((n : ℝ) - 1) - 1 = 2 * (n : ℝ) - 3 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hbu (by linarith)

end OnlineTransportation1195.Dev.T12.PartW
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
/-! ## Part W: walks with deadlines from Theorem 3.1 -/
alias walks_exist := OnlineTransportation1195.Dev.T12.PartW.walks_exist

alias exists_pr := OnlineTransportation1195.Dev.T12.PartW.exists_pr

/-! ## The itinerant-car process -/
/-- The data the process runs on. -/
structure Setup (n : ℕ) where
  D : Fin n → Fin n → ℝ
  G : Finset (Fin n)
  cap : Fin n → ℕ
  W : Fin n → List (Fin n)
  pr : Fin n → Fin n → ℝ
  o : Fin n

/-- A state: each label's position on its walk, and where it is parked. Labels are arrival
indices. -/
structure St (n : ℕ) where
  pos : ℕ → ℕ
  park : ℕ → Option (Fin n)

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
namespace Setup
variable (S : Setup n) (arr : List (Fin n))
def origin (ℓ : ℕ) : Fin n := arr.getD ℓ S.o

def walkOf (ℓ : ℕ) : List (Fin n) := S.W (S.origin arr ℓ)

/-- The current vertex of label `ℓ`. -/
def loc (s : St n) (ℓ : ℕ) : Fin n := (S.walkOf arr ℓ).getD (s.pos ℓ) (S.origin arr ℓ)

/-- The `j`-th vertex of label `ℓ`'s walk. -/
def vtx (ℓ j : ℕ) : Fin n := (S.walkOf arr ℓ).getD j (S.origin arr ℓ)

/-- Metric length driven by label `ℓ` so far. -/
noncomputable def plen (s : St n) (ℓ : ℕ) : ℝ :=
  wlen S.D (S.walkOf arr ℓ) (S.origin arr ℓ) (s.pos ℓ)

noncomputable def occupants (s : St n) (g : Fin n) : Finset ℕ :=
  (Finset.range arr.length).filter (fun ℓ => s.park ℓ = some g)

/-- An occupant of `g` with the largest priority, if any. -/
noncomputable def best (s : St n) (g : Fin n) : Option ℕ :=
  if h : (Setup.occupants arr s g).Nonempty then
    some (Classical.choose ((Setup.occupants arr s g).exists_max_image
      (fun b => S.pr (S.origin arr b) g) h))
  else none

/-- One move of the active label `a`: park (`inl g`) or hand over to the next active label. -/
noncomputable def step (s : St n) (a : ℕ) : St n × (Fin n ⊕ ℕ) :=
  let v := S.loc arr s a
  let adv : St n := ⟨Function.update s.pos a (s.pos a + 1), s.park⟩
  if v ∈ S.G then
    if (Setup.occupants arr s v).card < S.cap v then
      (⟨s.pos, Function.update s.park a (some v)⟩, Sum.inl v)
    else
      match S.best arr s v with
      | some b =>
        if S.pr (S.origin arr a) v < S.pr (S.origin arr b) v then
          (⟨Function.update s.pos b (s.pos b + 1),
            Function.update (Function.update s.park b none) a (some v)⟩, Sum.inr b)
        else (adv, Sum.inr a)
      | none => (adv, Sum.inr a)
  else (adv, Sum.inr a)

noncomputable def loop : ℕ → St n → ℕ → St n × Option (Fin n)
  | 0, s, _ => (s, none)
  | f + 1, s, a =>
    match S.step arr s a with
    | (s', Sum.inl g) => (s', some g)
    | (s', Sum.inr b) => loop f s' b

noncomputable def fuelOf : ℕ :=
  (arr.length + 1) * ((Finset.univ.sup fun u => (S.W u).length) + 1) + 1

/-- The state after the first `t` cars have been inserted. -/
noncomputable def stAfter : ℕ → St n
  | 0 => ⟨fun _ => 0, fun _ => none⟩
  | t + 1 => (S.loop arr (S.fuelOf arr) (stAfter t) t).1

/-- The garage where the physical car `t` ends: where the eviction chain of its insertion stops. -/
noncomputable def choice (t : ℕ) : Fin n :=
  ((S.loop arr (S.fuelOf arr) (S.stAfter arr t) t).2).getD S.o

/-- Total distance driven by all labels in state `s`. -/
noncomputable def Phi (s : St n) : ℝ := ∑ ℓ ∈ Finset.range arr.length, S.plen arr s ℓ

end Setup
end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
/-- Standing hypotheses on the setup. -/
structure Good (S : Setup n) (arr : List (Fin n)) : Prop where
  metric : IsMetric S.D
  head : ∀ u, (S.W u).head? = some u
  cover : ∀ u v, ∃ j < (S.W u).length, (S.W u).getD j u = v
  total : ∑ g ∈ S.G, S.cap g = arr.length

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartP
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
theorem Phi_zero {n : ℕ} (S : Setup n) (arr : List (Fin n)) : S.Phi arr (S.stAfter arr 0) = 0 := by
  simp [Setup.Phi, Setup.plen, Setup.stAfter, wlen]

end OnlineTransportation1195.Dev.T12.PartP
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartQ
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
/-- Only labels `≤ t` are parked. -/
def Inv (t : ℕ) (s : St n) : Prop := ∀ (ℓ : ℕ) (g : Fin n), s.park ℓ = some g → ℓ ≤ t

lemma choose_congr' {α : Type} {p q : α → Prop} (hpq : p = q) (hp : ∃ x, p x) (hq : ∃ x, q x) :
    Classical.choose hp = Classical.choose hq := by
  subst hpq; rfl

lemma occupants_eq (arr arr' : List (Fin n)) (hlen : arr.length = arr'.length) (s : St n)
    (g : Fin n) : Setup.occupants arr s g = Setup.occupants arr' s g := by
  simp only [Setup.occupants, hlen]

lemma mem_occupants {arr : List (Fin n)} {s : St n} {g : Fin n} {b : ℕ}
    (hb : b ∈ Setup.occupants arr s g) : s.park b = some g := by
  simp only [Setup.occupants, Finset.mem_filter] at hb
  exact hb.2

lemma best_mem (S : Setup n) (arr : List (Fin n)) (s : St n) (g : Fin n) (b : ℕ)
    (hb : S.best arr s g = some b) : b ∈ Setup.occupants arr s g := by
  unfold Setup.best at hb
  split_ifs at hb with h
  · cases hb
    exact (Classical.choose_spec ((Setup.occupants arr s g).exists_max_image
      (fun b => S.pr (S.origin arr b) g) h)).1

end OnlineTransportation1195.Dev.T12.PartQ
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartQ
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
variable (S : Setup n) (arr arr' : List (Fin n)) (hlen : arr.length = arr'.length) (t : ℕ)
  (hagree : ∀ j ≤ t, arr.getD j S.o = arr'.getD j S.o)
include hagree in
lemma origin_eq {j : ℕ} (hj : j ≤ t) : S.origin arr j = S.origin arr' j := hagree j hj

include hlen hagree in
lemma best_eq (s : St n) (hs : Inv t s) (g : Fin n) : S.best arr s g = S.best arr' s g := by
  have hocc := occupants_eq arr arr' hlen s g
  unfold Setup.best
  by_cases h : (Setup.occupants arr s g).Nonempty
  · have h' : (Setup.occupants arr' s g).Nonempty := hocc ▸ h
    rw [dif_pos h, dif_pos h']
    congr 1
    apply choose_congr'
    funext x
    apply propext
    rw [hocc]
    constructor
    · rintro ⟨hx, hmax⟩
      refine ⟨hx, fun y hy => ?_⟩
      have := hmax y hy
      rwa [origin_eq S arr arr' t hagree (hs y g (mem_occupants hy)),
        origin_eq S arr arr' t hagree (hs x g (mem_occupants hx))] at this
    · rintro ⟨hx, hmax⟩
      refine ⟨hx, fun y hy => ?_⟩
      have := hmax y hy
      rwa [← origin_eq S arr arr' t hagree (hs y g (mem_occupants hy)),
        ← origin_eq S arr arr' t hagree (hs x g (mem_occupants hx))] at this
  · have h' : ¬ (Setup.occupants arr' s g).Nonempty := hocc ▸ h
    rw [dif_neg h, dif_neg h']

include hlen hagree in
lemma step_eq (s : St n) (hs : Inv t s) (a : ℕ) (ha : a ≤ t) :
    S.step arr s a = S.step arr' s a := by
  have hloc : S.loc arr s a = S.loc arr' s a := by
    simp only [Setup.loc, Setup.walkOf, origin_eq S arr arr' t hagree ha]
  have hbest := best_eq S arr arr' hlen t hagree s hs
  have hocc := occupants_eq arr arr' hlen s
  have hoa := origin_eq S arr arr' t hagree ha
  simp only [Setup.step, hloc, hbest, hocc, hoa]
  rcases hb : S.best arr' s (S.loc arr' s a) with _ | b
  · rfl
  · have hbm := best_mem S arr' s _ b hb
    rw [← hocc] at hbm
    have hbt := hs b _ (mem_occupants hbm)
    simp only [origin_eq S arr arr' t hagree hbt]

end OnlineTransportation1195.Dev.T12.PartQ
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartQ
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
lemma step_inv (S : Setup n) (arr : List (Fin n)) (t : ℕ) (s : St n) (hs : Inv t s) (a : ℕ)
    (ha : a ≤ t) :
    Inv t (S.step arr s a).1 ∧ ∀ b, (S.step arr s a).2 = Sum.inr b → b ≤ t := by
  have hbest : ∀ g b, S.best arr s g = some b → b ≤ t := fun g b hb =>
    hs b g (mem_occupants (best_mem S arr s g b hb))
  unfold Setup.step
  dsimp only
  split_ifs with h1 h2
  · refine ⟨fun ℓ g hℓ => ?_, fun b hb => by simp at hb⟩
    by_cases hla : ℓ = a
    · subst hla; exact ha
    · dsimp only at hℓ; rw [Function.update_of_ne hla] at hℓ
      exact hs ℓ g hℓ
  · rcases hb : S.best arr s (S.loc arr s a) with _ | b
    · exact ⟨hs, fun b hb => by simp at hb; omega⟩
    · have hbt := hbest _ b hb
      dsimp only
      split_ifs
      · refine ⟨fun ℓ g hℓ => ?_, fun c hc => ?_⟩
        · by_cases hla : ℓ = a
          · subst hla; exact ha
          · dsimp only at hℓ; rw [Function.update_of_ne hla] at hℓ
            by_cases hlb : ℓ = b
            · subst hlb; exact hbt
            · rw [Function.update_of_ne hlb] at hℓ
              exact hs ℓ g hℓ
        · simp at hc; omega
      · exact ⟨hs, fun c hc => by simp at hc; omega⟩
  · exact ⟨hs, fun b hb => by simp at hb; omega⟩

lemma loop_eq (S : Setup n) (arr arr' : List (Fin n)) (hlen : arr.length = arr'.length) (t : ℕ)
    (hagree : ∀ j ≤ t, arr.getD j S.o = arr'.getD j S.o) :
    ∀ (f : ℕ) (s : St n) (a : ℕ), Inv t s → a ≤ t →
      S.loop arr f s a = S.loop arr' f s a ∧ Inv t (S.loop arr f s a).1 := by
  intro f
  induction f with
  | zero => intro s a hs _; exact ⟨rfl, hs⟩
  | succ f ih =>
    intro s a hs ha
    have heq := step_eq S arr arr' hlen t hagree s hs a ha
    have hinv := step_inv S arr t s hs a ha
    simp only [Setup.loop, heq]
    rw [heq] at hinv
    rcases hst : S.step arr' s a with ⟨s', _ | b⟩
    · rw [hst] at hinv
      exact ⟨rfl, hinv.1⟩
    · rw [hst] at hinv
      exact ih s' b hinv.1 (hinv.2 b rfl)

lemma fuel_eq (S : Setup n) (arr arr' : List (Fin n)) (hlen : arr.length = arr'.length) :
    S.fuelOf arr = S.fuelOf arr' := by
  simp only [Setup.fuelOf, hlen]

lemma stAfter_eq (S : Setup n) (arr arr' : List (Fin n)) (hlen : arr.length = arr'.length)
    (t : ℕ) (hagree : ∀ j ≤ t, arr.getD j S.o = arr'.getD j S.o) :
    ∀ m ≤ t, S.stAfter arr m = S.stAfter arr' m ∧ Inv t (S.stAfter arr m) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨rfl, fun ℓ g h => by simp [Setup.stAfter] at h⟩
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨h3, h4⟩ := loop_eq S arr arr' hlen t hagree (S.fuelOf arr) (S.stAfter arr m) m h2
      (by omega)
    refine ⟨?_, h4⟩
    simp only [Setup.stAfter]
    rw [h3, h1, fuel_eq S arr arr' hlen]

/-- Causality: the choice for car `t` reads only the first `t+1` arrivals. -/
theorem choice_causal (S : Setup n) (arr arr' : List (Fin n)) (hlen : arr.length = arr'.length)
    (t : ℕ) (hagree : ∀ j ≤ t, arr.getD j S.o = arr'.getD j S.o) :
    S.choice arr t = S.choice arr' t := by
  obtain ⟨h1, h2⟩ := stAfter_eq S arr arr' hlen t hagree t le_rfl
  obtain ⟨h3, _⟩ := loop_eq S arr arr' hlen t hagree (S.fuelOf arr) (S.stAfter arr t) t h2 le_rfl
  simp only [Setup.choice]
  rw [h3, h1, fuel_eq S arr arr' hlen]

end OnlineTransportation1195.Dev.T12.PartQ
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
alias choice_causal := OnlineTransportation1195.Dev.T12.PartQ.choice_causal

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartK
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
theorem wlen_mono (D : Fin n → Fin n → ℝ) (hD : ∀ a b, 0 ≤ D a b) (L : List (Fin n)) (x : Fin n)
    {i j : ℕ} (hij : i ≤ j) : wlen D L x i ≤ wlen D L x j := by
  unfold wlen
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    (fun _ _ _ => hD _ _)

theorem conn_symm (D : Fin n → Fin n → ℝ) (hD : ∀ a b, D a b = D b a) (h : ℝ) {a b : Fin n}
    (hab : Conn D h a b) : Conn D h b a := by
  unfold Conn at *
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (by rw [hD]; exact hbc) ih

theorem conn_trans (D : Fin n → Fin n → ℝ) (h : ℝ) {a b c : Fin n}
    (hab : Conn D h a b) (hbc : Conn D h b c) : Conn D h a c :=
  Relation.ReflTransGen.trans hab hbc

/-- Discrete layer cake: domination of all upper level counts gives domination of sums. -/
theorem sum_le_of_count {α β : Type*} (x : α → ℝ) (d : β → ℝ) :
    ∀ (N : ℕ) (A : Finset α) (B : Finset β), A.card = N → (∀ t ∈ B, 0 ≤ d t) →
      (∀ h : ℝ, 0 ≤ h → (A.filter (fun a => h < x a)).card ≤ (B.filter (fun b => h < d b)).card) →
      ∑ a ∈ A, x a ≤ ∑ b ∈ B, d b := by
  intro N
  induction N with
  | zero =>
    intro A B hA hd _
    rw [Finset.card_eq_zero.mp hA, Finset.sum_empty]
    exact Finset.sum_nonneg hd
  | succ N ih =>
    intro A B hA hd hcnt
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨l, hlA, hlmax⟩ := A.exists_max_image x hAne
    by_cases hxl : x l ≤ 0
    · calc ∑ a ∈ A, x a ≤ ∑ _a ∈ A, (0 : ℝ) :=
            Finset.sum_le_sum (fun a ha => (hlmax a ha).trans hxl)
        _ = 0 := by simp
        _ ≤ _ := Finset.sum_nonneg hd
    push Not at hxl
    have ht : ∃ t ∈ B, x l ≤ d t := by
      by_contra hcon
      push Not at hcon
      set V : Finset ℝ := insert (0 : ℝ) (B.image d) with hV
      have hVne : V.Nonempty := Finset.insert_nonempty _ _
      set hh := V.max' hVne with hhh
      have h0 : 0 ≤ hh := V.le_max' 0 (Finset.mem_insert_self _ _)
      have hlt : hh < x l := by
        have hmem := V.max'_mem hVne
        rcases Finset.mem_insert.mp hmem with h | h
        · rw [hhh, h]; exact hxl
        · obtain ⟨t, htB, hteq⟩ := Finset.mem_image.mp h
          rw [hhh, ← hteq]; exact hcon t htB
      have h1 := hcnt hh h0
      have h2 : B.filter (fun b => hh < d b) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro b hb
        exact not_lt.mpr (V.le_max' (d b) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem d hb)))
      have h3 : l ∈ A.filter (fun a => hh < x a) := Finset.mem_filter.mpr ⟨hlA, hlt⟩
      rw [h2, Finset.card_empty] at h1
      have := Finset.card_pos.mpr ⟨l, h3⟩
      omega
    obtain ⟨t, htB, hlt⟩ := ht
    have key := ih (A.erase l) (B.erase t) (by rw [Finset.card_erase_of_mem hlA]; omega)
      (fun b hb => hd b (Finset.mem_of_mem_erase hb)) (by
        intro h hh
        rw [Finset.filter_erase, Finset.filter_erase]
        by_cases hxh : h < x l
        · rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hlA, hxh⟩),
            Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨htB, (lt_of_lt_of_le hxh hlt : h < d t)⟩)]
          have := hcnt h hh
          omega
        · have hE : A.filter (fun a => h < x a) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro a ha
            push Not at hxh
            exact not_lt.mpr ((hlmax a ha).trans hxh)
          rw [hE]; simp)
    rw [← Finset.add_sum_erase A x hlA, ← Finset.add_sum_erase B d htB]
    linarith

end OnlineTransportation1195.Dev.T12.PartK
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option warn.classDefReducibility false
namespace OnlineTransportation1195.Dev.T12.PartL
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
/-- The star distance: centre `0`, leaves at distance `1` from it and `2` from each other. -/
noncomputable def sd {m : ℕ} (a b : Fin (m + 2)) : ℝ :=
  if a = b then 0 else if a = 0 ∨ b = 0 then 1 else 2

noncomputable def starMetric (m : ℕ) : MetricSpace (Fin (m + 2)) where
  dist := sd
  dist_self a := by simp [sd]
  dist_comm a b := by
    unfold sd
    by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
      by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
  dist_triangle a b c := by
    unfold sd
    split_ifs <;> subst_vars <;> simp_all <;> norm_num
  eq_of_dist_eq_zero := by
    intro a b h
    unfold sd at h
    split_ifs at h with h1 <;> norm_num at h
    exact h1

/-- The star instance: garages are the leaves, each of capacity one. -/
noncomputable def starI (m : ℕ) : TransportationInstance (m + 2) where
  metric := starMetric m
  garages := Finset.univ.erase 0
  capacity := fun _ => 1

lemma starI_k (m : ℕ) : (starI m).k = m + 1 := by
  show Fintype.card (Σ g : {g // g ∈ (starI m).garages}, Fin ((starI m).capacity g)) = _
  rw [Fintype.card_sigma]
  show ∑ g : {g // g ∈ (starI m).garages}, Fintype.card (Fin 1) = _
  simp only [Fintype.card_fin, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]
  rw [Fintype.card_coe]
  simp [starI]

lemma cost_eq (m : ℕ) (r : (starI m).Arrivals) (a : (starI m).Assignment) :
    (starI m).cost r a = ∑ t, sd (r t) ((starI m).garageOf a t) := rfl

lemma garageOf_ne_zero (m : ℕ) (a : (starI m).Assignment) (t : (starI m).Time) :
    (starI m).garageOf a t ≠ 0 := by
  intro h
  have := ((Fintype.equivFin (starI m).Slot).symm (a t)).1.2
  unfold TransportationInstance.garageOf at h
  rw [h] at this
  simp [starI] at this

lemma slot_inj (m : ℕ) : Function.Injective (fun s : (starI m).Slot => s.1.val) := by
  rintro ⟨⟨g, hg⟩, i⟩ ⟨⟨g', hg'⟩, j⟩ h
  simp only at h
  subst h
  have hi := i.isLt
  have hj := j.isLt
  have : i = j := Fin.ext (by simp [starI] at hi hj; omega)
  subst this
  rfl

lemma garageOf_inj (m : ℕ) (a : (starI m).Assignment) :
    Function.Injective ((starI m).garageOf a) := by
  intro t t' h
  have := slot_inj m h
  exact a.injective ((Fintype.equivFin _).symm.injective this)

/-- A causal update has a fixed point (iterate it `K` times). -/
lemma exists_fix {K : ℕ} {X : Type*} (F : (Fin K → X) → (Fin K → X))
    (hF : ∀ (m : ℕ) (r r' : Fin K → X), (∀ j : Fin K, j.val < m → r j = r' j) →
      ∀ j : Fin K, j.val < m + 1 → F r j = F r' j) (x : X) : ∃ r, F r = r := by
  have key : ∀ (m : ℕ) (r r' : Fin K → X), ∀ j : Fin K, j.val < m → F^[m] r j = F^[m] r' j := by
    intro m
    induction m with
    | zero => intro r r' j hj; omega
    | succ m ih =>
      intro r r' j hj
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hF m _ _ (fun i hi => ih r r' i hi) j hj
  refine ⟨F^[K] (fun _ => x), ?_⟩
  funext j
  have := key K (F (fun _ => x)) (fun _ => x) j j.isLt
  rw [← Function.iterate_succ_apply' F K, Function.iterate_succ_apply]
  exact this

lemma finRotate_symm_val {K : ℕ} (t : Fin K) (ht : t.val ≠ 0) :
    ((finRotate K).symm t).val = t.val - 1 := by
  cases K with
  | zero => exact t.elim0
  | succ K =>
    set s := (finRotate (K + 1)).symm t with hs
    have : t = finRotate (K + 1) s := by simp [hs]
    by_cases hl : s = Fin.last K
    · rw [hl, finRotate_last] at this
      subst this; simp at ht
    · rw [this, coe_finRotate_of_ne_last hl]; omega

theorem lower_star (m : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 2 * ((m + 2 : ℕ) : ℝ) - 3)
    (A : Policy (starI m)) (hA : IsCausal (starI m) A) : ¬ Competitive (starI m) A ρ := by
  intro hc
  have hK : (starI m).k = m + 1 := starI_k m
  let t0 : (starI m).Time := ⟨0, by omega⟩
  let F : (starI m).Arrivals → (starI m).Arrivals := fun r t =>
    if h : t.val = 0 then 0 else (starI m).garageOf (A r) ⟨t.val - 1, by omega⟩
  obtain ⟨r, hr⟩ := exists_fix F (by
    intro k r r' hrr j hj
    simp only [F]
    split_ifs with h
    · rfl
    · exact hA r r' _ (fun i hi => hrr i (by
        have := Fin.le_iff_val_le_val.mp hi
        simp only at this
        omega))) (0 : Fin (m + 2))
  have hr0 : r t0 = 0 := by rw [← congrFun hr t0]; simp [F, t0]
  have hrt : ∀ t : (starI m).Time, (ht : t.val ≠ 0) →
      r t = (starI m).garageOf (A r) ⟨t.val - 1, by omega⟩ := by
    intro t ht; rw [← congrFun hr t]; simp [F, ht]
  set a := A r
  -- lower bound on the online cost
  have hlow : ∀ t, (2 : ℝ) - (if t = t0 then 1 else 0) ≤ sd (r t) ((starI m).garageOf a t) := by
    intro t
    have hg := garageOf_ne_zero m a t
    by_cases ht : t = t0
    · subst ht; rw [hr0]; simp [sd, Ne.symm hg]; norm_num
    · have hv : t.val ≠ 0 := fun h => ht (Fin.ext h)
      rw [hrt t hv, if_neg ht]
      have hne : (starI m).garageOf a ⟨t.val - 1, by omega⟩ ≠ (starI m).garageOf a t := by
        intro h
        have := congrArg Fin.val (garageOf_inj m a h)
        simp at this; omega
      have hg' := garageOf_ne_zero m a ⟨t.val - 1, by omega⟩
      simp [sd, hne, hg, hg']
  have hcost : 2 * ((m + 2 : ℕ) : ℝ) - 3 ≤ (starI m).cost r a := by
    rw [cost_eq]
    refine le_trans ?_ (Finset.sum_le_sum (fun t _ => hlow t))
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp [Finset.card_univ, Fintype.card_fin, hK]
    push_cast; ring_nf; rfl
  -- an offline assignment of cost at most one
  let σ : (starI m).Assignment := a * (finRotate (starI m).k).symm
  have hσ : (starI m).cost r σ ≤ 1 := by
    rw [cost_eq]
    have : ∀ t, sd (r t) ((starI m).garageOf σ t) ≤ if t = t0 then 1 else 0 := by
      intro t
      have hgσ : (starI m).garageOf σ t = (starI m).garageOf a ((finRotate (starI m).k).symm t) := rfl
      by_cases ht : t = t0
      · rw [if_pos ht]; subst ht; rw [hr0]; unfold sd; split_ifs <;> simp_all
      · have hv : t.val ≠ 0 := fun h => ht (Fin.ext h)
        rw [if_neg ht, hgσ, hrt t hv]
        have : (finRotate (starI m).k).symm t = ⟨t.val - 1, by omega⟩ :=
          Fin.ext (finRotate_symm_val t hv)
        rw [this]; simp [sd]
    refine le_trans (Finset.sum_le_sum (fun t _ => this t)) ?_
    rw [Finset.sum_ite_eq']; simp
  have hopt : (starI m).opt r ≤ 1 := by
    refine le_trans ?_ hσ
    unfold TransportationInstance.opt
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ σ))
  have h1 := hc r
  have : ρ * (starI m).opt r ≤ ρ := by nlinarith
  linarith

theorem lower {n : ℕ} (hn : 2 ≤ n) (ρ : ℝ) (hρ : ρ < 2 * (n : ℝ) - 3) : ¬ PointRatio n ρ := by
  rintro ⟨h0, hall⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨A, hA, hc⟩ := hall (starI m)
  exact lower_star m ρ h0 hρ A hA hc

end OnlineTransportation1195.Dev.T12.PartL
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
/-! ## Part L: the lower bound -/
alias lower := OnlineTransportation1195.Dev.T12.PartL.lower

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartP
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ} (I : TransportationInstance n)
/-- The instance's distance. -/
noncomputable def Dm : Fin n → Fin n → ℝ := fun a b => @dist (Fin n) I.metric.toDist a b

theorem Dm_metric : IsMetric (Dm I) := by
  let _ := I.metric
  exact ⟨fun a b => dist_nonneg, fun a => dist_self a, fun a b h => dist_pos.mpr h,
    fun a b => dist_comm a b, fun a b c => dist_triangle a b c⟩

/-- Capacities extended by zero. -/
noncomputable def capOf (g : Fin n) : ℕ := if h : g ∈ I.garages then I.capacity ⟨g, h⟩ else 0

theorem capOf_sub (g : {g // g ∈ I.garages}) : capOf I g.1 = I.capacity g := by
  simp [capOf, g.2]

theorem sum_capOf : ∑ g ∈ I.garages, capOf I g = I.k := by
  unfold TransportationInstance.k
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← Finset.sum_coe_sort I.garages]
  exact Finset.sum_congr rfl (fun g _ => capOf_sub I g)

theorem card_filter_fin (k : ℕ) (p : ℕ → Prop) :
    (Finset.univ.filter (fun t : Fin k => p t)).card = ((Finset.range k).filter p).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext m
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t.2, ht⟩
  · rintro ⟨hm, hp⟩; exact ⟨⟨m, hm⟩, hp, rfl⟩

theorem garageOf_mem (a : I.Assignment) (t : I.Time) : I.garageOf a t ∈ I.garages :=
  ((Fintype.equivFin I.Slot).symm (a t)).1.2

theorem slot_mem_map (g : Fin n) (hg : g ∈ I.garages) (s : I.Slot) (hs : s.1.val = g) :
    s ∈ Finset.univ.map (Function.Embedding.sigmaMk
      (β := fun g : {g // g ∈ I.garages} => Fin (I.capacity g)) ⟨g, hg⟩) := by
  obtain ⟨⟨g', hg'⟩, i⟩ := s
  simp only at hs
  subst hs
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩

theorem card_garage_le (a : I.Assignment) (g : Fin n) :
    (Finset.univ.filter (fun t => I.garageOf a t = g)).card ≤ capOf I g := by
  by_cases hg : g ∈ I.garages
  · rw [capOf_sub I ⟨g, hg⟩]
    calc (Finset.univ.filter (fun t => I.garageOf a t = g)).card
        ≤ (Finset.univ.map (Function.Embedding.sigmaMk
            (β := fun g : {g // g ∈ I.garages} => Fin (I.capacity g)) ⟨g, hg⟩)).card := by
          refine Finset.card_le_card_of_injOn (fun t => (Fintype.equivFin I.Slot).symm (a t)) ?_ ?_
          · intro t ht
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
            exact slot_mem_map I g hg _ ht
          · intro t _ t' _ h
            exact a.injective ((Fintype.equivFin I.Slot).symm.injective h)
      _ = I.capacity ⟨g, hg⟩ := by simp
  · have : Finset.univ.filter (fun t => I.garageOf a t = g) = ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      exact hg (h ▸ garageOf_mem I a t)
    simp [this]

theorem exists_perm (ch : I.Time → Fin n) (hG : ∀ t, ch t ∈ I.garages)
    (hc : ∀ g, (Finset.univ.filter (fun t => ch t = g)).card ≤ capOf I g) :
    ∃ a : I.Assignment, ∀ t, I.garageOf a t = ch t := by
  let f : I.Time → {g // g ∈ I.garages} := fun t => ⟨ch t, hG t⟩
  have hfib : ∀ g : {g // g ∈ I.garages}, Nonempty ({t // f t = g} ↪ Fin (I.capacity g)) := by
    intro g
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, Fintype.card_subtype]
    have := hc g.1
    rw [capOf_sub I g] at this
    refine le_trans (le_of_eq ?_) this
    congr 1
    ext t
    simp [f, Subtype.ext_iff]
  let e : ∀ g, {t // f t = g} ↪ Fin (I.capacity g) := fun g => Classical.choice (hfib g)
  let emb : I.Time ↪ I.Slot :=
    (Equiv.sigmaFiberEquiv f).symm.toEmbedding.trans
      (Function.Embedding.sigmaMap (Function.Embedding.refl _) e)
  have hbij : Function.Bijective emb := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨emb.injective, ?_⟩
    rw [Fintype.card_fin]
    rfl
  let eq : I.Time ≃ I.Slot := Equiv.ofBijective emb hbij
  refine ⟨eq.trans (Fintype.equivFin I.Slot), fun t => ?_⟩
  change ((Fintype.equivFin I.Slot).symm (Fintype.equivFin I.Slot (eq t))).1.val = ch t
  rw [Equiv.symm_apply_apply]
  rfl

end OnlineTransportation1195.Dev.T12.PartP
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartS
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
/-! ## Invariants of the itinerant-car process -/
/-- The invariant shared by all states of the process. -/
structure Core (S : Setup n) (arr : List (Fin n)) (s : St n) : Prop where
  parkG : ∀ (ℓ : ℕ) (g : Fin n), s.park ℓ = some g → g ∈ S.G ∧ S.loc arr s ℓ = g
  capOK : ∀ g : Fin n, (Setup.occupants arr s g).card ≤ S.cap g
  passed : ∀ (ℓ : ℕ) (j : ℕ), j < s.pos ℓ → S.vtx arr ℓ j ∈ S.G →
    (Setup.occupants arr s (S.vtx arr ℓ j)).card = S.cap (S.vtx arr ℓ j) ∧
    ∀ b ∈ Setup.occupants arr s (S.vtx arr ℓ j),
      S.pr (S.origin arr b) (S.vtx arr ℓ j) ≤ S.pr (S.origin arr ℓ) (S.vtx arr ℓ j)
  notback : ∀ (ℓ : ℕ) (g : Fin n), s.park ℓ = some g → ∀ j < s.pos ℓ, S.vtx arr ℓ j ≠ g

/-- The invariant during the insertion of car `t`, with active label `a`. -/
structure InvL (S : Setup n) (arr : List (Fin n)) (t : ℕ) (s : St n) (a : ℕ) : Prop where
  core : Core S arr s
  ht : t < arr.length
  fresh : ∀ ℓ : ℕ, t < ℓ → s.pos ℓ = 0 ∧ s.park ℓ = none
  ha : a ≤ t
  hpa : s.park a = none
  parked : ∀ ℓ : ℕ, ℓ ≤ t → ℓ ≠ a → s.park ℓ ≠ none

/-- The invariant after the first `t` insertions. -/
structure Inv0 (S : Setup n) (arr : List (Fin n)) (t : ℕ) (s : St n) : Prop where
  core : Core S arr s
  fresh : ∀ ℓ : ℕ, t ≤ ℓ → s.pos ℓ = 0 ∧ s.park ℓ = none
  parked : ∀ ℓ : ℕ, ℓ < t → s.park ℓ ≠ none

/-- Remaining room on all walks. -/
def meas (S : Setup n) (arr : List (Fin n)) (s : St n) : ℕ :=
  ∑ ℓ ∈ Finset.range arr.length, ((S.walkOf arr ℓ).length - s.pos ℓ)

/-! ## Basic facts -/
theorem mem_occ (arr : List (Fin n)) (s : St n) (g : Fin n) (ℓ : ℕ) :
    ℓ ∈ Setup.occupants arr s g ↔ ℓ < arr.length ∧ s.park ℓ = some g := by
  simp [Setup.occupants]

theorem loc_eq (S : Setup n) (arr : List (Fin n)) (s : St n) (ℓ : ℕ) :
    S.loc arr s ℓ = S.vtx arr ℓ (s.pos ℓ) := rfl

theorem vtx_zero (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (ℓ : ℕ) :
    S.vtx arr ℓ 0 = S.origin arr ℓ := by
  have h := hS.head (S.origin arr ℓ)
  unfold Setup.vtx Setup.walkOf
  cases hW : S.W (S.origin arr ℓ) with
  | nil => rw [hW] at h; simp at h
  | cons x xs => rw [hW] at h; simp at h; simp [h]

theorem len_pos (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (ℓ : ℕ) :
    0 < (S.walkOf arr ℓ).length := by
  have h := hS.head (S.origin arr ℓ)
  unfold Setup.walkOf
  cases hW : S.W (S.origin arr ℓ) with
  | nil => rw [hW] at h; simp at h
  | cons x xs => simp

theorem best_some (S : Setup n) (arr : List (Fin n)) (s : St n) (g : Fin n) (b : ℕ)
    (h : S.best arr s g = some b) :
    b ∈ Setup.occupants arr s g ∧ ∀ c ∈ Setup.occupants arr s g,
      S.pr (S.origin arr c) g ≤ S.pr (S.origin arr b) g := by
  unfold Setup.best at h
  split_ifs at h with hne
  simp only [Option.some.injEq] at h
  subst h
  exact Classical.choose_spec ((Setup.occupants arr s g).exists_max_image
      (fun b => S.pr (S.origin arr b) g) hne)

theorem best_none (S : Setup n) (arr : List (Fin n)) (s : St n) (g : Fin n)
    (h : S.best arr s g = none) : Setup.occupants arr s g = ∅ := by
  unfold Setup.best at h
  split_ifs at h with hne
  exact Finset.not_nonempty_iff_eq_empty.mp hne

theorem step_spec (S : Setup n) (arr : List (Fin n)) (s s' : St n) (a : ℕ) (r : Fin n ⊕ ℕ)
    (h : S.step arr s a = (s', r)) :
    (S.loc arr s a ∈ S.G ∧
      (Setup.occupants arr s (S.loc arr s a)).card < S.cap (S.loc arr s a) ∧
      s' = ⟨s.pos, Function.update s.park a (some (S.loc arr s a))⟩ ∧
      r = Sum.inl (S.loc arr s a)) ∨
    (∃ b, S.loc arr s a ∈ S.G ∧
      ¬ (Setup.occupants arr s (S.loc arr s a)).card < S.cap (S.loc arr s a) ∧
      S.best arr s (S.loc arr s a) = some b ∧
      S.pr (S.origin arr a) (S.loc arr s a) < S.pr (S.origin arr b) (S.loc arr s a) ∧
      s' = ⟨Function.update s.pos b (s.pos b + 1),
            Function.update (Function.update s.park b none) a (some (S.loc arr s a))⟩ ∧
      r = Sum.inr b) ∨
    (s' = ⟨Function.update s.pos a (s.pos a + 1), s.park⟩ ∧ r = Sum.inr a ∧
      (S.loc arr s a ∈ S.G →
        ¬ (Setup.occupants arr s (S.loc arr s a)).card < S.cap (S.loc arr s a) ∧
        ∀ b, S.best arr s (S.loc arr s a) = some b →
          ¬ S.pr (S.origin arr a) (S.loc arr s a) < S.pr (S.origin arr b) (S.loc arr s a))) := by
  unfold Setup.step at h
  simp only at h
  split_ifs at h with h1 h2
  · left; simp only [Prod.mk.injEq] at h; exact ⟨h1, h2, h.1.symm, h.2.symm⟩
  · rcases hb : S.best arr s (S.loc arr s a) with _ | b
    · rw [hb] at h; simp only [Prod.mk.injEq] at h
      right; right
      exact ⟨h.1.symm, h.2.symm, fun _ => ⟨h2, fun b hb' => by simp at hb'⟩⟩
    · rw [hb] at h; simp only at h
      split_ifs at h with h3
      · right; left; simp only [Prod.mk.injEq] at h
        exact ⟨b, h1, h2, rfl, h3, h.1.symm, h.2.symm⟩
      · right; right; simp only [Prod.mk.injEq] at h
        refine ⟨h.1.symm, h.2.symm, fun _ => ⟨h2, fun b' hb' => ?_⟩⟩
        cases hb'; exact h3
  · right; right; simp only [Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm, fun h' => absurd h' h1⟩

/-! ## Counting parked labels -/
theorem sum_occ_le (S : Setup n) (arr : List (Fin n)) (t : ℕ) (s : St n) (a : ℕ)
    (hL : InvL S arr t s a) :
    ∑ g ∈ S.G, (Setup.occupants arr s g).card ≤ t := by
  rw [← Finset.card_biUnion]
  · calc _ ≤ ((Finset.range (t + 1)).erase a).card := by
          apply Finset.card_le_card
          intro ℓ hℓ
          simp only [Finset.mem_biUnion, mem_occ] at hℓ
          obtain ⟨g, -, -, hp⟩ := hℓ
          simp only [Finset.mem_erase, Finset.mem_range]
          refine ⟨?_, ?_⟩
          · rintro rfl; rw [hL.hpa] at hp; cases hp
          · by_contra hc; rw [not_lt] at hc
            rw [(hL.fresh ℓ (by omega)).2] at hp; cases hp
      _ = t := by
          have := hL.ha
          rw [Finset.card_erase_of_mem (by simp; omega)]; simp
  · intro g _ g' _ hne
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro ℓ h1 h2
    rw [mem_occ] at h1 h2
    exact hne (Option.some.inj (h1.2.symm.trans h2.2))

theorem pos_lt (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (t : ℕ) (s : St n)
    (a : ℕ) (hL : InvL S arr t s a) (ℓ : ℕ) :
    s.pos ℓ < (S.walkOf arr ℓ).length := by
  by_contra hge; rw [not_lt] at hge
  have hlen := len_pos S arr hS ℓ
  by_cases hla : ℓ = a
  · subst hla
    have hfull : ∀ g ∈ S.G, (Setup.occupants arr s g).card = S.cap g := by
      intro g hg
      obtain ⟨j, hj, hjg⟩ := hS.cover (S.origin arr ℓ) g
      have hv : S.vtx arr ℓ j = g := hjg
      have hj' : j < s.pos ℓ := by unfold Setup.walkOf at hge; omega
      have := (hL.core.passed ℓ j hj' (hv ▸ hg)).1
      rwa [hv] at this
    have h1 := sum_occ_le S arr t s ℓ hL
    rw [Finset.sum_congr rfl hfull, hS.total] at h1
    have := hL.ht; omega
  · by_cases hlt : ℓ ≤ t
    · obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.mp (hL.parked ℓ hlt hla)
      have hloc := (hL.core.parkG ℓ g hg).2
      apply hL.core.notback ℓ g hg 0 (by omega)
      rw [vtx_zero S arr hS, ← hloc]
      unfold Setup.loc
      rw [List.getD_eq_default _ _ hge]
    · have := (hL.fresh ℓ (by omega)).1; omega

/-! ## Distance and measure bookkeeping -/
theorem Phi_adv (S : Setup n) (arr : List (Fin n)) (s s' : St n) (c : ℕ) (hc : c < arr.length)
    (hpos : s'.pos = Function.update s.pos c (s.pos c + 1)) :
    S.Phi arr s' = S.Phi arr s + S.D (S.vtx arr c (s.pos c)) (S.vtx arr c (s.pos c + 1)) := by
  unfold Setup.Phi
  have hc' : c ∈ Finset.range arr.length := Finset.mem_range.mpr hc
  rw [← Finset.add_sum_erase _ _ hc', ← Finset.add_sum_erase _ _ hc']
  have hrest : ∑ x ∈ (Finset.range arr.length).erase c, S.plen arr s' x =
      ∑ x ∈ (Finset.range arr.length).erase c, S.plen arr s x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxc : x ≠ c := Finset.ne_of_mem_erase hx
    unfold Setup.plen; rw [hpos, Function.update_of_ne hxc]
  rw [hrest]
  have : S.plen arr s' c =
      S.plen arr s c + S.D (S.vtx arr c (s.pos c)) (S.vtx arr c (s.pos c + 1)) := by
    unfold Setup.plen wlen; rw [hpos, Function.update_self, Finset.sum_range_succ]; rfl
  rw [this]; ring

theorem Phi_same (S : Setup n) (arr : List (Fin n)) (s s' : St n) (hpos : s'.pos = s.pos) :
    S.Phi arr s' = S.Phi arr s := by
  unfold Setup.Phi Setup.plen; rw [hpos]

theorem meas_adv (S : Setup n) (arr : List (Fin n)) (s s' : St n) (c : ℕ) (hc : c < arr.length)
    (hpos : s'.pos = Function.update s.pos c (s.pos c + 1))
    (hlt : s'.pos c < (S.walkOf arr c).length) :
    meas S arr s' + 1 = meas S arr s := by
  unfold meas
  have hc' : c ∈ Finset.range arr.length := Finset.mem_range.mpr hc
  rw [← Finset.add_sum_erase _ _ hc', ← Finset.add_sum_erase _ _ hc']
  have hrest : ∑ x ∈ (Finset.range arr.length).erase c, ((S.walkOf arr x).length - s'.pos x) =
      ∑ x ∈ (Finset.range arr.length).erase c, ((S.walkOf arr x).length - s.pos x) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxc : x ≠ c := Finset.ne_of_mem_erase hx
    rw [hpos, Function.update_of_ne hxc]
  rw [hrest]
  rw [hpos, Function.update_self] at hlt ⊢
  omega

/-! ## Step preservation: advancing -/
theorem adv_inv (S : Setup n) (arr : List (Fin n)) (t : ℕ) (s : St n) (a : ℕ)
    (hL : InvL S arr t s a)
    (hC : S.loc arr s a ∈ S.G →
        ¬ (Setup.occupants arr s (S.loc arr s a)).card < S.cap (S.loc arr s a) ∧
        ∀ b, S.best arr s (S.loc arr s a) = some b →
          ¬ S.pr (S.origin arr a) (S.loc arr s a) < S.pr (S.origin arr b) (S.loc arr s a)) :
    InvL S arr t ⟨Function.update s.pos a (s.pos a + 1), s.park⟩ a := by
  have hocc : ∀ g, Setup.occupants arr ⟨Function.update s.pos a (s.pos a + 1), s.park⟩ g =
      Setup.occupants arr s g := fun g => rfl
  have hposne : ∀ ℓ, ℓ ≠ a → (Function.update s.pos a (s.pos a + 1)) ℓ = s.pos ℓ :=
    fun ℓ h => Function.update_of_ne h _ _
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hL.ht, ?_, hL.ha, hL.hpa, hL.parked⟩
  · intro ℓ g hp
    dsimp only at hp
    have hla : ℓ ≠ a := by rintro rfl; rw [hL.hpa] at hp; cases hp
    have := hL.core.parkG ℓ g hp
    rw [loc_eq] at this ⊢; dsimp only; rw [hposne ℓ hla]; exact this
  · intro g; rw [hocc]; exact hL.core.capOK g
  · intro ℓ j hj hg
    simp only [hocc]
    dsimp only at hj
    by_cases hla : ℓ = a
    · subst hla
      rw [Function.update_self] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hL.core.passed ℓ j hj hg
      · have hg' : S.loc arr s ℓ ∈ S.G := hg
        obtain ⟨hnf, hpr⟩ := hC hg'
        refine ⟨le_antisymm (hL.core.capOK _) (not_lt.mp hnf), fun c hc => ?_⟩
        change c ∈ Setup.occupants arr s (S.loc arr s ℓ) at hc
        change S.pr _ (S.loc arr s ℓ) ≤ S.pr _ (S.loc arr s ℓ)
        rcases hb : S.best arr s (S.loc arr s ℓ) with _ | b
        · rw [best_none S arr s _ hb] at hc; simp at hc
        · exact ((best_some S arr s _ b hb).2 c hc).trans (not_lt.mp (hpr b hb))
    · rw [hposne ℓ hla] at hj; exact hL.core.passed ℓ j hj hg
  · intro ℓ g hp j hj
    dsimp only at hp hj
    have hla : ℓ ≠ a := by rintro rfl; rw [hL.hpa] at hp; cases hp
    rw [hposne ℓ hla] at hj
    exact hL.core.notback ℓ g hp j hj
  · intro ℓ hℓ
    have hla : ℓ ≠ a := by have := hL.ha; omega
    dsimp only
    rw [hposne ℓ hla]; exact hL.fresh ℓ hℓ

/-! ## Step preservation: parking in a free slot -/
theorem park_inv (S : Setup n) (arr : List (Fin n)) (t : ℕ) (s : St n) (a : ℕ)
    (hL : InvL S arr t s a) (hv : S.loc arr s a ∈ S.G)
    (hlt : (Setup.occupants arr s (S.loc arr s a)).card < S.cap (S.loc arr s a)) :
    Inv0 S arr (t + 1) ⟨s.pos, Function.update s.park a (some (S.loc arr s a))⟩ ∧
      ∀ g, (Setup.occupants arr ⟨s.pos, Function.update s.park a (some (S.loc arr s a))⟩ g).card =
        (Setup.occupants arr s g).card + if g = S.loc arr s a then 1 else 0 := by
  set v := S.loc arr s a with hvdef
  set s' : St n := ⟨s.pos, Function.update s.park a (some v)⟩ with hs'
  have hat : a < arr.length := by have := hL.ha; have := hL.ht; omega
  have hmem : ∀ g ℓ, ℓ ∈ Setup.occupants arr s' g ↔
      (ℓ = a ∧ g = v) ∨ ℓ ∈ Setup.occupants arr s g := by
    intro g ℓ
    rw [mem_occ, mem_occ, hs']
    dsimp only
    by_cases hla : ℓ = a
    · subst hla
      simp only [Function.update_self, hL.hpa, Option.some.injEq, true_and, hat,
        reduceCtorEq, and_false, or_false]
      exact eq_comm
    · rw [Function.update_of_ne hla]; simp [hla]
  have hoccv : Setup.occupants arr s' v = insert a (Setup.occupants arr s v) := by
    ext ℓ; rw [hmem, Finset.mem_insert]; simp
  have hoccg : ∀ g, g ≠ v → Setup.occupants arr s' g = Setup.occupants arr s g := by
    intro g hg; ext ℓ; rw [hmem]; simp [hg]
  have hanot : ∀ g, a ∉ Setup.occupants arr s g := by
    intro g h; rw [mem_occ, hL.hpa] at h; cases h.2
  have hcard : ∀ g, (Setup.occupants arr s' g).card =
      (Setup.occupants arr s g).card + if g = v then 1 else 0 := by
    intro g
    by_cases hg : g = v
    · subst hg; rw [hoccv, Finset.card_insert_of_notMem (hanot _)]; simp
    · rw [hoccg g hg]; simp [hg]
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, hcard⟩
  · intro ℓ g hp
    dsimp only [s'] at hp
    by_cases hla : ℓ = a
    · subst hla; rw [Function.update_self] at hp; obtain rfl := Option.some.inj hp; exact ⟨hv, rfl⟩
    · rw [Function.update_of_ne hla] at hp; exact hL.core.parkG ℓ g hp
  · intro g
    rw [hcard]
    by_cases hg : g = v
    · subst hg; simp only [if_true]; omega
    · simp only [hg, if_false, add_zero]; exact hL.core.capOK g
  · intro ℓ j hj hg
    obtain ⟨hc, hp⟩ := hL.core.passed ℓ j hj hg
    have hne : S.vtx arr ℓ j ≠ v := by
      intro he; rw [he] at hc; omega
    rw [hoccg _ hne]; exact ⟨hc, hp⟩
  · intro ℓ g hp j hj
    dsimp only [s'] at hp hj
    by_cases hla : ℓ = a
    · subst hla; rw [Function.update_self] at hp; obtain rfl := Option.some.inj hp
      intro he
      have := (hL.core.passed ℓ j hj (he ▸ hv)).1
      rw [he] at this; omega
    · rw [Function.update_of_ne hla] at hp; exact hL.core.notback ℓ g hp j hj
  · intro ℓ hℓ
    have hla : ℓ ≠ a := by have := hL.ha; omega
    dsimp only [s']
    rw [Function.update_of_ne hla]; exact hL.fresh ℓ (by omega)
  · intro ℓ hℓ
    dsimp only [s']
    by_cases hla : ℓ = a
    · subst hla; rw [Function.update_self]; simp
    · rw [Function.update_of_ne hla]; exact hL.parked ℓ (by omega) hla

/-! ## Step preservation: evicting -/
theorem evict_inv (S : Setup n) (arr : List (Fin n)) (t : ℕ) (s s' : St n) (a b : ℕ)
    (hL : InvL S arr t s a) (hv : S.loc arr s a ∈ S.G)
    (hfull : ¬ (Setup.occupants arr s (S.loc arr s a)).card < S.cap (S.loc arr s a))
    (hb : S.best arr s (S.loc arr s a) = some b)
    (hlt : S.pr (S.origin arr a) (S.loc arr s a) < S.pr (S.origin arr b) (S.loc arr s a))
    (hs' : s' = ⟨Function.update s.pos b (s.pos b + 1),
            Function.update (Function.update s.park b none) a (some (S.loc arr s a))⟩) :
    InvL S arr t s' b ∧
      (∀ g, (Setup.occupants arr s' g).card = (Setup.occupants arr s g).card) ∧
      S.loc arr s b = S.loc arr s a ∧ b < arr.length ∧ s'.pos = Function.update s.pos b (s.pos b + 1) := by
  set v := S.loc arr s a with hvdef
  obtain ⟨hbm, hbmax⟩ := best_some S arr s v b hb
  have hbm' := (mem_occ arr s v b).mp hbm
  have hat : a < arr.length := by have := hL.ha; have := hL.ht; omega
  have hab : b ≠ a := by rintro rfl; rw [hL.hpa] at hbm'; cases hbm'.2
  have hbt : b ≤ t := by
    by_contra hc; rw [(hL.fresh b (by omega)).2] at hbm'; cases hbm'.2
  have hlocb : S.loc arr s b = v := (hL.core.parkG b v hbm'.2).2
  have hpa' : s'.park a = some v := by rw [hs']; exact Function.update_self _ _ _
  have hpb' : s'.park b = none := by
    rw [hs']; dsimp only; rw [Function.update_of_ne hab, Function.update_self]
  have hpo' : ∀ ℓ, ℓ ≠ a → ℓ ≠ b → s'.park ℓ = s.park ℓ := by
    intro ℓ h1 h2; rw [hs']; dsimp only
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
  have hposb : s'.pos b = s.pos b + 1 := by rw [hs']; exact Function.update_self _ _ _
  have hposo : ∀ ℓ, ℓ ≠ b → s'.pos ℓ = s.pos ℓ := by
    intro ℓ h; rw [hs']; exact Function.update_of_ne h _ _
  have hmem : ∀ g ℓ, ℓ ∈ Setup.occupants arr s' g ↔
      (ℓ = a ∧ g = v) ∨ (ℓ ≠ b ∧ ℓ ∈ Setup.occupants arr s g) := by
    intro g ℓ
    rw [mem_occ, mem_occ]
    by_cases hla : ℓ = a
    · subst hla
      rw [hpa', hL.hpa]
      simp only [Option.some.injEq, true_and, hat, reduceCtorEq, and_false, or_false]
      exact eq_comm
    · by_cases hlb : ℓ = b
      · subst hlb; rw [hpb']; simp [hab]
      · rw [hpo' ℓ hla hlb]; simp [hla, hlb]
  have hanot : ∀ g, a ∉ Setup.occupants arr s g := by
    intro g h; rw [mem_occ, hL.hpa] at h; cases h.2
  have hcard : ∀ g, (Setup.occupants arr s' g).card = (Setup.occupants arr s g).card := by
    intro g
    by_cases hg : g = v
    · subst hg
      have : Setup.occupants arr s' v = insert a ((Setup.occupants arr s v).erase b) := by
        ext ℓ; rw [hmem, Finset.mem_insert, Finset.mem_erase]; simp
      rw [this, Finset.card_insert_of_notMem (fun h => hanot v (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hbm]
      have := Finset.card_pos.mpr ⟨b, hbm⟩
      omega
    · congr 1; ext ℓ; rw [hmem]; simp only [hg, and_false, false_or]
      constructor
      · exact fun h => h.2
      · intro h; refine ⟨?_, h⟩; rintro rfl; rw [mem_occ] at h
        exact hg (Option.some.inj (h.2.symm.trans hbm'.2))
  have hlocs : ∀ ℓ, ℓ ≠ b → S.loc arr s' ℓ = S.loc arr s ℓ := by
    intro ℓ h; rw [loc_eq, loc_eq, hposo ℓ h]
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, hL.ht, ?_, hbt, hpb', ?_⟩, hcard, hlocb, hbm'.1, by rw [hs']⟩
  · intro ℓ g hp
    by_cases hla : ℓ = a
    · subst hla; rw [hpa'] at hp; obtain rfl := Option.some.inj hp
      exact ⟨hv, by rw [hlocs ℓ hab.symm]⟩
    · by_cases hlb : ℓ = b
      · subst hlb; rw [hpb'] at hp; cases hp
      · rw [hpo' ℓ hla hlb] at hp; rw [hlocs ℓ hlb]; exact hL.core.parkG ℓ g hp
  · intro g; rw [hcard]; exact hL.core.capOK g
  · intro ℓ j hj hg
    rw [hcard]
    by_cases hnew : ℓ = b ∧ j = s.pos b
    · obtain ⟨rfl, rfl⟩ := hnew
      have hw : S.vtx arr ℓ (s.pos ℓ) = v := hlocb
      rw [hw]
      refine ⟨le_antisymm (hL.core.capOK _) (not_lt.mp hfull), fun c hc => ?_⟩
      rcases (hmem v c).mp hc with ⟨rfl, -⟩ | ⟨-, hc'⟩
      · exact hlt.le
      · exact hbmax c hc'
    · have hj' : j < s.pos ℓ := by
        by_cases hlb : ℓ = b
        · subst hlb; rw [hposb] at hj
          have : j ≠ s.pos ℓ := fun h => hnew ⟨rfl, h⟩
          omega
        · rwa [hposo ℓ hlb] at hj
      obtain ⟨hc, hp⟩ := hL.core.passed ℓ j hj' hg
      refine ⟨hc, fun c hcm => ?_⟩
      rcases (hmem _ c).mp hcm with ⟨rfl, hw⟩ | ⟨-, hc'⟩
      · rw [hw] at hp ⊢
        exact hlt.le.trans (hp b hbm)
      · exact hp c hc'
  · intro ℓ g hp j hj
    by_cases hla : ℓ = a
    · subst hla; rw [hpa'] at hp; obtain rfl := Option.some.inj hp
      rw [hposo ℓ hab.symm] at hj
      intro he
      have := (hL.core.passed ℓ j hj (he ▸ hv)).2 b (he ▸ hbm)
      rw [he] at this
      exact absurd hlt (not_lt.mpr this)
    · by_cases hlb : ℓ = b
      · subst hlb; rw [hpb'] at hp; cases hp
      · rw [hpo' ℓ hla hlb] at hp; rw [hposo ℓ hlb] at hj
        exact hL.core.notback ℓ g hp j hj
  · intro ℓ hℓ
    have hla : ℓ ≠ a := by have := hL.ha; omega
    have hlb : ℓ ≠ b := by omega
    rw [hposo ℓ hlb, hpo' ℓ hla hlb]; exact hL.fresh ℓ hℓ
  · intro ℓ hℓ hlb
    by_cases hla : ℓ = a
    · subst hla; rw [hpa']; simp
    · rw [hpo' ℓ hla hlb]; exact hL.parked ℓ hℓ hla

/-! ## One step of the process -/
theorem step_move (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (t : ℕ) (s s' : St n)
    (a b : ℕ) (hL : InvL S arr t s a) (h : S.step arr s a = (s', Sum.inr b)) :
    InvL S arr t s' b ∧
      S.Phi arr s' = S.Phi arr s + S.D (S.loc arr s a) (S.loc arr s' b) ∧
      (∀ g, (Setup.occupants arr s' g).card = (Setup.occupants arr s g).card) ∧
      meas S arr s' + 1 = meas S arr s := by
  have hat : a < arr.length := by have := hL.ha; have := hL.ht; omega
  rcases step_spec S arr s s' a _ h with ⟨-, -, -, hr⟩ | ⟨b', hv, hfull, hb, hlt, hs', hr⟩ |
      ⟨hs', hr, hC⟩
  · cases hr
  · cases hr
    obtain ⟨hL', hcard, hlocb, hbN, hpos⟩ := evict_inv S arr t s s' a b hL hv hfull hb hlt hs'
    refine ⟨hL', ?_, hcard, meas_adv S arr s s' b hbN hpos (pos_lt S arr hS t s' b hL' b)⟩
    rw [Phi_adv S arr s s' b hbN hpos, ← hlocb, loc_eq, loc_eq, hpos, Function.update_self]
  · cases hr
    subst hs'
    have hL' := adv_inv S arr t s a hL hC
    refine ⟨hL', ?_, fun g => rfl, meas_adv S arr s _ a hat rfl (pos_lt S arr hS t _ a hL' a)⟩
    rw [Phi_adv S arr s _ a hat rfl, loc_eq, loc_eq]
    dsimp only
    rw [Function.update_self]

theorem step_park (S : Setup n) (arr : List (Fin n)) (t : ℕ) (s s' : St n) (a : ℕ) (g : Fin n)
    (hL : InvL S arr t s a) (h : S.step arr s a = (s', Sum.inl g)) :
    Inv0 S arr (t + 1) s' ∧ g ∈ S.G ∧ g = S.loc arr s a ∧ S.Phi arr s' = S.Phi arr s ∧
      ∀ g', (Setup.occupants arr s' g').card =
        (Setup.occupants arr s g').card + if g' = g then 1 else 0 := by
  rcases step_spec S arr s s' a _ h with ⟨hv, hlt, hs', hr⟩ | ⟨b', -, -, -, -, -, hr⟩ |
      ⟨-, hr, -⟩
  · cases hr
    subst hs'
    obtain ⟨h1, h2⟩ := park_inv S arr t s a hL hv hlt
    exact ⟨h1, hv, rfl, Phi_same S arr _ _ rfl, h2⟩
  · cases hr
  · cases hr

/-! ## The loop -/
theorem loop_spec (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (t : ℕ) :
    ∀ (f : ℕ) (s : St n) (a : ℕ), InvL S arr t s a → meas S arr s < f →
      ∃ g, (S.loop arr f s a).2 = some g ∧ Inv0 S arr (t + 1) (S.loop arr f s a).1 ∧ g ∈ S.G ∧
        (∀ x, S.D x g ≤ S.D x (S.loc arr s a) + (S.Phi arr (S.loop arr f s a).1 - S.Phi arr s)) ∧
        ∀ g', (Setup.occupants arr (S.loop arr f s a).1 g').card =
          (Setup.occupants arr s g').card + if g' = g then 1 else 0
  | 0, s, a, _, hm => absurd hm (Nat.not_lt_zero _)
  | f + 1, s, a, hL, hm => by
    rcases hst : S.step arr s a with ⟨s', g | b⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := step_park S arr t s s' a g hL hst
      have hloop : S.loop arr (f + 1) s a = (s', some g) := by simp only [Setup.loop, hst]
      rw [hloop]
      refine ⟨g, rfl, h1, h2, fun x => ?_, h5⟩
      dsimp only
      rw [h4, ← h3]; simp
    · obtain ⟨h1, h2, h3, h4⟩ := step_move S arr hS t s s' a b hL hst
      have hloop : S.loop arr (f + 1) s a = S.loop arr f s' b := by simp only [Setup.loop, hst]
      rw [hloop]
      obtain ⟨g, k1, k2, k3, k4, k5⟩ := loop_spec S arr hS t f s' b h1 (by omega)
      refine ⟨g, k1, k2, k3, fun x => ?_, fun g' => by rw [k5, h3]⟩
      have := k4 x
      have htri := hS.metric.tri x (S.loc arr s a) (S.loc arr s' b)
      rw [h2] at this; linarith

theorem meas_lt_fuel (S : Setup n) (arr : List (Fin n)) (s : St n) :
    meas S arr s < S.fuelOf arr := by
  unfold Setup.fuelOf meas
  set K := Finset.univ.sup fun u => (S.W u).length with hK
  have h1 : ∑ ℓ ∈ Finset.range arr.length, ((S.walkOf arr ℓ).length - s.pos ℓ) ≤
      ∑ _ℓ ∈ Finset.range arr.length, K := by
    apply Finset.sum_le_sum; intro ℓ _
    have : (S.walkOf arr ℓ).length ≤ K :=
      Finset.le_sup (f := fun u => (S.W u).length) (Finset.mem_univ (S.origin arr ℓ))
    omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h1
  have : arr.length * K ≤ (arr.length + 1) * (K + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-! ## Insertions -/
theorem insert_spec (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (t : ℕ)
    (ht : t < arr.length) (hI : Inv0 S arr t (S.stAfter arr t)) :
    Inv0 S arr (t + 1) (S.stAfter arr (t + 1)) ∧ S.choice arr t ∈ S.G ∧
      S.D (S.origin arr t) (S.choice arr t) ≤
        S.Phi arr (S.stAfter arr (t + 1)) - S.Phi arr (S.stAfter arr t) ∧
      ∀ g', (Setup.occupants arr (S.stAfter arr (t + 1)) g').card =
        (Setup.occupants arr (S.stAfter arr t) g').card + if g' = S.choice arr t then 1 else 0 := by
  have hL : InvL S arr t (S.stAfter arr t) t :=
    ⟨hI.core, ht, fun ℓ hℓ => hI.fresh ℓ hℓ.le, le_rfl, (hI.fresh t le_rfl).2,
      fun ℓ hℓ hne => hI.parked ℓ (lt_of_le_of_ne hℓ hne)⟩
  obtain ⟨g, k1, k2, k3, k4, k5⟩ :=
    loop_spec S arr hS t (S.fuelOf arr) (S.stAfter arr t) t hL (meas_lt_fuel S arr _)
  have hst : S.stAfter arr (t + 1) = (S.loop arr (S.fuelOf arr) (S.stAfter arr t) t).1 := rfl
  have hch : S.choice arr t = g := by unfold Setup.choice; rw [k1]; rfl
  have hloc : S.loc arr (S.stAfter arr t) t = S.origin arr t := by
    rw [loc_eq, (hI.fresh t le_rfl).1, vtx_zero S arr hS]
  rw [hst, hch]
  refine ⟨k2, k3, ?_, k5⟩
  have := k4 (S.origin arr t)
  rw [hloc, hS.metric.self] at this
  linarith

theorem all_inv (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) :
    ∀ t ≤ arr.length, Inv0 S arr t (S.stAfter arr t) ∧
      ∀ g, (Setup.occupants arr (S.stAfter arr t) g).card =
        ((Finset.range t).filter (fun t' => S.choice arr t' = g)).card := by
  intro t
  induction t with
  | zero =>
    intro _
    have hocc : ∀ g, Setup.occupants arr (S.stAfter arr 0) g = ∅ := by
      intro g; ext ℓ; simp [mem_occ, Setup.stAfter]
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro ℓ g hp; simp [Setup.stAfter] at hp
    · intro g; rw [hocc]; simp
    · intro ℓ j hj; simp [Setup.stAfter] at hj
    · intro ℓ g hp; simp [Setup.stAfter] at hp
    · intro ℓ _; simp [Setup.stAfter]
    · intro ℓ hℓ; omega
    · intro g; rw [hocc]; simp
  | succ t ih =>
    intro ht
    obtain ⟨hI, hc⟩ := ih (by omega)
    obtain ⟨h1, -, -, h4⟩ := insert_spec S arr hS t (by omega) hI
    refine ⟨h1, fun g => ?_⟩
    rw [h4, hc, Finset.range_add_one, Finset.filter_insert]
    by_cases hg : g = S.choice arr t
    · rw [if_pos hg.symm, if_pos hg, Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg (Ne.symm hg), if_neg hg, add_zero]

/-! ## The Part S stubs -/
/-- At the end every label is parked at a garage, at its current vertex. -/
theorem final_parked (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (ℓ : ℕ)
    (hℓ : ℓ < arr.length) :
    ∃ g ∈ S.G, (S.stAfter arr arr.length).park ℓ = some g ∧
      S.loc arr (S.stAfter arr arr.length) ℓ = g := by
  have hI := (all_inv S arr hS arr.length le_rfl).1
  obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.mp (hI.parked ℓ hℓ)
  obtain ⟨h1, h2⟩ := hI.core.parkG ℓ g hg
  exact ⟨g, h1, hg, h2⟩

end OnlineTransportation1195.Dev.T12.PartS
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
variable (S : Setup n) (arr : List (Fin n)) (hS : Good S arr)
include hS
/-! ## Part S: the process is well defined; final-state invariants -/
alias final_parked := OnlineTransportation1195.Dev.T12.PartS.final_parked

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartS
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
/-- A garage passed by a label is full of occupants of priority at most that label's. -/
theorem final_inv (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (ℓ : ℕ)
    (hℓ : ℓ < arr.length) (j : ℕ)
    (hj : j < (S.stAfter arr arr.length).pos ℓ) (hg : S.vtx arr ℓ j ∈ S.G) :
    (Setup.occupants arr (S.stAfter arr arr.length) (S.vtx arr ℓ j)).card = S.cap (S.vtx arr ℓ j) ∧
      ∀ b ∈ Setup.occupants arr (S.stAfter arr arr.length) (S.vtx arr ℓ j),
        S.pr (S.origin arr b) (S.vtx arr ℓ j) ≤ S.pr (S.origin arr ℓ) (S.vtx arr ℓ j) :=
  (all_inv S arr hS arr.length le_rfl).1.core.passed ℓ j hj hg

end OnlineTransportation1195.Dev.T12.PartS
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
variable (S : Setup n) (arr : List (Fin n)) (hS : Good S arr)
include hS
alias final_inv := OnlineTransportation1195.Dev.T12.PartS.final_inv

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartS
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
/-- A label is never parked at a garage it passed earlier. -/
theorem final_inv2 (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (ℓ : ℕ)
    (hℓ : ℓ < arr.length) (g : Fin n)
    (hp : (S.stAfter arr arr.length).park ℓ = some g) (j : ℕ)
    (hj : j < (S.stAfter arr arr.length).pos ℓ) : S.vtx arr ℓ j ≠ g :=
  (all_inv S arr hS arr.length le_rfl).1.core.notback ℓ g hp j hj

end OnlineTransportation1195.Dev.T12.PartS
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
variable (S : Setup n) (arr : List (Fin n)) (hS : Good S arr)
include hS
alias final_inv2 := OnlineTransportation1195.Dev.T12.PartS.final_inv2

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartS
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
/-- Each car's final garage is reached within the distance driven during its insertion. -/
theorem choice_chain (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (t : ℕ)
    (ht : t < arr.length) :
    S.choice arr t ∈ S.G ∧
      S.D (S.origin arr t) (S.choice arr t) ≤
        S.Phi arr (S.stAfter arr (t + 1)) - S.Phi arr (S.stAfter arr t) := by
  obtain ⟨-, h2, h3, -⟩ :=
    insert_spec S arr hS t ht (all_inv S arr hS t ht.le).1
  exact ⟨h2, h3⟩

end OnlineTransportation1195.Dev.T12.PartS
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
variable (S : Setup n) (arr : List (Fin n)) (hS : Good S arr)
include hS
alias choice_chain := OnlineTransportation1195.Dev.T12.PartS.choice_chain

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartS
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
/-- No garage receives more physical cars than its capacity. -/
theorem choice_count (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (g : Fin n) :
    ((Finset.range arr.length).filter (fun t => S.choice arr t = g)).card ≤ S.cap g := by
  obtain ⟨hI, hc⟩ := all_inv S arr hS arr.length le_rfl
  rw [← hc g]
  exact hI.core.capOK g

end OnlineTransportation1195.Dev.T12.PartS
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
variable (S : Setup n) (arr : List (Fin n)) (hS : Good S arr)
include hS
alias choice_count := OnlineTransportation1195.Dev.T12.PartS.choice_count

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartK
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
variable {n : ℕ}
/-- The counting step at threshold `h`. -/
theorem count_le (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (c : ℝ)
    (hW : ∀ (r u : Fin n) (h : ℝ), 0 ≤ h → Conn S.D h r u →
      ∃ j < (S.W r).length, (S.W r).getD j r = u ∧ wlen S.D (S.W r) r j ≤ c * h)
    (hpr : ∀ a b (h : ℝ), 0 ≤ h → (Conn S.D h a b ↔ S.pr a b ≤ h))
    (og : ℕ → Fin n) (hogG : ∀ t < arr.length, og t ∈ S.G)
    (hog : ∀ g, ((Finset.range arr.length).filter (fun t => og t = g)).card ≤ S.cap g)
    (h : ℝ) (hh : 0 ≤ h) :
    ((Finset.range arr.length).filter
        (fun ℓ => c * h < S.plen arr (S.stAfter arr arr.length) ℓ)).card ≤
      ((Finset.range arr.length).filter (fun t => h < S.D (S.origin arr t) (og t))).card := by
  set s := S.stAfter arr arr.length with hs
  set k := arr.length with hk
  set X := (Finset.range k).filter (fun ℓ => c * h < S.plen arr s ℓ) with hX
  have hXk : ∀ ℓ ∈ X, ℓ < k := fun ℓ hℓ => Finset.mem_range.mp (Finset.mem_filter.mp hℓ).1
  have pass : ∀ ℓ ∈ X, ∀ g, Conn S.D h (S.origin arr ℓ) g → ∃ j < s.pos ℓ, S.vtx arr ℓ j = g := by
    intro ℓ hℓ g hc
    have hlen := (Finset.mem_filter.mp hℓ).2
    obtain ⟨j, -, hjg, hjw⟩ := hW (S.origin arr ℓ) g h hh hc
    refine ⟨j, ?_, hjg⟩
    by_contra hcon
    push Not at hcon
    have hm := wlen_mono S.D hS.metric.nonneg (S.W (S.origin arr ℓ)) (S.origin arr ℓ) hcon
    have : S.plen arr s ℓ ≤ c * h := le_trans hm hjw
    linarith
  set B : Finset (Fin n) :=
    Finset.univ.filter (fun v => ∃ ℓ ∈ X, Conn S.D h (S.origin arr ℓ) v) with hB
  have memB : ∀ v, v ∈ B ↔ ∃ ℓ ∈ X, Conn S.D h (S.origin arr ℓ) v := by
    intro v; simp [hB]
  have B_closed : ∀ v w, v ∈ B → Conn S.D h v w → w ∈ B := by
    intro v w hv hvw
    obtain ⟨ℓ, hℓ, hc⟩ := (memB v).mp hv
    exact (memB w).mpr ⟨ℓ, hℓ, conn_trans S.D h hc hvw⟩
  have conn_occ : ∀ g ∈ S.G, g ∈ B → (Setup.occupants arr s g).card = S.cap g ∧
      ∀ b ∈ Setup.occupants arr s g, Conn S.D h (S.origin arr b) g := by
    intro g hgG hgB
    obtain ⟨ℓ, hℓX, hc⟩ := (memB g).mp hgB
    obtain ⟨j, hj, hjg⟩ := pass ℓ hℓX g hc
    have hvG : S.vtx arr ℓ j ∈ S.G := by rw [hjg]; exact hgG
    have hinv := final_inv S arr hS ℓ (hXk ℓ hℓX) j hj hvG
    rw [hjg] at hinv
    refine ⟨hinv.1, fun b hb => ?_⟩
    rw [hpr _ _ h hh]
    exact (hinv.2 b hb).trans ((hpr _ _ h hh).mp hc)
  have occ_B : ∀ g ∈ S.G, g ∈ B → ∀ b ∈ Setup.occupants arr s g, S.origin arr b ∈ B := by
    intro g hgG hgB b hb
    have hcb := (conn_occ g hgG hgB).2 b hb
    exact B_closed g _ hgB (conn_symm S.D hS.metric.symm h hcb)
  have X_out : ∀ ℓ ∈ X, ∀ g, s.park ℓ = some g → g ∉ B := by
    intro ℓ hℓX g hp hgB
    have hℓk := hXk ℓ hℓX
    obtain ⟨g', hg'G, hp', -⟩ := final_parked S arr hS ℓ hℓk
    have hgg : g' = g := by
      have : (some g' : Option (Fin n)) = some g := hp'.symm.trans hp
      exact Option.some_inj.mp this
    subst hgg
    have hocc : ℓ ∈ Setup.occupants arr s g' :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hℓk, hp⟩
    have hc := (conn_occ g' hg'G hgB).2 ℓ hocc
    obtain ⟨j, hj, hjg⟩ := pass ℓ hℓX g' hc
    exact final_inv2 S arr hS ℓ hℓk g' hp j hj hjg
  -- counting
  set LB := (Finset.range k).filter (fun t => S.origin arr t ∈ B) with hLB
  set GB := S.G.filter (fun g => g ∈ B) with hGB
  set P := GB.biUnion (Setup.occupants arr s) with hP
  have hPcard : P.card = ∑ g ∈ GB, S.cap g := by
    rw [hP, Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun g hg => ?_)
      obtain ⟨hgG, hgB⟩ := Finset.mem_filter.mp hg
      exact (conn_occ g hgG hgB).1
    · intro x _ y _ hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro b hbx hby
      have h1 := (Finset.mem_filter.mp hbx).2
      have h2 := (Finset.mem_filter.mp hby).2
      exact hxy (Option.some_inj.mp (h1.symm.trans h2))
  have hPsub : P ⊆ LB := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨hgG, hgB⟩ := Finset.mem_filter.mp hg
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hbg).1, occ_B g hgG hgB b hbg⟩
  have hXsub : X ⊆ LB := by
    intro ℓ hℓ
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hℓ).1,
      (memB _).mpr ⟨ℓ, hℓ, Relation.ReflTransGen.refl⟩⟩
  have hdisj : Disjoint X P := by
    rw [Finset.disjoint_left]
    intro ℓ hℓX hℓP
    obtain ⟨g, hg, hbg⟩ := Finset.mem_biUnion.mp hℓP
    exact X_out ℓ hℓX g (Finset.mem_filter.mp hbg).2 (Finset.mem_filter.mp hg).2
  have hXP : X.card + P.card ≤ LB.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hXsub hPsub)
  set Q := LB.filter (fun t => og t ∈ B) with hQ
  have hQcard : Q.card ≤ ∑ g ∈ GB, S.cap g := by
    have hsub : Q ⊆ GB.biUnion (fun g => (Finset.range k).filter (fun t => og t = g)) := by
      intro t ht
      obtain ⟨htLB, hogB⟩ := Finset.mem_filter.mp ht
      have htk := (Finset.mem_filter.mp htLB).1
      refine Finset.mem_biUnion.mpr ⟨og t, Finset.mem_filter.mpr
        ⟨hogG t (Finset.mem_range.mp htk), hogB⟩, Finset.mem_filter.mpr ⟨htk, rfl⟩⟩
    calc Q.card ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun g _ => hog g)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := LB) (fun t => og t ∈ B)
  have hYsub : LB.filter (fun t => ¬ og t ∈ B) ⊆
      (Finset.range k).filter (fun t => h < S.D (S.origin arr t) (og t)) := by
    intro t ht
    obtain ⟨htLB, hogB⟩ := Finset.mem_filter.mp ht
    obtain ⟨htk, horB⟩ := Finset.mem_filter.mp htLB
    refine Finset.mem_filter.mpr ⟨htk, ?_⟩
    by_contra hle
    push Not at hle
    exact hogB (B_closed _ _ horB (Relation.ReflTransGen.single hle))
  have hY := Finset.card_le_card hYsub
  rw [← hQ] at hsplit
  omega

/-- Counting at threshold `h` and integrating: the total distance driven is at most `c` times the
cost of any capacity-respecting assignment `og`. -/
theorem analysis (S : Setup n) (arr : List (Fin n)) (hS : Good S arr) (c : ℝ) (hc : 0 < c)
    (hW : ∀ (r u : Fin n) (h : ℝ), 0 ≤ h → Conn S.D h r u →
      ∃ j < (S.W r).length, (S.W r).getD j r = u ∧ wlen S.D (S.W r) r j ≤ c * h)
    (hpr : ∀ a b (h : ℝ), 0 ≤ h → (Conn S.D h a b ↔ S.pr a b ≤ h))
    (og : ℕ → Fin n) (hogG : ∀ t < arr.length, og t ∈ S.G)
    (hog : ∀ g, ((Finset.range arr.length).filter (fun t => og t = g)).card ≤ S.cap g) :
    S.Phi arr (S.stAfter arr arr.length) ≤
      c * ∑ t ∈ Finset.range arr.length, S.D (S.origin arr t) (og t) := by
  set s := S.stAfter arr arr.length with hs
  have hsum := sum_le_of_count (fun ℓ => S.plen arr s ℓ / c)
    (fun t => S.D (S.origin arr t) (og t)) _ (Finset.range arr.length) (Finset.range arr.length)
    rfl (fun t _ => hS.metric.nonneg _ _) (by
      intro h hh
      have hiff : ∀ ℓ, (h < S.plen arr s ℓ / c ↔ c * h < S.plen arr s ℓ) := fun ℓ => by
        rw [lt_div_iff₀ hc, mul_comm]
      rw [Finset.filter_congr (fun ℓ _ => hiff ℓ)]
      exact count_le S arr hS c hW hpr og hogG hog h hh)
  unfold Setup.Phi
  calc ∑ ℓ ∈ Finset.range arr.length, S.plen arr s ℓ
      = c * ∑ ℓ ∈ Finset.range arr.length, S.plen arr s ℓ / c := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ℓ _ => ?_)
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hc.le

end OnlineTransportation1195.Dev.T12.PartK
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
/-! ## Part K: the threshold analysis -/
alias analysis := OnlineTransportation1195.Dev.T12.PartK.analysis

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12.PartP
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T12
theorem upper {n : ℕ} (hn : 2 ≤ n) (I : TransportationInstance n) :
    ∃ A : Policy I, IsCausal I A ∧ Competitive I A (2 * (n : ℝ) - 3) := by
  have hD := Dm_metric I
  choose W hWhead hW using fun r => walks_exist hn (Dm I) hD r
  obtain ⟨pr, hpr⟩ := exists_pr (Dm I) hD
  let S : Setup n := ⟨Dm I, I.garages, capOf I, W, pr, ⟨0, by omega⟩⟩
  have hgood : ∀ r : I.Arrivals, Good S (List.ofFn r) := fun r =>
    { metric := hD
      head := hWhead
      cover := fun u v => by
        obtain ⟨j, hj, hju, -⟩ :=
          hW u v (Dm I u v) (hD.nonneg u v) (Relation.ReflTransGen.single le_rfl)
        exact ⟨j, hj, hju⟩
      total := by
        rw [List.length_ofFn]
        exact sum_capOf I }
  have hch : ∀ r : I.Arrivals, ∃ a : I.Assignment,
      ∀ t : I.Time, I.garageOf a t = S.choice (List.ofFn r) t := by
    intro r
    apply exists_perm I
    · intro t
      exact (choice_chain S _ (hgood r) t (by simp)).1
    · intro g
      have := choice_count S _ (hgood r) g
      rw [List.length_ofFn] at this
      refine le_trans (le_of_eq ?_) this
      convert card_filter_fin I.k (fun t => S.choice (List.ofFn r) t = g) using 2 <;>
        (ext; simp)
  choose A hA using hch
  refine ⟨A, ?_, ?_⟩
  · intro r q t hrq
    rw [hA, hA]
    apply choice_causal S _ _ (by simp)
    intro j hj
    have hjk : j < I.k := lt_of_le_of_lt hj t.2
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hjk]
    simp only [dite_true, Option.getD_some]
    exact hrq ⟨j, hjk⟩ hj
  · intro r
    have hc : (0 : ℝ) < 2 * (n : ℝ) - 3 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    obtain ⟨a, ha⟩ : ∃ a, I.opt r = I.cost r a := by
      unfold TransportationInstance.opt
      generalize_proofs hne
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
      exact ⟨a, ha.symm⟩
    have hlen : (List.ofFn r).length = I.k := List.length_ofFn
    have horig : ∀ t : I.Time, S.origin (List.ofFn r) t = r t := by
      intro t
      simp [Setup.origin, S, List.getD_eq_getElem?_getD]
    let og : ℕ → Fin n := fun t => if h : t < I.k then I.garageOf a ⟨t, h⟩ else S.o
    have hogG : ∀ t < (List.ofFn r).length, og t ∈ S.G := by
      intro t ht
      rw [hlen] at ht
      simp only [og, ht, dite_true]
      exact garageOf_mem I a _
    have hog : ∀ g, ((Finset.range (List.ofFn r).length).filter (fun t => og t = g)).card
        ≤ S.cap g := by
      intro g
      rw [hlen]
      refine le_trans (le_of_eq ?_) (card_garage_le I a g)
      convert (card_filter_fin I.k (fun t => og t = g)).symm using 2
      congr 1
      ext t
      simp [og]
    have hW' : ∀ (r u : Fin n) (h : ℝ), 0 ≤ h → Conn S.D h r u →
        ∃ j < (S.W r).length, (S.W r).getD j r = u ∧ wlen S.D (S.W r) r j ≤
          (2 * (n : ℝ) - 3) * h := fun r u h hh hc => hW r u h hh hc
    have hA_an := analysis S (List.ofFn r) (hgood r) _ hc hW' hpr og hogG hog
    rw [hlen] at hA_an
    have hcost : I.cost r (A r) =
        ∑ t ∈ Finset.range I.k, S.D (S.origin (List.ofFn r) t) (S.choice (List.ofFn r) t) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun t => S.D (S.origin (List.ofFn r) t) (S.choice (List.ofFn r) t))]
      unfold TransportationInstance.cost
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [horig, hA]
      rfl
    have hcosta : I.cost r a =
        ∑ t ∈ Finset.range I.k, S.D (S.origin (List.ofFn r) t) (og t) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun t => S.D (S.origin (List.ofFn r) t) (og t))]
      unfold TransportationInstance.cost
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [horig]
      simp only [og, t.2, dite_true]
      rfl
    have htel : ∑ t ∈ Finset.range I.k, S.D (S.origin (List.ofFn r) t) (S.choice (List.ofFn r) t)
        ≤ S.Phi (List.ofFn r) (S.stAfter (List.ofFn r) I.k) := by
      calc _ ≤ ∑ t ∈ Finset.range I.k, (S.Phi (List.ofFn r) (S.stAfter (List.ofFn r) (t + 1)) -
              S.Phi (List.ofFn r) (S.stAfter (List.ofFn r) t)) := by
            refine Finset.sum_le_sum (fun t ht => ?_)
            rw [Finset.mem_range] at ht
            exact (choice_chain S _ (hgood r) t (by rw [hlen]; exact ht)).2
        _ = _ := by
            rw [Finset.sum_range_sub (fun t => S.Phi (List.ofFn r) (S.stAfter (List.ofFn r) t)),
              Phi_zero, sub_zero]
    rw [hcost, ha, hcosta]
    exact htel.trans hA_an

end OnlineTransportation1195.Dev.T12.PartP
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T12
open OnlineTransportation1195.Main
variable {n : ℕ}
/-! ## Part P: the policy -/
alias upper := OnlineTransportation1195.Dev.T12.PartP.upper

theorem main (n : ℕ) (hn : 2 ≤ n) :
    PointRatio n (2 * (n : ℝ) - 3) ∧
      ∀ ρ : ℝ, ρ < 2 * (n : ℝ) - 3 → ¬ PointRatio n ρ := by
  refine ⟨⟨?_, fun I => upper hn I⟩, fun ρ hρ => lower hn ρ hρ⟩
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end OnlineTransportation1195.Dev.T12
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Main
theorem chk_optimal_point_count_ratio (n : ℕ) (hn : 2 ≤ n) :
    PointRatio n (2 * (n : ℝ) - 3) ∧
      ∀ ρ : ℝ, ρ < 2 * (n : ℝ) - 3 → ¬ PointRatio n ρ :=
  OnlineTransportation1195.Dev.T12.main n hn

end OnlineTransportation1195.Main
end

theorem solution : type_of% @OnlineTransportation1195.Main.chk_optimal_point_count_ratio := @OnlineTransportation1195.Main.chk_optimal_point_count_ratio
