-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.A10_lower
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:38:57.140753+00:00
-- url     : https://prove2.me/submissions/40a19e3a-1161-4d3a-8cdb-408644ada83e

import Mathlib
import Definitions.Def_VehicleRoutingSurvey_Routing_MetricAlgorithms

namespace Aux_A10_lower

/-- distance between indices -/
def ad (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

/-- the metric `⌈|i-j|/2⌉` (shortest-path metric of the square of a path) -/
def dd (m : ℕ) (i j : Fin (m + 1)) : ℝ := (((ad i.val j.val + 1) / 2 : ℕ) : ℝ)

theorem dd_self (m : ℕ) (i : Fin (m + 1)) : dd m i i = 0 := by
  unfold dd ad; simp

theorem dd_symm (m : ℕ) (i j : Fin (m + 1)) : dd m i j = dd m j i := by
  unfold dd ad
  congr 2
  split_ifs <;> omega

theorem dd_nonneg (m : ℕ) (i j : Fin (m + 1)) : 0 ≤ dd m i j := by
  unfold dd; exact Nat.cast_nonneg _

theorem dd_tri (m : ℕ) (i j k : Fin (m + 1)) : dd m i j ≤ dd m i k + dd m k j := by
  have : (ad i.val j.val + 1) / 2 ≤ (ad i.val k.val + 1) / 2 + (ad k.val j.val + 1) / 2 := by
    unfold ad; split_ifs <;> omega
  unfold dd
  exact_mod_cast this

theorem dd_ge_one (m : ℕ) (i j : Fin (m + 1)) (h : i ≠ j) : 1 ≤ dd m i j := by
  have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
  unfold dd
  have : 1 ≤ (ad i.val j.val + 1) / 2 := by unfold ad; split_ifs <;> omega
  exact_mod_cast this

theorem dd_val (m : ℕ) (i j : Fin (m + 1)) (c : ℕ) (h : (ad i.val j.val + 1) / 2 = c) :
    dd m i j = c := by
  unfold dd; rw [h]

theorem dd_one' (m : ℕ) (i j : Fin (m + 1)) (h : (ad i.val j.val + 1) / 2 = 1) :
    dd m i j = 1 := by
  unfold dd; rw [h]; norm_num

/-- the folding permutation: evens up, then odds down -/
def sigf (s k : ℕ) : ℕ := if k ≤ s then 2 * k else 2 * (2 * s + 1 - k) + 1

def sigi (s v : ℕ) : ℕ := if v % 2 = 0 then v / 2 else 2 * s + 1 - (v - 1) / 2

theorem sigf_lt (s k : ℕ) (hk : k < 2 * s + 2) : sigf s k < 2 * s + 2 := by
  unfold sigf; split_ifs <;> omega

theorem sigi_lt (s v : ℕ) (hv : v < 2 * s + 2) : sigi s v < 2 * s + 2 := by
  unfold sigi; split_ifs <;> omega

theorem sigi_sigf (s k : ℕ) (hk : k < 2 * s + 2) : sigi s (sigf s k) = k := by
  unfold sigf sigi; split_ifs <;> omega

theorem sigf_sigi (s v : ℕ) (hv : v < 2 * s + 2) : sigf s (sigi s v) = v := by
  unfold sigf sigi; split_ifs <;> omega

def sig (m s : ℕ) (hm : m = 2 * s + 1) : Equiv.Perm (Fin (m + 1)) where
  toFun k := ⟨sigf s k.val, by have := sigf_lt s k.val (by omega); omega⟩
  invFun v := ⟨sigi s v.val, by have := sigi_lt s v.val (by omega); omega⟩
  left_inv k := Fin.ext (sigi_sigf s k.val (by omega))
  right_inv v := Fin.ext (sigf_sigi s v.val (by omega))

theorem fr_val (m : ℕ) (k : Fin (m + 1)) :
    (finRotate (m + 1) k).val = if k.val = m then 0 else k.val + 1 := by
  rw [finRotate_succ_apply, Fin.val_add_one]
  by_cases h : k = Fin.last m
  · have e : k.val = m := by rw [h, Fin.val_last]
    rw [if_pos h, if_pos e]
  · have e : k.val ≠ m := fun e => h (Fin.ext (by rw [e, Fin.val_last]))
    rw [if_neg h, if_neg e]

theorem sig_term (m s : ℕ) (hm : m = 2 * s + 1) (k : Fin (m + 1)) :
    dd m (sig m s hm k) (sig m s hm (finRotate (m + 1) k)) = 1 := by
  have hk := k.isLt
  have h1 : (sig m s hm k).val = sigf s k.val := rfl
  have h3 : (sig m s hm (finRotate (m + 1) k)).val = sigf s (finRotate (m + 1) k).val := rfl
  rw [fr_val] at h3
  apply dd_one'
  rw [h1, h3]
  unfold ad sigf
  split_ifs <;> omega

theorem tour_sig (m s : ℕ) (hm : m = 2 * s + 1) :
    SupplyChainTheory.tourLength (dd m) (sig m s hm) = (m : ℝ) + 1 := by
  unfold SupplyChainTheory.tourLength
  rw [Finset.sum_congr rfl (fun k _ => sig_term m s hm k)]
  simp

theorem tour_ge_one (m : ℕ) (hm1 : 1 ≤ m) (τ : Equiv.Perm (Fin (m + 1))) :
    1 ≤ SupplyChainTheory.tourLength (dd m) τ := by
  unfold SupplyChainTheory.tourLength
  have h0 : (finRotate (m + 1) 0).val = 1 := by
    have hz : ¬ ((0 : Fin (m + 1)).val = m) := by rw [Fin.val_zero]; omega
    rw [fr_val, if_neg hz, Fin.val_zero]
  have hne : τ 0 ≠ τ (finRotate (m + 1) 0) := by
    intro e
    have := τ.injective e
    have := congrArg Fin.val this
    rw [h0, Fin.val_zero] at this
    omega
  have h1 := dd_ge_one m _ _ hne
  have h2 : dd m (τ 0) (τ (finRotate (m + 1) 0)) ≤
      ∑ k, dd m (τ k) (τ (finRotate (m + 1) k)) :=
    Finset.single_le_sum (f := fun k => dd m (τ k) (τ (finRotate (m + 1) k)))
      (fun k _ => dd_nonneg m _ _) (Finset.mem_univ 0)
  linarith

theorem tour_nonneg (m : ℕ) (τ : Equiv.Perm (Fin (m + 1))) :
    0 ≤ SupplyChainTheory.tourLength (dd m) τ := by
  unfold SupplyChainTheory.tourLength
  exact Finset.sum_nonneg (fun k _ => dd_nonneg m _ _)

/-- vertex with value `j` (mod `m+1`) -/
def vtx (m j : ℕ) : Fin (m + 1) := ⟨j % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

theorem vtx_val (m j : ℕ) (hj : j ≤ m) : (vtx m j).val = j := Nat.mod_eq_of_lt (by omega)

/-- the path graph `0 - 1 - ... - m` -/
def path (m : ℕ) : SimpleGraph (Fin (m + 1)) :=
  SimpleGraph.fromRel (fun i j => i.val + 1 = j.val)

theorem path_adj (m : ℕ) (i j : Fin (m + 1)) :
    (path m).Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  unfold path
  rw [SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun e => ?_, h⟩
    rw [e] at h
    omega

theorem edge_form (m : ℕ) (e : Sym2 (Fin (m + 1))) (he : e ∈ (path m).edgeSet) :
    ∃ i, i < m ∧ e = s(vtx m i, vtx m (i + 1)) := by
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro he
  rw [SimpleGraph.mem_edgeSet, path_adj] at he
  have ha := a.isLt
  have hb := b.isLt
  rcases he with h | h
  · refine ⟨a.val, by omega, ?_⟩
    have e1 : vtx m a.val = a := Fin.ext (vtx_val m a.val (by omega))
    have e2 : vtx m (a.val + 1) = b := Fin.ext (by rw [vtx_val m (a.val + 1) (by omega)]; omega)
    rw [e1, e2]
  · refine ⟨b.val, by omega, ?_⟩
    have e1 : vtx m b.val = b := Fin.ext (vtx_val m b.val (by omega))
    have e2 : vtx m (b.val + 1) = a := Fin.ext (by rw [vtx_val m (b.val + 1) (by omega)]; omega)
    rw [e1, e2, Sym2.eq_swap]

theorem edge_mem (m i : ℕ) (hi : i < m) : s(vtx m i, vtx m (i + 1)) ∈ (path m).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, path_adj, vtx_val m i (by omega), vtx_val m (i + 1) (by omega)]
  left; rfl

theorem edge_inj (m i j : ℕ) (hi : i < m) (hj : j < m)
    (h : s(vtx m i, vtx m (i + 1)) = s(vtx m j, vtx m (j + 1))) : i = j := by
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · have := congrArg Fin.val h1
    rwa [vtx_val m i (by omega), vtx_val m j (by omega)] at this
  · have := congrArg Fin.val h1
    rw [vtx_val m i (by omega), vtx_val m (j + 1) (by omega)] at this
    have := congrArg Fin.val h2
    rw [vtx_val m (i + 1) (by omega), vtx_val m j (by omega)] at this
    omega

theorem mem_ef {V : Type} {G : SimpleGraph V} {inst : Fintype G.edgeSet} {e : Sym2 V} :
    e ∈ G.edgeFinset ↔ e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset

theorem edgeCost_mk (m : ℕ) (i j : Fin (m + 1)) :
    SupplyChainTheory.edgeCost (dd m) s(i, j) = (dd m i j + dd m j i) / 2 := rfl

theorem tree_lower (m : ℕ) (G : SimpleGraph (Fin (m + 1))) {inst : Fintype G.edgeSet}
    (hG : G.IsTree) : (m : ℝ) ≤ ∑ e ∈ G.edgeFinset, SupplyChainTheory.edgeCost (dd m) e := by
  have hc := hG.card_edgeFinset
  rw [Fintype.card_fin] at hc
  have h1 : ∀ e ∈ G.edgeFinset, (1 : ℝ) ≤ SupplyChainTheory.edgeCost (dd m) e := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    have hne : a ≠ b := G.ne_of_adj (by rwa [SimpleGraph.mem_edgeSet] at he)
    rw [edgeCost_mk]
    have := dd_ge_one m a b hne
    have := dd_ge_one m b a (Ne.symm hne)
    linarith
  have h2 := Finset.card_nsmul_le_sum G.edgeFinset _ 1 h1
  rw [nsmul_eq_mul, mul_one] at h2
  have hcR : (G.edgeFinset.card : ℝ) = m := by
    have : G.edgeFinset.card = m := by omega
    rw [this]
  linarith

theorem path_cost (m : ℕ) {inst : Fintype (path m).edgeSet} (hT : (path m).IsTree) :
    ∑ e ∈ (path m).edgeFinset, SupplyChainTheory.edgeCost (dd m) e = m := by
  have hc := hT.card_edgeFinset
  rw [Fintype.card_fin] at hc
  have h1 : ∀ e ∈ (path m).edgeFinset, SupplyChainTheory.edgeCost (dd m) e = 1 := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    obtain ⟨i, hi, rfl⟩ := edge_form m e he
    rw [edgeCost_mk, dd_one' m (vtx m i) (vtx m (i + 1))
      (by rw [vtx_val m i (by omega), vtx_val m (i + 1) (by omega)]; unfold ad; split_ifs <;> omega),
      dd_one' m (vtx m (i + 1)) (vtx m i)
      (by rw [vtx_val m i (by omega), vtx_val m (i + 1) (by omega)]; unfold ad; split_ifs <;> omega)]
    norm_num
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (path m).edgeFinset.card = m := by omega
  rw [this]

theorem path_reach (m : ℕ) : ∀ k, k ≤ m → (path m).Reachable (vtx m 0) (vtx m k) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro hk
    refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
    rw [path_adj, vtx_val m k (by omega), vtx_val m (k + 1) hk]
    left; rfl

theorem path_tree (m : ℕ) : (path m).IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨0⟩⟩
    have h0 : ∀ u : Fin (m + 1), (path m).Reachable (vtx m 0) u := by
      intro u
      have e : vtx m u.val = u := Fin.ext (vtx_val m u.val (by have := u.isLt; omega))
      rw [← e]
      exact path_reach m u.val (by have := u.isLt; omega)
    exact (h0 u).symm.trans (h0 v)
  · have hE : (path m).edgeFinset =
        (Finset.range m).image (fun i => s(vtx m i, vtx m (i + 1))) := by
      ext e
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_image]
      constructor
      · intro he
        obtain ⟨i, hi, rfl⟩ := edge_form m e he
        exact ⟨i, Finset.mem_range.mpr hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact edge_mem m i (Finset.mem_range.mp hi)
    have hcard : (path m).edgeFinset.card = m := by
      rw [hE, Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj h
      exact edge_inj m i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hcard, Nat.card_eq_fintype_card,
      Fintype.card_fin]

theorem path_degree (m : ℕ) (hm : 2 ≤ m) (v : Fin (m + 1)) {inst : Fintype ((path m).neighborSet v)} :
    Odd ((path m).degree v) ↔ (v.val = 0 ∨ v.val = m) := by
  have hv := v.isLt
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases h0 : v.val = 0
  · have : (path m).neighborFinset v = {vtx m 1} := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, path_adj, Finset.mem_singleton]
      constructor
      · intro h; apply Fin.ext; rw [vtx_val m 1 (by omega)]; omega
      · intro h; rw [h, vtx_val m 1 (by omega)]; omega
    rw [this, Finset.card_singleton]
    simp [h0]
  by_cases hm' : v.val = m
  · have : (path m).neighborFinset v = {vtx m (m - 1)} := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, path_adj, Finset.mem_singleton]
      have hw := w.isLt
      constructor
      · intro h; apply Fin.ext; rw [vtx_val m (m - 1) (by omega)]; omega
      · intro h; rw [h, vtx_val m (m - 1) (by omega)]; omega
    rw [this, Finset.card_singleton]
    simp [hm']
  · have : (path m).neighborFinset v = {vtx m (v.val - 1), vtx m (v.val + 1)} := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, path_adj, Finset.mem_insert, Finset.mem_singleton]
      have hw := w.isLt
      constructor
      · intro h
        rcases h with h | h
        · right; apply Fin.ext; rw [vtx_val m (v.val + 1) (by omega)]; omega
        · left; apply Fin.ext; rw [vtx_val m (v.val - 1) (by omega)]; omega
      · intro h
        rcases h with h | h
        · rw [h, vtx_val m (v.val - 1) (by omega)]; omega
        · rw [h, vtx_val m (v.val + 1) (by omega)]; omega
    have hne : vtx m (v.val - 1) ≠ vtx m (v.val + 1) := by
      intro h
      have := congrArg Fin.val h
      rw [vtx_val m (v.val - 1) (by omega), vtx_val m (v.val + 1) (by omega)] at this
      omega
    rw [this, Finset.card_pair hne]
    simp only [h0, hm', or_self, iff_false]
    decide

/-- the forward walk `0, 1, ..., k` in the complete graph -/
def fw (m : ℕ) : (k : ℕ) → (⊤ : SimpleGraph (Fin (m + 1))).Walk (vtx m 0) (vtx m k)
  | 0 => SimpleGraph.Walk.nil
  | k + 1 =>
    if h : vtx m k = vtx m (k + 1) then h ▸ fw m k else
      (fw m k).concat ((SimpleGraph.top_adj _ _).mpr h)

theorem fw_edges (m k : ℕ) (hk : k + 1 ≤ m) :
    (fw m (k + 1)).edges = (fw m k).edges ++ [s(vtx m k, vtx m (k + 1))] := by
  have h : vtx m k ≠ vtx m (k + 1) := by
    intro e
    have := congrArg Fin.val e
    rw [vtx_val m k (by omega), vtx_val m (k + 1) hk] at this
    omega
  show (if h : vtx m k = vtx m (k + 1) then h ▸ fw m k else
      (fw m k).concat ((SimpleGraph.top_adj _ _).mpr h)).edges = _
  rw [dif_neg h, SimpleGraph.Walk.edges_concat, List.concat_eq_append]

theorem fw_support (m k : ℕ) (hk : k + 1 ≤ m) :
    (fw m (k + 1)).support = (fw m k).support ++ [vtx m (k + 1)] := by
  have h : vtx m k ≠ vtx m (k + 1) := by
    intro e
    have := congrArg Fin.val e
    rw [vtx_val m k (by omega), vtx_val m (k + 1) hk] at this
    omega
  show (if h : vtx m k = vtx m (k + 1) then h ▸ fw m k else
      (fw m k).concat ((SimpleGraph.top_adj _ _).mpr h)).support = _
  rw [dif_neg h, SimpleGraph.Walk.support_concat]

theorem fw_support_eq (m : ℕ) : ∀ k, k ≤ m → (fw m k).support = (List.range (k + 1)).map (vtx m) := by
  intro k
  induction k with
  | zero =>
    intro _
    rfl
  | succ k ih =>
    intro hk
    rw [fw_support m k hk, ih (by omega), List.range_succ (n := k + 1), List.map_append,
      List.map_singleton]

theorem map_vtx_eq (m : ℕ) : (List.range (m + 1)).map (vtx m) = List.finRange (m + 1) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < m + 1 := by simpa using h1
  apply Fin.ext
  simp [vtx, Nat.mod_eq_of_lt hi]

theorem fw_edges_mem (m : ℕ) : ∀ k, k ≤ m → ∀ e,
    (e ∈ (fw m k).edges ↔ ∃ i, i < k ∧ e = s(vtx m i, vtx m (i + 1))) := by
  intro k
  induction k with
  | zero =>
    intro _ e
    have : (fw m 0).edges = [] := rfl
    rw [this]
    simp
  | succ k ih =>
    intro hk e
    rw [fw_edges m k hk, List.mem_append, ih (by omega), List.mem_singleton]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨k, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      by_cases hik : i < k
      · exact Or.inl ⟨i, hik, h⟩
      · right; rw [h, show i = k by omega]

theorem fw_nodup (m : ℕ) : ∀ k, k ≤ m → (fw m k).edges.Nodup := by
  intro k
  induction k with
  | zero =>
    intro _
    exact List.nodup_nil
  | succ k ih =>
    intro hk
    rw [fw_edges m k hk, List.nodup_append]
    refine ⟨ih (by omega), List.nodup_singleton _, ?_⟩
    intro e he e' he' hee
    rw [List.mem_singleton] at he'
    rw [hee, he'] at he
    obtain ⟨i, hi, h⟩ := (fw_edges_mem m k (by omega) _).mp he
    have := edge_inj m k i (by omega) (by omega) h
    omega

theorem edgeCost_nonneg (m : ℕ) (e : Sym2 (Fin (m + 1))) :
    0 ≤ SupplyChainTheory.edgeCost (dd m) e := by
  refine Sym2.ind (fun a b => ?_) e
  rw [edgeCost_mk]
  linarith [dd_nonneg m a b, dd_nonneg m b a]

end Aux_A10_lower

open Aux_A10_lower in
theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ (n : ℕ) (d : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)),
      N ≤ n ∧ 1 ≤ n ∧ SupplyChainTheory.IsMetric d ∧
      0 < SupplyChainTheory.optTourLength d ∧ VehicleRoutingSurvey.Routing.ChristofidesRun d τ ∧
      (3 / 2 - ε) * SupplyChainTheory.optTourLength d < SupplyChainTheory.tourLength d τ := by
  intro ε hε N
  obtain ⟨s, hsN, hs1, hsε⟩ : ∃ s : ℕ, N ≤ s ∧ 1 ≤ s ∧ 1 / ε ≤ (s : ℝ) := by
    refine ⟨N + ⌈1 / ε⌉₊ + 1, by omega, by omega, ?_⟩
    have := Nat.le_ceil (1 / ε)
    push_cast
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  set m := 2 * s + 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hmet : SupplyChainTheory.IsMetric (dd m) :=
    ⟨dd_symm m, dd_nonneg m, dd_self m, fun i j k => dd_tri m i j k⟩
  have hbdd : BddBelow (Set.range (SupplyChainTheory.tourLength (dd m))) :=
    ⟨0, by rintro _ ⟨τ, rfl⟩; exact tour_nonneg m τ⟩
  have hpos : 0 < SupplyChainTheory.optTourLength (dd m) := by
    unfold SupplyChainTheory.optTourLength
    have : (1 : ℝ) ≤ sInf (Set.range (SupplyChainTheory.tourLength (dd m))) :=
      le_csInf (Set.range_nonempty _) (by rintro _ ⟨τ, rfl⟩; exact tour_ge_one m (by omega) τ)
    linarith
  have hopt : SupplyChainTheory.optTourLength (dd m) ≤ (m : ℝ) + 1 := by
    unfold SupplyChainTheory.optTourLength
    rw [← tour_sig m s hm]
    exact csInf_le hbdd (Set.mem_range_self _)
  -- the matching edge
  have hv0 : (vtx m 0).val = 0 := vtx_val m 0 (by omega)
  have hvm : (vtx m m).val = m := vtx_val m m le_rfl
  have h0m : vtx m m ≠ vtx m 0 := by
    intro e; have := congrArg Fin.val e; rw [hv0, hvm] at this; omega
  have hodd : SupplyChainTheory.oddNodes (path m) = {vtx m 0, vtx m m} := by
    ext v
    unfold SupplyChainTheory.oddNodes
    rw [Finset.mem_filter, path_degree m hm2 v, Finset.mem_insert, Finset.mem_singleton]
    have := v.isLt
    constructor
    · rintro ⟨_, h | h⟩
      · left; apply Fin.ext; rw [hv0, h]
      · right; apply Fin.ext; rw [hvm, h]
    · rintro (h | h)
      · exact ⟨Finset.mem_univ _, Or.inl (by rw [h, hv0])⟩
      · exact ⟨Finset.mem_univ _, Or.inr (by rw [h, hvm])⟩
  refine ⟨m + 1, dd m, Equiv.refl _, by omega, by omega, hmet, hpos, ?_, ?_⟩
  · unfold VehicleRoutingSurvey.Routing.ChristofidesRun
    refine ⟨path m, {s(vtx m 0, vtx m m)}, ?_, ?_, vtx m 0, (fw m m).concat
      ((SimpleGraph.top_adj _ _).mpr h0m), ?_, ?_⟩
    · unfold SupplyChainTheory.IsMST
      refine ⟨path_tree m, fun T' hT' => ?_⟩
      unfold SupplyChainTheory.graphWeight
      rw [path_cost m (path_tree m)]
      exact tree_lower m T' hT'
    · unfold SupplyChainTheory.IsMinMatchingOn
      rw [hodd]
      have hperf : SupplyChainTheory.IsPerfectMatchingOn {vtx m 0, vtx m m}
          {s(vtx m 0, vtx m m)} := by
        unfold SupplyChainTheory.IsPerfectMatchingOn
        refine ⟨?_, ?_⟩
        · intro e he
          rw [Finset.mem_singleton] at he
          subst he
          refine ⟨fun hd => h0m (Sym2.mk_isDiag_iff.mp hd).symm, ?_⟩
          intro v hv
          rcases Sym2.mem_iff.mp hv with h | h <;> simp [h]
        · intro v hv
          refine ⟨s(vtx m 0, vtx m m), ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
          · rcases Finset.mem_insert.mp hv with h | h
            · rw [h]; exact Sym2.mem_mk_left _ _
            · rw [Finset.mem_singleton.mp h]; exact Sym2.mem_mk_right _ _
          · rintro e ⟨he, _⟩
            exact Finset.mem_singleton.mp he
      refine ⟨hperf, fun M' hM' => ?_⟩
      unfold SupplyChainTheory.IsPerfectMatchingOn at hM'
      obtain ⟨e, ⟨heM, h0e⟩, _⟩ := hM'.2 (vtx m 0) (by simp)
      have hediag := (hM'.1 e heM).1
      have hend := (hM'.1 e heM).2
      have hee : e = s(vtx m 0, vtx m m) := by
        obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp h0e
        subst hw
        have hw' : w ∈ ({vtx m 0, vtx m m} : Finset (Fin (m + 1))) := hend w (Sym2.mem_mk_right _ _)
        rcases Finset.mem_insert.mp hw' with h | h
        · exfalso; apply hediag; rw [h]; exact Sym2.mk_isDiag_iff.mpr rfl
        · rw [Finset.mem_singleton.mp h]
      unfold SupplyChainTheory.edgeSetWeight
      rw [Finset.sum_singleton]
      have := Finset.single_le_sum (f := fun e => SupplyChainTheory.edgeCost (dd m) e)
        (fun e _ => edgeCost_nonneg m e) heM
      rw [hee] at this
      exact this
    · -- edges of the closed walk
      rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append]
      have hnd1 := fw_nodup m m le_rfl
      have hnot : s(vtx m m, vtx m 0) ∉ (fw m m).edges := by
        intro h
        obtain ⟨i, hi, h⟩ := (fw_edges_mem m m le_rfl _).mp h
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have := congrArg Fin.val h1; rw [hvm, vtx_val m i (by omega)] at this; omega
        · have := congrArg Fin.val h1; rw [hvm, vtx_val m (i + 1) (by omega)] at this
          have := congrArg Fin.val h2; rw [hv0, vtx_val m i (by omega)] at this
          omega
      have hndL : ((fw m m).edges ++ [s(vtx m m, vtx m 0)]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hnd1, List.nodup_singleton _, ?_⟩
        intro e he e' he' hee
        rw [List.mem_singleton] at he'
        rw [hee, he'] at he
        exact hnot he
      have hpathE : s(vtx m 0, vtx m m) ∉ (path m).edgeSet := by
        rw [SimpleGraph.mem_edgeSet, path_adj, hv0, hvm]
        omega
      rw [Multiset.Nodup.ext (Multiset.coe_nodup.mpr hndL)]
      · intro e
        rw [Multiset.mem_coe, Multiset.mem_add, Finset.mem_val, Finset.mem_val,
          Finset.mem_singleton, List.mem_append, List.mem_singleton, fw_edges_mem m m le_rfl,
          mem_ef]
        constructor
        · rintro (⟨i, hi, rfl⟩ | rfl)
          · exact Or.inl (edge_mem m i hi)
          · exact Or.inr Sym2.eq_swap
        · rintro (h | rfl)
          · exact Or.inl (edge_form m e h)
          · exact Or.inr Sym2.eq_swap
      · rw [Multiset.nodup_add]
        refine ⟨Finset.nodup _, Finset.nodup _, ?_⟩
        rw [Multiset.disjoint_left]
        intro e he he'
        rw [Finset.mem_val, Finset.mem_singleton] at he'
        rw [Finset.mem_val, mem_ef, he'] at he
        exact hpathE he
    · unfold SupplyChainTheory.IsShortcut
      rw [SimpleGraph.Walk.support_concat, fw_support_eq m m le_rfl,
        map_vtx_eq]
      refine ⟨fun v => List.mem_append_left _ (List.mem_finRange v), fun a b => ?_⟩
      simp only [Equiv.refl_symm, Equiv.refl_apply]
      rw [List.idxOf_append_of_mem (List.mem_finRange a), List.idxOf_append_of_mem (List.mem_finRange b),
        List.idxOf_finRange, List.idxOf_finRange, Fin.lt_iff_val_lt_val]
  · -- cost of the Christofides tour
    have hcost : SupplyChainTheory.tourLength (dd m) (Equiv.refl _) = (m : ℝ) + (s + 1 : ℝ) := by
      unfold SupplyChainTheory.tourLength
      simp only [Equiv.refl_apply]
      let f : ℕ → ℝ := fun j => dd m (vtx m j) (vtx m (j + 1))
      have hterm : ∀ k : Fin (m + 1), dd m k (finRotate (m + 1) k) = f k.val := by
        intro k
        have e1 : vtx m k.val = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
        have e2 : vtx m (k.val + 1) = finRotate (m + 1) k := by
          apply Fin.ext
          rw [fr_val]
          show (k.val + 1) % (m + 1) = _
          by_cases h : k.val = m
          · rw [if_pos h, h, Nat.mod_self]
          · rw [if_neg h]; exact Nat.mod_eq_of_lt (by have := k.isLt; omega)
        show dd m k (finRotate (m + 1) k) = dd m (vtx m k.val) (vtx m (k.val + 1))
        rw [e1, e2]
      rw [Finset.sum_congr rfl (fun k _ => hterm k), Fin.sum_univ_eq_sum_range f (m + 1),
        Finset.sum_range_succ]
      have hmid : ∀ i ∈ Finset.range m, f i = 1 := by
        intro i hi
        rw [Finset.mem_range] at hi
        show dd m (vtx m i) (vtx m (i + 1)) = 1
        apply dd_one'
        rw [vtx_val m i (by omega), vtx_val m (i + 1) (by omega)]
        unfold ad; split_ifs <;> omega
      rw [Finset.sum_congr rfl hmid, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have hz : (vtx m (m + 1)).val = 0 := Nat.mod_self _
      have hlast : f m = (s + 1 : ℝ) := by
        show dd m (vtx m m) (vtx m (m + 1)) = _
        rw [dd_val m (vtx m m) (vtx m (m + 1)) (s + 1) (by rw [hvm, hz]; unfold ad; split_ifs <;> omega)]
        simp
      rw [hlast]
    rw [hcost]
    have hmR : (m : ℝ) = 2 * (s : ℝ) + 1 := by rw [hm]; push_cast; ring
    have h3 : 1 < ε * ((m : ℝ) + 1) := by
      have h4 := mul_le_mul_of_nonneg_left hsε hε.le
      have h5 : ε * (1 / ε) = 1 := by field_simp
      have h6 : ε * ((m : ℝ) + 1) = 2 * (ε * s) + 2 * ε := by rw [hmR]; ring
      linarith
    by_cases h2 : ε ≤ 3 / 2
    · have := mul_le_mul_of_nonneg_left hopt (by linarith : (0 : ℝ) ≤ 3 / 2 - ε)
      have e2 : (3 / 2 - ε) * ((m : ℝ) + 1) = 3 / 2 * (m : ℝ) + 3 / 2 - ε * ((m : ℝ) + 1) := by ring
      linarith
    · push_neg at h2
      have : (3 / 2 - ε) * SupplyChainTheory.optTourLength (dd m) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hpos
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      linarith
