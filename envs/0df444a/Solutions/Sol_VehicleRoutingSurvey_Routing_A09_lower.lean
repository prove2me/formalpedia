-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.A09_lower
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:29:16.526816+00:00
-- url     : https://prove2.me/submissions/2b190f66-099a-4d8c-85e6-60201d1fc165

import Mathlib
import Definitions.Def_VehicleRoutingSurvey_Routing_MetricAlgorithms

namespace Aux_A09_lower

open TSPHeuristics.Shared

section Lists
variable {α : Type} (d : α → α → ℝ)

def pl : α → List α → ℝ
  | _, [] => 0
  | x, y :: r => d x y + pl y r

def lst : α → List α → α
  | x, [] => x
  | _, y :: r => lst y r

def cyc (L : List α) : ℝ := (List.zipWith d L (L.rotate 1)).sum

theorem zip_eq (x0 : α) : ∀ (x : α) (l : List α),
    (List.zipWith d (x :: l) (l ++ [x0])).sum = pl d x l + d (lst x l) x0
  | x, [] => by simp [pl, lst]
  | x, y :: r => by
    have ih := zip_eq x0 y r
    show (List.zipWith d (x :: y :: r) (y :: (r ++ [x0]))).sum = _
    rw [List.zipWith_cons_cons, List.sum_cons, ih]
    simp only [pl, lst]
    ring

theorem rot1 (x : α) (l : List α) : (x :: l).rotate 1 = l ++ [x] := by
  simp

theorem cyc_cons (x : α) (l : List α) : cyc d (x :: l) = pl d x l + d (lst x l) x := by
  unfold cyc
  rw [rot1]
  exact zip_eq d x x l

theorem three (x y z : α) (L : List α) :
    cyc d (x :: y :: z :: L) = cyc d (x :: z :: L) + d x y + d y z - d x z := by
  rw [cyc_cons, cyc_cons]
  simp only [pl, lst]
  ring

end Lists

/-- the metric -/
def dd (m : ℕ) (i j : Fin (m + 1)) : ℝ :=
  if i = j then 0 else
    if i.val = 0 ∨ j.val = 0 ∨ i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val ∨ i.val + j.val + 1 = 2 * m
    then 1 else 2

theorem dd_self (m : ℕ) (i : Fin (m + 1)) : dd m i i = 0 := by
  simp [dd]

theorem dd_one (m : ℕ) (i j : Fin (m + 1)) (h : i.val ≠ j.val)
    (hc : i.val = 0 ∨ j.val = 0 ∨ i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val ∨ i.val + j.val + 1 = 2 * m) :
    dd m i j = 1 := by
  have h' : i ≠ j := fun e => h (congrArg Fin.val e)
  unfold dd
  rw [if_neg h', if_pos hc]

theorem dd_two (m : ℕ) (i j : Fin (m + 1)) (h : i.val ≠ j.val)
    (hc : ¬ (i.val = 0 ∨ j.val = 0 ∨ i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val ∨
      i.val + j.val + 1 = 2 * m)) :
    dd m i j = 2 := by
  have h' : i ≠ j := fun e => h (congrArg Fin.val e)
  unfold dd
  rw [if_neg h', if_neg hc]

theorem dd_ge_one (m : ℕ) (i j : Fin (m + 1)) (h : i ≠ j) : 1 ≤ dd m i j := by
  unfold dd
  rw [if_neg h]
  split_ifs <;> norm_num

theorem dd_le_two (m : ℕ) (i j : Fin (m + 1)) : dd m i j ≤ 2 := by
  unfold dd
  split_ifs <;> norm_num

theorem dd_nonneg (m : ℕ) (i j : Fin (m + 1)) : 0 ≤ dd m i j := by
  unfold dd
  split_ifs <;> norm_num

theorem dd_symm (m : ℕ) (i j : Fin (m + 1)) : dd m i j = dd m j i := by
  by_cases h : i = j
  · subst h; rfl
  · have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
    by_cases hc : i.val = 0 ∨ j.val = 0 ∨ i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val ∨
        i.val + j.val + 1 = 2 * m
    · rw [dd_one m i j hv hc, dd_one m j i (Ne.symm hv) (by omega)]
    · rw [dd_two m i j hv hc, dd_two m j i (Ne.symm hv) (by omega)]

theorem dd_tri (m : ℕ) (i j k : Fin (m + 1)) : dd m i k ≤ dd m i j + dd m j k := by
  by_cases hik : i = k
  · subst hik; rw [dd_self]; linarith [dd_nonneg m i j, dd_nonneg m j i]
  by_cases hij : i = j
  · subst hij; rw [dd_self]; linarith
  by_cases hjk : j = k
  · subst hjk; rw [dd_self]; linarith
  linarith [dd_le_two m i k, dd_ge_one m i j hij, dd_ge_one m j k hjk]

theorem dd_tsp (m : ℕ) : IsTSPDist (dd m) where
  symm := dd_symm m
  nonneg := dd_nonneg m
  triangle := dd_tri m
  diag := dd_self m

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
  have key : sigf s k.val ≠ sigf s (if k.val = m then 0 else k.val + 1) ∧
      (sigf s k.val = 0 ∨ sigf s (if k.val = m then 0 else k.val + 1) = 0 ∨
        sigf s k.val + 2 ≤ sigf s (if k.val = m then 0 else k.val + 1) ∨
        sigf s (if k.val = m then 0 else k.val + 1) + 2 ≤ sigf s k.val ∨
        sigf s k.val + sigf s (if k.val = m then 0 else k.val + 1) + 1 = 2 * m) := by
    unfold sigf
    split_ifs <;> omega
  apply dd_one
  · rw [h1, h3]; exact key.1
  · rw [h1, h3]; exact key.2

theorem tour_sig (m s : ℕ) (hm : m = 2 * s + 1) :
    tourLength (dd m) (sig m s hm) = (m : ℝ) + 1 := by
  unfold tourLength
  rw [Finset.sum_congr rfl (fun k _ => sig_term m s hm k)]
  simp

theorem tour_pos (m : ℕ) (hm1 : 1 ≤ m) (τ : Equiv.Perm (Fin (m + 1))) :
    0 < tourLength (dd m) τ := by
  unfold tourLength
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

/-- vertex with value `j` (mod `m+1`) -/
def vtx (m j : ℕ) : Fin (m + 1) := ⟨j % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

theorem vtx_val (m j : ℕ) (hj : j ≤ m) : (vtx m j).val = j := Nat.mod_eq_of_lt (by omega)

def Lst (m : ℕ) : ℕ → List (Fin (m + 1))
  | 0 => []
  | k + 1 => vtx m (k + 1) :: Lst m k

theorem mem_Lst (m : ℕ) : ∀ k x, x ∈ Lst m k → ∃ j, 1 ≤ j ∧ j ≤ k ∧ x = vtx m j
  | 0, x, hx => by simp [Lst] at hx
  | k + 1, x, hx => by
    simp only [Lst, List.mem_cons] at hx
    rcases hx with h | h
    · exact ⟨k + 1, by omega, le_rfl, h⟩
    · obtain ⟨j, h1, h2, h3⟩ := mem_Lst m k x h
      exact ⟨j, h1, by omega, h3⟩


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

/-- star graph centred at 0 -/
def star (m : ℕ) : SimpleGraph (Fin (m + 1)) := SimpleGraph.fromRel (fun i _ => i.val = 0)

theorem star_adj (m : ℕ) (i j : Fin (m + 1)) :
    (star m).Adj i j ↔ i ≠ j ∧ (i.val = 0 ∨ j.val = 0) := by
  unfold star
  rw [SimpleGraph.fromRel_adj]

theorem edge_form (m : ℕ) (e : Sym2 (Fin (m + 1))) (he : e ∈ (star m).edgeSet) :
    ∃ j : Fin (m + 1), j.val ≠ 0 ∧ e = s(0, j) := by
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro he
  rw [SimpleGraph.mem_edgeSet, star_adj] at he
  obtain ⟨hne, ha | hb⟩ := he
  · have ha0 : a = 0 := Fin.ext (by simp [ha])
    subst ha0
    exact ⟨b, fun hb => hne (Fin.ext (by simp [hb])), rfl⟩
  · have hb0 : b = 0 := Fin.ext (by simp [hb])
    subst hb0
    exact ⟨a, fun ha => hne (Fin.ext (by simp [ha])), Sym2.eq_swap⟩

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

theorem star_cost (m : ℕ) {inst : Fintype (star m).edgeSet} (hT : (star m).IsTree) :
    ∑ e ∈ (star m).edgeFinset, SupplyChainTheory.edgeCost (dd m) e = m := by
  have hc := hT.card_edgeFinset
  rw [Fintype.card_fin] at hc
  have h1 : ∀ e ∈ (star m).edgeFinset, SupplyChainTheory.edgeCost (dd m) e = 1 := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    obtain ⟨j, hj, rfl⟩ := edge_form m e he
    rw [edgeCost_mk, dd_one m 0 j (by rw [Fin.val_zero]; omega) (Or.inl rfl),
      dd_one m j 0 (by rw [Fin.val_zero]; omega) (Or.inr (Or.inl rfl))]
    norm_num
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (star m).edgeFinset.card = m := by omega
  rw [this]

theorem star_tree (m : ℕ) : (star m).IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨0⟩⟩
    have h0 : ∀ u : Fin (m + 1), (star m).Reachable u 0 := by
      intro u
      by_cases hu : u = 0
      · rw [hu]
      · exact SimpleGraph.Adj.reachable ((star_adj m u 0).mpr ⟨hu, Or.inr rfl⟩)
    exact (h0 u).trans (h0 v).symm
  · have hE : (star m).edgeFinset =
        (Finset.univ.erase (0 : Fin (m + 1))).image (fun j => s(0, j)) := by
      ext e
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_image]
      constructor
      · intro he
        obtain ⟨j, hj, rfl⟩ := edge_form m e he
        refine ⟨j, Finset.mem_erase.mpr ⟨fun h => hj (by simp [h]), Finset.mem_univ _⟩, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rw [SimpleGraph.mem_edgeSet, star_adj]
        exact ⟨Ne.symm (Finset.mem_erase.mp hj).1, Or.inl rfl⟩
    have hinj : Function.Injective (fun j : Fin (m + 1) => s(0, j)) :=
      fun a b h => Sym2.congr_right.mp h
    have hcard : (star m).edgeFinset.card = m := by
      rw [hE, Finset.card_image_of_injective _ hinj]
      simp
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hcard, Nat.card_eq_fintype_card,
      Fintype.card_fin]

/-- a loop from the centre to `j` and back -/
def L (m : ℕ) (j : Fin (m + 1)) : (star m).Walk 0 0 :=
  if h : j = 0 then SimpleGraph.Walk.nil else
    SimpleGraph.Walk.cons ((star_adj m 0 j).mpr ⟨Ne.symm h, Or.inl rfl⟩)
      (SimpleGraph.Walk.cons ((star_adj m j 0).mpr ⟨h, Or.inr rfl⟩) SimpleGraph.Walk.nil)

theorem L_edges (m : ℕ) (j : Fin (m + 1)) (h : j ≠ 0) : (L m j).edges = [s(0, j), s(j, 0)] := by
  unfold L
  rw [dif_neg h]
  rfl

theorem L_support (m : ℕ) (j : Fin (m + 1)) (h : j ≠ 0) : (L m j).support = [0, j, 0] := by
  unfold L
  rw [dif_neg h]
  rfl

def W (m : ℕ) : ℕ → (star m).Walk 0 0
  | 0 => SimpleGraph.Walk.nil
  | k + 1 => (W m k).append (L m (vtx m (k + 1)))

theorem vtx_ne (m k : ℕ) (hk : k + 1 ≤ m) : vtx m (k + 1) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [vtx_val m (k + 1) hk, Fin.val_zero] at this
  omega

theorem W_edges (m k : ℕ) (hk : k + 1 ≤ m) :
    (W m (k + 1)).edges = (W m k).edges ++ [s(0, vtx m (k + 1)), s(vtx m (k + 1), 0)] := by
  show ((W m k).append (L m (vtx m (k + 1)))).edges = _
  rw [SimpleGraph.Walk.edges_append, L_edges m _ (vtx_ne m k hk)]

theorem W_support (m k : ℕ) (hk : k + 1 ≤ m) :
    (W m (k + 1)).support = (W m k).support ++ [vtx m (k + 1), 0] := by
  show ((W m k).append (L m (vtx m (k + 1)))).support = _
  rw [SimpleGraph.Walk.support_append, L_support m _ (vtx_ne m k hk)]
  rfl

theorem count_pair {β : Type} [DecidableEq β] (e x : β) :
    [x, x].count e = if x = e then 2 else 0 := by
  by_cases h : x = e
  · subst h; simp
  · rw [if_neg h]
    exact List.count_eq_zero.mpr (by simp [Ne.symm h])

theorem W_count (m : ℕ) (j : Fin (m + 1)) (hj1 : 1 ≤ j.val) :
    ∀ k, k ≤ m → (W m k).edges.count s(0, j) = if j.val ≤ k then 2 else 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [if_neg (show ¬ (j.val ≤ 0) by omega)]
    rfl
  | succ k ih =>
    intro hk
    rw [W_edges m k hk, List.count_append, ih (by omega),
      show s(vtx m (k + 1), 0) = s(0, vtx m (k + 1)) from Sym2.eq_swap, count_pair]
    have hv := vtx_val m (k + 1) hk
    by_cases hjk : j.val ≤ k
    · have hne : s(0, vtx m (k + 1)) ≠ s(0, j) := by
        intro h
        have := congrArg Fin.val (Sym2.congr_right.mp h)
        omega
      rw [if_pos hjk, if_neg hne]
      simp [show j.val ≤ k + 1 by omega]
    · rw [if_neg hjk]
      by_cases hje : j.val = k + 1
      · have he : s(0, vtx m (k + 1)) = s(0, j) := by
          rw [Sym2.congr_right]; exact Fin.ext (by rw [hv, hje])
        rw [if_pos he]
        simp [show j.val ≤ k + 1 by omega]
      · have hne : s(0, vtx m (k + 1)) ≠ s(0, j) := by
          intro h
          have := congrArg Fin.val (Sym2.congr_right.mp h)
          omega
        rw [if_neg hne]
        simp [show ¬ j.val ≤ k + 1 by omega]

theorem W_supp (m : ℕ) : ∀ k, k ≤ m → ((W m k).support.length = 2 * k + 1) ∧
    ∀ x : Fin (m + 1), (x.val = 0 → x ∈ (W m k).support ∧ (W m k).support.idxOf x = 0) ∧
      (1 ≤ x.val → x.val ≤ k → x ∈ (W m k).support ∧ (W m k).support.idxOf x = 2 * x.val - 1) ∧
      (k < x.val → x ∉ (W m k).support) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, fun x => ⟨fun hx => ?_, fun h1 h2 => absurd h2 (by omega), fun hx => ?_⟩⟩
    · have : x = 0 := Fin.ext (by simp [hx])
      subst this
      exact ⟨by simp [W], by simp [W]⟩
    · intro hmem
      have : x = 0 := by simpa [W] using hmem
      rw [this, Fin.val_zero] at hx
      omega
  | succ k ih =>
    intro hk
    obtain ⟨ihl, ih⟩ := ih (by omega)
    have hv := vtx_val m (k + 1) hk
    rw [W_support m k hk]
    refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil, ihl]; omega, fun x => ⟨fun hx => ?_, fun h1 h2 => ?_, fun hx => ?_⟩⟩
    · obtain ⟨h1, h2⟩ := (ih x).1 hx
      exact ⟨List.mem_append_left _ h1, by rw [List.idxOf_append_of_mem h1, h2]⟩
    · by_cases hxk : x.val ≤ k
      · obtain ⟨h3, h4⟩ := (ih x).2.1 h1 hxk
        exact ⟨List.mem_append_left _ h3, by rw [List.idxOf_append_of_mem h3, h4]⟩
      · have hxv : x = vtx m (k + 1) := Fin.ext (by rw [hv]; omega)
        have hnm := (ih x).2.2 (by omega)
        refine ⟨List.mem_append_right _ (by simp [hxv]), ?_⟩
        rw [List.idxOf_append_of_notMem hnm, ihl, hxv, List.idxOf_cons_self, hv]
        omega
    · have hnm := (ih x).2.2 (by omega)
      intro hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hnm h
      · rcases List.mem_cons.mp h with h | h
        · have := congrArg Fin.val h; rw [hv] at this; omega
        · rw [List.mem_singleton] at h
          have := congrArg Fin.val h; rw [Fin.val_zero] at this; omega

theorem W_idx (m : ℕ) (x : Fin (m + 1)) :
    (W m m).support.idxOf x = if x.val = 0 then 0 else 2 * x.val - 1 := by
  obtain ⟨_, h⟩ := W_supp m m le_rfl
  have := x.isLt
  by_cases hx : x.val = 0
  · rw [if_pos hx]; exact ((h x).1 hx).2
  · rw [if_neg hx]; exact ((h x).2.1 (by omega) (by omega)).2

theorem W_mem (m : ℕ) (x : Fin (m + 1)) : x ∈ (W m m).support := by
  obtain ⟨_, h⟩ := W_supp m m le_rfl
  have := x.isLt
  by_cases hx : x.val = 0
  · exact ((h x).1 hx).1
  · exact ((h x).2.1 (by omega) (by omega)).1

theorem bad_tour (m s : ℕ) (hm : m = 2 * s + 1) (hs : 1 ≤ s) :
    SupplyChainTheory.tourLength (dd m) (Equiv.refl _) = 2 * (m : ℝ) - 1 := by
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
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Fin.sum_univ_eq_sum_range f (m + 1)]
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm' : m + 1 = (2 * s' + 1) + 1 + 1 + 1 := by omega
  rw [hm', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∀ i ∈ Finset.range (2 * s' + 1), f (i + 1) = 2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    show dd m (vtx m (i + 1)) (vtx m (i + 1 + 1)) = 2
    apply dd_two
    · rw [vtx_val m (i + 1) (by omega), vtx_val m (i + 1 + 1) (by omega)]; omega
    · rw [vtx_val m (i + 1) (by omega), vtx_val m (i + 1 + 1) (by omega)]; omega
  rw [Finset.sum_congr rfl hmid, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have f0 : f 0 = 1 := by
    show dd m (vtx m 0) (vtx m (0 + 1)) = 1
    apply dd_one
    · rw [vtx_val m 0 (by omega), vtx_val m (0 + 1) (by omega)]; omega
    · left; exact vtx_val m 0 (by omega)
  have f1 : f (2 * s' + 1 + 1) = 1 := by
    show dd m (vtx m (2 * s' + 1 + 1)) (vtx m (2 * s' + 1 + 1 + 1)) = 1
    apply dd_one
    · rw [vtx_val m (2 * s' + 1 + 1) (by omega), vtx_val m (2 * s' + 1 + 1 + 1) (by omega)]; omega
    · rw [vtx_val m (2 * s' + 1 + 1) (by omega), vtx_val m (2 * s' + 1 + 1 + 1) (by omega)]; omega
  have hz : (vtx m (2 * s' + 1 + 1 + 1 + 1)).val = 0 := by
    show (2 * s' + 1 + 1 + 1 + 1) % (m + 1) = 0
    rw [← hm', Nat.mod_self]
  have f2 : f (2 * s' + 1 + 1 + 1) = 1 := by
    show dd m (vtx m (2 * s' + 1 + 1 + 1)) (vtx m (2 * s' + 1 + 1 + 1 + 1)) = 1
    apply dd_one
    · rw [vtx_val m (2 * s' + 1 + 1 + 1) (by omega), hz]; omega
    · right; left; exact hz
  rw [f0, f1, f2, hm]
  push_cast
  ring

end Aux_A09_lower

open Aux_A09_lower in
theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ (n : ℕ) (d : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)),
      N ≤ n ∧ 1 ≤ n ∧ SupplyChainTheory.IsMetric d ∧
      0 < SupplyChainTheory.optTourLength d ∧ VehicleRoutingSurvey.Routing.DoubleTreeRun d τ ∧
      (2 - ε) * SupplyChainTheory.optTourLength d < SupplyChainTheory.tourLength d τ := by
  intro ε hε N
  obtain ⟨s, hsN, hs1, hsε⟩ : ∃ s : ℕ, N ≤ s ∧ 1 ≤ s ∧ 3 / ε ≤ (s : ℝ) := by
    refine ⟨N + ⌈3 / ε⌉₊ + 1, by omega, by omega, ?_⟩
    have := Nat.le_ceil (3 / ε)
    push_cast
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  set m := 2 * s + 1 with hm
  have hmet : SupplyChainTheory.IsMetric (dd m) :=
    ⟨dd_symm m, dd_nonneg m, dd_self m, fun i j k => dd_tri m i k j⟩
  have hbdd : BddBelow (Set.range (SupplyChainTheory.tourLength (dd m))) :=
    ⟨0, by rintro _ ⟨τ, rfl⟩; exact tour_nonneg m τ⟩
  have hpos : 0 < SupplyChainTheory.optTourLength (dd m) := by
    unfold SupplyChainTheory.optTourLength
    have : (1 : ℝ) ≤ sInf (Set.range (SupplyChainTheory.tourLength (dd m))) :=
      le_csInf (Set.range_nonempty _) (by rintro _ ⟨τ, rfl⟩; exact tour_ge_one m (by omega) τ)
    linarith
  have hopt : SupplyChainTheory.optTourLength (dd m) ≤ (m : ℝ) + 1 := by
    have h1 : SupplyChainTheory.tourLength (dd m) (sig m s hm) = (m : ℝ) + 1 := tour_sig m s hm
    unfold SupplyChainTheory.optTourLength
    rw [← h1]
    exact csInf_le hbdd (Set.mem_range_self _)
  refine ⟨m + 1, dd m, Equiv.refl _, by omega, by omega, hmet, hpos, ?_, ?_⟩
  · unfold VehicleRoutingSurvey.Routing.DoubleTreeRun
    refine ⟨star m, ?_, 0, W m m, ?_, ?_⟩
    · unfold SupplyChainTheory.IsMST
      refine ⟨star_tree m, fun T' hT' => ?_⟩
      unfold SupplyChainTheory.graphWeight
      rw [star_cost m (star_tree m)]
      exact tree_lower m T' hT'
    · intro e he
      obtain ⟨j, hj, rfl⟩ := edge_form m e he
      rw [W_count m j (by omega) m le_rfl, if_pos (show j.val ≤ m by have := j.isLt; omega)]
    · unfold SupplyChainTheory.IsShortcut
      refine ⟨W_mem m, fun a b => ?_⟩
      simp only [Equiv.refl_symm, Equiv.refl_apply]
      rw [W_idx, W_idx, Fin.lt_iff_val_lt_val]
      split_ifs <;> omega
  · rw [bad_tour m s hm hs1]
    have hmR : (m : ℝ) = 2 * (s : ℝ) + 1 := by rw [hm]; push_cast; ring
    have h3 : 3 < ε * ((m : ℝ) + 1) := by
      have h4 := mul_le_mul_of_nonneg_left hsε hε.le
      have h5 : ε * (3 / ε) = 3 := by field_simp
      have h6 : ε * ((m : ℝ) + 1) = 2 * (ε * s) + 2 * ε := by rw [hmR]; ring
      linarith
    by_cases h2 : ε ≤ 2
    · have := mul_le_mul_of_nonneg_left hopt (by linarith : (0 : ℝ) ≤ 2 - ε)
      have e2 : (2 - ε) * ((m : ℝ) + 1) = 2 * (m : ℝ) + 2 - ε * ((m : ℝ) + 1) := by ring
      linarith
    · push_neg at h2
      have : (2 - ε) * SupplyChainTheory.optTourLength (dd m) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hpos
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
