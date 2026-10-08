-- Prove2me | solution 1 for VanderbeiLP.Networks.spanning_tree_iff_basis
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:40:42.049262+00:00
-- url     : https://prove2.me/submissions/1629df60-c0b9-472b-b339-90a4b004a959

/-
Theorem 14.1 of Vanderbei's Linear Programming: for a connected network, an arc set `T ⊆ A`
indexes a basis of the truncated incidence matrix `Ã` exactly when it is a spanning tree.

Basis ⇒ tree. A walk in the arc graph of `T \ {a}` from `i` to `j`, for an arc `a = (i, j)` of `T`,
gives a combination of the columns of `T \ {a}` equal to the column of `a` (`walk_comb`); with
linear independence this shows every arc of `T` is a bridge (`not_reachable`, `acyclic_of_indep`),
and two arcs on one pair of nodes are dependent (`injOn_of_indep`). An acyclic arc set with
`|N| - 1` arcs inside the connected arc graph of `A` extends to a spanning tree of `A` with the same
number of edges, so it is that tree.

Tree ⇒ basis. A tree has `|N| - 1` edges. For a combination of columns of `T` vanishing on the rows
`k ≠ r` (hence also on the row `r`, since each column sums to zero), summing the rows over the side
of `i` in `T \ {a}` leaves minus the coefficient of `a` (`cut_sum`); so every coefficient is zero.
-/
import Mathlib
import Definitions.Def_VanderbeiLP_Networks_Network

set_option autoImplicit false

namespace VanderbeiLP.Networks
open Finset

section IntLib
variable {N : Type*} [DecidableEq N]

theorem incidence_eq {i j : N} (h : i ≠ j) (k : N) :
    incidence k (i, j) = (if k = j then 1 else 0) - (if k = i then 1 else 0) := by
  unfold incidence
  by_cases h2 : k = j
  · subst h2; simp [Ne.symm h]
  · by_cases h1 : k = i
    · subst h1; simp [h2]
    · simp [h1, h2]

theorem sum_incidence (A : Finset (N × N)) (hA : IsNetwork A) (C : Finset N) (a : N × N)
    (ha : a ∈ A) :
    ∑ k ∈ C, incidence k a = (if a.2 ∈ C then 1 else 0) - (if a.1 ∈ C then 1 else 0) := by
  have h := hA a ha
  obtain ⟨i, j⟩ := a
  simp only at h ⊢
  simp only [incidence_eq h, Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- A walk in the arc graph gives a combination of arc columns equal to `e_v - e_u`. -/
theorem walk_comb (T' : Finset (N × N)) {u v : N} (p : (arcGraph T').Walk u v) :
    ∃ g : N × N → ℝ, ∀ k, ∑ b ∈ T', g b * incidence k b =
      (if k = v then 1 else 0) - (if k = u then 1 else 0) := by
  induction p with
  | nil => exact ⟨fun _ => 0, fun k => by simp⟩
  | @cons u w v hadj p ih =>
    obtain ⟨g, hg⟩ := ih
    have hadj' := hadj
    unfold arcGraph at hadj'
    rw [SimpleGraph.fromEdgeSet_adj] at hadj'
    obtain ⟨⟨b, hb0, hbe⟩, hne⟩ := hadj'
    have hb : b ∈ T' := Finset.mem_coe.1 hb0
    rcases Sym2.eq_iff.1 hbe with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨fun b' => g b' + if b' = b then 1 else 0, fun k => ?_⟩
      have : ∑ b' ∈ T', (g b' + if b' = b then (1 : ℝ) else 0) * incidence k b' =
          (∑ b' ∈ T', g b' * incidence k b') + incidence k b := by
        simp [add_mul, Finset.sum_add_distrib, ite_mul, hb]
      rw [this, hg k]
      have hb' : b = (u, w) := Prod.ext h1 h2
      rw [hb', incidence_eq hne]
      ring
    · refine ⟨fun b' => g b' - if b' = b then 1 else 0, fun k => ?_⟩
      have : ∑ b' ∈ T', (g b' - if b' = b then (1 : ℝ) else 0) * incidence k b' =
          (∑ b' ∈ T', g b' * incidence k b') - incidence k b := by
        simp [sub_mul, Finset.sum_sub_distrib, ite_mul, hb]
      rw [this, hg k]
      have hb' : b = (w, u) := Prod.ext h1 h2
      rw [hb', incidence_eq (Ne.symm hne)]
      ring

end IntLib

section IntLib2
variable {N : Type*} [Fintype N] [DecidableEq N]

theorem indep_zero (r : N) (T : Finset (N × N))
    (hind : LinearIndependent ℝ (fun a : T => fun k : {k : N // k ≠ r} => truncIncidence r k a.1))
    (g : N × N → ℝ) (hg : ∀ k, k ≠ r → ∑ b ∈ T, g b * incidence k b = 0) :
    ∀ b ∈ T, g b = 0 := by
  rw [Fintype.linearIndependent_iff] at hind
  intro b hb
  refine hind (fun a => g a.1) ?_ ⟨b, hb⟩
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.zero_apply]
  have := hg k.1 k.2
  rw [← Finset.sum_coe_sort T] at this
  exact this

theorem not_reachable (r : N) (T : Finset (N × N))
    (hind : LinearIndependent ℝ (fun a : T => fun k : {k : N // k ≠ r} => truncIncidence r k a.1))
    (a : N × N) (ha : a ∈ T) (hne : a.1 ≠ a.2) :
    ¬ (arcGraph (T.erase a)).Reachable a.1 a.2 := by
  rintro ⟨p⟩
  obtain ⟨g, hg⟩ := walk_comb (T.erase a) p
  have key := indep_zero r T hind (fun b => if b = a then -1 else g b) ?_ a ha
  · simp at key
  · intro k _
    rw [← Finset.add_sum_erase T _ ha]
    have : ∑ b ∈ T.erase a, (if b = a then (-1 : ℝ) else g b) * incidence k b =
        ∑ b ∈ T.erase a, g b * incidence k b :=
      Finset.sum_congr rfl (fun b hb => by rw [if_neg (Finset.ne_of_mem_erase hb)])
    rw [this, hg k]
    obtain ⟨i, j⟩ := a
    simp only [if_true] 
    rw [incidence_eq hne]
    ring

theorem arcGraph_adj {T : Finset (N × N)} {u w : N} :
    (arcGraph T).Adj u w ↔ u ≠ w ∧ ∃ b ∈ T, s(b.1, b.2) = s(u, w) := by
  unfold arcGraph
  rw [SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨b, hb, hbe⟩, hne⟩
    exact ⟨hne, b, Finset.mem_coe.1 hb, hbe⟩
  · rintro ⟨hne, b, hb, hbe⟩
    exact ⟨⟨b, Finset.mem_coe.2 hb, hbe⟩, hne⟩

theorem injOn_of_indep (r : N) (T : Finset (N × N))
    (hind : LinearIndependent ℝ (fun a : T => fun k : {k : N // k ≠ r} => truncIncidence r k a.1))
    (hT : IsNetwork T) : Set.InjOn (fun a : N × N => s(a.1, a.2)) (T : Set (N × N)) := by
  intro a ha b hb hab
  by_contra hne
  have ha' : a ∈ T := Finset.mem_coe.1 ha
  have hb' : b ∈ T := Finset.mem_coe.1 hb
  simp only at hab
  rcases Sym2.eq_iff.1 hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne (Prod.ext h1 h2)
  · have key := indep_zero r T hind (fun c => (if c = a then (1 : ℝ) else 0) + (if c = b then 1 else 0)) ?_ a ha'
    · simp [hne] at key
    · intro k _
      have : ∑ c ∈ T, ((if c = a then (1 : ℝ) else 0) + (if c = b then 1 else 0)) * incidence k c =
          incidence k a + incidence k b := by
        simp [add_mul, Finset.sum_add_distrib, ite_mul, ha', hb']
      rw [this]
      have hna := hT a ha'
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only at h1 h2 hna
      subst h1; subst h2
      rw [incidence_eq hna, incidence_eq (Ne.symm hna)]
      ring

theorem acyclic_of_indep (r : N) (T : Finset (N × N))
    (hind : LinearIndependent ℝ (fun a : T => fun k : {k : N // k ≠ r} => truncIncidence r k a.1))
    (hT : IsNetwork T) : (arcGraph T).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro v w hadj
  rw [SimpleGraph.isBridge_iff]
  intro hreach
  obtain ⟨hvw, a, ha, hae⟩ := arcGraph_adj.1 hadj
  have hle : (arcGraph T).deleteEdges {s(v, w)} ≤ arcGraph (T.erase a) := by
    intro x y hxy
    rw [SimpleGraph.deleteEdges_adj] at hxy
    obtain ⟨hadj', hnot⟩ := hxy
    obtain ⟨hxy', b, hb, hbe⟩ := arcGraph_adj.1 hadj'
    refine arcGraph_adj.2 ⟨hxy', b, Finset.mem_erase.2 ⟨?_, hb⟩, hbe⟩
    rintro rfl
    apply hnot
    rw [← hbe, hae]
    simp
  have hr := hreach.mono hle
  rcases Sym2.eq_iff.1 hae with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact not_reachable r T hind a ha (hT a ha) (h1 ▸ h2 ▸ hr)
  · exact not_reachable r T hind a ha (hT a ha) (h1 ▸ h2 ▸ hr.symm)


theorem not_reachable_of_acyclic (T : Finset (N × N)) (hac : (arcGraph T).IsAcyclic)
    (hinj : Set.InjOn (fun a : N × N => s(a.1, a.2)) (T : Set (N × N)))
    (a : N × N) (ha : a ∈ T) (hne : a.1 ≠ a.2) :
    ¬ (arcGraph (T.erase a)).Reachable a.1 a.2 := by
  intro h
  have hadj : (arcGraph T).Adj a.1 a.2 := arcGraph_adj.2 ⟨hne, a, ha, rfl⟩
  have hbr := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hac) hadj
  rw [SimpleGraph.isBridge_iff] at hbr
  apply hbr
  refine h.mono ?_
  intro x y hxy
  obtain ⟨hxy', b, hb, hbe⟩ := arcGraph_adj.1 hxy
  have hb' := Finset.mem_erase.1 hb
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨arcGraph_adj.2 ⟨hxy', b, hb'.2, hbe⟩, ?_⟩
  intro hmem
  rw [Set.mem_singleton_iff, ← hbe] at hmem
  exact hb'.1 (hinj (Finset.mem_coe.2 hb'.2) (Finset.mem_coe.2 ha) hmem)

open Classical in
/-- Summing the rows over the side of `a` in `T \ {a}` isolates the coefficient of `a`. -/
theorem cut_sum (T : Finset (N × N)) (hT : IsNetwork T) (a : N × N) (ha : a ∈ T)
    (hnr : ¬ (arcGraph (T.erase a)).Reachable a.1 a.2) (g : N × N → ℝ) :
    ∑ k ∈ Finset.univ.filter (fun k => (arcGraph (T.erase a)).Reachable a.1 k),
      ∑ b ∈ T, g b * incidence k b = -g a := by
  classical
  set S : Finset N := Finset.univ.filter (fun k => (arcGraph (T.erase a)).Reachable a.1 k) with hS
  have hmemS : ∀ k, k ∈ S ↔ (arcGraph (T.erase a)).Reachable a.1 k := fun k => by simp [hS]
  have h2 : ∑ k ∈ S, ∑ b ∈ T, g b * incidence k b =
      ∑ b ∈ T, g b * ((if b.2 ∈ S then (1 : ℝ) else 0) - (if b.1 ∈ S then 1 else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [← Finset.mul_sum, sum_incidence T hT S b hb]
  rw [h2, Finset.sum_eq_single_of_mem a ha]
  · have h1S : a.1 ∈ S := (hmemS _).2 (SimpleGraph.Reachable.refl _)
    have h2S : a.2 ∉ S := fun h => hnr ((hmemS _).1 h)
    simp [h1S, h2S]
  · intro b hb hne'
    have hadj : (arcGraph (T.erase a)).Adj b.1 b.2 :=
      arcGraph_adj.2 ⟨hT b hb, b, Finset.mem_erase.2 ⟨hne', hb⟩, rfl⟩
    have : b.2 ∈ S ↔ b.1 ∈ S := by
      rw [hmemS, hmemS]
      exact ⟨fun h => h.trans hadj.reachable.symm, fun h => h.trans hadj.reachable⟩
    by_cases h : b.1 ∈ S
    · simp [h, this.2 h]
    · simp [h, show b.2 ∉ S from fun h' => h (this.1 h')]

theorem indep_of_tree (r : N) (T : Finset (N × N)) (hT : IsNetwork T)
    (hac : (arcGraph T).IsAcyclic)
    (hinj : Set.InjOn (fun a : N × N => s(a.1, a.2)) (T : Set (N × N))) :
    LinearIndependent ℝ (fun a : T => fun k : {k : N // k ≠ r} => truncIncidence r k a.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set g' : N × N → ℝ := fun c => if h : c ∈ T then g ⟨c, h⟩ else 0 with hg'
  have hrow : ∀ k, k ≠ r → ∑ c ∈ T, g' c * incidence k c = 0 := by
    intro k hk
    have := congrFun hg ⟨k, hk⟩
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.zero_apply] at this
    rw [← Finset.sum_coe_sort T]
    simpa [hg', truncIncidence] using this
  have hall : ∀ k, ∑ c ∈ T, g' c * incidence k c = 0 := by
    intro k
    by_cases hk : k = r
    · subst hk
      have htot : ∑ k' : N, ∑ c ∈ T, g' c * incidence k' c = 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero (fun c hc => ?_)
        rw [← Finset.mul_sum]
        have := sum_incidence T hT Finset.univ c hc
        simp at this
        simp [this]
      rw [Finset.sum_eq_single k (fun k' _ hk' => hrow k' hk') (fun h => absurd (Finset.mem_univ _) h)] at htot
      exact htot
    · exact hrow k hk
  intro ⟨a, ha⟩
  have hnr := not_reachable_of_acyclic T hac hinj a ha (hT a ha)
  have := cut_sum T hT a ha hnr g'
  rw [Finset.sum_eq_zero (fun k _ => hall k)] at this
  simpa [hg', ha] using this.symm


theorem edgeFinset_arcGraph (T : Finset (N × N)) (hT : IsNetwork T)
    [Fintype (arcGraph T).edgeSet] :
    (arcGraph T).edgeFinset = T.image (fun a : N × N => s(a.1, a.2)) := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image]
    rw [arcGraph_adj]
    constructor
    · rintro ⟨_, a, ha, he⟩
      exact ⟨a, ha, he⟩
    · rintro ⟨a, ha, he⟩
      refine ⟨?_, a, ha, he⟩
      rintro rfl
      rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hT a ha (h1.trans h2.symm)
      · exact hT a ha (h1.trans h2.symm)

theorem card_edgeFinset_arcGraph (T : Finset (N × N)) (hT : IsNetwork T)
    (hinj : Set.InjOn (fun a : N × N => s(a.1, a.2)) (T : Set (N × N)))
    [Fintype (arcGraph T).edgeSet] : (arcGraph T).edgeFinset.card = T.card := by
  rw [edgeFinset_arcGraph T hT]
  exact Finset.card_image_of_injOn hinj

theorem card_ne (r : N) : Fintype.card {k : N // k ≠ r} + 1 = Fintype.card N := by
  have := Fintype.card_subtype_compl (fun k : N => k = r)
  rw [Fintype.card_subtype_eq] at this
  have h1 : 0 < Fintype.card N := Fintype.card_pos_iff.2 ⟨r⟩
  simp only [ne_eq]
  omega

theorem spanning_tree_iff_basis_core (A : Finset (N × N)) (hA : IsNetwork A)
    (hconn : IsConnectedNetwork A) (r : N) (T : Finset (N × N)) (hT : T ⊆ A) :
    IsBasisArcs r T ↔ IsSpanningTree A T := by
  classical
  have hTn : IsNetwork T := fun b hb => hA b (hT hb)
  constructor
  · rintro ⟨hcard, hind⟩
    have hac := acyclic_of_indep r T hind hTn
    have hinj := injOn_of_indep r T hind hTn
    refine ⟨hT, ⟨?_, hac⟩, hinj⟩
    haveI : Nonempty N := ⟨r⟩
    have hG : (arcGraph A).Connected := ⟨hconn⟩
    have hFG : arcGraph T ≤ arcGraph A :=
      SimpleGraph.fromEdgeSet_mono (Set.image_mono (Finset.coe_subset.2 hT))
    obtain ⟨F', hFF', _, hF'⟩ := hG.exists_isTree_le_of_le_of_isAcyclic hFG hac
    have hc1 := hF'.card_edgeFinset
    have hc2 := card_edgeFinset_arcGraph T hTn hinj
    have hc3 := card_ne r
    have hsub : (arcGraph T).edgeFinset ⊆ F'.edgeFinset := SimpleGraph.edgeFinset_mono hFF'
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have : arcGraph T = F' := SimpleGraph.edgeFinset_inj.1 heq
    rw [this]
    exact hF'.connected
  · rintro ⟨_, htree, hinj⟩
    refine ⟨?_, indep_of_tree r T hTn htree.IsAcyclic hinj⟩
    have hc1 := htree.card_edgeFinset
    have hc2 := card_edgeFinset_arcGraph T hTn hinj
    have hc3 := card_ne r
    omega

end IntLib2
end VanderbeiLP.Networks

open VanderbeiLP.Networks in
theorem solution {N : Type*} [Fintype N] [DecidableEq N]
    (A : Finset (N × N)) (hA : IsNetwork A) (hconn : IsConnectedNetwork A)
    (r : N) (T : Finset (N × N)) (hT : T ⊆ A) :
    IsBasisArcs r T ↔ IsSpanningTree A T :=
  spanning_tree_iff_basis_core A hA hconn r T hT
