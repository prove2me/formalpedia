-- Prove2me | solution 1 for SWSSNet.Diffusion.atar_prop_A_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:57:28.189963+00:00
-- url     : https://prove2.me/submissions/48930f09-0882-4131-9f20-ab4d2e344e6a

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSAtarAux

open SWSSNet.Diffusion

variable {I J : ℕ}

theorem bip_adj_iff (adj : Fin I → Fin J → Prop) (a b : Fin I ⊕ Fin J) :
    (bipGraph adj).Adj a b ↔
      (∃ i j, a = Sum.inl i ∧ b = Sum.inr j ∧ adj i j) ∨
      (∃ i j, b = Sum.inl i ∧ a = Sum.inr j ∧ adj i j) := by
  unfold bipGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with ⟨i, j, rfl, rfl, _⟩ | ⟨i, j, rfl, rfl, _⟩ <;> simp

/-- The edge weight attached to `z`. -/
def wt (z : Fin I → Fin J → ℝ) : Fin I ⊕ Fin J → Fin I ⊕ Fin J → ℝ
  | Sum.inl i, Sum.inr j => z i j
  | Sum.inr j, Sum.inl i => z i j
  | _, _ => 0

theorem wt_symm (z : Fin I → Fin J → ℝ) (a b : Fin I ⊕ Fin J) : wt z a b = wt z b a := by
  rcases a with i | j <;> rcases b with i' | j' <;> rfl

theorem wt_zero_of_not_adj (adj : Fin I → Fin J → Prop) (z : Fin I → Fin J → ℝ)
    (hz : ∀ i j, ¬ adj i j → z i j = 0) (a b : Fin I ⊕ Fin J)
    (h : ¬ (bipGraph adj).Adj a b) : wt z a b = 0 := by
  rw [bip_adj_iff] at h
  rcases a with i | j <;> rcases b with i' | j'
  · rfl
  · exact hz i j' fun h' => h (Or.inl ⟨i, j', rfl, rfl, h'⟩)
  · exact hz i' j fun h' => h (Or.inr ⟨i', j, rfl, rfl, h'⟩)
  · rfl

theorem wt_sum (z : Fin I → Fin J → ℝ) (hrow : ∀ i, ∑ j, z i j = 0) (hcol : ∀ j, ∑ i, z i j = 0)
    (a : Fin I ⊕ Fin J) : ∑ b, wt z a b = 0 := by
  rw [Fintype.sum_sum_type]
  rcases a with i | j
  · simp only [wt, Finset.sum_const_zero, zero_add]
    exact hrow i
  · simp only [wt, Finset.sum_const_zero, add_zero]
    exact hcol j

/-- The support subgraph. -/
def supp (adj : Fin I → Fin J → Prop) (z : Fin I → Fin J → ℝ) : SimpleGraph (Fin I ⊕ Fin J) where
  Adj a b := (bipGraph adj).Adj a b ∧ wt z a b ≠ 0
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [wt_symm]; exact h.2⟩⟩
  loopless := ⟨fun a h => (bipGraph adj).loopless.irrefl a h.1⟩

theorem supp_adj (adj : Fin I → Fin J → Prop) (z : Fin I → Fin J → ℝ) (a b : Fin I ⊕ Fin J) :
    (supp adj z).Adj a b ↔ (bipGraph adj).Adj a b ∧ wt z a b ≠ 0 := Iff.rfl

/-- On a tree, a flow with vanishing row and column sums is zero. -/
theorem flow_zero (adj : Fin I → Fin J → Prop) (htree : (bipGraph adj).IsTree)
    (z : Fin I → Fin J → ℝ) (hz : ∀ i j, ¬ adj i j → z i j = 0)
    (hrow : ∀ i, ∑ j, z i j = 0) (hcol : ∀ j, ∑ i, z i j = 0) : z = 0 := by
  classical
  by_contra hne
  obtain ⟨i0, j0, h0⟩ : ∃ i j, z i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext fun i => funext fun j => h i j)
  set H := supp adj z with hH
  have hle : H ≤ bipGraph adj := fun a b h => ((supp_adj adj z a b).1 h).1
  have hac : H.IsAcyclic := htree.isAcyclic.anti hle
  have hadj0 : H.Adj (Sum.inl i0) (Sum.inr j0) := by
    rw [hH, supp_adj]
    refine ⟨?_, h0⟩
    rw [bip_adj_iff]
    exact Or.inl ⟨i0, j0, rfl, rfl, by
      by_contra hn; exact h0 (hz _ _ hn)⟩
  have : Nonempty (Fin I ⊕ Fin J) := ⟨Sum.inl i0⟩
  obtain ⟨u, v, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
  have hlen : 1 ≤ p.length := by
    have := hmax _ _ (SimpleGraph.Walk.cons hadj0 SimpleGraph.Walk.nil)
      (by simp [SimpleGraph.Walk.isPath_def])
    simpa using this
  have hnil : ¬ p.Nil := by
    rw [← SimpleGraph.Walk.length_eq_zero_iff]; omega
  have hus : H.Adj u p.snd := p.adj_snd hnil
  have honly : ∀ b, H.Adj u b → b = p.snd := by
    intro b hb
    by_cases hsupp : b ∈ p.support
    · exact hac.eq_snd_of_adj_start hp hb hsupp
    · exfalso
      have hpath : (SimpleGraph.Walk.cons hb.symm p).IsPath := hp.cons hsupp
      have := hmax _ _ _ hpath
      simp at this
  have hsum := wt_sum z hrow hcol u
  rw [Finset.sum_eq_single p.snd] at hsum
  · exact ((supp_adj adj z _ _).1 hus).2 hsum
  · intro b _ hb
    by_contra hw
    by_cases hG : (bipGraph adj).Adj u b
    · exact hb (honly b ((supp_adj adj z _ _).2 ⟨hG, hw⟩))
    · exact hw (wt_zero_of_not_adj adj z hz u b hG)
  · simp


/-- Number of edges of the class–pool tree. -/
theorem card_edges (adj : Fin I → Fin J → Prop) [DecidableRel adj] (htree : (bipGraph adj).IsTree) :
    (Finset.univ.filter (fun q : Fin I × Fin J => adj q.1 q.2)).card + 1 = I + J := by
  classical
  have h := htree.card_edgeFinset
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  rw [← h]
  congr 1
  refine Finset.card_bij (fun q _ => s(Sum.inl q.1, Sum.inr q.2)) ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, bip_adj_iff]
    exact Or.inl ⟨q.1, q.2, rfl, rfl, hq⟩
  · intro q _ q' _ h
    simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false, or_false] at h
    exact Prod.ext h.1 h.2
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, bip_adj_iff] at he
    rcases he with ⟨i, j, rfl, rfl, h⟩ | ⟨i, j, rfl, rfl, h⟩
    · exact ⟨(i, j), by simp [h], rfl⟩
    · exact ⟨(i, j), by simp [h], Sym2.eq_swap⟩

end SWSSAtarAux

namespace SWSSAtarAux

open SWSSNet.Diffusion

variable {I J : ℕ}

section Exist

variable (adj : Fin I → Fin J → Prop) [DecidableRel adj]

/-- The set of edges as pairs. -/
def edges : Finset (Fin I × Fin J) := Finset.univ.filter (fun q : Fin I × Fin J => adj q.1 q.2)

/-- The flow carried by edge values `f`. -/
def zOf (f : edges adj → ℝ) (i : Fin I) (j : Fin J) : ℝ :=
  if h : adj i j then f ⟨(i, j), by simp [edges, h]⟩ else 0

/-- Row and column sums of the flow. -/
def T : (edges adj → ℝ) →ₗ[ℝ] (Fin I → ℝ) × (Fin J → ℝ) where
  toFun f := (fun i => ∑ j, zOf adj f i j, fun j => ∑ i, zOf adj f i j)
  map_add' f g := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib] <;>
      refine Finset.sum_congr rfl fun _ _ => ?_ <;> unfold zOf <;> split_ifs <;> simp
  map_smul' c f := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum] <;>
      refine Finset.sum_congr rfl fun _ _ => ?_ <;> unfold zOf <;> split_ifs <;> simp

/-- The balance functional `⟨e,α⟩ − ⟨e,β⟩`. -/
def phi : (Fin I → ℝ) × (Fin J → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x.1 i - ∑ j, x.2 j
  map_add' x y := by simp [Finset.sum_add_distrib]; ring
  map_smul' c x := by simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]; ring

theorem T_injective (htree : (bipGraph adj).IsTree) : Function.Injective (T adj) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have hz := flow_zero adj htree (zOf adj f)
    (fun i j h => by simp [zOf, h])
    (fun i => congrFun (congrArg Prod.fst hf) i)
    (fun j => congrFun (congrArg Prod.snd hf) j)
  funext q
  obtain ⟨⟨i, j⟩, hq⟩ := q
  have hadj : adj i j := by simpa [edges] using hq
  have := congrFun (congrFun hz i) j
  simpa [zOf, hadj] using this

theorem range_T (htree : (bipGraph adj).IsTree) (hne : Nonempty (Fin I ⊕ Fin J)) :
    LinearMap.range (T adj) = LinearMap.ker (phi (I := I) (J := J)) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨f, rfl⟩
    simp only [LinearMap.mem_ker, phi, T, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_comm]; ring
  · rw [LinearMap.finrank_range_of_inj (T_injective adj htree), Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe]
    have hrank := LinearMap.finrank_range_add_finrank_ker (phi (I := I) (J := J))
    have hsurj : LinearMap.range (phi (I := I) (J := J)) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      obtain ⟨v⟩ := hne
      rcases v with i0 | j0
      · refine ⟨(Pi.single i0 c, 0), ?_⟩
        simp [phi]
      · refine ⟨(0, Pi.single j0 (-c)), ?_⟩
        simp [phi]
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, Fintype.card_fin] at hrank
    have hc := card_edges adj htree
    simp only [edges]
    omega

end Exist

end SWSSAtarAux

open SWSSNet.Diffusion SWSSAtarAux

theorem solution {I J : ℕ} (N : TreeNetwork I J) (α : Fin I → ℝ) (β : Fin J → ℝ)
    (hD : ∑ i, α i = ∑ j, β j) :
    ∃! z : Fin I → Fin J → ℝ, IsFlow N α β z := by
  classical
  have hne : Nonempty (Fin I ⊕ Fin J) := N.isTree.connected.nonempty
  have hmem : (α, β) ∈ LinearMap.ker (phi (I := I) (J := J)) := by
    simp [phi, hD]
  rw [← range_T N.adj N.isTree hne] at hmem
  obtain ⟨f, hf⟩ := hmem
  refine ⟨zOf N.adj f, ⟨fun i j h => by simp [zOf, h], fun i => ?_, fun j => ?_⟩, ?_⟩
  · exact congrFun (congrArg Prod.fst hf) i
  · exact congrFun (congrArg Prod.snd hf) j
  · intro z hz
    have h0 := flow_zero N.adj N.isTree (z - zOf N.adj f)
      (fun i j h => by simp [hz.1 i j h, zOf, h])
      (fun i => by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, hz.2.1 i]
        rw [show ∑ j, zOf N.adj f i j = α i from congrFun (congrArg Prod.fst hf) i]; ring)
      (fun j => by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, hz.2.2 j]
        rw [show ∑ i, zOf N.adj f i j = β j from congrFun (congrArg Prod.snd hf) j]; ring)
    exact sub_eq_zero.mp h0
