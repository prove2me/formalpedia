-- Prove2me | solution 1 for SimpleGraph.petersen_two_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:09:39.391993+00:00
-- url     : https://prove2.me/submissions/d32efc67-59d2-4fab-9cbe-482ba970440c

module
public import Definitions.Def_Euler_Orientation
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Set.Card
public import Definitions.Def_Euler_Petersen
public import Theorems.Thm_SimpleGraph_exists_perm_decomp
public import Theorems.Thm_SimpleGraph_card_image_edge_filter
public import Theorems.Thm_SimpleGraph_exists_balanced_orientation


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (k : ℕ) (h : ∀ v, G.degree v = 2 * k) :
    ∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G) ∧
      (∀ i v, ((F i).neighborSet v).ncard = 2) ∧
      (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ ⨆ i, F i = G := by
  obtain ⟨Ds, hinj, hbal, hcov⟩ :=
    exists_balanced_orientation (G := G) fun v => ⟨k, by rw [h v]; omega⟩
  set D := Ds.image Dart.toProd
  have hDmem : ∀ p, p ∈ D ↔ ∃ d ∈ Ds, d.toProd = p := fun p => by simp [D]
  have htoProd_inj : ∀ d ∈ Ds, ∀ d' ∈ Ds, d.toProd = d'.toProd → d = d' :=
    fun d _ d' _ h => (Dart.ext_iff d d').mpr h
  -- grados de salida y de entrada
  have hsum : ∀ v, (Ds.filter fun d => d.fst = v).card + (Ds.filter fun d => d.snd = v).card =
      2 * k := by
    intro v
    rw [← card_image_edge_filter hinj, ← h v, ← card_incidenceFinset_eq_degree]
    congr 1
    ext e
    simp only [mem_filter, mem_image, mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨d, -, rfl⟩, hv⟩; exact ⟨d.edge_mem, hv⟩
    · rintro ⟨he, hv⟩; obtain ⟨d, hd, rfl⟩ := hcov e he; exact ⟨⟨d, hd, rfl⟩, hv⟩
  have hfilter1 : ∀ v, (D.filter fun p => p.1 = v).card = (Ds.filter fun d => d.fst = v).card := by
    intro v
    rw [show D.filter (fun p => p.1 = v) = (Ds.filter fun d => d.fst = v).image Dart.toProd by
      ext p; simp [D, and_comm]; constructor
      · rintro ⟨h1, a, rfl, ha⟩; exact ⟨a, rfl, h1, ha⟩
      · rintro ⟨a, rfl, h1, ha⟩; exact ⟨h1, a, rfl, ha⟩, card_image_of_injOn fun d hd d' hd' =>
        htoProd_inj d (mem_filter.mp hd).1 d' (mem_filter.mp hd').1]
  have hfilter2 : ∀ v, (D.filter fun p => p.2 = v).card = (Ds.filter fun d => d.snd = v).card := by
    intro v
    rw [show D.filter (fun p => p.2 = v) = (Ds.filter fun d => d.snd = v).image Dart.toProd by
      ext p; simp [D, and_comm]; constructor
      · rintro ⟨h1, a, rfl, ha⟩; exact ⟨a, rfl, h1, ha⟩
      · rintro ⟨a, rfl, h1, ha⟩; exact ⟨h1, a, rfl, ha⟩, card_image_of_injOn fun d hd d' hd' =>
        htoProd_inj d (mem_filter.mp hd).1 d' (mem_filter.mp hd').1]
  have hout : ∀ v, (D.filter fun p => p.1 = v).card = k := by
    intro v; have := hsum v; have := hbal v; rw [hfilter1]; omega
  have hin : ∀ v, (D.filter fun p => p.2 = v).card = k := by
    intro v; have := hsum v; have := hbal v; rw [hfilter2]; omega
  obtain ⟨σ, hσD, hσdisj, hσcov⟩ := exists_perm_decomp k D hout hin
  -- propiedades de `D`
  have hDadj : ∀ u w, (u, w) ∈ D → G.Adj u w := by
    intro u w huw
    obtain ⟨d, -, hd⟩ := (hDmem _).mp huw
    have := d.adj
    rw [show d.fst = u from congrArg Prod.fst hd, show d.snd = w from congrArg Prod.snd hd] at this
    exact this
  have hDanti : ∀ u w, (u, w) ∈ D → (w, u) ∉ D := by
    intro u w huw hwu
    obtain ⟨d, hd, hdp⟩ := (hDmem _).mp huw
    obtain ⟨d', hd', hdp'⟩ := (hDmem _).mp hwu
    have he : d.edge = d'.edge := by
      rw [Dart.edge, Dart.edge, hdp, hdp']; exact Sym2.eq_swap
    have := hinj d hd d' hd' he
    subst this
    have h1 := congrArg Prod.fst (hdp.symm.trans hdp')
    exact (hDadj u w huw).ne h1
  refine ⟨fun i => permGraph (σ i), fun i u w huw => ?_, fun i v => ?_, fun i j hij => ?_, ?_⟩
  · rcases huw.2 with h | h
    · exact h ▸ hDadj _ _ (hσD i u)
    · exact (h ▸ hDadj _ _ (hσD i w)).symm
  · have hne1 : σ i v ≠ v := fun h' => (hDadj _ _ (hσD i v)).ne h'.symm
    have hne2 : (σ i).symm v ≠ v := by
      intro h'
      have := hDadj _ _ (hσD i ((σ i).symm v))
      rw [Equiv.apply_symm_apply, h'] at this
      exact G.loopless.irrefl _ this
    have hset : (permGraph (σ i)).neighborSet v = {σ i v, (σ i).symm v} := by
      ext w
      simp only [mem_neighborSet, permGraph, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, h' | h'⟩
        · exact Or.inl h'.symm
        · right; rw [← h']; simp
      · rintro (rfl | rfl)
        · exact ⟨hne1.symm, Or.inl rfl⟩
        · exact ⟨hne2.symm, Or.inr (by simp)⟩
    rw [hset, Set.ncard_pair]
    intro heq
    have h1 := hσD i v
    have h2 := hσD i (σ i v)
    have : σ i (σ i v) = v := by
      conv_rhs => rw [← Equiv.apply_symm_apply (σ i) v]
      rw [← heq]
    rw [this] at h2
    exact hDanti _ _ h1 h2
  · rw [disjoint_iff_inf_le]
    intro u w ⟨hi, hj⟩
    exfalso
    rcases hi.2 with h1 | h1 <;> rcases hj.2 with h2 | h2
    · exact hij (hσdisj i j u (h1.trans h2.symm))
    · exact hDanti _ _ (h1 ▸ hσD i u) (h2 ▸ hσD j w)
    · exact hDanti _ _ (h1 ▸ hσD i w) (h2 ▸ hσD j u)
    · exact hij (hσdisj i j w (h1.trans h2.symm))
  · ext u w
    rw [iSup_adj]
    constructor
    · rintro ⟨i, hi⟩
      rcases hi.2 with h' | h'
      · exact h' ▸ hDadj _ _ (hσD i u)
      · exact (h' ▸ hDadj _ _ (hσD i w)).symm
    · intro huw
      obtain ⟨d, hd, hde⟩ := hcov s(u, w) huw
      have hdD : d.toProd ∈ D := mem_image_of_mem _ hd
      obtain ⟨i, hi⟩ := hσcov _ hdD
      refine ⟨i, huw.ne, ?_⟩
      rcases Sym2.eq_iff.mp hde with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [← h1, ← h2]; exact hi
      · right; rw [← h1, ← h2]; exact hi
end SimpleGraph
