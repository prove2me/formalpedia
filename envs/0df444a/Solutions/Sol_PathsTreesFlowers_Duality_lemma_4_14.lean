-- Prove2me | solution 1 for PathsTreesFlowers.Duality.lemma_4_14
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:16:30.25368+00:00
-- url     : https://prove2.me/submissions/36ec9a6c-c563-4411-8a4c-baa69c20840b

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_Shrink



namespace PathsTreesFlowers.Duality

open EdmondsMatching65.Polyhedron (IsMatching)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma p14_card_ends (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) (e : E)
    (h : G.ends e ∈ U.sym2) : (U.filter (fun v => v ∈ G.ends e)).card = 2 := by
  have hl := G.loopless e
  generalize G.ends e = z at h hl
  induction z using Sym2.ind with
  | h a b =>
    rw [Finset.mk_mem_sym2_iff] at h
    rw [Sym2.mk_isDiag_iff] at hl
    have : U.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h'⟩; exact h'
      · rintro (rfl | rfl)
        · exact ⟨h.1, Or.inl rfl⟩
        · exact ⟨h.2, Or.inr rfl⟩
    rw [this, Finset.card_pair hl]

lemma p14_match_card (G : EdmondsMatching65.Polyhedron.Graph V E) (F : Finset E)
    (hF : IsMatching G F) (U : Finset V) (hin : ∀ e ∈ F, G.ends e ∈ U.sym2) :
    2 * F.card ≤ U.card := by
  have hdisj : ∀ e ∈ F, ∀ f ∈ F, e ≠ f →
      Disjoint (U.filter (fun v => v ∈ G.ends e)) (U.filter (fun v => v ∈ G.ends f)) := by
    intro e he f hf hne
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_filter] at hv hv'
    exact hF e he f hf hne v hv.2 hv'.2
  have hc : (F.biUnion (fun e => U.filter (fun v => v ∈ G.ends e))).card = 2 * F.card := by
    rw [Finset.card_biUnion (fun e he f hf hne => hdisj e he f hf hne)]
    rw [Finset.sum_congr rfl (fun e he => p14_card_ends G U e (hin e he))]
    simp [mul_comm]
  have hsub : (F.biUnion (fun e => U.filter (fun v => v ∈ G.ends e))) ⊆ U := by
    intro v hv
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hv
    obtain ⟨_, _, hv, _⟩ := hv; exact hv
  have := Finset.card_le_card hsub
  omega

def cv (vs : List V) (h : 0 < vs.length) (i : ℕ) : V := vs[i % vs.length]'(Nat.mod_lt _ h)
def ce (es : List E) (h : 0 < es.length) (i : ℕ) : E := es[i % es.length]'(Nat.mod_lt _ h)

lemma cv_inj {vs : List V} (hn : vs.Nodup) (h : 0 < vs.length) (a b : ℕ) :
    cv vs h a = cv vs h b ↔ a % vs.length = b % vs.length := by
  unfold cv
  rw [List.Nodup.getElem_inj_iff hn]

lemma ce_inj {es : List E} (hn : es.Nodup) (h : 0 < es.length) (a b : ℕ) :
    ce es h a = ce es h b ↔ a % es.length = b % es.length := by
  unfold ce
  rw [List.Nodup.getElem_inj_iff hn]

lemma cv_mem (vs : List V) (h : 0 < vs.length) (i : ℕ) : cv vs h i ∈ vs := List.getElem_mem _
lemma ce_mem (es : List E) (h : 0 < es.length) (i : ℕ) : ce es h i ∈ es := List.getElem_mem _

lemma ce_ends (G : EdmondsMatching65.Polyhedron.Graph V E) {vs : List V} {es : List E}
    (hB : IsCircuit G vs es) (h : 0 < vs.length) (h' : 0 < es.length) (i : ℕ) :
    G.ends (ce es h' i) = s(cv vs h i, cv vs h (i + 1)) := by
  obtain ⟨_, _, _, hlen, hmap⟩ := hB
  have hi : i % es.length < es.length := Nat.mod_lt _ h'
  have hv : i % es.length < vs.length := by omega
  have hz : i % es.length < (List.zipWith (fun a b => s(a, b)) vs (vs.rotate 1)).length := by
    simp [List.length_zipWith]; omega
  have := List.getElem_of_eq hmap (i := i % es.length) (by simpa using hi)
  simp only [List.getElem_map, List.getElem_zipWith, List.getElem_rotate] at this
  unfold ce cv
  rw [this]
  congr 2
  · rw [hlen]
  · rw [← hlen, Nat.mod_add_mod]

lemma mem_ce {es : List E} (h : 0 < es.length) {e : E} (he : e ∈ es) : ∃ i, e = ce es h i := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
  exact ⟨i, by unfold ce; simp [Nat.mod_eq_of_lt hi]⟩

lemma modeq_small (m a b : ℕ) (hab : a % m = b % m) (h1 : a < b + m) (h2 : b < a + m) : a = b := by
  have : (a : ℤ) ≡ b [ZMOD m] := by
    rw [Int.modEq_iff_dvd]
    have := (Nat.modEq_iff_dvd.1 hab)
    exact this
  have hd := (Int.modEq_iff_dvd.1 this)
  have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  omega


lemma p14_build (G : EdmondsMatching65.Polyhedron.Graph V E) {vs : List V} {es : List E}
    (hB : IsCircuit G vs es) (hodd : Odd vs.length) (h : 0 < vs.length) (j : ℕ) :
    ∃ MB : Finset E, IsMaxMatchingOn G es.toFinset MB ∧
      (∀ f ∈ MB, ∀ x ∈ G.ends f, x ≠ cv vs h j ∧ x ∈ vs) := by
  have hlen := hB.2.2.2.1
  have h' : 0 < es.length := by omega
  obtain ⟨k, hk⟩ := hodd
  have hnv := hB.1
  have hne := hB.2.1
  set m := vs.length with hm
  have hvi : ∀ a b, cv vs h a = cv vs h b ↔ a % m = b % m := fun a b => cv_inj hnv h a b
  have hei : ∀ a b, ce es h' a = ce es h' b ↔ a % m = b % m := fun a b => by
    rw [ce_inj hne h', hlen]
  have hmem : ∀ a x, x ∈ G.ends (ce es h' a) ↔ x = cv vs h a ∨ x = cv vs h (a + 1) := by
    intro a x; rw [ce_ends G hB h h' a, Sym2.mem_iff]
  refine ⟨(Finset.range k).image (fun t => ce es h' (j + 1 + 2 * t)), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    simp only [Finset.mem_image] at hf
    obtain ⟨t, _, rfl⟩ := hf
    simpa using ce_mem es h' _
  · intro e he f hf hef x hx hx'
    simp only [Finset.mem_image] at he hf
    obtain ⟨t, ht, rfl⟩ := he
    obtain ⟨t', ht', rfl⟩ := hf
    rw [Finset.mem_range] at ht ht'
    rw [hmem] at hx hx'
    have htt : t ≠ t' := by rintro rfl; exact hef rfl
    rcases hx with rfl | rfl <;> rcases hx' with h1 | h1 <;>
      rw [hvi] at h1 <;>
      · have := modeq_small m _ _ h1 (by omega) (by omega)
        omega
  · intro M' hM'sub hM'
    have h2 := p14_match_card G M' hM' vs.toFinset (by
      intro e he
      have he' := hM'sub he
      rw [List.mem_toFinset] at he'
      obtain ⟨i, rfl⟩ := mem_ce h' he'
      rw [Finset.mem_sym2_iff]
      intro x hx
      rw [hmem] at hx
      rw [List.mem_toFinset]
      rcases hx with rfl | rfl <;> apply cv_mem)
    rw [List.toFinset_card_of_nodup hnv] at h2
    rw [Finset.card_image_of_injOn]
    · simp only [Finset.card_range]; omega
    · intro t ht t' ht' hh
      simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
      have := (hei _ _).1 hh
      have := modeq_small m _ _ this (by omega) (by omega)
      omega
  · intro f hf x hx
    simp only [Finset.mem_image] at hf
    obtain ⟨t, ht, rfl⟩ := hf
    rw [Finset.mem_range] at ht
    rw [hmem] at hx
    constructor
    · intro hxj
      rcases hx with rfl | rfl <;> rw [hvi] at hxj <;>
      · have := modeq_small m _ _ hxj (by omega) (by omega)
        omega
    · rcases hx with rfl | rfl <;> apply cv_mem


theorem l414_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (vs : List V) (es : List E) (hB : IsCircuit G vs es) (hodd : Odd vs.length)
    (M₁ : Finset {e : E // ¬ InsidePart G (blockPartition vs.toFinset) e})
    (hM₁ : EdmondsMatching65.Polyhedron.IsMatching (shrink G (blockPartition vs.toFinset)) M₁) :
    ∃ MB : Finset E, IsMaxMatchingOn G es.toFinset MB ∧
      EdmondsMatching65.Polyhedron.IsMatching G
        (M₁.map (Function.Embedding.subtype _) ∪ MB) := by
  have h : 0 < vs.length := by have := hB.2.2.1; omega
  have hrel : ∀ a b, b ∈ (blockPartition vs.toFinset).part a ↔ (blockSetoid vs.toFinset).r a b := fun a b =>
    Finpartition.mem_part_ofSetoid_iff_rel
  have F1 : ∀ x ∈ vs.toFinset, ∀ y ∈ vs.toFinset, toPart (blockPartition vs.toFinset) x = toPart (blockPartition vs.toFinset) y := by
    intro x hx y hy
    apply Subtype.ext
    show (blockPartition vs.toFinset).part x = (blockPartition vs.toFinset).part y
    have : y ∈ (blockPartition vs.toFinset).part x := (hrel x y).2 (Or.inr ⟨hx, hy⟩)
    exact ((blockPartition vs.toFinset).part_eq_of_mem ((blockPartition vs.toFinset).part_mem.2 (Finset.mem_univ x)) this).symm
  have F2 : ∀ e, G.ends e ∈ vs.toFinset.sym2 → InsidePart G (blockPartition vs.toFinset) e := by
    intro e he
    have hl := G.loopless e
    generalize hz : G.ends e = z at he hl
    induction z using Sym2.ind with
    | h a b =>
      rw [Finset.mk_mem_sym2_iff] at he
      refine ⟨(blockPartition vs.toFinset).part a, (blockPartition vs.toFinset).part_mem.2 (Finset.mem_univ a), ?_⟩
      rw [hz, Finset.mk_mem_sym2_iff]
      exact ⟨(hrel a a).2 (Or.inl rfl), (hrel a b).2 (Or.inr ⟨he.1, he.2⟩)⟩
  have hends : ∀ e : {e : E // ¬ InsidePart G (blockPartition vs.toFinset) e}, (shrink G (blockPartition vs.toFinset)).ends e =
      Sym2.map (toPart (blockPartition vs.toFinset)) (G.ends e.1) := fun e => rfl
  have hpt : ∀ (e : {e : E // ¬ InsidePart G (blockPartition vs.toFinset) e}) (x : V), x ∈ G.ends e.1 →
      toPart (blockPartition vs.toFinset) x ∈ (shrink G (blockPartition vs.toFinset)).ends e := by
    intro e x hx
    rw [hends, Sym2.mem_map]; exact ⟨x, hx, rfl⟩
  -- the touched vertex
  have hvsU : ∀ x, x ∈ vs ↔ x ∈ vs.toFinset := fun x => (List.mem_toFinset).symm
  obtain ⟨j, hC⟩ : ∃ j : ℕ, ∀ e ∈ M₁, ∀ x ∈ G.ends e.1, x ∈ vs → x = cv vs h j := by
    by_cases hex : ∃ e ∈ M₁, ∃ x ∈ G.ends e.1, x ∈ vs
    · obtain ⟨e₀, he₀, x₀, hx₀, hx₀vs⟩ := hex
      obtain ⟨j, hj⟩ : ∃ j, x₀ = cv vs h j := by
        obtain ⟨i, hi, hi'⟩ := List.mem_iff_getElem.1 hx₀vs
        exact ⟨i, by unfold cv; simp [Nat.mod_eq_of_lt hi, hi']⟩
      refine ⟨j, fun e he x hx hxvs => ?_⟩
      rw [← hj]
      by_cases hee : e = e₀
      · subst hee
        by_contra hne
        apply e.2
        apply F2
        have : G.ends e.1 = s(x, x₀) := (Sym2.mem_and_mem_iff hne).1 ⟨hx, hx₀⟩
        rw [this, Finset.mk_mem_sym2_iff]
        exact ⟨(hvsU x).1 hxvs, (hvsU x₀).1 hx₀vs⟩
      · exfalso
        have := hM₁ e₀ he₀ e he (Ne.symm hee) (toPart (blockPartition vs.toFinset) x₀) (hpt e₀ x₀ hx₀)
        apply this
        rw [F1 x₀ ((hvsU x₀).1 hx₀vs) x ((hvsU x).1 hxvs)]
        exact hpt e x hx
    · push_neg at hex
      exact ⟨0, fun e he x hx hxvs => absurd hxvs (hex e he x hx)⟩
  obtain ⟨MB, hMB, hMBv⟩ := p14_build G hB hodd h j
  refine ⟨MB, hMB, ?_⟩
  have hMBm := hMB.2.1
  intro f1 hf1 f2 hf2 hne x hx1 hx2
  simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.subtype_apply] at hf1 hf2
  rcases hf1 with ⟨e1, he1, rfl⟩ | hf1 <;> rcases hf2 with ⟨e2, he2, rfl⟩ | hf2
  · have hne' : e1 ≠ e2 := fun hh => hne (by rw [hh])
    exact hM₁ e1 he1 e2 he2 hne' (toPart (blockPartition vs.toFinset) x) (hpt e1 x hx1) (hpt e2 x hx2)
  · exact (hMBv f2 hf2 x hx2).1 (hC e1 he1 x hx1 ((hMBv f2 hf2 x hx2).2))
  · exact (hMBv f1 hf1 x hx1).1 (hC e2 he2 x hx2 ((hMBv f1 hf1 x hx1).2))
  · exact hMBm f1 hf1 f2 hf2 hne x hx1 hx2

end PathsTreesFlowers.Duality

open PathsTreesFlowers.Duality


theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (vs : List V) (es : List E) (hB : IsCircuit G vs es) (hodd : Odd vs.length)
    (M₁ : Finset {e : E // ¬ InsidePart G (blockPartition vs.toFinset) e})
    (hM₁ : EdmondsMatching65.Polyhedron.IsMatching (shrink G (blockPartition vs.toFinset)) M₁) :
    ∃ MB : Finset E, IsMaxMatchingOn G es.toFinset MB ∧
      EdmondsMatching65.Polyhedron.IsMatching G
        (M₁.map (Function.Embedding.subtype _) ∪ MB) := by
  exact l414_core G vs es hB hodd M₁ hM₁
