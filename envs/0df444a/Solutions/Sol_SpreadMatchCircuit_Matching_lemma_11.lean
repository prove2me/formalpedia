-- Prove2me | solution 1 for SpreadMatchCircuit.Matching.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:54:15.261163+00:00
-- url     : https://prove2.me/submissions/8f4ab85b-8536-4bdb-9bd6-0663d114971c

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw
import Definitions.Def_SpreadMatchCircuit_Matching_Approximator

section
namespace SpreadMatchCircuit.Matching.Dev.Cnt

open Finset SpreadMatchCircuit.Matching

variable {n : ℕ}

lemma mem_endpoints {e : Edge n} {v : Fin n} : v ∈ endpoints e ↔ v ∈ e.1 := by
  simp [endpoints, Sym2.mem_toFinset]

/-- Apply a vertex permutation to an edge. -/
def emap (σ : Equiv.Perm (Fin n)) (e : Edge n) : Edge n :=
  ⟨e.1.map σ, by rw [Sym2.isDiag_map σ.injective]; exact e.2⟩

lemma emap_val (σ : Equiv.Perm (Fin n)) (e : Edge n) : (emap σ e).1 = e.1.map σ := rfl

lemma emap_injective (σ : Equiv.Perm (Fin n)) : Function.Injective (emap σ) := by
  intro a b h
  apply Subtype.ext
  have : a.1.map σ = b.1.map σ := congrArg Subtype.val h
  exact Sym2.map.injective σ.injective this

lemma endpoints_emap (σ : Equiv.Perm (Fin n)) (e : Edge n) :
    endpoints (emap σ e) = (endpoints e).map σ.toEmbedding := by
  ext v
  simp only [mem_endpoints, emap_val, Sym2.mem_map, Finset.mem_map, Equiv.toEmbedding_apply]

lemma emap_eq_self (σ : Equiv.Perm (Fin n)) {e : Edge n} (h : ∀ w ∈ endpoints e, σ w = w) :
    emap σ e = e := by
  apply Subtype.ext
  rw [emap_val]
  have : e.1.map σ = e.1.map id :=
    Sym2.map_congr (fun x hx => h x (mem_endpoints.mpr hx))
  rw [this, Sym2.map_id]
  rfl

/-- Apply a vertex permutation to a graph. -/
def fmap (σ : Equiv.Perm (Fin n)) (x : Finset (Edge n)) : Finset (Edge n) :=
  x.map ⟨emap σ, emap_injective σ⟩

lemma isMatching_fmap (σ : Equiv.Perm (Fin n)) {x : Finset (Edge n)} (hx : IsMatching x) :
    IsMatching (fmap σ x) := by
  intro f hf f' hf' hne
  simp only [fmap, Finset.mem_map, Function.Embedding.coeFn_mk] at hf hf'
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, hb, rfl⟩ := hf'
  have hab : a ≠ b := fun h => hne (h ▸ rfl)
  rw [endpoints_emap, endpoints_emap]
  exact (Finset.disjoint_map _).mpr (hx a ha b hb hab)

lemma isCrossEdge_emap {L : Finset (Fin n)} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ w, σ w ∈ L ↔ w ∈ L) {e : Edge n} (he : IsCrossEdge L e) :
    IsCrossEdge L (emap σ e) := by
  obtain ⟨u, hu, v, hv, h⟩ := he
  exact ⟨σ u, (hσ u).2 hu, σ v, fun h' => hv ((hσ v).1 h'), by
    rw [emap_val, h, Sym2.map_mk]⟩

lemma swap_mem_iff {L : Finset (Fin n)} {a b : Fin n} (hab : a ∈ L ↔ b ∈ L) (w : Fin n) :
    Equiv.swap a b w ∈ L ↔ w ∈ L := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact hab.symm
  · subst h2; exact hab
  · exact Iff.rfl

lemma halfSide_card (N : ℕ) : (halfSide N).card = N := by
  have : (halfSide N).map Fin.valEmbedding = range N := by
    ext i
    simp only [halfSide, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hi; exact ⟨⟨i, by omega⟩, hi, rfl⟩
  rw [← card_map Fin.valEmbedding, this, card_range]

lemma inter_verts_card_le (S : Finset (Fin n)) (m : Finset (Edge n))
    (h : ∀ f ∈ m, ∀ a ∈ endpoints f, ∀ b ∈ endpoints f, a ∈ S → b ∈ S → a = b) :
    (S ∩ verts m).card ≤ m.card := by
  classical
  have hsub : S ∩ verts m ⊆ m.biUnion (fun f => S ∩ endpoints f) := by
    intro w hw
    rw [Finset.mem_inter] at hw
    obtain ⟨f, hf, hwf⟩ := Finset.mem_biUnion.mp hw.2
    exact Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_inter.mpr ⟨hw.1, hwf⟩⟩
  calc (S ∩ verts m).card ≤ (m.biUnion (fun f => S ∩ endpoints f)).card := card_le_card hsub
    _ ≤ ∑ f ∈ m, (S ∩ endpoints f).card := card_biUnion_le
    _ ≤ ∑ f ∈ m, 1 := by
        apply sum_le_sum
        intro f hf
        apply Finset.card_le_one.mpr
        intro a ha b hb
        rw [Finset.mem_inter] at ha hb
        exact h f hf a ha.2 b hb.2 ha.1 hb.1
    _ = m.card := by simp

lemma cross_endpoints {L : Finset (Fin n)} {f : Edge n} (hf : IsCrossEdge L f) :
    (∀ a ∈ endpoints f, ∀ b ∈ endpoints f, a ∈ L → b ∈ L → a = b) ∧
    (∀ a ∈ endpoints f, ∀ b ∈ endpoints f, a ∈ Lᶜ → b ∈ Lᶜ → a = b) := by
  obtain ⟨u, hu, v, hv, h⟩ := hf
  simp only [mem_endpoints, h, Sym2.mem_iff, Finset.mem_compl]
  constructor
  · rintro a (rfl | rfl) b (rfl | rfl) ha hb <;> first | rfl | exact absurd ha hv | exact absurd hb hv
  · rintro a (rfl | rfl) b (rfl | rfl) ha hb <;> first | rfl | exact absurd hu ha | exact absurd hu hb

lemma mem_crossMatchings {N k : ℕ} {x : Finset (Edge (2 * N))} :
    x ∈ crossMatchings N k ↔ IsMatching x ∧ x.card = k ∧ IsCrossGraph (halfSide N) x := by
  simp [crossMatchings]

open scoped Classical in
/-- Cross `k`-matchings containing `m`. -/
noncomputable def A (N k : ℕ) (m : Finset (Edge (2 * N))) : Finset (Finset (Edge (2 * N))) :=
  (crossMatchings N k).filter (fun x => m ⊆ x)

lemma mem_A {N k : ℕ} {m x : Finset (Edge (2 * N))} :
    x ∈ A N k m ↔ x ∈ crossMatchings N k ∧ m ⊆ x := by
  simp [A]

lemma step (N k : ℕ) (m : Finset (Edge (2 * N))) (e : Edge (2 * N)) (he : e ∉ m)
    (hne : (A N k (insert e m)).Nonempty) :
    (A N k (insert e m)).card * (N - m.card) ^ 2 ≤ (A N k m).card * (k - m.card) := by
  classical
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨hy0c, hy0s⟩ := mem_A.mp hy0
  obtain ⟨hmat, -, hcross⟩ := mem_crossMatchings.mp hy0c
  have hey0 : e ∈ y0 := hy0s (mem_insert_self _ _)
  have hmy0 : m ⊆ y0 := (subset_insert _ _).trans hy0s
  obtain ⟨u, hu, v, hv, huv⟩ := hcross e hey0
  set L := halfSide N with hL
  set V := verts m with hV
  have hnotV : ∀ w ∈ endpoints e, w ∉ V := by
    intro w hw hwV
    obtain ⟨f, hf, hwf⟩ := Finset.mem_biUnion.mp hwV
    have hfe : e ≠ f := fun h => he (h ▸ hf)
    exact Finset.disjoint_left.mp (hmat e hey0 f (hmy0 hf) hfe) hw hwf
  have huV : u ∉ V := hnotV u (mem_endpoints.mpr (by rw [huv]; exact Sym2.mem_mk_left u v))
  have hvV : v ∉ V := hnotV v (mem_endpoints.mpr (by rw [huv]; exact Sym2.mem_mk_right u v))
  set Lf := L \ V with hLf
  set Rf := Lᶜ \ V with hRf
  have hcardL : L.card = N := halfSide_card N
  have hcardR : Lᶜ.card = N := by
    rw [card_compl, hcardL, Fintype.card_fin]; omega
  have hLV : (L ∩ V).card ≤ m.card :=
    inter_verts_card_le L m (fun f hf => (cross_endpoints (hcross f (hmy0 hf))).1)
  have hRV : (Lᶜ ∩ V).card ≤ m.card :=
    inter_verts_card_le Lᶜ m (fun f hf => (cross_endpoints (hcross f (hmy0 hf))).2)
  have hLfc : N - m.card ≤ Lf.card := by
    have := card_sdiff_add_card_inter L V; rw [← hLf] at this; omega
  have hRfc : N - m.card ≤ Rf.card := by
    have := card_sdiff_add_card_inter Lᶜ V; rw [← hRf] at this; omega
  let σ : Fin (2 * N) → Fin (2 * N) → Equiv.Perm (Fin (2 * N)) :=
    fun a b => Equiv.swap u a * Equiv.swap v b
  have hσapp : ∀ a b w, σ a b w = Equiv.swap u a (Equiv.swap v b w) := fun _ _ _ => rfl
  -- properties of σ for admissible (a, b)
  have hσL : ∀ a ∈ Lf, ∀ b ∈ Rf, ∀ w, σ a b w ∈ L ↔ w ∈ L := by
    intro a ha b hb w
    rw [hσapp]
    have ha' : a ∈ L := (mem_sdiff.mp ha).1
    have hb' : b ∉ L := Finset.mem_compl.mp (mem_sdiff.mp hb).1
    rw [swap_mem_iff (by simp [hu, ha']), swap_mem_iff (by simp [hv, hb'])]
  have hσu : ∀ a ∈ Lf, ∀ b ∈ Rf, σ a b u = a := by
    intro a ha b hb
    have hb' : b ∉ L := Finset.mem_compl.mp (mem_sdiff.mp hb).1
    have n1 : u ≠ v := fun h => hv (h ▸ hu)
    have n2 : u ≠ b := fun h => hb' (h ▸ hu)
    rw [hσapp, Equiv.swap_apply_of_ne_of_ne n1 n2, Equiv.swap_apply_left]
  have hσv : ∀ a ∈ Lf, ∀ b ∈ Rf, σ a b v = b := by
    intro a ha b hb
    have ha' : a ∈ L := (mem_sdiff.mp ha).1
    have hb' : b ∉ L := Finset.mem_compl.mp (mem_sdiff.mp hb).1
    have n1 : b ≠ u := fun h => hb' (h ▸ hu)
    have n2 : b ≠ a := fun h => hb' (h ▸ ha')
    rw [hσapp, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne n1 n2]
  have hσV : ∀ a ∈ Lf, ∀ b ∈ Rf, ∀ w ∈ V, σ a b w = w := by
    intro a ha b hb w hw
    have haV : a ∉ V := (mem_sdiff.mp ha).2
    have hbV : b ∉ V := (mem_sdiff.mp hb).2
    have n1 : w ≠ v := fun h => hvV (h ▸ hw)
    have n2 : w ≠ b := fun h => hbV (h ▸ hw)
    have n3 : w ≠ u := fun h => huV (h ▸ hw)
    have n4 : w ≠ a := fun h => haV (h ▸ hw)
    rw [hσapp, Equiv.swap_apply_of_ne_of_ne n1 n2, Equiv.swap_apply_of_ne_of_ne n3 n4]
  have hσe : ∀ a ∈ Lf, ∀ b ∈ Rf, (emap (σ a b) e).1 = s(a, b) := by
    intro a ha b hb
    rw [emap_val, huv, Sym2.map_mk, hσu a ha b hb, hσv a ha b hb]
  let φ : Finset (Edge (2 * N)) × (Fin (2 * N) × Fin (2 * N)) →
      (Σ _ : Finset (Edge (2 * N)), Edge (2 * N)) :=
    fun p => ⟨fmap (σ p.2.1 p.2.2) p.1, emap (σ p.2.1 p.2.2) e⟩
  have hmaps : Set.MapsTo φ (A N k (insert e m) ×ˢ (Lf ×ˢ Rf) : Finset _)
      ((A N k m).sigma (fun y => y \ m) : Finset _) := by
    rintro ⟨x, a, b⟩ hp
    simp only [coe_product, Set.mem_prod, mem_coe] at hp
    obtain ⟨hx, ha, hb⟩ := hp
    obtain ⟨hxc, hxs⟩ := mem_A.mp hx
    obtain ⟨hxm, hxk, hxcr⟩ := mem_crossMatchings.mp hxc
    have hex : e ∈ x := hxs (mem_insert_self _ _)
    have hmx : m ⊆ x := (subset_insert _ _).trans hxs
    simp only [mem_coe, mem_sigma, φ]
    refine ⟨mem_A.mpr ⟨mem_crossMatchings.mpr ⟨isMatching_fmap _ hxm, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [fmap, card_map, hxk]
    · intro f hf
      simp only [fmap, Finset.mem_map, Function.Embedding.coeFn_mk] at hf
      obtain ⟨g, hg, rfl⟩ := hf
      exact isCrossEdge_emap _ (hσL a ha b hb) (hxcr g hg)
    · intro f hf
      have hfix : emap (σ a b) f = f := emap_eq_self _ (fun w hw =>
        hσV a ha b hb w (Finset.mem_biUnion.mpr ⟨f, hf, hw⟩))
      rw [← hfix]
      exact Finset.mem_map_of_mem _ (hmx hf)
    · rw [mem_sdiff]
      refine ⟨Finset.mem_map_of_mem (f := ⟨emap (σ a b), emap_injective _⟩) hex, ?_⟩
      intro hm
      have haV : a ∉ V := (mem_sdiff.mp ha).2
      apply haV
      refine Finset.mem_biUnion.mpr ⟨_, hm, mem_endpoints.mpr ?_⟩
      rw [hσe a ha b hb]; exact Sym2.mem_mk_left a b
  have hinj : Set.InjOn φ (A N k (insert e m) ×ˢ (Lf ×ˢ Rf) : Finset _) := by
    rintro ⟨x, a, b⟩ hp ⟨x', a', b'⟩ hp' hφ
    simp only [coe_product, Set.mem_prod, mem_coe] at hp hp'
    obtain ⟨-, ha, hb⟩ := hp
    obtain ⟨-, ha', hb'⟩ := hp'
    simp only [φ, Sigma.mk.inj_iff, heq_eq_eq] at hφ
    obtain ⟨h1, h2⟩ := hφ
    have h3 : s(a, b) = s(a', b') := by
      rw [← hσe a ha b hb, ← hσe a' ha' b' hb', h2]
    have haL : a ∈ L := (mem_sdiff.mp ha).1
    have hbL : b ∉ L := Finset.mem_compl.mp (mem_sdiff.mp hb).1
    have ha'L : a' ∈ L := (mem_sdiff.mp ha').1
    have hb'L : b' ∉ L := Finset.mem_compl.mp (mem_sdiff.mp hb').1
    rcases Sym2.eq_iff.mp h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : x = x' := Finset.map_injective _ h1
      rw [this]
    · exact absurd haL hb'L
  have h1 := card_le_card_of_injOn φ hmaps hinj
  rw [card_product, card_product, card_sigma] at h1
  have hsum : ∑ y ∈ A N k m, (y \ m).card = (A N k m).card * (k - m.card) := by
    apply sum_const_nat
    intro y hy
    obtain ⟨hyc, hys⟩ := mem_A.mp hy
    rw [card_sdiff_of_subset hys, (mem_crossMatchings.mp hyc).2.1]
  calc (A N k (insert e m)).card * (N - m.card) ^ 2
      ≤ (A N k (insert e m)).card * (Lf.card * Rf.card) := by
        apply Nat.mul_le_mul_left; rw [sq]; exact Nat.mul_le_mul hLfc hRfc
    _ ≤ _ := h1.trans hsum.le

theorem prod_bound (N k : ℕ) (m : Finset (Edge (2 * N))) :
    (A N k m).card * ∏ i ∈ range m.card, (N - i) ^ 2 ≤
      (A N k ∅).card * ∏ i ∈ range m.card, (k - i) := by
  classical
  induction m using Finset.induction_on with
  | empty => simp
  | insert e m he ih =>
    rw [card_insert_of_notMem he, prod_range_succ, prod_range_succ]
    by_cases hne : (A N k (insert e m)).Nonempty
    · have hs := step N k m e he hne
      calc (A N k (insert e m)).card * ((∏ i ∈ range m.card, (N - i) ^ 2) * (N - m.card) ^ 2)
          = ((A N k (insert e m)).card * (N - m.card) ^ 2) * ∏ i ∈ range m.card, (N - i) ^ 2 := by
            ring
        _ ≤ ((A N k m).card * (k - m.card)) * ∏ i ∈ range m.card, (N - i) ^ 2 :=
            Nat.mul_le_mul_right _ hs
        _ = ((A N k m).card * ∏ i ∈ range m.card, (N - i) ^ 2) * (k - m.card) := by ring
        _ ≤ ((A N k ∅).card * ∏ i ∈ range m.card, (k - i)) * (k - m.card) :=
            Nat.mul_le_mul_right _ ih
        _ = _ := by ring
    · rw [not_nonempty_iff_eq_empty.mp hne]; simp

theorem cross_spread (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (m : Finset (Edge (2 * N)))
    (hm : IsMatching m) (hj : 50 * m.card ≤ k) :
    uniformProb (crossMatchings N k) (fun x => m ⊆ x) ≤ (2 * (k : ℝ) / (N : ℝ) ^ 2) ^ m.card := by
  classical
  have hP := prod_bound N k m
  have hA0 : A N k ∅ = crossMatchings N k :=
    filter_true_of_mem (fun x _ => empty_subset x)
  rw [hA0] at hP
  have hU : uniformProb (crossMatchings N k) (fun x => m ⊆ x) =
      ((A N k m).card : ℝ) / ((crossMatchings N k).card : ℝ) := by
    unfold uniformProb A; congr
  rw [hU]
  set X := (crossMatchings N k).card with hX
  set a := (A N k m).card with ha
  set j := m.card with hjdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbase : (0 : ℝ) ≤ 2 * (k : ℝ) / (N : ℝ) ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos X with h0 | hpos
  · rw [h0]; simp; positivity
  have e1 : ((∏ i ∈ range j, (N - i) ^ 2 : ℕ) : ℝ) = ∏ i ∈ range j, ((N : ℝ) - i) ^ 2 := by
    rw [Nat.cast_prod]; apply prod_congr rfl; intro i hi
    have := mem_range.mp hi
    rw [Nat.cast_pow, Nat.cast_sub (by omega)]
  have e2 : ((∏ i ∈ range j, (k - i) : ℕ) : ℝ) = ∏ i ∈ range j, ((k : ℝ) - i) := by
    rw [Nat.cast_prod]; apply prod_congr rfl; intro i hi
    have := mem_range.mp hi
    rw [Nat.cast_sub (by omega)]
  have hPr : (a : ℝ) * ∏ i ∈ range j, ((N : ℝ) - i) ^ 2 ≤ X * ∏ i ∈ range j, ((k : ℝ) - i) := by
    rw [← e1, ← e2]; exact_mod_cast hP
  have hD : 0 < ∏ i ∈ range j, ((N : ℝ) - i) ^ 2 := by
    apply prod_pos; intro i hi
    have := mem_range.mp hi
    have : (i : ℝ) < N := by exact_mod_cast (show i < N by omega)
    nlinarith
  have hXr : (0 : ℝ) < X := by exact_mod_cast hpos
  calc (a : ℝ) / X ≤ (∏ i ∈ range j, ((k : ℝ) - i)) / ∏ i ∈ range j, ((N : ℝ) - i) ^ 2 := by
        rw [div_le_div_iff₀ hXr hD]; linarith
    _ = ∏ i ∈ range j, (((k : ℝ) - i) / ((N : ℝ) - i) ^ 2) := by rw [prod_div_distrib]
    _ ≤ ∏ i ∈ range j, (2 * (k : ℝ) / (N : ℝ) ^ 2) := by
        apply prod_le_prod
        · intro i hi
          have := mem_range.mp hi
          have : (i : ℝ) ≤ k := by exact_mod_cast (show i ≤ k by omega)
          apply div_nonneg <;> nlinarith
        · intro i hi
          have hi' := mem_range.mp hi
          have h50 : 50 * (i : ℝ) + 50 ≤ k := by exact_mod_cast (show 50 * i + 50 ≤ k by omega)
          have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
          have hi0 : (0 : ℝ) ≤ i := by positivity
          have hNi : 0 < (N : ℝ) - i := by linarith
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hk0 : (0 : ℝ) < k := by linarith
          have hsq : (N : ℝ) ^ 2 ≤ 2 * ((N : ℝ) - i) ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hsq hk0.le]
    _ = _ := by rw [prod_const, card_range]

end SpreadMatchCircuit.Matching.Dev.Cnt
end

section
namespace SpreadMatchCircuit.Matching.Dev.L11

open Finset SpreadMatchCircuit.Matching

lemma firstOf_filter_cases {α : Type} (ord : LinearOrder α) (F : Finset α) (p : α → Prop)
    [DecidablePred p] (d : α) :
    (firstOf ord (F.filter p) d ∈ F ∧ p (firstOf ord (F.filter p) d)) ∨
      firstOf ord (F.filter p) d = d := by
  unfold firstOf
  split_ifs with h
  · left; exact mem_filter.mp (@Finset.min'_mem α ord _ h)
  · right; rfl

lemma firstOf_filter_spec {α : Type} (ord : LinearOrder α) (F : Finset α) (p : α → Prop)
    [DecidablePred p] (d : α) (Q : α → Prop) (hex : ∃ x ∈ F, p x) (hQ : ∀ x ∈ F, p x → Q x) :
    Q (firstOf ord (F.filter p) d) := by
  have hne : (F.filter p).Nonempty := by
    obtain ⟨x, hx, hpx⟩ := hex; exact ⟨x, mem_filter.mpr ⟨hx, hpx⟩⟩
  unfold firstOf
  rw [dif_pos hne]
  have := mem_filter.mp (@Finset.min'_mem α ord _ hne)
  exact hQ _ this.1 this.2

lemma uniformProb_mono {β : Type} (F : Finset β) (A B : β → Prop) (h : ∀ x ∈ F, A x → B x) :
    uniformProb F A ≤ uniformProb F B := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_le_card (fun x hx => by
    rw [mem_filter] at hx ⊢; exact ⟨hx.1, h x hx.1 hx.2⟩)

lemma uniformProb_le_one {β : Type} (F : Finset β) (A : β → Prop) : uniformProb F A ≤ 1 := by
  classical
  unfold uniformProb
  apply div_le_one_of_le₀ _ (by positivity)
  exact_mod_cast card_filter_le _ _

lemma exists_of_uniformProb_pos {β : Type} (F : Finset β) (A : β → Prop)
    (h : 0 < uniformProb F A) : ∃ x ∈ F, A x := by
  classical
  by_contra hc
  push Not at hc
  unfold uniformProb at h
  rw [filter_false_of_mem hc] at h
  simp at h

variable {N : ℕ}

lemma selector_spec (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N))))
    (x : Finset (Edge (2 * N))) :
    G.selector ord x ⊆ x ∧ (G.selector ord x ∈ G.candidates ∨ G.selector ord x = ∅) := by
  unfold AndGate.selector
  classical
  rcases firstOf_filter_cases ord G.candidates (fun m => m ⊆ x) ∅ with h | h
  · exact ⟨h.2, Or.inl h.1⟩
  · rw [h]; exact ⟨empty_subset _, Or.inr rfl⟩

lemma candidates_card (G : AndGate N) (t : ℝ) (hG : G.SizeBounded t) (c : Finset (Edge (2 * N)))
    (hc : c ∈ G.candidates) : (c.card : ℝ) ≤ 2 * t := by
  classical
  unfold AndGate.candidates at hc
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_image₂.mp (mem_filter.mp hc).1
  have h1 := hG.1 a ha
  have h2 := hG.2 b hb
  have : ((a ∪ b).card : ℝ) ≤ a.card + b.card := by exact_mod_cast card_union_le a b
  linarith

lemma coreProb_empty (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (M : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M) :
    G.coreProb ord k M ∅ = 1 := by
  unfold AndGate.coreProb
  simp only [empty_subset, true_and]
  exact div_self hP.ne'

lemma largestCore_spec (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r : ℝ) (M : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M) :
    IsMatching (G.largestCore ord k r M) ∧
      (r ^ (G.largestCore ord k r M).card)⁻¹ ≤
        G.coreProb ord k M (G.largestCore ord k r M) := by
  classical
  unfold AndGate.largestCore
  refine firstOf_filter_spec ord _ _ ∅
    (fun c => IsMatching c ∧ (r ^ c.card)⁻¹ ≤ G.coreProb ord k M c) ?_ ?_
  · have h0 : (∅ : Finset (Edge (2 * N))) ∈
        (univ.filter fun m => IsMatching m ∧ (r ^ m.card)⁻¹ ≤ G.coreProb ord k M m) := by
      rw [mem_filter]
      refine ⟨mem_univ _, ?_, ?_⟩
      · intro e he; simp at he
      · rw [coreProb_empty G ord k M hP]; simp
    obtain ⟨c, hc, hmax⟩ := exists_max_image _ card ⟨_, h0⟩
    exact ⟨c, hc, hmax⟩
  · intro x hx _
    exact (mem_filter.mp hx).2

/-- A core is contained in some new positive error, hence not in `M`. -/
lemma core_witness (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r : ℝ) (hr : 0 < r) (M : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M) :
    ∃ x ∈ crossMatchings N k, G.largestCore ord k r M ⊆ G.selector ord x ∧ x ∈ G.newPos k M := by
  obtain ⟨-, hcore⟩ := largestCore_spec G ord k r M hP
  have hpos : 0 < G.coreProb ord k M (G.largestCore ord k r M) :=
    lt_of_lt_of_le (by positivity) hcore
  unfold AndGate.coreProb at hpos
  have hU := (div_pos_iff_of_pos_right hP).mp hpos
  exact exists_of_uniformProb_pos _ _ hU

lemma largestCore_not_mem (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r : ℝ) (hr : 0 < r) (M : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M) :
    G.largestCore ord k r M ∉ M := by
  classical
  intro hmem
  obtain ⟨x, -, hsub, hx⟩ := core_witness G ord k r hr M hP
  have hx' : x ∈ errorPos N k G.g M := (mem_sdiff.mp hx).1
  unfold errorPos at hx'
  have hnf := (mem_filter.mp hx').2.2
  exact hnf ⟨_, hmem, hsub.trans (selector_spec G ord x).1⟩

lemma loop_spec (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r t : ℝ) (hr : 0 < r) :
    ∀ (steps : ℕ) (M : Finset (Finset (Edge (2 * N)))),
      Fintype.card (Finset (Edge (2 * N))) < M.card + steps →
      (¬ 0 < G.newPosProb k (G.loop ord k r t steps M)) ∨
      (0 < G.newPosProb k (G.loop ord k r t steps M) ∧
        t < ((G.largestCore ord k r (G.loop ord k r t steps M)).card : ℝ)) := by
  intro steps
  induction steps with
  | zero =>
    intro M hM
    exfalso
    have := card_le_univ M
    omega
  | succ s ih =>
    intro M hM
    rw [AndGate.loop]
    by_cases hP : 0 < G.newPosProb k M
    · rw [if_pos hP]
      by_cases ht : ((G.largestCore ord k r M).card : ℝ) ≤ t
      · rw [if_pos ht]
        apply ih
        rw [card_insert_of_notMem (largestCore_not_mem G ord k r hr M hP)]
        omega
      · rw [if_neg ht]
        exact Or.inr ⟨hP, lt_of_not_ge ht⟩
    · rw [if_neg hP]
      exact Or.inl hP

lemma base_le (N k : ℕ) (r : ℝ) (hkpos : (0 : ℝ) < k)
    (hr : r ≤ (2 * (N : ℝ)) ^ 2 / (16 * (k : ℝ))) (hNpos : (0 : ℝ) < N) :
    r * (2 * (k : ℝ) / (N : ℝ) ^ 2) ≤ 1 / 2 := by
  have : r ≤ (N : ℝ) ^ 2 / (4 * k) := by
    have h := hr
    rw [show (2 * (N : ℝ)) ^ 2 / (16 * (k : ℝ)) = (N : ℝ) ^ 2 / (4 * k) by
      field_simp; ring] at h
    exact h
  rw [le_div_iff₀ (by positivity)] at this
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith


lemma halting_bound (N k : ℕ) (hk₁ : 1 ≤ k) (hkN : k ≤ N) (t r : ℝ)
    (htk : t ≤ (k : ℝ) / 100)
    (hr₀ : 0 < r) (hr : r ≤ (2 * (N : ℝ)) ^ 2 / (16 * (k : ℝ)))
    (ord : LinearOrder (Finset (Edge (2 * N)))) (G : AndGate N) (hG : G.SizeBounded t)
    (M : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M)
    (hct : t < ((G.largestCore ord k r M).card : ℝ)) :
    G.newPosProb k M ≤ (2 : ℝ) ^ (-t) := by
  by_cases ht0 : t < 0
  · calc G.newPosProb k M ≤ 1 := uniformProb_le_one _ _
      _ ≤ 2 ^ (-t) := Real.one_le_rpow (by norm_num) (by linarith)
  push Not at ht0
  set c := G.largestCore ord k r M with hc
  set j := c.card with hj
  obtain ⟨hcm, hcore⟩ := largestCore_spec G ord k r M hP
  -- size bound j ≤ 2t
  obtain ⟨x, -, hsub, -⟩ := core_witness G ord k r hr₀ M hP
  have hj2t : (j : ℝ) ≤ 2 * t := by
    have hcard : (j : ℝ) ≤ (G.selector ord x).card := by exact_mod_cast card_le_card hsub
    rcases (selector_spec G ord x).2 with hs | hs
    · exact hcard.trans (candidates_card G t hG _ hs)
    · rw [hs] at hcard; simp at hcard
      have : (j : ℝ) = 0 := by exact_mod_cast hcard
      linarith
  have hj50 : 50 * j ≤ k := by
    have : (50 * j : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hcs := Dev.Cnt.cross_spread N k hk₁ hkN c hcm hj50
  -- P ≤ r^j * U(c ⊆ sel ∧ newPos)
  have hrj : 0 < r ^ j := pow_pos hr₀ j
  unfold AndGate.coreProb at hcore
  rw [le_div_iff₀ hP] at hcore
  have hU : uniformProb (crossMatchings N k) (fun x => c ⊆ G.selector ord x ∧ x ∈ G.newPos k M)
      ≤ uniformProb (crossMatchings N k) (fun x => c ⊆ x) :=
    uniformProb_mono _ _ _ (fun x _ h => h.1.trans (selector_spec G ord x).1)
  have hP1 : G.newPosProb k M ≤ r ^ j * (2 * (k : ℝ) / (N : ℝ) ^ 2) ^ j := by
    have := mul_le_mul_of_nonneg_left (hcore.trans (hU.trans hcs)) hrj.le
    rwa [← mul_assoc, mul_inv_cancel₀ hrj.ne', one_mul] at this
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hbase := base_le N k r hkpos hr hNpos
  have hb0 : 0 ≤ r * (2 * (k : ℝ) / (N : ℝ) ^ 2) :=
    mul_nonneg hr₀.le (div_nonneg (by linarith) (sq_nonneg _))
  calc G.newPosProb k M ≤ r ^ j * (2 * (k : ℝ) / (N : ℝ) ^ 2) ^ j := hP1
    _ = (r * (2 * (k : ℝ) / (N : ℝ) ^ 2)) ^ j := by rw [mul_pow]
    _ ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_left₀ hb0 hbase j
    _ = (2 : ℝ) ^ (-(j : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
    _ ≤ (2 : ℝ) ^ (-t) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith

end SpreadMatchCircuit.Matching.Dev.L11

namespace SpreadMatchCircuit.Matching

open Finset Dev.L11

theorem chk_lemma_11 (N k : ℕ) (hk₁ : 1 ≤ k) (hkN : k ≤ N) (t r : ℝ)
    (htk : t ≤ (k : ℝ) / 100)
    (hr₀ : 0 < r) (hr : r ≤ (2 * (N : ℝ)) ^ 2 / (16 * (k : ℝ)))
    (ord : LinearOrder (Finset (Edge (2 * N)))) (G : AndGate N) (hG : G.SizeBounded t) :
    uniformProb (crossMatchings N k) (fun x => x ∈ G.newPos k (G.algorithm1 ord k r t))
      ≤ (2 : ℝ) ^ (-t) := by
  have hspec := loop_spec G ord k r t hr₀ (Fintype.card (Finset (Edge (2 * N))) + 1) ∅
    (by simp)
  change G.newPosProb k (G.algorithm1 ord k r t) ≤ _
  rw [show G.loop ord k r t (Fintype.card (Finset (Edge (2 * N))) + 1) ∅ =
    G.algorithm1 ord k r t from rfl] at hspec
  generalize G.algorithm1 ord k r t = M at hspec ⊢
  rcases hspec with hP | ⟨hP, hct⟩
  · exact (le_of_not_gt hP).trans (Real.rpow_pos_of_pos (by norm_num) _).le
  · exact halting_bound N k hk₁ hkN t r htk hr₀ hr ord G hG M hP hct

end SpreadMatchCircuit.Matching
end

theorem solution : type_of% @SpreadMatchCircuit.Matching.chk_lemma_11 := @SpreadMatchCircuit.Matching.chk_lemma_11
