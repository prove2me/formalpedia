-- Prove2me | solution 1 for SpreadMatchCircuit.Matching.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:24:55.719172+00:00
-- url     : https://prove2.me/submissions/a81decef-0e80-4b75-aa13-6e000c91f9b7

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw
import Definitions.Def_SpreadMatchCircuit_Matching_Approximator
import Definitions.Def_SpreadMatchCircuit_Matching_MonotoneCircuit
import Definitions.Def_SpreadMatchCircuit_Matching_Promise
import Definitions.Def_SpreadMatchCircuit_Matching_Encoding
import Theorems.Thm_SpreadMatchCircuit_Matching_lemma_5
import Theorems.Thm_SpreadMatchCircuit_Matching_lemma_11
import Theorems.Thm_SpreadMatchCircuit_Matching_lemma_12

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
namespace SpreadMatchCircuit.Matching.Dev.Gates

open SpreadMatchCircuit.Matching
open Finset

/-- Evaluation of a circuit on a graph on `Fin (2N)`: the input node `i` reads the edge `inp i`
(and is constantly false when `inp i = none`). -/
def ev {ι : Type} {N : ℕ} (C : MonotoneCircuit ι) (inp : ι → Option (Edge (2 * N)))
    (x : Finset (Edge (2 * N))) : Bool :=
  C.eval (fun i => match inp i with | some e => decide (e ∈ x) | none => false)

section Construction

variable {ι : Type} {N : ℕ} (C : MonotoneCircuit ι) (inp : ι → Option (Edge (2 * N)))
  (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ) (r t : ℝ)

/-- The value of node `g` on the graph `x`. -/
def val (g : Fin C.size) (x : Finset (Edge (2 * N))) : Bool :=
  C.nodeValue (fun i => match inp i with | some e => decide (e ∈ x) | none => false) g

/-- The approximating family `M_g`. -/
noncomputable def fam (g : Fin C.size) : Finset (Finset (Edge (2 * N))) :=
  match C.gate g with
  | .input i => match inp i with | some e => { {e} } | none => ∅
  | .and a b =>
      (AndGate.mk (val C inp ⟨a.val, a.isLt.trans g.isLt⟩) (val C inp ⟨b.val, b.isLt.trans g.isLt⟩)
        (fam ⟨a.val, a.isLt.trans g.isLt⟩) (fam ⟨b.val, b.isLt.trans g.isLt⟩)).algorithm1 ord k r t
  | .or a b => fam ⟨a.val, a.isLt.trans g.isLt⟩ ∪ fam ⟨b.val, b.isLt.trans g.isLt⟩
termination_by g.val
decreasing_by
  all_goals first | exact a.isLt | exact b.isLt

/-- The AND gate data at node `g` (a trivial dummy gate at non-AND nodes). -/
noncomputable def gateOf (g : Fin C.size) : AndGate N :=
  match C.gate g with
  | .and a b =>
      AndGate.mk (val C inp ⟨a.val, a.isLt.trans g.isLt⟩) (val C inp ⟨b.val, b.isLt.trans g.isLt⟩)
        (fam C inp ord k r t ⟨a.val, a.isLt.trans g.isLt⟩)
        (fam C inp ord k r t ⟨b.val, b.isLt.trans g.isLt⟩)
  | _ => AndGate.mk (fun _ => false) (fun _ => false) ∅ ∅

end Construction

variable {ι : Type} {N : ℕ} (C : MonotoneCircuit ι) (inp : ι → Option (Edge (2 * N)))
  (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ) (r t : ℝ)

lemma val_input {g : Fin C.size} {i : ι} (hg : C.gate g = .input i) (x : Finset (Edge (2 * N))) :
    val C inp g x = match inp i with | some e => decide (e ∈ x) | none => false := by
  unfold val
  rw [MonotoneCircuit.nodeValue]
  split <;> simp_all

lemma val_and {g : Fin C.size} {a b : Fin g.val} (hg : C.gate g = .and a b)
    (x : Finset (Edge (2 * N))) :
    val C inp g x = (val C inp ⟨a.val, a.isLt.trans g.isLt⟩ x &&
      val C inp ⟨b.val, b.isLt.trans g.isLt⟩ x) := by
  unfold val
  rw [MonotoneCircuit.nodeValue]
  split <;> simp_all

lemma val_or {g : Fin C.size} {a b : Fin g.val} (hg : C.gate g = .or a b)
    (x : Finset (Edge (2 * N))) :
    val C inp g x = (val C inp ⟨a.val, a.isLt.trans g.isLt⟩ x ||
      val C inp ⟨b.val, b.isLt.trans g.isLt⟩ x) := by
  unfold val
  rw [MonotoneCircuit.nodeValue]
  split <;> simp_all

lemma fam_input {g : Fin C.size} {i : ι} (hg : C.gate g = .input i) :
    fam C inp ord k r t g = match inp i with | some e => { {e} } | none => ∅ := by
  rw [fam]
  split <;> simp_all

lemma fam_or {g : Fin C.size} {a b : Fin g.val} (hg : C.gate g = .or a b) :
    fam C inp ord k r t g = fam C inp ord k r t ⟨a.val, a.isLt.trans g.isLt⟩ ∪
      fam C inp ord k r t ⟨b.val, b.isLt.trans g.isLt⟩ := by
  rw [fam]
  split <;> simp_all

lemma gateOf_and {g : Fin C.size} {a b : Fin g.val} (hg : C.gate g = .and a b) :
    gateOf C inp ord k r t g =
      AndGate.mk (val C inp ⟨a.val, a.isLt.trans g.isLt⟩) (val C inp ⟨b.val, b.isLt.trans g.isLt⟩)
        (fam C inp ord k r t ⟨a.val, a.isLt.trans g.isLt⟩)
        (fam C inp ord k r t ⟨b.val, b.isLt.trans g.isLt⟩) := by
  rw [gateOf]
  split <;> simp_all

lemma fam_and {g : Fin C.size} {a b : Fin g.val} (hg : C.gate g = .and a b) :
    fam C inp ord k r t g = (gateOf C inp ord k r t g).algorithm1 ord k r t := by
  rw [gateOf_and C inp ord k r t hg, fam]
  split <;> simp_all

/-! ### Invariant 1: members are matchings with at most `t` edges -/

lemma isMatching_empty {n : ℕ} : IsMatching (∅ : Finset (Edge n)) := by
  intro e he; simp at he

lemma firstOf_prop {α : Type} (o : LinearOrder α) (F : Finset α) (d : α) (P : α → Prop)
    (hF : ∀ x ∈ F, P x) (hd : P d) : P (firstOf o F d) := by
  unfold firstOf
  split_ifs with h
  · exact hF _ (@Finset.min'_mem α o F h)
  · exact hd

open scoped Classical in
lemma largestCore_isMatching (G : AndGate N) (M : Finset (Finset (Edge (2 * N)))) :
    IsMatching (G.largestCore ord k r M) := by
  unfold AndGate.largestCore
  apply firstOf_prop _ _ _ IsMatching _ isMatching_empty
  intro x hx
  simp only [Finset.mem_filter] at hx
  exact hx.1.2.1

lemma loop_good (G : AndGate N) :
    ∀ (steps : ℕ) (M : Finset (Finset (Edge (2 * N)))),
      (∀ m ∈ M, IsMatching m ∧ (m.card : ℝ) ≤ t) →
      ∀ m ∈ G.loop ord k r t steps M, IsMatching m ∧ (m.card : ℝ) ≤ t := by
  intro steps
  induction steps with
  | zero => intro M hM; simpa [AndGate.loop] using hM
  | succ s ih =>
    intro M hM
    rw [AndGate.loop]
    split_ifs with h1 h2
    · apply ih
      intro m hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact ⟨largestCore_isMatching ord k r G M, h2⟩
      · exact hM m hm
    · exact hM
    · exact hM

lemma algorithm1_good (G : AndGate N) :
    ∀ m ∈ G.algorithm1 ord k r t, IsMatching m ∧ (m.card : ℝ) ≤ t :=
  loop_good ord k r t G _ ∅ (by simp)

lemma fam_good (ht1 : 1 ≤ t) :
    ∀ g : Fin C.size, ∀ m ∈ fam C inp ord k r t g, IsMatching m ∧ (m.card : ℝ) ≤ t := by
  intro g
  induction g using WellFoundedLT.induction with
  | _ g ih =>
  rcases hg : C.gate g with i | ⟨a, b⟩ | ⟨a, b⟩
  · rw [fam_input C inp ord k r t hg]
    cases hi : inp i with
    | none => simp
    | some e =>
      intro m hm
      simp only [Finset.mem_singleton] at hm
      subst hm
      refine ⟨?_, by simpa using ht1⟩
      intro e1 h1 e2 h2 hne
      simp only [Finset.mem_singleton] at h1 h2
      exact absurd (h1.trans h2.symm) hne
  · rw [fam_and C inp ord k r t hg]
    exact algorithm1_good ord k r t _
  · rw [fam_or C inp ord k r t hg]
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact ih _ a.isLt m hm
    · exact ih _ b.isLt m hm

lemma gateOf_sizeBounded (ht1 : 1 ≤ t) (g : Fin C.size) :
    (gateOf C inp ord k r t g).SizeBounded t := by
  rcases hg : C.gate g with i | ⟨a, b⟩ | ⟨a, b⟩
  · rw [gateOf]; split <;> simp_all [AndGate.SizeBounded]
  · rw [gateOf_and C inp ord k r t hg]
    exact ⟨fun m hm => (fam_good C inp ord k r t ht1 _ m hm).2,
      fun m hm => (fam_good C inp ord k r t ht1 _ m hm).2⟩
  · rw [gateOf]; split <;> simp_all [AndGate.SizeBounded]

/-! ### Invariant 2: errors are covered by the new errors of AND nodes -/

lemma mem_errorPos {g : Finset (Edge (2 * N)) → Bool} {M : Finset (Finset (Edge (2 * N)))}
    {x : Finset (Edge (2 * N))} :
    x ∈ errorPos N k g M ↔ x ∈ crossMatchings N k ∧ g x = true ∧ ¬ Fires M x := by
  simp [errorPos]

lemma mem_errorNeg (b : ℕ) {g : Finset (Edge (2 * N)) → Bool}
    {M : Finset (Finset (Edge (2 * N)))} {x : Finset (Edge (2 * N))} :
    x ∈ errorNeg N b g M ↔ x ∈ incidentCovers N b ∧ g x = false ∧ Fires M x := by
  simp [errorNeg]

lemma pos_cover : ∀ g : Fin C.size, ∀ x ∈ crossMatchings N k,
    val C inp g x = true → ¬ Fires (fam C inp ord k r t g) x →
    ∃ h : Fin C.size, x ∈ (gateOf C inp ord k r t h).newPos k
      ((gateOf C inp ord k r t h).algorithm1 ord k r t) := by
  intro g
  induction g using WellFoundedLT.induction with
  | _ g ih =>
  intro x hx hv hf
  rcases hg : C.gate g with i | ⟨a, b⟩ | ⟨a, b⟩
  · rw [val_input C inp hg] at hv
    rw [fam_input C inp ord k r t hg] at hf
    cases hi : inp i with
    | none => simp [hi] at hv
    | some e =>
      simp only [hi, decide_eq_true_eq] at hv hf
      exact absurd ⟨{e}, Finset.mem_singleton_self _, by simpa using hv⟩ hf
  · have hG := gateOf_and C inp ord k r t hg
    have hF := fam_and C inp ord k r t hg
    by_cases hn : x ∈ (gateOf C inp ord k r t g).newPos k
        ((gateOf C inp ord k r t g).algorithm1 ord k r t)
    · exact ⟨g, hn⟩
    have h1 : x ∈ errorPos N k (gateOf C inp ord k r t g).g
        ((gateOf C inp ord k r t g).algorithm1 ord k r t) := by
      rw [mem_errorPos]
      refine ⟨hx, ?_, ?_⟩
      · rw [hG]; simpa [AndGate.g, val_and C inp hg] using hv
      · rwa [← hF]
    rw [AndGate.newPos, Finset.mem_sdiff] at hn
    have h2 := not_not.mp (fun h => hn ⟨h1, h⟩)
    rw [hG] at h2
    rcases Finset.mem_union.mp h2 with h3 | h3
    · rw [mem_errorPos] at h3
      exact ih _ a.isLt x hx h3.2.1 h3.2.2
    · rw [mem_errorPos] at h3
      exact ih _ b.isLt x hx h3.2.1 h3.2.2
  · rw [val_or C inp hg] at hv
    rw [fam_or C inp ord k r t hg] at hf
    have hfa : ¬ Fires (fam C inp ord k r t ⟨a.val, a.isLt.trans g.isLt⟩) x :=
      fun ⟨m, hm, hmx⟩ => hf ⟨m, Finset.mem_union_left _ hm, hmx⟩
    have hfb : ¬ Fires (fam C inp ord k r t ⟨b.val, b.isLt.trans g.isLt⟩) x :=
      fun ⟨m, hm, hmx⟩ => hf ⟨m, Finset.mem_union_right _ hm, hmx⟩
    rcases Bool.or_eq_true_iff.mp hv with hv | hv
    · exact ih _ a.isLt x hx hv hfa
    · exact ih _ b.isLt x hx hv hfb

lemma neg_cover (b : ℕ) : ∀ g : Fin C.size, ∀ W ∈ Finset.powersetCard b (Finset.univ : Finset (Fin (2 * N))),
    val C inp g (incident W) = false → Fires (fam C inp ord k r t g) (incident W) →
    ∃ h : Fin C.size, incident W ∈ (gateOf C inp ord k r t h).newNeg b
      ((gateOf C inp ord k r t h).algorithm1 ord k r t) := by
  intro g
  induction g using WellFoundedLT.induction with
  | _ g ih =>
  intro W hW hv hf
  have hx : incident W ∈ incidentCovers N b := Finset.mem_image_of_mem _ hW
  rcases hg : C.gate g with i | ⟨a, a'⟩ | ⟨a, a'⟩
  · rw [val_input C inp hg] at hv
    rw [fam_input C inp ord k r t hg] at hf
    cases hi : inp i with
    | none => simp [hi, Fires] at hf
    | some e =>
      simp only [hi, decide_eq_false_iff_not] at hv hf
      obtain ⟨m, hm, hmx⟩ := hf
      rw [Finset.mem_singleton] at hm
      subst hm
      exact absurd (hmx (Finset.mem_singleton_self e)) hv
  · have hG := gateOf_and C inp ord k r t hg
    have hF := fam_and C inp ord k r t hg
    by_cases hn : incident W ∈ (gateOf C inp ord k r t g).newNeg b
        ((gateOf C inp ord k r t g).algorithm1 ord k r t)
    · exact ⟨g, hn⟩
    have h1 : incident W ∈ errorNeg N b (gateOf C inp ord k r t g).g
        ((gateOf C inp ord k r t g).algorithm1 ord k r t) := by
      rw [mem_errorNeg]
      refine ⟨hx, ?_, ?_⟩
      · rw [hG]; simpa [AndGate.g, val_and C inp hg] using hv
      · rwa [← hF]
    rw [AndGate.newNeg, Finset.mem_sdiff] at hn
    have h2 := not_not.mp (fun h => hn ⟨h1, h⟩)
    rw [hG] at h2
    rcases Finset.mem_union.mp h2 with h3 | h3
    · rw [mem_errorNeg] at h3
      exact ih _ a.isLt W hW h3.2.1 h3.2.2
    · rw [mem_errorNeg] at h3
      exact ih _ a'.isLt W hW h3.2.1 h3.2.2
  · rw [val_or C inp hg] at hv
    rw [fam_or C inp ord k r t hg] at hf
    simp only [Bool.or_eq_false_iff] at hv
    obtain ⟨m, hm, hmx⟩ := hf
    rcases Finset.mem_union.mp hm with hm | hm
    · exact ih _ a.isLt W hW hv.1 ⟨m, hm, hmx⟩
    · exact ih _ a'.isLt W hW hv.2 ⟨m, hm, hmx⟩

/-! ### Union bound and the main theorem -/

open scoped Classical in
lemma prob_union {β : Type} (F : Finset β) (A : β → Prop) {s : ℕ} (B : Fin s → β → Prop) (c : ℝ)
    (hsub : ∀ x ∈ F, A x → ∃ h, B h x) (hB : ∀ h, uniformProb F (B h) ≤ c) :
    uniformProb F A ≤ (s : ℝ) * c := by
  unfold uniformProb at hB ⊢
  have hsub' : F.filter A ⊆ Finset.univ.biUnion (fun h => F.filter (B h)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨h, hh⟩ := hsub x hx.1 hx.2
    exact Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx.1, hh⟩⟩
  have hcard : ((F.filter A).card : ℝ) ≤ ∑ h, ((F.filter (B h)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub').trans Finset.card_biUnion_le
  calc ((F.filter A).card : ℝ) / F.card
      ≤ (∑ h, ((F.filter (B h)).card : ℝ)) / F.card :=
        div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
    _ = ∑ h, ((F.filter (B h)).card : ℝ) / F.card := Finset.sum_div _ _ _
    _ ≤ ∑ _h : Fin s, c := Finset.sum_le_sum (fun h _ => hB h)
    _ = (s : ℝ) * c := by simp

theorem approx_circuit {ι : Type} (N k b : ℕ) (t ε r : ℝ) (ht1 : 1 ≤ t)
    (C : MonotoneCircuit ι) (inp : ι → Option (Edge (2 * N)))
    (ord : LinearOrder (Finset (Edge (2 * N))))
    (h11 : ∀ G : AndGate N, G.SizeBounded t →
      uniformProb (crossMatchings N k) (fun x => x ∈ G.newPos k (G.algorithm1 ord k r t)) ≤ (2 : ℝ) ^ (-t))
    (h12 : ∀ G : AndGate N, G.SizeBounded t →
      uniformProb (Finset.powersetCard b (Finset.univ : Finset (Fin (2 * N))))
        (fun W => incident W ∈ G.newNeg b (G.algorithm1 ord k r t)) ≤ (4 : ℝ) ^ t * ε) :
    ∃ M : Finset (Finset (Edge (2 * N))),
      (∀ m ∈ M, IsMatching m ∧ (m.card : ℝ) ≤ t) ∧
      uniformProb (crossMatchings N k) (fun x => ev C inp x = true ∧ ¬ Fires M x)
        ≤ (C.size : ℝ) * (2 : ℝ) ^ (-t) ∧
      uniformProb (Finset.powersetCard b (Finset.univ : Finset (Fin (2 * N))))
        (fun W => ev C inp (incident W) = false ∧ Fires M (incident W))
        ≤ (C.size : ℝ) * ((4 : ℝ) ^ t * ε) := by
  refine ⟨fam C inp ord k r t C.output, fam_good C inp ord k r t ht1 _, ?_, ?_⟩
  · apply prob_union _ _
      (fun h x => x ∈ (gateOf C inp ord k r t h).newPos k
        ((gateOf C inp ord k r t h).algorithm1 ord k r t))
    · intro x hx hA
      exact pos_cover C inp ord k r t C.output x hx hA.1 hA.2
    · intro h
      exact h11 _ (gateOf_sizeBounded C inp ord k r t ht1 h)
  · apply prob_union _ _
      (fun h W => incident W ∈ (gateOf C inp ord k r t h).newNeg b
        ((gateOf C inp ord k r t h).algorithm1 ord k r t))
    · intro W hW hA
      exact neg_cover C inp ord k r t b C.output W hW hA.1 hA.2
    · intro h
      exact h12 _ (gateOf_sizeBounded C inp ord k r t ht1 h)

end SpreadMatchCircuit.Matching.Dev.Gates
end

section
/-! Theorem 1, part A: embedding the cross graphs of `halfSide k` on `Fin (2k)` into the cross
graphs of `(L, Lᶜ)` on `Fin n`. -/

namespace SpreadMatchCircuit.Matching.Dev.T1

open Finset SpreadMatchCircuit.Matching

lemma mem_endpoints' {n : ℕ} {e : Edge n} {v : Fin n} : v ∈ endpoints e ↔ v ∈ e.1 := by
  simp [endpoints, Sym2.mem_toFinset]

lemma exists_embed {n k : ℕ} (L : Finset (Fin n)) (hL : k ≤ L.card) (hLc : k ≤ Lᶜ.card) :
    ∃ φ : Fin (2 * k) → Fin n, Function.Injective φ ∧
      (∀ i : Fin (2 * k), (i : ℕ) < k → φ i ∈ L) ∧ (∀ i : Fin (2 * k), k ≤ (i : ℕ) → φ i ∉ L) := by
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hL
  obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq hLc
  have hfA : ∀ j : Fin k, A.orderEmbOfFin hAc j ∈ L := fun j => hA (orderEmbOfFin_mem A hAc j)
  have hgB : ∀ j : Fin k, B.orderEmbOfFin hBc j ∉ L := fun j => by
    have := hB (orderEmbOfFin_mem B hBc j)
    simpa using this
  refine ⟨fun i => if h : (i : ℕ) < k then A.orderEmbOfFin hAc ⟨i, h⟩
      else B.orderEmbOfFin hBc ⟨i - k, by have := i.isLt; omega⟩, ?_, ?_, ?_⟩
  · intro i j hij
    simp only at hij
    by_cases hi : (i : ℕ) < k <;> by_cases hj : (j : ℕ) < k <;>
      simp only [hi, hj, dite_true, dite_false] at hij
    · have := (A.orderEmbOfFin hAc).injective hij
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · exact absurd (hij ▸ hfA _) (hgB _)
    · exact absurd (hij ▸ hgB _) (fun h => h (hfA _))
    · have := (B.orderEmbOfFin hBc).injective hij
      have h2 := congrArg Fin.val this
      simp only at h2
      exact Fin.ext (by omega)
  · intro i hi
    simp only [hi, dite_true]
    exact hfA _
  · intro i hi
    have : ¬ (i : ℕ) < k := by omega
    simp only [this, dite_false]
    exact hgB _

section Emb

variable {n k : ℕ} (φ : Fin (2 * k) → Fin n) (hφ : Function.Injective φ)

/-- The edge map induced by an injective vertex map. -/
def emb (e : Edge (2 * k)) : Edge n :=
  ⟨e.1.map φ, by rw [Sym2.isDiag_map hφ]; exact e.2⟩

lemma emb_injective : Function.Injective (emb φ hφ) := by
  intro a b h
  apply Subtype.ext
  have : a.1.map φ = b.1.map φ := congrArg Subtype.val h
  exact Sym2.map.injective hφ this

lemma endpoints_emb (e : Edge (2 * k)) : endpoints (emb φ hφ e) = (endpoints e).image φ := by
  ext v
  simp only [mem_endpoints', emb, Sym2.mem_map, Finset.mem_image]

open scoped Classical in
/-- The input map: the variable `e` of `C` reads the cross edge of `Fin (2k)` mapping to `e`. -/
noncomputable def inp (e : Edge n) : Option (Edge (2 * k)) :=
  if h : ∃ e', IsCrossEdge (halfSide k) e' ∧ emb φ hφ e' = e then some (Classical.choose h)
  else none

open scoped Classical in
/-- The image in `Fin n` of the cross part of a graph on `Fin (2k)`. -/
noncomputable def img (x : Finset (Edge (2 * k))) : Finset (Edge n) :=
  (x.filter (IsCrossEdge (halfSide k))).map ⟨emb φ hφ, emb_injective φ hφ⟩

lemma ev_eq {C : MonotoneCircuit (Edge n)} (x : Finset (Edge (2 * k))) :
    Gates.ev C (inp φ hφ) x = C.eval (graphInput (img φ hφ x)) := by
  classical
  unfold Gates.ev
  congr 1
  funext e
  unfold graphInput
  by_cases h : ∃ e', IsCrossEdge (halfSide k) e' ∧ emb φ hφ e' = e
  · have hs := Classical.choose_spec h
    have hi : inp φ hφ e = some (Classical.choose h) := by
      unfold inp; rw [dif_pos h]
    rw [hi]
    simp only
    rw [decide_eq_decide]
    constructor
    · intro hx
      simp only [img, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk]
      exact ⟨_, ⟨hx, hs.1⟩, hs.2⟩
    · intro hx
      simp only [img, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk] at hx
      obtain ⟨a, ⟨ha, _⟩, hae⟩ := hx
      have : a = Classical.choose h := emb_injective φ hφ (hae.trans hs.2.symm)
      exact this ▸ ha
  · have hi : inp φ hφ e = none := by
      unfold inp; rw [dif_neg h]
    rw [hi]
    simp only
    symm
    rw [decide_eq_false_iff_not]
    intro hx
    simp only [img, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk] at hx
    obtain ⟨a, ⟨_, ha⟩, hae⟩ := hx
    exact h ⟨a, ha, hae⟩

variable {L : Finset (Fin n)}

lemma isCrossGraph_img (hL1 : ∀ i : Fin (2 * k), (i : ℕ) < k → φ i ∈ L)
    (hL2 : ∀ i : Fin (2 * k), k ≤ (i : ℕ) → φ i ∉ L) (x : Finset (Edge (2 * k))) :
    IsCrossGraph L (img φ hφ x) := by
  classical
  intro f hf
  simp only [img, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk] at hf
  obtain ⟨a, ⟨_, u, hu, v, hv, hav⟩, rfl⟩ := hf
  refine ⟨φ u, hL1 u ?_, φ v, hL2 v ?_, ?_⟩
  · simpa [halfSide] using hu
  · have : ¬ (v : ℕ) < k := by simpa [halfSide] using hv
    omega
  · simp only [emb, hav, Sym2.map_mk]

lemma matching_card_le_of_incident {m : Finset (Edge n)} (hm : IsMatching m) (W : Finset (Fin n))
    (hsub : ∀ f ∈ m, ¬ Disjoint (endpoints f) W) : m.card ≤ W.card := by
  classical
  have h1 : m ⊆ W.biUnion (fun v => m.filter (fun f => v ∈ endpoints f)) := by
    intro f hf
    obtain ⟨v, hv1, hv2⟩ := Finset.not_disjoint_iff.mp (hsub f hf)
    exact Finset.mem_biUnion.mpr ⟨v, hv2, Finset.mem_filter.mpr ⟨hf, hv1⟩⟩
  calc m.card ≤ _ := card_le_card h1
    _ ≤ ∑ v ∈ W, (m.filter (fun f => v ∈ endpoints f)).card := card_biUnion_le
    _ ≤ ∑ v ∈ W, 1 := by
        apply sum_le_sum
        intro v _
        apply Finset.card_le_one.mpr
        intro a ha b hb
        rw [Finset.mem_filter] at ha hb
        by_contra hne
        exact Finset.disjoint_left.mp (hm a ha.1 b hb.1 hne) ha.2 hb.2
    _ = W.card := by simp

end Emb

/-- The reduction of Theorem 1 to graphs on `Fin (2k)`. -/
theorem reduce {n k q : ℕ} (hq : 1 ≤ q) (L : Finset (Fin n)) (hL : k ≤ L.card)
    (hLc : k ≤ Lᶜ.card) (C : MonotoneCircuit (Edge n)) (hC : DistinguishesMatchings C L k q) :
    ∃ inp : Edge n → Option (Edge (2 * k)),
      (∀ x ∈ crossMatchings k k, Gates.ev C inp x = true) ∧
      (∀ W : Finset (Fin (2 * k)), W.card = q - 1 → Gates.ev C inp (incident W) = false) := by
  classical
  obtain ⟨φ, hφ, hL1, hL2⟩ := exists_embed L hL hLc
  refine ⟨inp φ hφ, ?_, ?_⟩
  · intro x hx
    simp only [crossMatchings, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxm, hxc, hxcr⟩ := hx
    rw [ev_eq]
    apply (hC _ (isCrossGraph_img φ hφ hL1 hL2 x)).1
    refine ⟨img φ hφ x, subset_refl _, ?_, ?_⟩
    · intro f hf f' hf' hne
      simp only [img, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk] at hf hf'
      obtain ⟨a, ⟨ha, _⟩, rfl⟩ := hf
      obtain ⟨b, ⟨hb, _⟩, rfl⟩ := hf'
      have hab : a ≠ b := fun h => hne (h ▸ rfl)
      rw [endpoints_emb, endpoints_emb]
      exact (Finset.disjoint_image hφ).mpr (hxm a ha b hb hab)
    · have : x.filter (IsCrossEdge (halfSide k)) = x := Finset.filter_true_of_mem hxcr
      simp only [img, card_map]
      rw [this, hxc]
  · intro W hW
    rw [ev_eq]
    apply (hC _ (isCrossGraph_img φ hφ hL1 hL2 _)).2
    rintro ⟨m, hmsub, hm, hmc⟩
    have := matching_card_le_of_incident hm (W.image φ) (by
      intro f hf
      have hf' := hmsub hf
      simp only [img, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk] at hf'
      obtain ⟨a, ⟨ha, _⟩, rfl⟩ := hf'
      simp only [incident, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨v, hv1, hv2⟩ := Finset.not_disjoint_iff.mp ha
      rw [endpoints_emb]
      exact Finset.not_disjoint_iff.mpr
        ⟨φ v, Finset.mem_image_of_mem _ hv1, Finset.mem_image_of_mem _ hv2⟩)
    have h2 := Finset.card_image_le (s := W) (f := φ)
    omega

end SpreadMatchCircuit.Matching.Dev.T1
end

section
/-! Theorem 1, part B: the spread law on the cross matchings caught by the approximator. -/

namespace SpreadMatchCircuit.Matching.Dev.T1

open Finset SpreadMatchCircuit.Matching

lemma uP_mono {β : Type} (F : Finset β) (A B : β → Prop) (h : ∀ x ∈ F, A x → B x) :
    uniformProb F A ≤ uniformProb F B := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_le_card (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, h _ hx.1 hx.2⟩)

lemma lawProb_map_uniform {α β : Type} [Fintype β] (S : Finset α) (hS : S.Nonempty) (Z : α → β)
    (A : β → Prop) [DecidablePred (fun x => A (Z x))] :
    lawProb (PMF.map Z (PMF.uniformOfFinset S hS)) A =
      ((S.filter (fun x => A (Z x))).card : ℝ) / S.card := by
  classical
  unfold lawProb
  rw [← ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _), ← PMF.toOuterMeasure_apply_finset,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  congr 3
  ext x
  simp

lemma cross_nonempty (N k : ℕ) (hk : k ≤ N) : (crossMatchings N k).Nonempty := by
  classical
  let e : Fin k → Edge (2 * N) := fun i =>
    ⟨s(⟨i, by omega⟩, ⟨i + N, by omega⟩), by
      rw [Sym2.mk_isDiag_iff]; intro h; have h' := congrArg Fin.val h; simp at h'; have := i.isLt; omega⟩
  have hend : ∀ i : Fin k, ∀ v : Fin (2 * N), v ∈ endpoints (e i) ↔
      (v : ℕ) = i ∨ (v : ℕ) = i + N := by
    intro i v
    simp only [Dev.Cnt.mem_endpoints, e, Sym2.mem_iff, Fin.ext_iff]
  have hinj : Function.Injective e := by
    intro i j h
    have h1 : (⟨i, by omega⟩ : Fin (2 * N)) ∈ endpoints (e j) := by
      rw [← h, hend]; left; rfl
    rw [hend] at h1
    apply Fin.ext
    simp only at h1
    omega
  refine ⟨univ.map ⟨e, hinj⟩, ?_⟩
  simp only [crossMatchings, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_⟩
  · intro f hf f' hf' hne
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hf hf'
    obtain ⟨i, rfl⟩ := hf
    obtain ⟨j, rfl⟩ := hf'
    have hij : (i : ℕ) ≠ j := fun h => hne (by rw [Fin.ext h])
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [hend] at hv hv'
    have := i.isLt
    have := j.isLt
    omega
  · simp
  · intro f hf
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hf
    obtain ⟨i, rfl⟩ := hf
    refine ⟨⟨i, by omega⟩, ?_, ⟨i + N, by omega⟩, ?_, rfl⟩
    · have := i.isLt; simp [halfSide]; omega
    · simp [halfSide]

open scoped Classical in
theorem exists_law (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (t r' : ℝ) (htk : t ≤ (k : ℝ) / 100)
    (hr0 : 0 < r') (hr : r' ≤ (N : ℝ) ^ 2 / (4 * k)) (M : Finset (Finset (Edge (2 * N))))
    (hM : ∀ m ∈ M, IsMatching m ∧ (m.card : ℝ) ≤ t)
    (hS : (crossMatchings N k).card ≤ 2 * ((crossMatchings N k).filter (Fires M)).card) :
    ∃ μ : PMF (Finset (Edge (2 * N))), lawSupport μ ⊆ M ∧ IsBoundedMatchingLaw μ t ∧
      IsSpread μ r' := by
  set c := crossMatchings N k with hcdef
  set S := c.filter (Fires M) with hSdef
  have hcpos : 0 < c.card := card_pos.mpr (cross_nonempty N k hkN)
  have hSne : S.Nonempty := card_pos.mp (by omega)
  let Z : Finset (Edge (2 * N)) → Finset (Edge (2 * N)) := fun x =>
    if h : Fires M x then Classical.choose h else ∅
  have hZ : ∀ x ∈ S, Z x ∈ M ∧ Z x ⊆ x := by
    intro x hx
    have hf := (mem_filter.mp hx).2
    simp only [Z, dif_pos hf]
    exact Classical.choose_spec hf
  set μ := PMF.map Z (PMF.uniformOfFinset S hSne) with hμ
  have hsupp : lawSupport μ ⊆ M := by
    intro z hz
    simp only [lawSupport, Finset.mem_filter, Finset.mem_univ, true_and, μ, PMF.support_map,
      PMF.support_uniformOfFinset, Set.mem_image, Finset.mem_coe] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (hZ x hx).1
  refine ⟨μ, hsupp, fun z hz => hM z (hsupp hz), ?_⟩
  intro m hm
  rw [hμ, lawProb_map_uniform]
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast card_pos.mpr hSne
  have hle1 : ((S.filter (fun x => m ⊆ Z x)).card : ℝ) / S.card ≤ 1 := by
    rw [div_le_one hSpos]; exact_mod_cast card_filter_le _ _
  rcases Nat.eq_zero_or_pos m.card with h0 | hpos
  · rw [h0]; simpa using hle1
  by_cases hmt : (m.card : ℝ) ≤ t
  · -- the main case
    have hj : 50 * m.card ≤ k := by
      have : (50 * m.card : ℝ) ≤ k := by nlinarith
      exact_mod_cast this
    have hcs := Dev.Cnt.cross_spread N k hk hkN m hm hj
    unfold uniformProb at hcs
    rw [← hcdef] at hcs
    have hcs' : ((c.filter (fun x => m ⊆ x)).card : ℝ) / c.card ≤ (2 * (k : ℝ) / (N : ℝ) ^ 2) ^ m.card := by
      convert hcs using 4
      ext x; simp only [Finset.mem_filter]
    have hsub : ((S.filter (fun x => m ⊆ Z x)).card : ℝ) ≤ (c.filter (fun x => m ⊆ x)).card := by
      exact_mod_cast card_le_card (fun x hx => by
        simp only [S, Finset.mem_filter] at hx ⊢
        exact ⟨hx.1.1, hx.2.trans (hZ x (mem_filter.mpr hx.1)).2⟩)
    have hS' : (c.card : ℝ) ≤ 2 * S.card := by exact_mod_cast hS
    have hcpos' : (0 : ℝ) < c.card := by exact_mod_cast hcpos
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    set X := 2 * (k : ℝ) / (N : ℝ) ^ 2 with hX
    have hX0 : 0 ≤ X := by positivity
    have h2X : 2 * X ≤ 1 / r' := by
      rw [hX, le_div_iff₀ hr0]
      rw [le_div_iff₀ (by positivity)] at hr
      have : 2 * (2 * (k : ℝ) / (N : ℝ) ^ 2) * r' = (4 * k * r') / N ^ 2 := by ring
      rw [this, div_le_one (by positivity)]
      linarith
    calc ((S.filter (fun x => m ⊆ Z x)).card : ℝ) / S.card
        ≤ 2 * (((c.filter (fun x => m ⊆ x)).card : ℝ) / c.card) := by
          rw [div_le_iff₀ hSpos]
          calc ((S.filter (fun x => m ⊆ Z x)).card : ℝ)
              ≤ (c.filter (fun x => m ⊆ x)).card := hsub
            _ = 2 * (((c.filter (fun x => m ⊆ x)).card : ℝ) / c.card) * (c.card / 2) := by
                field_simp
            _ ≤ 2 * (((c.filter (fun x => m ⊆ x)).card : ℝ) / c.card) * S.card := by
                apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 2 * X ^ m.card := by linarith
      _ ≤ 2 ^ m.card * X ^ m.card := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m.card := pow_le_pow_right₀ (by norm_num) hpos
      _ = (2 * X) ^ m.card := by rw [mul_pow]
      _ ≤ (1 / r') ^ m.card := pow_le_pow_left₀ (by positivity) h2X _
      _ = (r' ^ m.card)⁻¹ := by rw [one_div, inv_pow]
  · have hempty : S.filter (fun x => m ⊆ Z x) = ∅ := by
      apply filter_false_of_mem
      intro x hx hmx
      have h1 := (hM _ (hZ x hx).1).2
      have h2 : (m.card : ℝ) ≤ (Z x).card := by exact_mod_cast card_le_card hmx
      exact hmt (h2.trans h1)
    rw [hempty, card_empty, Nat.cast_zero, zero_div]
    positivity

end SpreadMatchCircuit.Matching.Dev.T1
end

section
/-! Theorem 1 from Lemmas 5, 11 and 12. -/

namespace SpreadMatchCircuit.Matching

open Finset

namespace Dev.T1

lemma arith_eta (α5 α12 η : ℝ) (hα5 : 0 < α5) (hα12 : 0 < α12)
    (hηdef : η = 1 / (1728 * α12 + 128 * α5 + 200)) :
    0 < η ∧ 128 * α5 * η ≤ 1 ∧ 1728 * α12 * η ≤ 1 ∧ η ≤ 1 / 200 := by
  have hDpos : 0 < 1728 * α12 + 128 * α5 + 200 := by positivity
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hηD : η * (1728 * α12 + 128 * α5 + 200) = 1 := by rw [hηdef]; field_simp
  refine ⟨hη0, ?_, ?_, ?_⟩ <;> nlinarith

lemma exp_neg_one_lt : Real.exp (-1) < 1 / 2 := by
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
  have := Real.exp_one_gt_d9
  norm_num at this ⊢; linarith

lemma arith_v (η v s : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 200) (hs1 : 1 ≤ s)
    (hv : 2 / η ^ 2 ≤ v) :
    2 ≤ η ^ 2 * v ∧ 400 ≤ v ∧ 2 ≤ η * v ∧ η ^ 2 * v ≤ v * s / 200 := by
  have hη2 : η ^ 2 ≤ η / 200 := by nlinarith
  have h400 : 400 ≤ 2 / η ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hv1 : 400 ≤ v := by linarith
  have h2 : 2 ≤ η ^ 2 * v := by
    have : η ^ 2 * (2 / η ^ 2) = 2 := by field_simp
    nlinarith [sq_nonneg η]
  refine ⟨h2, hv1, ?_, ?_⟩
  · have : η ^ 2 * v ≤ η * v := by nlinarith
    linarith
  · have : η ^ 2 * v ≤ η / 200 * v := by nlinarith
    have : η / 200 * v ≤ v / 200 := by nlinarith
    nlinarith

lemma arith_cond12 (α12 η v s B : ℝ) (hα12 : 0 < α12) (hη0 : 0 < η)
    (hη12 : 1728 * α12 * η ≤ 1) (hη : η ≤ 1 / 200) (hs0 : 0 < s) (hv1 : 1 ≤ v)
    (hB : 0 < B) (hvB : v * s ≤ 2 * B) :
    α12 * (2 * (η ^ 2 * v) + (η * v) ^ 2) * (3 * (2 * (s * s)) / B) ^ 2 ≤ s * s / 4 := by
  have h1 : 2 * (η ^ 2 * v) + (η * v) ^ 2 ≤ 3 * η ^ 2 * v ^ 2 := by
    nlinarith [sq_nonneg η]
  have hv0 : 0 < v := by linarith
  have h2 : (3 * (2 * (s * s)) / B) ^ 2 ≤ (12 * s / v) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff₀ hB hv0]
    nlinarith
  calc α12 * (2 * (η ^ 2 * v) + (η * v) ^ 2) * (3 * (2 * (s * s)) / B) ^ 2
      ≤ α12 * (3 * η ^ 2 * v ^ 2) * (12 * s / v) ^ 2 := by gcongr
    _ = 432 * α12 * η ^ 2 * (s * s) := by field_simp; ring
    _ ≤ (s * s) / 4 := by
        have : 1728 * α12 * η ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_pos hs0 hs0]

lemma arith_r5 (α5 η v s B : ℝ) (hα5 : 0 < α5) (hη0 : 0 < η)
    (hη5 : 128 * α5 * η ≤ 1) (hη : η ≤ 1 / 200) (hs0 : 0 < s) (hv1 : 1 ≤ v)
    (hB : 0 < B) (hvB : v * s ≤ 2 * B) :
    α5 * (η ^ 2 * v + (η * v) ^ 2) / (B / (2 * (s * s))) ^ 2 ≤ s * s / 4 := by
  have hv0 : 0 < v := by linarith
  have h1 : η ^ 2 * v + (η * v) ^ 2 ≤ 2 * η ^ 2 * v ^ 2 := by nlinarith [sq_nonneg η]
  have h2 : 1 / (B / (2 * (s * s))) ^ 2 ≤ (4 * s / v) ^ 2 := by
    rw [one_div, ← inv_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [inv_div, div_le_div_iff₀ hB hv0]
    nlinarith
  calc α5 * (η ^ 2 * v + (η * v) ^ 2) / (B / (2 * (s * s))) ^ 2
      = α5 * (η ^ 2 * v + (η * v) ^ 2) * (1 / (B / (2 * (s * s))) ^ 2) := by ring
    _ ≤ α5 * (2 * η ^ 2 * v ^ 2) * (4 * s / v) ^ 2 := by gcongr
    _ = 32 * α5 * η ^ 2 * (s * s) := by field_simp; ring
    _ ≤ s * s / 4 := by
        have : 128 * α5 * η ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_pos hs0 hs0]

lemma arith_err1 (S t : ℝ) (hS : S < Real.exp (-1) * Real.exp (t / 2)) (ht : 0 ≤ t) :
    S * (2 : ℝ) ^ (-t) ≤ 1 / 2 := by
  have hl2 := Real.log_two_gt_d9
  rw [Real.rpow_def_of_pos (by norm_num)]
  calc S * Real.exp (Real.log 2 * -t)
      ≤ Real.exp (-1) * Real.exp (t / 2) * Real.exp (Real.log 2 * -t) := by
        gcongr
    _ = Real.exp (-1 + (t / 2 - Real.log 2 * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr; norm_num at hl2; nlinarith
    _ ≤ 1 / 2 := exp_neg_one_lt.le

lemma arith_err0 (S η u : ℝ) (hS : S < Real.exp (-1) * Real.exp (η * u / 2)) (hη0 : 0 < η)
    (hη : η ≤ 1 / 200) (hu : 0 ≤ u) :
    S * ((4 : ℝ) ^ (η * u) * Real.exp (-u)) ≤ 1 / 2 := by
  have hl2' := Real.log_two_lt_d9
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  calc S * (Real.exp (Real.log 4 * (η * u)) * Real.exp (-u))
      ≤ Real.exp (-1) * Real.exp (η * u / 2) * (Real.exp (Real.log 4 * (η * u)) * Real.exp (-u)) := by
        gcongr
    _ = Real.exp (-1 + (η * u / 2 + Real.log 4 * (η * u) - u)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr
        rw [hl4]
        norm_num at hl2'
        have : 0 ≤ η * u := by positivity
        nlinarith
    _ ≤ 1 / 2 := exp_neg_one_lt.le

end Dev.T1

open Dev.T1 in
/-- The main regime of Theorem 1, `q ≥ (2/η²)√k`, for given constants of Lemmas 5 and 12. -/
theorem Dev.T1.main_regime (α5 α12 : ℝ) (hα5 : 0 < α5) (hα12 : 0 < α12)
    (h5 : ∀ (n : ℕ) (μ : PMF (Finset (Edge n))) (ε t γ r : ℝ) (w : ℕ),
        0 < ε → ε < 1 / 2 → 1 < t → 0 < γ → γ ≤ 1 → (w : ℝ) = γ * (n : ℝ) →
        r = α5 * (t + Real.log (1 / ε) ^ 2) / γ ^ 2 →
        IsBoundedMatchingLaw μ t → IsSpread μ r →
        1 - ε < uniformProb (Finset.powersetCard w (Finset.univ : Finset (Fin n)))
          (fun W => ∃ z ∈ lawSupport μ, z ⊆ incident W))
    (h12 : ∀ (N k b : ℕ) (t ε r : ℝ), 1 ≤ k → k ≤ N → b < k →
        t ≤ (b : ℝ) / 100 → 0 < ε →
        α12 * (2 * t + Real.log (1 / ε) ^ 2) * (3 * (2 * (N : ℝ)) / (b : ℝ)) ^ 2 ≤ r →
        ∀ (ord : LinearOrder (Finset (Edge (2 * N)))) (G : AndGate N), G.SizeBounded t →
          uniformProb (Finset.powersetCard b (Finset.univ : Finset (Fin (2 * N))))
            (fun W => incident W ∈ G.newNeg b (G.algorithm1 ord k r t))
            ≤ (4 : ℝ) ^ t * ε)
    (η : ℝ) (hη0 : 0 < η) (hη5 : 128 * α5 * η ≤ 1) (hη12 : 1728 * α12 * η ≤ 1)
    (hη : η ≤ 1 / 200)
    (n k q : ℕ) (hqk : q < k) (L : Finset (Fin n)) (hL : k ≤ L.card) (hLc : k ≤ Lᶜ.card)
    (C : MonotoneCircuit (Edge n)) (hC : DistinguishesMatchings C L k q)
    (s : ℝ) (hs1 : 1 ≤ s) (hss : s * s = (k : ℝ)) (hq : 2 / η ^ 2 * s ≤ (q : ℝ)) :
    Real.exp (-1) * Real.exp (η ^ 2 / 2 * (q : ℝ) / s) ≤ (C.size : ℝ) := by
  have hk1 : 1 ≤ k := by omega
  have hs0 : 0 < s := by linarith
  by_contra hlt
  push Not at hlt
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = (q : ℝ) / s := ⟨_, rfl⟩
  have hQ : (q : ℝ) = v * s := by rw [hvdef]; field_simp
  have hv : 2 / η ^ 2 ≤ v := by rw [hvdef, le_div_iff₀ hs0]; exact hq
  obtain ⟨ht2, hv400, hηv, htq⟩ := arith_v η v s hη0 hη hs1 hv
  have hq2 : 2 ≤ q := by
    have : (2 : ℝ) ≤ q := by rw [hQ]; nlinarith
    exact_mod_cast this
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hQK : (q : ℝ) < k := by exact_mod_cast hqk
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = η ^ 2 * v := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = η * v := ⟨_, rfl⟩
  have htu : t = η * u := by rw [htdef, hudef]; ring
  have hexp : η ^ 2 / 2 * (q : ℝ) / s = η * u / 2 := by rw [hQ, hudef]; field_simp
  rw [hexp] at hlt
  rw [← htdef] at ht2 htq
  have ht1 : 1 ≤ t := by linarith
  have htk : t ≤ (k : ℝ) / 100 := by rw [← hQ] at htq; linarith
  have hb : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hbk : q - 1 < k := by omega
  have htb : t ≤ ((q - 1 : ℕ) : ℝ) / 100 := by rw [hb, ← hQ] at *; linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = Real.exp (-u) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; exact Real.exp_pos _
  have hεhalf : ε < 1 / 2 := by
    rw [hεdef]
    calc Real.exp (-u) ≤ Real.exp (-1) := by
          apply Real.exp_le_exp.mpr; rw [hudef]; linarith
      _ < 1 / 2 := exp_neg_one_lt
  have hlog : Real.log (1 / ε) = u := by
    rw [hεdef, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hK : (k : ℝ) = s * s := hss.symm
  have hbpos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by rw [hb]; linarith
  have hvB : v * s ≤ 2 * ((q - 1 : ℕ) : ℝ) := by rw [hb, ← hQ]; linarith
  have hcond : α12 * (2 * t + Real.log (1 / ε) ^ 2) * (3 * (2 * (k : ℝ)) / ((q - 1 : ℕ) : ℝ)) ^ 2
      ≤ (k : ℝ) / 4 := by
    rw [hlog, htdef, hudef, hK]
    exact arith_cond12 α12 η v s _ hα12 hη0 hη12 hη hs0 (by linarith) hbpos hvB
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hr0 : (0 : ℝ) < (k : ℝ) / 4 := by positivity
  have hr11 : (k : ℝ) / 4 ≤ (2 * (k : ℝ)) ^ 2 / (16 * (k : ℝ)) := by
    apply le_of_eq; field_simp; ring
  obtain ⟨inp, hpos, hneg⟩ := reduce (by omega : 1 ≤ q) L hL hLc C hC
  let ord : LinearOrder (Finset (Edge (2 * k))) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  obtain ⟨M, hM, hE1, hE0⟩ := Gates.approx_circuit k k (q - 1) t ε ((k : ℝ) / 4) ht1 C inp ord
    (fun G hG => lemma_11 k k hk1 le_rfl t _ htk hr0 hr11 ord G hG)
    (fun G hG => h12 k k (q - 1) t ε _ hk1 le_rfl hbk htb hε0 hcond ord G hG)
  have hB1 : (C.size : ℝ) * (2 : ℝ) ^ (-t) ≤ 1 / 2 := by
    rw [htu]; exact arith_err1 _ _ hlt (by have : 0 ≤ u := by rw [hudef]; positivity
                                           positivity)
  have hB0 : (C.size : ℝ) * ((4 : ℝ) ^ t * ε) ≤ 1 / 2 := by
    rw [htu, hεdef]
    exact arith_err0 _ η u hlt hη0 hη (by rw [hudef]; positivity)
  have hE1' : uniformProb (crossMatchings k k) (fun x => ¬ Fires M x) ≤ 1 / 2 :=
    (uP_mono _ _ _ (fun x hx h => ⟨hpos x hx, h⟩)).trans (hE1.trans hB1)
  have hcard : (crossMatchings k k).card ≤
      2 * (@Finset.filter _ (Fires M) (fun _ => Classical.propDecidable _)
        (crossMatchings k k)).card := by
    have hc : 0 < (crossMatchings k k).card := card_pos.mpr (cross_nonempty k k le_rfl)
    have hsplit := @card_filter_add_card_filter_not _ (crossMatchings k k) (Fires M)
      (fun _ => Classical.propDecidable _) (fun _ => Classical.propDecidable _)
    unfold uniformProb at hE1'
    rw [div_le_iff₀ (by exact_mod_cast hc)] at hE1'
    have : (2 : ℝ) * (@Finset.filter _ (fun x => ¬ Fires M x) (fun _ => Classical.propDecidable _)
        (crossMatchings k k)).card ≤ (crossMatchings k k).card := by
      linarith
    have h' : 2 * (@Finset.filter _ (fun x => ¬ Fires M x) (fun _ => Classical.propDecidable _)
        (crossMatchings k k)).card ≤ (crossMatchings k k).card := by exact_mod_cast this
    omega
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = ((q - 1 : ℕ) : ℝ) / (2 * (k : ℝ)) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγdef]; positivity
  have hγ1 : γ ≤ 1 := by
    rw [hγdef, div_le_one (by positivity)]
    have : ((q - 1 : ℕ) : ℝ) < k := by exact_mod_cast hbk
    linarith
  have hw : ((q - 1 : ℕ) : ℝ) = γ * ((2 * k : ℕ) : ℝ) := by
    rw [hγdef]; push_cast; field_simp
  obtain ⟨r5, hr5def⟩ : ∃ r5 : ℝ, r5 = α5 * (t + Real.log (1 / ε) ^ 2) / γ ^ 2 := ⟨_, rfl⟩
  have hr5pos : 0 < r5 := by
    rw [hr5def]; have : 0 < t := by linarith
    positivity
  have hr5le : r5 ≤ (k : ℝ) ^ 2 / (4 * k) := by
    have hkk : (k : ℝ) ^ 2 / (4 * k) = s * s / 4 := by rw [hK]; field_simp
    rw [hkk, hr5def, hlog, htdef, hudef, hγdef, hK]
    exact arith_r5 α5 η v s _ hα5 hη0 hη5 hη hs0 (by linarith) hbpos hvB
  obtain ⟨μ, hsupp, hbd, hspr⟩ := exists_law k k hk1 le_rfl t r5 htk hr5pos hr5le M hM hcard
  have h5app := h5 (2 * k) μ ε t γ r5 (q - 1) hε0 hεhalf (by linarith) hγ0 hγ1 hw hr5def hbd hspr
  have hmono := uP_mono (Finset.powersetCard (q - 1) (Finset.univ : Finset (Fin (2 * k))))
    (fun W => ∃ z ∈ lawSupport μ, z ⊆ incident W)
    (fun W => Gates.ev C inp (incident W) = false ∧ Fires M (incident W))
    (fun W hW ⟨z, hz, hzW⟩ =>
      ⟨hneg W (mem_powersetCard.mp hW).2, z, hsupp hz, hzW⟩)
  linarith

theorem chk_theorem_1 :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ (n k q : ℕ), q < k → 2 * k ≤ n →
        ∀ L : Finset (Fin n), k ≤ L.card → k ≤ Lᶜ.card →
          ∀ C : MonotoneCircuit (Edge n), DistinguishesMatchings C L k q →
            a * Real.exp (c * (q : ℝ) / Real.sqrt (k : ℝ)) ≤ (C.size : ℝ) := by
  obtain ⟨α5, hα5, h5⟩ := lemma_5
  obtain ⟨α12, hα12, h12⟩ := lemma_12
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 1 / (1728 * α12 + 128 * α5 + 200) := ⟨_, rfl⟩
  obtain ⟨hη0, hη5, hη12, hη⟩ := Dev.T1.arith_eta α5 α12 η hα5 hα12 hηdef
  refine ⟨Real.exp (-1), η ^ 2 / 2, Real.exp_pos _, by positivity, ?_⟩
  intro n k q hqk h2k L hL hLc C hC
  have hk1 : 1 ≤ k := by omega
  have hs1 : 1 ≤ Real.sqrt k := by rw [Real.one_le_sqrt]; exact_mod_cast hk1
  have hss : Real.sqrt k * Real.sqrt k = (k : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
  by_cases hq : (q : ℝ) < 2 / η ^ 2 * Real.sqrt k
  · have hsize : (1 : ℝ) ≤ C.size := by
      have : 0 < C.size := Fin.pos C.output
      exact_mod_cast this
    have hs0 : 0 < Real.sqrt k := by linarith
    have h1 : η ^ 2 / 2 * (q : ℝ) / Real.sqrt k ≤ 1 := by
      rw [div_le_one hs0]
      have : η ^ 2 / 2 * (2 / η ^ 2 * Real.sqrt k) = Real.sqrt k := by field_simp
      nlinarith [sq_nonneg η]
    calc Real.exp (-1) * Real.exp (η ^ 2 / 2 * (q : ℝ) / Real.sqrt k)
        ≤ Real.exp (-1) * Real.exp 1 := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
      _ ≤ C.size := hsize
  · exact Dev.T1.main_regime α5 α12 hα5 hα12 h5 h12 η hη0 hη5 hη12 hη n k q hqk L hL hLc C hC
      _ hs1 hss (le_of_not_gt hq)

end SpreadMatchCircuit.Matching
end

theorem solution : type_of% @SpreadMatchCircuit.Matching.chk_theorem_1 := @SpreadMatchCircuit.Matching.chk_theorem_1
