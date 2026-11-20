-- Prove2me | solution 1 for SpreadMatchCircuit.Matching.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:46:36.740393+00:00
-- url     : https://prove2.me/submissions/a14afbaa-c057-4286-810d-6e4384bbb80c

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Approximator
import Theorems.Thm_SpreadMatchCircuit_Matching_lemma_5

section
namespace SpreadMatchCircuit.Matching.Dev.L12

open Finset SpreadMatchCircuit.Matching

/-! ### Generic helpers -/

lemma firstOf_filter_spec {α : Type} (ord : LinearOrder α) (F : Finset α) (p : α → Prop)
    [DecidablePred p] (d : α) (Q : α → Prop) (hex : ∃ x ∈ F, p x) (hQ : ∀ x ∈ F, p x → Q x) :
    Q (firstOf ord (F.filter p) d) := by
  have hne : (F.filter p).Nonempty := by
    obtain ⟨x, hx, hpx⟩ := hex; exact ⟨x, mem_filter.mpr ⟨hx, hpx⟩⟩
  unfold firstOf
  rw [dif_pos hne]
  have := mem_filter.mp (@Finset.min'_mem α ord _ hne)
  exact hQ _ this.1 this.2

lemma uniformProb_le_one {β : Type} (F : Finset β) (A : β → Prop) : uniformProb F A ≤ 1 := by
  classical
  unfold uniformProb
  apply div_le_one_of_le₀ _ (by positivity)
  exact_mod_cast card_filter_le _ _

lemma uniformProb_eq {β : Type} (F : Finset β) (A : β → Prop) [DecidablePred A] :
    uniformProb F A = ((F.filter A).card : ℝ) / F.card := by
  unfold uniformProb
  congr

lemma exists_of_uniformProb_pos {β : Type} (F : Finset β) (A : β → Prop)
    (h : 0 < uniformProb F A) : ∃ x ∈ F, A x := by
  classical
  by_contra hc
  push Not at hc
  unfold uniformProb at h
  rw [filter_false_of_mem hc] at h
  simp at h

open scoped Classical in
/-- The push-forward of the uniform law on a nonempty finite set. -/
lemma exists_pushforward {α β : Type} [Fintype α] (S : Finset β) (hS : S.Nonempty)
    (f : β → α) :
    ∃ μ : PMF α, (∀ (A : α → Prop) [DecidablePred A], lawProb μ A =
      ((S.filter fun x => A (f x)).card : ℝ) / S.card) ∧
      ∀ z ∈ lawSupport μ, ∃ x ∈ S, f x = z := by
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  set q : α → ℝ := fun z => ((S.filter fun x => f x = z).card : ℝ) / S.card with hq
  have hq0 : ∀ z, 0 ≤ q z := fun z => by positivity
  have hsum : ∑ z, q z = 1 := by
    simp only [q, ← Finset.sum_div]
    have := card_eq_sum_card_fiberwise (s := S) (t := (univ : Finset α)) (f := f)
      (fun _ _ => mem_coe.mpr (mem_univ _))
    rw [div_eq_one_iff_eq hSpos.ne']
    exact_mod_cast this.symm
  let μ : PMF α := PMF.ofFintype (fun z => ENNReal.ofReal (q z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hq0 z), hsum, ENNReal.ofReal_one])
  refine ⟨μ, ?_, ?_⟩
  · intro A _
    unfold lawProb
    simp only [μ, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hq0 _)]
    simp only [q, ← Finset.sum_div]
    congr 1
    have := card_eq_sum_card_fiberwise (s := S.filter fun x => A (f x)) (t := univ.filter A)
      (f := f) (by intro x hx; simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢; simp [hx.2])
    rw [this]; push_cast
    refine sum_congr (by ext; simp) ?_
    intro z hz
    rw [filter_filter]
    congr 2
    apply filter_congr
    intro x _
    simp only [mem_filter, mem_univ, true_and] at hz
    constructor <;> intro h <;> aesop
  · intro z hz
    simp only [lawSupport, mem_filter, PMF.mem_support_iff] at hz
    have hqz : 0 < q z := by
      by_contra h
      push Not at h
      apply hz.2
      simp [μ, PMF.ofFintype_apply, ENNReal.ofReal_eq_zero.mpr h]
    have hc : 0 < (S.filter fun x => f x = z).card := by
      by_contra h
      push Not at h
      have : (S.filter fun x => f x = z).card = 0 := Nat.le_zero.mp h
      simp [q, this] at hqz
    obtain ⟨x, hx⟩ := card_pos.mp hc
    exact ⟨x, (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩

/-! ### Edges, incidence, pulling back along an embedding -/

section Edges

variable {m n : ℕ}

lemma mem_endpoints {e : Edge n} {v : Fin n} : v ∈ endpoints e ↔ v ∈ e.1 := by
  simp [endpoints, Sym2.mem_toFinset]

lemma mem_incident' {W : Finset (Fin n)} {e : Edge n} :
    e ∈ incident W ↔ ∃ v ∈ endpoints e, v ∈ W := by
  simp [incident, Finset.not_disjoint_iff]

lemma incident_mono {S T : Finset (Fin n)} (h : S ⊆ T) : incident S ⊆ incident T := by
  intro e he
  obtain ⟨v, hv, hvS⟩ := mem_incident'.mp he
  exact mem_incident'.mpr ⟨v, hv, h hvS⟩

lemma matching_mono {x y : Finset (Edge n)} (hx : IsMatching x) (h : y ⊆ x) : IsMatching y :=
  fun e he e' he' hne => hx e (h he) e' (h he') hne

/-- The image of an edge under a vertex embedding. -/
def emap (ι : Fin m ↪ Fin n) (e : Edge m) : Edge n :=
  ⟨Sym2.map ι e.1, by rw [Sym2.isDiag_map ι.injective]; exact e.2⟩

lemma emap_injective (ι : Fin m ↪ Fin n) : Function.Injective (emap ι) := by
  intro e e' h
  apply Subtype.ext
  exact Sym2.map.injective ι.injective (congrArg Subtype.val h)

lemma mem_endpoints_emap (ι : Fin m ↪ Fin n) (e : Edge m) (v : Fin n) :
    v ∈ endpoints (emap ι e) ↔ ∃ u ∈ endpoints e, ι u = v := by
  simp only [mem_endpoints, emap, Sym2.mem_map]

lemma emap_lift (ι : Fin m ↪ Fin n) (e : Edge n) (h : ∀ v ∈ endpoints e, ∃ u, ι u = v) :
    ∃ e', emap ι e' = e := by
  obtain ⟨z, hz⟩ := e
  induction z using Sym2.ind with
  | h x y =>
    obtain ⟨x', hx'⟩ := h x (mem_endpoints.mpr (Sym2.mem_mk_left x y))
    obtain ⟨y', hy'⟩ := h y (mem_endpoints.mpr (Sym2.mem_mk_right x y))
    subst hx' hy'
    refine ⟨⟨s(x', y'), ?_⟩, ?_⟩
    · intro hd
      apply hz
      rw [Sym2.mk_isDiag_iff] at hd ⊢
      rw [hd]
    · apply Subtype.ext
      simp [emap]

open scoped Classical in
/-- Pull back a graph on `Fin n` along a vertex embedding. -/
noncomputable def pb (ι : Fin m ↪ Fin n) (Z : Finset (Edge n)) : Finset (Edge m) :=
  univ.filter fun e => emap ι e ∈ Z

lemma mem_pb {ι : Fin m ↪ Fin n} {Z : Finset (Edge n)} {e : Edge m} :
    e ∈ pb ι Z ↔ emap ι e ∈ Z := by
  simp [pb]

lemma subset_pb {ι : Fin m ↪ Fin n} {Z : Finset (Edge n)} {s : Finset (Edge m)} :
    s ⊆ pb ι Z ↔ s.map ⟨emap ι, emap_injective ι⟩ ⊆ Z := by
  constructor
  · intro h e he
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    exact mem_pb.mp (h he')
  · intro h e he
    exact mem_pb.mpr (h (mem_map_of_mem _ he))

lemma pb_matching (ι : Fin m ↪ Fin n) {Z : Finset (Edge n)} (hZ : IsMatching Z) :
    IsMatching (pb ι Z) := by
  intro e he e' he' hne
  have := hZ _ (mem_pb.mp he) _ (mem_pb.mp he') (fun h => hne (emap_injective ι h))
  rw [Finset.disjoint_left] at this ⊢
  intro v hv hv'
  exact this ((mem_endpoints_emap ι e _).mpr ⟨v, hv, rfl⟩)
    ((mem_endpoints_emap ι e' _).mpr ⟨v, hv', rfl⟩)

lemma pb_card_le (ι : Fin m ↪ Fin n) (Z : Finset (Edge n)) : (pb ι Z).card ≤ Z.card := by
  apply card_le_card_of_injOn (emap ι)
  · intro e he; exact mem_pb.mp he
  · exact (emap_injective ι).injOn

lemma exists_cover (W : Finset (Fin n)) :
    ∀ m : Finset (Edge n), m ⊆ incident W → ∃ S ⊆ W, S.card ≤ m.card ∧ m ⊆ incident S := by
  classical
  intro m
  induction m using Finset.induction_on with
  | empty => intro _; exact ⟨∅, empty_subset _, by simp, empty_subset _⟩
  | insert e m he ih =>
    intro h
    obtain ⟨S, hSW, hSc, hmS⟩ := ih ((subset_insert e m).trans h)
    obtain ⟨v, hv, hvW⟩ := mem_incident'.mp (h (mem_insert_self e m))
    refine ⟨insert v S, insert_subset hvW hSW, ?_, ?_⟩
    · rw [card_insert_of_notMem he]; exact (card_insert_le v S).trans (by omega)
    · intro e' he'
      rcases mem_insert.mp he' with rfl | he'
      · exact mem_incident'.mpr ⟨v, hv, mem_insert_self v S⟩
      · exact incident_mono (subset_insert v S) (hmS he')

end Edges

/-! ### Binomial estimates -/

lemma choose_step (n k : ℕ) (h : n + 1 ≤ 4 * (k + 1)) :
    (n + 1).choose (k + 1) ≤ 4 * n.choose k := by
  have e := Nat.add_one_mul_choose_eq n k
  have : (n + 1).choose (k + 1) * (k + 1) ≤ 4 * n.choose k * (k + 1) := by
    calc (n + 1).choose (k + 1) * (k + 1) = (n + 1) * n.choose k := e.symm
      _ ≤ (4 * (k + 1)) * n.choose k := Nat.mul_le_mul_right _ h
      _ = 4 * n.choose k * (k + 1) := by ring
  exact Nat.le_of_mul_le_mul_right this (Nat.succ_pos k)

lemma choose_ratio (a b : ℕ) (h2 : b ≤ 2 * a) :
    ∀ s, 3 * s ≤ b → b.choose a ≤ 4 ^ s * (b - s).choose (a - s) := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
    intro hs
    have h1 := ih (by omega)
    have h2' : (b - s).choose (a - s) ≤ 4 * (b - (s + 1)).choose (a - (s + 1)) := by
      have e1 : b - s = (b - (s + 1)) + 1 := by omega
      have e2 : a - s = (a - (s + 1)) + 1 := by omega
      rw [e1, e2]; apply choose_step; omega
    calc b.choose a ≤ 4 ^ s * (b - s).choose (a - s) := h1
      _ ≤ 4 ^ s * (4 * (b - (s + 1)).choose (a - (s + 1))) := Nat.mul_le_mul_left _ h2'
      _ = 4 ^ (s + 1) * (b - (s + 1)).choose (a - (s + 1)) := by ring

lemma count_supersets {n : ℕ} (W S : Finset (Fin n)) (hS : S ⊆ W) (a : ℕ) (hsa : S.card ≤ a)
    (P : Finset (Fin n) → Prop) [DecidablePred P] (hP : ∀ U, S ⊆ U → P U) :
    (W.card - S.card).choose (a - S.card) ≤ ((powersetCard a W).filter P).card := by
  classical
  rw [← card_sdiff_of_subset hS, ← card_powersetCard]
  apply card_le_card_of_injOn (fun U => U ∪ S)
  · intro U hU
    have hU' := mem_powersetCard.mp hU
    have hdisj : Disjoint U S := by
      rw [disjoint_left]; intro v hv hvS
      exact (mem_sdiff.mp (hU'.1 hv)).2 hvS
    rw [mem_coe, mem_filter, mem_powersetCard]
    refine ⟨⟨union_subset (hU'.1.trans sdiff_subset) hS, ?_⟩, hP _ subset_union_right⟩
    rw [card_union_of_disjoint hdisj, hU'.2]; omega
  · intro U hU U' hU' h
    have h1 := mem_powersetCard.mp hU
    have h2 := mem_powersetCard.mp hU'
    simp only at h
    ext v
    constructor
    · intro hv
      have : v ∈ U' ∪ S := h ▸ mem_union_left S hv
      rcases mem_union.mp this with h' | h'
      · exact h'
      · exact absurd h' (mem_sdiff.mp (h1.1 hv)).2
    · intro hv
      have : v ∈ U ∪ S := h.symm ▸ mem_union_left S hv
      rcases mem_union.mp this with h' | h'
      · exact h'
      · exact absurd h' (mem_sdiff.mp (h2.1 hv)).2

/-! ### Facts about the gate -/

variable {N : ℕ}

lemma newPos_fires (G : AndGate N) (k : ℕ) (M : Finset (Finset (Edge (2 * N))))
    (x : Finset (Edge (2 * N))) (hx : x ∈ G.newPos k M) : Fires G.M₁ x ∧ Fires G.M₂ x := by
  classical
  unfold AndGate.newPos errorPos at hx
  simp only [mem_sdiff, mem_union, mem_filter] at hx
  obtain ⟨⟨hxc, hg, -⟩, hn⟩ := hx
  unfold AndGate.g at hg
  rw [Bool.and_eq_true] at hg
  constructor
  · by_contra h; exact hn (Or.inl ⟨hxc, hg.1, h⟩)
  · by_contra h; exact hn (Or.inr ⟨hxc, hg.2, h⟩)

lemma newPos_cross (G : AndGate N) (k : ℕ) (M : Finset (Finset (Edge (2 * N))))
    (x : Finset (Edge (2 * N))) (hx : x ∈ G.newPos k M) : x ∈ crossMatchings N k := by
  classical
  unfold AndGate.newPos errorPos at hx
  exact (mem_filter.mp (mem_sdiff.mp hx).1).1

lemma newNeg_fires {G : AndGate N} {b : ℕ} {M : Finset (Finset (Edge (2 * N)))}
    {x : Finset (Edge (2 * N))} (hx : x ∈ G.newNeg b M) : Fires M x := by
  classical
  unfold AndGate.newNeg errorNeg at hx
  exact (mem_filter.mp (mem_sdiff.mp hx).1).2.2

lemma newNeg_not_fires (G : AndGate N) (b : ℕ) (M : Finset (Finset (Edge (2 * N))))
    (x : Finset (Edge (2 * N))) (hx : x ∈ G.newNeg b M) : ¬ (Fires G.M₁ x ∧ Fires G.M₂ x) := by
  classical
  unfold AndGate.newNeg errorNeg at hx
  simp only [mem_sdiff, mem_union, mem_filter] at hx
  obtain ⟨⟨hxc, hg, -⟩, hn⟩ := hx
  rintro ⟨h1, h2⟩
  unfold AndGate.g at hg
  rcases Bool.and_eq_false_iff.mp hg with h | h
  · exact hn (Or.inl ⟨hxc, h, h1⟩)
  · exact hn (Or.inr ⟨hxc, h, h2⟩)

lemma mem_candidates {G : AndGate N} {c : Finset (Edge (2 * N))} (hc : c ∈ G.candidates) :
    IsMatching c ∧ ∃ m₁ ∈ G.M₁, ∃ m₂ ∈ G.M₂, m₁ ∪ m₂ = c := by
  classical
  unfold AndGate.candidates at hc
  obtain ⟨h1, h2⟩ := mem_filter.mp hc
  exact ⟨h2, mem_image₂.mp h1⟩

lemma candidates_card (G : AndGate N) (t : ℝ) (hG : G.SizeBounded t) (c : Finset (Edge (2 * N)))
    (hc : c ∈ G.candidates) : (c.card : ℝ) ≤ 2 * t := by
  obtain ⟨-, a, ha, b, hb, rfl⟩ := mem_candidates hc
  have h1 := hG.1 a ha
  have h2 := hG.2 b hb
  have : ((a ∪ b).card : ℝ) ≤ a.card + b.card := by exact_mod_cast card_union_le a b
  linarith

lemma selector_mem_candidates (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N))))
    (k : ℕ) (M : Finset (Finset (Edge (2 * N)))) (x : Finset (Edge (2 * N)))
    (hx : x ∈ G.newPos k M) : G.selector ord x ∈ G.candidates := by
  classical
  have hxc := newPos_cross G k M x hx
  obtain ⟨⟨m1, hm1, h1⟩, ⟨m2, hm2, h2⟩⟩ := newPos_fires G k M x hx
  have hxm : IsMatching x := by unfold crossMatchings at hxc; exact (mem_filter.mp hxc).2.1
  unfold AndGate.selector
  apply firstOf_filter_spec ord G.candidates (fun m => m ⊆ x) ∅ (· ∈ G.candidates)
  · refine ⟨m1 ∪ m2, ?_, union_subset h1 h2⟩
    unfold AndGate.candidates
    rw [mem_filter]
    exact ⟨mem_image₂_of_mem hm1 hm2, matching_mono hxm (union_subset h1 h2)⟩
  · intro y hy _; exact hy

lemma coreProb_empty (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (M : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M) :
    G.coreProb ord k M ∅ = 1 := by
  unfold AndGate.coreProb
  simp only [empty_subset, true_and]
  exact div_self hP.ne'

open scoped Classical in
lemma exists_max_core (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r : ℝ) (M : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M) :
    ∃ c ∈ (univ.filter fun m => IsMatching m ∧ (r ^ m.card)⁻¹ ≤ G.coreProb ord k M m),
      ∀ m' ∈ (univ.filter fun m => IsMatching m ∧ (r ^ m.card)⁻¹ ≤ G.coreProb ord k M m),
        m'.card ≤ c.card := by
  classical
  have h0 : (∅ : Finset (Edge (2 * N))) ∈
      (univ.filter fun m => IsMatching m ∧ (r ^ m.card)⁻¹ ≤ G.coreProb ord k M m) := by
    rw [mem_filter]
    refine ⟨mem_univ _, ?_, ?_⟩
    · intro e he; simp at he
    · rw [coreProb_empty G ord k M hP]; simp
  exact exists_max_image _ card ⟨_, h0⟩

lemma largestCore_spec (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r : ℝ) (M : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M) :
    IsMatching (G.largestCore ord k r M) ∧
      (r ^ (G.largestCore ord k r M).card)⁻¹ ≤
        G.coreProb ord k M (G.largestCore ord k r M) := by
  classical
  unfold AndGate.largestCore
  refine firstOf_filter_spec ord _ _ ∅
    (fun c => IsMatching c ∧ (r ^ c.card)⁻¹ ≤ G.coreProb ord k M c)
    (exists_max_core G ord k r M hP) ?_
  intro x hx _
  exact (mem_filter.mp hx).2

lemma largestCore_max (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r : ℝ) (M : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M)
    (m : Finset (Edge (2 * N))) (hm : IsMatching m) (hc : (r ^ m.card)⁻¹ ≤ G.coreProb ord k M m) :
    m.card ≤ (G.largestCore ord k r M).card := by
  classical
  unfold AndGate.largestCore
  refine firstOf_filter_spec ord _ _ ∅ (fun c => m.card ≤ c.card)
    (exists_max_core G ord k r M hP) ?_
  intro x _ hmax
  exact hmax m (mem_filter.mpr ⟨mem_univ _, hm, hc⟩)

lemma core_witness (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r : ℝ) (hr : 0 < r) (M : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M) :
    ∃ x ∈ crossMatchings N k, G.largestCore ord k r M ⊆ G.selector ord x ∧ x ∈ G.newPos k M := by
  obtain ⟨-, hcore⟩ := largestCore_spec G ord k r M hP
  have hpos : 0 < G.coreProb ord k M (G.largestCore ord k r M) :=
    lt_of_lt_of_le (by positivity) hcore
  unfold AndGate.coreProb at hpos
  have hU := (div_pos_iff_of_pos_right hP).mp hpos
  exact exists_of_uniformProb_pos _ _ hU

/-- A member of `M_g` was inserted as a largest core of size `≤ t` at some earlier family. -/
def IsCore (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ) (r t : ℝ)
    (m : Finset (Edge (2 * N))) : Prop :=
  (m.card : ℝ) ≤ t ∧ ∃ M', 0 < G.newPosProb k M' ∧ m = G.largestCore ord k r M'

lemma loop_core (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ) (r t : ℝ) :
    ∀ (steps : ℕ) (M : Finset (Finset (Edge (2 * N)))), (∀ m ∈ M, IsCore G ord k r t m) →
      ∀ m ∈ G.loop ord k r t steps M, IsCore G ord k r t m := by
  intro steps
  induction steps with
  | zero => intro M hM; rw [AndGate.loop]; exact hM
  | succ s ih =>
    intro M hM
    rw [AndGate.loop]
    split_ifs with hP ht
    · apply ih
      intro m hm
      rcases mem_insert.mp hm with rfl | hm
      · exact ⟨ht, M, hP, rfl⟩
      · exact hM m hm
    · exact hM
    · exact hM

lemma alg_core (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ) (r t : ℝ)
    (m : Finset (Edge (2 * N))) (hm : m ∈ G.algorithm1 ord k r t) : IsCore G ord k r t m :=
  loop_core G ord k r t _ ∅ (by simp) m hm

lemma small_t (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ) (r t : ℝ)
    (ht : t < 1) (hG : G.SizeBounded t) (b : ℕ) (W : Finset (Fin (2 * N)))
    (hW : incident W ∈ G.newNeg b (G.algorithm1 ord k r t)) : False := by
  obtain ⟨m, hm, -⟩ := newNeg_fires hW
  obtain ⟨-, M', hP, -⟩ := alg_core G ord k r t m hm
  unfold AndGate.newPosProb at hP
  obtain ⟨x, -, hx⟩ := exists_of_uniformProb_pos _ _ hP
  obtain ⟨⟨m1, hm1, -⟩, ⟨m2, hm2, -⟩⟩ := newPos_fires G k M' x hx
  have e1 : m1 = ∅ := by
    have h := hG.1 m1 hm1
    have : m1.card < 1 := by exact_mod_cast (show (m1.card : ℝ) < 1 by linarith)
    exact card_eq_zero.mp (Nat.lt_one_iff.mp this)
  have e2 : m2 = ∅ := by
    have h := hG.2 m2 hm2
    have : m2.card < 1 := by exact_mod_cast (show (m2.card : ℝ) < 1 by linarith)
    exact card_eq_zero.mp (Nat.lt_one_iff.mp this)
  apply newNeg_not_fires G b _ _ hW
  exact ⟨⟨m1, hm1, by simp [e1]⟩, ⟨m2, hm2, by simp [e2]⟩⟩

/-! ### Part B: one fixed `W₁` carrying a core, via Lemma 5 on the complement of `W₁` -/

/-- The hypothesis shape of Lemma 5 for a given constant `α`. -/
def Lemma5Prop (α : ℝ) : Prop :=
  ∀ (n : ℕ) (μ : PMF (Finset (Edge n))) (ε t γ r : ℝ) (w : ℕ),
    0 < ε → ε < 1 / 2 → 1 < t → 0 < γ → γ ≤ 1 → (w : ℝ) = γ * (n : ℝ) →
    r = α * (t + Real.log (1 / ε) ^ 2) / γ ^ 2 →
    IsBoundedMatchingLaw μ t → IsSpread μ r →
    1 - ε < uniformProb (Finset.powersetCard w (Finset.univ : Finset (Fin n)))
      (fun W => ∃ z ∈ lawSupport μ, z ⊆ incident W)

open scoped Classical in
lemma partB {α : ℝ} (hα : 0 < α) (h5 : Lemma5Prop α) (G : AndGate N)
    (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ) (r t ε : ℝ)
    (hG : G.SizeBounded t) (ht : 1 ≤ t) (hε : 0 < ε) (hε2 : ε < 1 / 2) (hr : 0 < r)
    (M' : Finset (Finset (Edge (2 * N)))) (hP : 0 < G.newPosProb k M')
    (W1 : Finset (Fin (2 * N))) (hsub : G.largestCore ord k r M' ⊆ incident W1)
    (w b : ℕ) (hw : 1 ≤ w) (hb : W1.card + w = b) (hb2 : b ≤ 2 * N)
    (hr5 : α * (2 * t + Real.log (1 / ε) ^ 2) /
      ((w : ℝ) / ((2 * N - W1.card : ℕ) : ℝ)) ^ 2 ≤ r)
    (M : Finset (Finset (Edge (2 * N)))) :
    ((((powersetCard b univ).filter fun W => incident W ∈ G.newNeg b M).filter
        fun W => W1 ⊆ W).card : ℝ)
      ≤ ε * ((2 * N - W1.card).choose w : ℝ) := by
  set c := G.largestCore ord k r M' with hc
  set n' := 2 * N - W1.card with hn'
  have hcompl : W1ᶜ.card = n' := by rw [card_compl, Fintype.card_fin]
  set ι : Fin n' ↪ Fin (2 * N) := (W1ᶜ.orderEmbOfFin hcompl).toEmbedding with hι
  have hιmem : ∀ u, ι u ∉ W1 := fun u => mem_compl.mp (W1ᶜ.orderEmbOfFin_mem hcompl u)
  have hιsurj : ∀ v, v ∉ W1 → ∃ u, ι u = v := by
    intro v hv
    have : v ∈ Set.range (W1ᶜ.orderEmbOfFin hcompl) := by
      rw [Finset.range_orderEmbOfFin]; simpa using hv
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu⟩
  set S := (crossMatchings N k).filter fun x => c ⊆ G.selector ord x ∧ x ∈ G.newPos k M'
    with hS
  have hSne : S.Nonempty := by
    obtain ⟨x, hx, h1, h2⟩ := core_witness G ord k r hr M' hP
    exact ⟨x, mem_filter.mpr ⟨hx, h1, h2⟩⟩
  obtain ⟨μ, hμP, hμS⟩ := exists_pushforward S hSne (fun x => pb ι (G.selector ord x))
  have hn'w : w ≤ n' := by omega
  have hn'pos : (0 : ℝ) < n' := by exact_mod_cast (show 0 < n' by omega)
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw
  set γ : ℝ := (w : ℝ) / (n' : ℝ) with hγ
  have hγ0 : 0 < γ := div_pos hwpos hn'pos
  have hγ1 : γ ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hn'w) hn'pos.le
  have hwγ : (w : ℝ) = γ * n' := by rw [hγ]; field_simp
  have hX : 0 < 2 * t + Real.log (1 / ε) ^ 2 := by
    have := sq_nonneg (Real.log (1 / ε)); linarith
  set r5 := α * (2 * t + Real.log (1 / ε) ^ 2) / γ ^ 2 with hr5def
  have hr5pos : 0 < r5 := div_pos (mul_pos hα hX) (pow_pos hγ0 2)
  have hbounded : IsBoundedMatchingLaw μ (2 * t) := by
    intro z hz
    obtain ⟨x, hxS, rfl⟩ := hμS z hz
    have hcand := selector_mem_candidates G ord k M' x (mem_filter.mp hxS).2.2
    refine ⟨pb_matching ι (mem_candidates hcand).1, ?_⟩
    have h1 : ((pb ι (G.selector ord x)).card : ℝ) ≤ (G.selector ord x).card := by
      exact_mod_cast pb_card_le ι _
    exact h1.trans (candidates_card G t hG _ hcand)
  have hspread : IsSpread μ r5 := by
    intro m hm
    rw [hμP]
    have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
    by_cases hm0 : m = ∅
    · subst hm0
      simp only [card_empty, pow_zero, inv_one]
      exact div_le_one_of_le₀ (by exact_mod_cast card_filter_le _ _) hSpos.le
    have hmpos : 0 < m.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hm0)
    set A := m.map ⟨emap ι, emap_injective ι⟩ ∪ c with hA
    have hdisj : Disjoint (m.map ⟨emap ι, emap_injective ι⟩) c := by
      rw [disjoint_left]
      intro e he hec
      obtain ⟨e', -, rfl⟩ := mem_map.mp he
      obtain ⟨v, hv, hvW⟩ := mem_incident'.mp (hsub hec)
      obtain ⟨u, -, rfl⟩ := (mem_endpoints_emap ι e' v).mp hv
      exact hιmem u hvW
    have hAcard : A.card = m.card + c.card := by rw [card_union_of_disjoint hdisj, card_map]
    have hfilt : (S.filter fun x => m ⊆ pb ι (G.selector ord x)) =
        (crossMatchings N k).filter (fun x => A ⊆ G.selector ord x ∧ x ∈ G.newPos k M') := by
      ext x
      rw [mem_filter, mem_filter, mem_filter, subset_pb, hA, union_subset_iff]
      constructor
      · rintro ⟨⟨hx, hc1, hn⟩, hm1⟩; exact ⟨hx, ⟨hm1, hc1⟩, hn⟩
      · rintro ⟨hx, ⟨hm1, hc1⟩, hn⟩; exact ⟨⟨hx, hc1, hn⟩, hm1⟩
    rw [hfilt]
    have hle : (r ^ m.card)⁻¹ ≤ (r5 ^ m.card)⁻¹ := by
      apply inv_anti₀ (pow_pos hr5pos _)
      apply pow_le_pow_left₀ hr5pos.le
      rw [hr5def, hγ]; exact hr5
    refine le_trans ?_ hle
    by_cases hAm : IsMatching A
    · have hnot0 : ¬ ((r ^ A.card)⁻¹ ≤ G.coreProb ord k M' A) := by
        intro h
        have := largestCore_max G ord k r M' hP A hAm h
        rw [← hc] at this
        omega
      have hnot : G.coreProb ord k M' A < (r ^ A.card)⁻¹ := lt_of_not_ge hnot0
      obtain ⟨-, hcore⟩ := largestCore_spec G ord k r M' hP
      rw [← hc] at hcore
      unfold AndGate.coreProb uniformProb at hnot hcore
      have hD : (0 : ℝ) < (crossMatchings N k).card := by
        have := (mem_filter.mp (hSne.choose_spec)).1
        exact_mod_cast card_pos.mpr ⟨_, this⟩
      have hnot' : (((crossMatchings N k).filter
          (fun x => A ⊆ G.selector ord x ∧ x ∈ G.newPos k M')).card : ℝ) /
            (crossMatchings N k).card / G.newPosProb k M' < (r ^ A.card)⁻¹ := by
        convert hnot
      have hcore' : (r ^ c.card)⁻¹ ≤ (S.card : ℝ) / (crossMatchings N k).card /
          G.newPosProb k M' := by
        convert hcore
      clear hnot hcore
      set a := (((crossMatchings N k).filter
        (fun x => A ⊆ G.selector ord x ∧ x ∈ G.newPos k M')).card : ℝ)
      set D := ((crossMatchings N k).card : ℝ)
      set P := G.newPosProb k M'
      rw [hAcard, pow_add, mul_inv] at hnot'
      have hrm : 0 < (r ^ m.card)⁻¹ := inv_pos.mpr (pow_pos hr _)
      have h3 : a / D / P < (r ^ m.card)⁻¹ * (S.card / D / P) :=
        lt_of_lt_of_le hnot' (mul_le_mul_of_nonneg_left hcore' hrm.le)
      rw [div_le_iff₀ hSpos]
      have h4 : a / D / P = a / (D * P) := by rw [div_div]
      have h5' : (S.card : ℝ) / D / P = S.card / (D * P) := by rw [div_div]
      rw [h4, h5', div_lt_iff₀ (mul_pos hD hP)] at h3
      have : (r ^ m.card)⁻¹ * (S.card / (D * P)) * (D * P) = (r ^ m.card)⁻¹ * S.card := by
        rw [mul_assoc, div_mul_cancel₀ _ (mul_pos hD hP).ne']
      linarith
    · have hempty : (crossMatchings N k).filter
          (fun x => A ⊆ G.selector ord x ∧ x ∈ G.newPos k M') = ∅ := by
        apply filter_false_of_mem
        rintro x - ⟨hAx, hx⟩
        exact hAm (matching_mono
          (mem_candidates (selector_mem_candidates G ord k M' x hx)).1 hAx)
      rw [hempty, card_empty, Nat.cast_zero, zero_div]
      positivity
  have key := h5 n' μ ε (2 * t) γ r5 w hε hε2 (by linarith) hγ0 hγ1 hwγ rfl hbounded hspread
  -- count of bad `W'`
  have hcount : (((powersetCard w (univ : Finset (Fin n'))).filter
      fun W' => ¬ ∃ z ∈ lawSupport μ, z ⊆ incident W').card : ℝ) < ε * (n'.choose w) := by
    have key' : 1 - ε < (((powersetCard w (univ : Finset (Fin n'))).filter
        fun W' => ∃ z ∈ lawSupport μ, z ⊆ incident W').card : ℝ) / (n'.choose w) := by
      unfold uniformProb at key
      rw [card_powersetCard, card_univ, Fintype.card_fin] at key
      convert key
    clear key
    have hCpos : (0 : ℝ) < n'.choose w := by exact_mod_cast Nat.choose_pos hn'w
    have hsplit := card_filter_add_card_filter_not
      (s := powersetCard w (univ : Finset (Fin n')))
      (fun W' => ∃ z ∈ lawSupport μ, z ⊆ incident W')
    rw [card_powersetCard, card_univ, Fintype.card_fin] at hsplit
    rw [lt_div_iff₀ hCpos] at key'
    have : (((powersetCard w (univ : Finset (Fin n'))).filter
        fun W' => ∃ z ∈ lawSupport μ, z ⊆ incident W').card : ℝ) +
        (((powersetCard w (univ : Finset (Fin n'))).filter
        fun W' => ¬ ∃ z ∈ lawSupport μ, z ⊆ incident W').card : ℝ) = n'.choose w := by
      exact_mod_cast hsplit
    nlinarith
  have hsubset : (((powersetCard b univ).filter fun W => incident W ∈ G.newNeg b M).filter
        fun W => W1 ⊆ W) ⊆
      ((powersetCard w (univ : Finset (Fin n'))).filter
        fun W' => ¬ ∃ z ∈ lawSupport μ, z ⊆ incident W').image (fun W' => W1 ∪ W'.map ι) := by
    intro W hW
    simp only [mem_filter, mem_powersetCard] at hW
    obtain ⟨⟨⟨-, hWb⟩, hWneg⟩, hW1W⟩ := hW
    rw [mem_image]
    refine ⟨univ.filter (fun u => ι u ∈ W), ?_, ?_⟩
    · have eqW : W1 ∪ (univ.filter (fun u => ι u ∈ W)).map ι = W := by
        ext v
        simp only [mem_union, mem_map, mem_filter, mem_univ, true_and]
        constructor
        · rintro (h | ⟨u, hu, rfl⟩)
          · exact hW1W h
          · exact hu
        · intro hv
          by_cases h : v ∈ W1
          · exact Or.inl h
          · obtain ⟨u, rfl⟩ := hιsurj v h
            exact Or.inr ⟨u, hv, rfl⟩
      have hd : Disjoint W1 ((univ.filter (fun u => ι u ∈ W)).map ι) := by
        rw [disjoint_right]
        intro v hv
        obtain ⟨u, -, rfl⟩ := mem_map.mp hv
        exact hιmem u
      have hcardW := congrArg card eqW
      rw [card_union_of_disjoint hd, card_map] at hcardW
      rw [mem_filter, mem_powersetCard]
      refine ⟨⟨subset_univ _, by omega⟩, ?_⟩
      rintro ⟨z, hz, hzW'⟩
      obtain ⟨x, hxS, rfl⟩ := hμS z hz
      have hx := (mem_filter.mp hxS).2.2
      have hsel : G.selector ord x ⊆ incident W := by
        intro e he
        by_cases hdW : e ∈ incident W1
        · exact incident_mono hW1W hdW
        · have hall : ∀ v ∈ endpoints e, v ∉ W1 := by
            intro v hv hvW
            exact hdW (mem_incident'.mpr ⟨v, hv, hvW⟩)
          obtain ⟨e', rfl⟩ := emap_lift ι e (fun v hv => hιsurj v (hall v hv))
          have h1 : e' ∈ pb ι (G.selector ord x) := mem_pb.mpr he
          obtain ⟨u, hu, huW'⟩ := mem_incident'.mp (hzW' h1)
          exact mem_incident'.mpr ⟨ι u, (mem_endpoints_emap ι e' _).mpr ⟨u, hu, rfl⟩,
            (mem_filter.mp huW').2⟩
      obtain ⟨-, m1, hm1, m2, hm2, hcu⟩ :=
        mem_candidates (selector_mem_candidates G ord k M' x hx)
      apply newNeg_not_fires G b M _ hWneg
      rw [← hcu] at hsel
      exact ⟨⟨m1, hm1, subset_union_left.trans hsel⟩, ⟨m2, hm2, subset_union_right.trans hsel⟩⟩
    · ext v
      simp only [mem_union, mem_map, mem_filter, mem_univ, true_and]
      constructor
      · rintro (h | ⟨u, hu, rfl⟩)
        · exact hW1W h
        · exact hu
      · intro hv
        by_cases h : v ∈ W1
        · exact Or.inl h
        · obtain ⟨u, rfl⟩ := hιsurj v h
          exact Or.inr ⟨u, hv, rfl⟩
  have h1 := card_le_card hsubset
  have h2 := card_image_le (s := (powersetCard w (univ : Finset (Fin n'))).filter
        fun W' => ¬ ∃ z ∈ lawSupport μ, z ⊆ incident W') (f := fun W' => W1 ∪ W'.map ι)
  have h12 : ((((powersetCard b univ).filter fun W => incident W ∈ G.newNeg b M).filter
        fun W => W1 ⊆ W).card : ℝ) ≤ (((powersetCard w (univ : Finset (Fin n'))).filter
        fun W' => ¬ ∃ z ∈ lawSupport μ, z ⊆ incident W').card : ℝ) := by
    exact_mod_cast h1.trans h2
  exact (h12.trans hcount.le)

/-! ### Part C: the main case, by double counting splits `W = W₁ ∪ W₂` -/

open scoped Classical in
lemma main_case {α : ℝ} (hα : 0 < α) (h5 : Lemma5Prop α) (N k b : ℕ) (t ε r : ℝ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (hbk : b < k) (htb : t ≤ (b : ℝ) / 100) (hε : 0 < ε)
    (hεh : ε < 1 / 2) (ht1 : 1 ≤ t)
    (hr : α * (2 * t + Real.log (1 / ε) ^ 2) * (3 * (2 * (N : ℝ)) / (b : ℝ)) ^ 2 ≤ r)
    (ord : LinearOrder (Finset (Edge (2 * N)))) (G : AndGate N) (hG : G.SizeBounded t) :
    (((powersetCard b (univ : Finset (Fin (2 * N)))).filter
        fun W => incident W ∈ G.newNeg b (G.algorithm1 ord k r t)).card : ℝ)
      ≤ (4 : ℝ) ^ t * ε * ((2 * N).choose b : ℝ) := by
  set M := G.algorithm1 ord k r t with hM
  set bad := (powersetCard b (univ : Finset (Fin (2 * N)))).filter
    (fun W => incident W ∈ G.newNeg b M) with hbad
  have hb100 : 100 ≤ b := by
    have : (100 : ℝ) ≤ b := by linarith
    exact_mod_cast this
  set w := b / 2 with hw
  set a := b - w with ha
  have hb2N : b ≤ 2 * N := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hwR : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hX : 0 < 2 * t + Real.log (1 / ε) ^ 2 := by
    have := sq_nonneg (Real.log (1 / ε)); linarith
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hr5 : α * (2 * t + Real.log (1 / ε) ^ 2) / ((w : ℝ) / ((2 * N - a : ℕ) : ℝ)) ^ 2 ≤ r := by
    refine le_trans ?_ hr
    rw [div_eq_mul_inv, ← inv_pow, inv_div]
    apply mul_le_mul_of_nonneg_left _ (mul_pos hα hX).le
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff₀ hwR hbR]
    have hnat : (2 * N - a) * b ≤ 3 * (2 * N) * w := by
      calc (2 * N - a) * b ≤ 2 * N * b := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ ≤ 2 * N * (3 * w) := Nat.mul_le_mul_left _ (by omega)
        _ = 3 * (2 * N) * w := by ring
    exact_mod_cast hnat
  -- Part B for every firing `W₁`
  have hB : ∀ W1 ∈ (powersetCard a (univ : Finset (Fin (2 * N)))).filter
      (fun W1 => Fires M (incident W1)),
      ((bad.filter fun W => W1 ⊆ W).card : ℝ) ≤ ε * ((2 * N - a).choose w : ℝ) := by
    intro W1 hW1
    rw [mem_filter, mem_powersetCard] at hW1
    obtain ⟨⟨-, hW1a⟩, ⟨m, hmM, hmsub⟩⟩ := hW1
    obtain ⟨-, M', hP, rfl⟩ := alg_core G ord k r t m hmM
    have := partB hα h5 G ord k r t ε hG ht1 hε hεh hrpos M' hP W1 hmsub w b (by omega)
      (by omega) hb2N (by rw [hW1a]; exact hr5) M
    rw [hW1a] at this
    exact this
  -- each bad `W` has many firing `W₁ ⊆ W`
  have hA : ∀ W ∈ bad, (b.choose a : ℝ) ≤
      (4 : ℝ) ^ t * (((powersetCard a W).filter fun W1 => Fires M (incident W1)).card : ℝ) := by
    intro W hW
    rw [hbad, mem_filter, mem_powersetCard] at hW
    obtain ⟨⟨-, hWb⟩, hWneg⟩ := hW
    obtain ⟨m, hmM, hmsub⟩ := newNeg_fires hWneg
    have hmt := (alg_core G ord k r t m hmM).1
    obtain ⟨S, hSW, hSm, hmS⟩ := exists_cover W m hmsub
    have hst : (S.card : ℝ) ≤ t := le_trans (by exact_mod_cast hSm) hmt
    have h3s : 3 * S.card ≤ b := by
      have h1 : (100 * S.card : ℝ) ≤ b := by linarith
      have h2 : 100 * S.card ≤ b := by exact_mod_cast h1
      omega
    have hsa : S.card ≤ a := by omega
    have hcr := choose_ratio a b (by omega) S.card h3s
    have hcnt := count_supersets W S hSW a hsa (fun W1 => Fires M (incident W1))
      (fun U hU => ⟨m, hmM, hmS.trans (incident_mono hU)⟩)
    rw [hWb] at hcnt
    have h4 : ((4 : ℝ) ^ S.card) ≤ (4 : ℝ) ^ t := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hst
    calc (b.choose a : ℝ) ≤ ((4 ^ S.card * (b - S.card).choose (a - S.card) : ℕ) : ℝ) := by
          exact_mod_cast hcr
      _ = (4 : ℝ) ^ S.card * ((b - S.card).choose (a - S.card) : ℝ) := by push_cast; ring
      _ ≤ (4 : ℝ) ^ t *
          (((powersetCard a W).filter fun W1 => Fires M (incident W1)).card : ℝ) :=
          mul_le_mul h4 (by exact_mod_cast hcnt) (by positivity) (by positivity)
  -- double counting
  have hDC : ∑ W ∈ bad, ((((powersetCard a W).filter fun W1 => Fires M (incident W1)).card : ℕ)
      : ℝ) = ∑ W1 ∈ (powersetCard a (univ : Finset (Fin (2 * N)))).filter
        (fun W1 => Fires M (incident W1)), (((bad.filter fun W => W1 ⊆ W).card : ℕ) : ℝ) := by
    have e1 : ∀ W : Finset (Fin (2 * N)), (powersetCard a W).filter
        (fun W1 => Fires M (incident W1)) = (powersetCard a univ).filter
        (fun W1 => W1 ⊆ W ∧ Fires M (incident W1)) := by
      intro W; ext W1; simp only [mem_filter, mem_powersetCard]; constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨subset_univ _, h2⟩, h1, h3⟩
      · rintro ⟨⟨-, h2⟩, h1, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    clear_value bad
    simp_rw [e1, card_filter]
    push_cast
    rw [sum_comm, sum_filter (s := powersetCard a univ)]
    apply sum_congr rfl
    intro W1 _
    split_ifs with hF
    · apply sum_congr rfl; intro W _; simp [hF]
    · apply sum_eq_zero; intro W _; rw [if_neg (fun h => hF ⟨subset_univ _, h.2⟩)]
  have hCa : (0 : ℝ) < b.choose a := by exact_mod_cast Nat.choose_pos (by omega)
  have hid : ((2 * N).choose a : ℝ) * ((2 * N - a).choose w : ℝ) =
      ((2 * N).choose b : ℝ) * (b.choose a : ℝ) := by
    have := Nat.choose_mul (n := 2 * N) (k := b) (s := a) (by omega)
    rw [show b - a = w by omega] at this
    exact_mod_cast this.symm
  have hPa : ((((powersetCard a (univ : Finset (Fin (2 * N)))).filter
      (fun W1 => Fires M (incident W1))).card : ℕ) : ℝ) ≤ (2 * N).choose a := by
    have := card_filter_le (powersetCard a (univ : Finset (Fin (2 * N))))
      (fun W1 => Fires M (incident W1))
    rw [card_powersetCard, card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hεC : 0 ≤ ε * ((2 * N - a).choose w : ℝ) := by positivity
  have hmain : (bad.card : ℝ) * b.choose a ≤
      (4 : ℝ) ^ t * ε * ((2 * N).choose b : ℝ) * b.choose a := by
    calc (bad.card : ℝ) * b.choose a = ∑ W ∈ bad, (b.choose a : ℝ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ W ∈ bad, (4 : ℝ) ^ t *
          (((powersetCard a W).filter fun W1 => Fires M (incident W1)).card : ℝ) :=
          sum_le_sum hA
      _ = (4 : ℝ) ^ t * ∑ W ∈ bad,
          (((powersetCard a W).filter fun W1 => Fires M (incident W1)).card : ℝ) := by
          rw [mul_sum]
      _ = (4 : ℝ) ^ t * ∑ W1 ∈ (powersetCard a (univ : Finset (Fin (2 * N)))).filter
          (fun W1 => Fires M (incident W1)), ((bad.filter fun W => W1 ⊆ W).card : ℝ) := by
          rw [hDC]
      _ ≤ (4 : ℝ) ^ t * ∑ W1 ∈ (powersetCard a (univ : Finset (Fin (2 * N)))).filter
          (fun W1 => Fires M (incident W1)), ε * ((2 * N - a).choose w : ℝ) := by
          apply mul_le_mul_of_nonneg_left (sum_le_sum hB) (by positivity)
      _ = (4 : ℝ) ^ t * ((((powersetCard a (univ : Finset (Fin (2 * N)))).filter
          (fun W1 => Fires M (incident W1))).card : ℝ) * (ε * ((2 * N - a).choose w : ℝ))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (4 : ℝ) ^ t * (((2 * N).choose a : ℝ) * (ε * ((2 * N - a).choose w : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hPa hεC
      _ = (4 : ℝ) ^ t * ε * (((2 * N).choose a : ℝ) * ((2 * N - a).choose w : ℝ)) := by ring
      _ = (4 : ℝ) ^ t * ε * ((2 * N).choose b : ℝ) * b.choose a := by rw [hid]; ring
  exact le_of_mul_le_mul_right hmain hCa

end SpreadMatchCircuit.Matching.Dev.L12

namespace SpreadMatchCircuit.Matching

open Finset Dev.L12

theorem chk_lemma_12 :
    ∃ α : ℝ, 0 < α ∧
      ∀ (N k b : ℕ) (t ε r : ℝ), 1 ≤ k → k ≤ N → b < k →
        t ≤ (b : ℝ) / 100 → 0 < ε →
        α * (2 * t + Real.log (1 / ε) ^ 2) * (3 * (2 * (N : ℝ)) / (b : ℝ)) ^ 2 ≤ r →
        ∀ (ord : LinearOrder (Finset (Edge (2 * N)))) (G : AndGate N), G.SizeBounded t →
          uniformProb (Finset.powersetCard b (Finset.univ : Finset (Fin (2 * N))))
            (fun W => incident W ∈ G.newNeg b (G.algorithm1 ord k r t))
            ≤ (4 : ℝ) ^ t * ε := by
  obtain ⟨α, hα, h5⟩ := lemma_5
  refine ⟨α, hα, ?_⟩
  intro N k b t ε r hk1 hkN hbk htb hε hr ord G hG
  have h4t0 : 0 < (4 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  by_cases ht1 : t < 1
  · have h0 : uniformProb (powersetCard b (univ : Finset (Fin (2 * N))))
        (fun W => incident W ∈ G.newNeg b (G.algorithm1 ord k r t)) ≤ 0 := by
      by_contra hpos
      push Not at hpos
      obtain ⟨W, -, hW⟩ := exists_of_uniformProb_pos _ _ hpos
      exact small_t G ord k r t ht1 hG b W hW
    exact h0.trans (by positivity)
  push Not at ht1
  by_cases hεh : 1 / 2 ≤ ε
  · have h4 : (4 : ℝ) ≤ 4 ^ t := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) ht1
      simpa using this
    calc _ ≤ (1 : ℝ) := uniformProb_le_one _ _
      _ ≤ 4 ^ t * ε := by nlinarith
  push Not at hεh
  have hmain := main_case hα h5 N k b t ε r hk1 hkN hbk htb hε hεh ht1 hr ord G hG
  rw [uniformProb_eq, card_powersetCard, card_univ, Fintype.card_fin]
  have hC : (0 : ℝ) < (2 * N).choose b := by exact_mod_cast Nat.choose_pos (by omega)
  rw [div_le_iff₀ hC]
  exact hmain

end SpreadMatchCircuit.Matching
end

theorem solution : type_of% @SpreadMatchCircuit.Matching.chk_lemma_12 := @SpreadMatchCircuit.Matching.chk_lemma_12
