-- Prove2me | solution 1 for TriangleFreeSegments.Probes.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T11:27:16.016225+00:00
-- url     : https://prove2.me/submissions/fb1c5a0f-5b35-4f31-ba94-0941b78c92f3

import Mathlib
import Definitions.Def_TriangleFreeSegments_Probes_Setting

-- Complete module: SPProof/SegmentBasics.lean

namespace TriangleFreeSegments.Probes.SPFresh

abbrev Endpoints := (ℝ × ℝ) × (ℝ × ℝ)

def Oriented (e : Endpoints) : Prop := e.1.2 < e.2.2

noncomputable def xAt (e : Endpoints) (y : ℝ) : ℝ :=
  e.1.1 + (y - e.1.2) / (e.2.2 - e.1.2) * (e.2.1 - e.1.1)

def Crosses (e : Endpoints) (R : Rect) (P : ProbeData) : Prop :=
  e.1.2 < P.b' ∧ P.d' < e.2.2 ∧
    ∀ y ∈ Set.Icc P.b' P.d', P.a' < xAt e y ∧ xAt e y < R.c

theorem oriented_ne {e : Endpoints} (he : Oriented e) : e.1 ≠ e.2 := by
  intro h
  exact (ne_of_lt he) (congrArg Prod.snd h)

theorem continuous_xAt (e : Endpoints) : Continuous (xAt e) := by
  unfold xAt
  fun_prop

@[simp] theorem xAt_lower (e : Endpoints) : xAt e e.1.2 = e.1.1 := by
  simp [xAt]

theorem xAt_upper {e : Endpoints} (he : Oriented e) : xAt e e.2.2 = e.2.1 := by
  have hn : e.2.2 - e.1.2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt he)
  simp [xAt, hn]

theorem xAt_affine {e : Endpoints} (he : Oriented e) (t : ℝ) :
    xAt e ((1 - t) * e.1.2 + t * e.2.2) = (1 - t) * e.1.1 + t * e.2.1 := by
  have hn : e.2.2 - e.1.2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt he)
  unfold xAt
  field_simp [hn]
  ring

theorem mem_seg_iff {e : Endpoints} (he : Oriented e) (p : ℝ × ℝ) :
    p ∈ seg e ↔ p.2 ∈ Set.Icc e.1.2 e.2.2 ∧ p.1 = xAt e p.2 := by
  rw [seg, segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · change e.1.2 ≤ (1 - t) * e.1.2 + t * e.2.2 ∧
        (1 - t) * e.1.2 + t * e.2.2 ≤ e.2.2
      have he' : e.1.2 < e.2.2 := he
      constructor <;> nlinarith [he', ht.1, ht.2]
    · exact (xAt_affine he t).symm
  · rintro ⟨hy, hx⟩
    let t := (p.2 - e.1.2) / (e.2.2 - e.1.2)
    have hd : 0 < e.2.2 - e.1.2 := sub_pos.mpr he
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hy.1) hd.le
      · apply (div_le_one hd).mpr
        linarith [hy.2]
    refine ⟨t, ht, ?_⟩
    apply Prod.ext
    · change (1 - t) * e.1.1 + t * e.2.1 = p.1
      rw [hx]
      dsimp [xAt, t]
      ring
    · change (1 - t) * e.1.2 + t * e.2.2 = p.2
      dsimp [t]
      field_simp [ne_of_gt hd]
      ring

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/SharedBasics.lean

open Set
open scoped BigOperators

namespace TriangleFreeSegments.Probes.SPFresh

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/ColorSets.lean

namespace TriangleFreeSegments.Probes.SPFresh

variable {α : Type*} [DecidableEq α]

theorem color_union_large (X Y : Finset α) (k : ℕ)
    (hX : k ≤ X.card) (hY : k ≤ Y.card) (hne : X ≠ Y) :
    k + 1 ≤ (X ∪ Y).card := by
  by_contra h
  have hu : (X ∪ Y).card ≤ k := by omega
  have hx : X = X ∪ Y := Finset.eq_of_subset_of_card_le Finset.subset_union_left (hu.trans hX)
  have hy : Y = X ∪ Y := Finset.eq_of_subset_of_card_le Finset.subset_union_right (hu.trans hY)
  exact hne (hx.trans hy.symm)

theorem color_insert_large (X : Finset α) (a : α) (k : ℕ)
    (hX : k ≤ X.card) (ha : a ∉ X) : k + 1 ≤ (insert a X).card := by
  rw [Finset.card_insert_of_notMem ha]
  omega

theorem cliqueFree_three_iff {I : Type*} (G : SimpleGraph I) :
    G.CliqueFree 3 ↔ ∀ a b c, G.Adj a b → G.Adj a c → ¬ G.Adj b c := by
  classical
  constructor
  · intro h a b c hab hac hbc
    exact h {a,b,c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)
  · intro h s hs
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact h a b c hab hac hbc

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/Configuration.lean

open Set

namespace TriangleFreeSegments.Probes.SPFresh

def ValidProbe (R : Rect) (P : ProbeData) : Prop :=
  R.a < P.a' ∧ P.a' < R.c ∧ R.b < P.b' ∧ P.b' < P.d' ∧ P.d' < R.d

structure Configuration (k : ℕ) (R : Rect) (I J : Type)
    [Fintype I] [Fintype J] [DecidableEq I] where
  e : I → Endpoints
  pr : J → ProbeData
  hits : J → Finset I
  oriented : ∀ i, Oriented (e i)
  inside : ∀ i, seg (e i) ⊆ R.inner
  distinct : Function.Injective (fun i => seg (e i))
  triangleFree : (interGraph (fun i => seg (e i))).CliqueFree 3
  valid : ∀ j, ValidProbe R (pr j)
  hit_nonempty : ∀ j, (hits j).Nonempty
  crosses : ∀ j i, i ∈ hits j → Crosses (e i) R (pr j)
  misses : ∀ j i, i ∉ hits j → Disjoint (seg (e i)) (probeRect R (pr j))
  independent : ∀ j i i', i ∈ hits j → i' ∈ hits j → i ≠ i' →
    Disjoint (seg (e i)) (seg (e i'))
  separated : Pairwise fun j j' => Disjoint (probeRect R (pr j)) (probeRect R (pr j'))
  colorful : ∀ (c : ℕ) (φ : I → Fin c),
    (∀ i i', (interGraph (fun i => seg (e i))).Adj i i' → φ i ≠ φ i') →
    ∃ j, k ≤ ((hits j).image φ).card

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/RectBasics.lean

namespace TriangleFreeSegments.Probes.SPFresh

def rectClosed (R : Rect) : Set (ℝ × ℝ) := Set.Icc R.a R.c ×ˢ Set.Icc R.b R.d

theorem inner_subset_closed (R : Rect) : R.inner ⊆ rectClosed R := by
  intro x hx
  exact ⟨⟨hx.1.1.le,hx.1.2.le⟩,⟨hx.2.1.le,hx.2.2.le⟩⟩

theorem probe_bands_disjoint {R : Rect} {P Q : ProbeData}
    (hP : P.a' ≤ R.c) (hQ : Q.a' ≤ R.c)
    (h : Disjoint (probeRect R P) (probeRect R Q)) :
    Disjoint (Set.Icc P.b' P.d') (Set.Icc Q.b' Q.d') := by
  apply Set.disjoint_left.mpr
  intro y hy hy'
  have hp : (R.c,y) ∈ probeRect R P := ⟨⟨hP,le_rfl⟩,hy⟩
  exact Set.disjoint_left.mp h hp ⟨⟨hQ,le_rfl⟩,hy'⟩

theorem disjoint_of_band_subsets {S T : Set (ℝ × ℝ)} {b d b' d' : ℝ}
    (hS : ∀x∈S,x.2∈Set.Icc b d) (hT : ∀x∈T,x.2∈Set.Icc b' d')
    (h : Disjoint (Set.Icc b d) (Set.Icc b' d')) : Disjoint S T := by
  exact Set.disjoint_left.mpr (fun x hx hy => Set.disjoint_left.mp h (hS x hx) (hT x hy))

theorem probe_subset_of_bounds {R T : Rect} {P Q : ProbeData}
    (ha : P.a' ≤ Q.a') (hc : T.c ≤ R.c) (hb : P.b' ≤ Q.b') (hd : Q.d' ≤ P.d') :
    probeRect T Q ⊆ probeRect R P := by
  intro x hx
  exact ⟨⟨ha.trans hx.1.1,hx.1.2.trans hc⟩,⟨hb.trans hx.2.1,hx.2.2.trans hd⟩⟩

theorem disjoint_ne {S T : Set (ℝ × ℝ)} (h : Disjoint S T) (hne : S.Nonempty) : S ≠ T := by
  intro he
  obtain ⟨x,hx⟩ := hne
  exact Set.disjoint_left.mp h hx (he ▸ hx)

theorem seg_nonempty (e : Endpoints) : (seg e).Nonempty := ⟨e.1,left_mem_segment _ _ _⟩

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/CrossingGeometry.lean

namespace TriangleFreeSegments.Probes.SPFresh

theorem crossing_point {e : Endpoints} {R : Rect} {P : ProbeData}
    (he : Oriented e) (hc : Crosses e R P) {y : ℝ} (hy : y ∈ Set.Icc P.b' P.d') :
    (xAt e y, y) ∈ seg e ∩ probeRect R P := by
  refine ⟨(mem_seg_iff he _).mpr ⟨⟨?_, ?_⟩, rfl⟩, ?_⟩
  · exact hc.1.le.trans hy.1
  · exact hy.2.trans hc.2.1.le
  · exact ⟨⟨(hc.2.2 y hy).1.le, (hc.2.2 y hy).2.le⟩, hy⟩

theorem crossing_nonempty {e : Endpoints} {R : Rect} {P : ProbeData}
    (he : Oriented e) (hc : Crosses e R P) (hp : P.b' ≤ P.d') :
    (seg e ∩ probeRect R P).Nonempty :=
  ⟨_, crossing_point he hc ⟨le_rfl, hp⟩⟩

theorem crossing_left_disjoint {e : Endpoints} {R : Rect} {P : ProbeData}
    (he : Oriented e) (hc : Crosses e R P) : Disjoint (seg e) (leftEdge P) := by
  rw [Set.disjoint_left]
  intro p hp hl
  have hx := (mem_seg_iff he p).mp hp
  have hx' : p.1 = P.a' := Set.mem_singleton_iff.mp hl.1
  have hs := (hc.2.2 p.2 hl.2).1
  rw [← hx.2, hx'] at hs
  exact (lt_irrefl _) hs

theorem crossing_endpoints_outside {e : Endpoints} {R : Rect} {P : ProbeData}
    (hc : Crosses e R P) : e.1 ∉ probeRect R P ∧ e.2 ∉ probeRect R P := by
  constructor
  · intro hp
    exact (not_le_of_gt hc.1) hp.2.1
  · intro hp
    exact (not_le_of_gt hc.2.1) hp.2.2

theorem diagonal_oriented {R : Rect} {P : ProbeData} (hp : P.b' < P.d') :
    Oriented (diag R P) := hp

theorem diagonal_subset_probe {R : Rect} {P : ProbeData}
    (hx : P.a' ≤ R.c) (hy : P.b' ≤ P.d') : seg (diag R P) ⊆ probeRect R P := by
  exact ((convex_Icc P.a' R.c).prod (convex_Icc P.b' P.d')).segment_subset
    ⟨⟨le_rfl, hx⟩, ⟨le_rfl, hy⟩⟩ ⟨⟨hx, le_rfl⟩, ⟨hy, le_rfl⟩⟩

theorem diagonal_meets_crossing {e : Endpoints} {R : Rect} {P : ProbeData}
    (he : Oriented e) (hc : Crosses e R P) (hp : P.b' < P.d') :
    (seg e ∩ seg (diag R P)).Nonempty := by
  let f := fun y => xAt e y - xAt (diag R P) y
  have hf : Continuous f := (continuous_xAt e).sub (continuous_xAt (diag R P))
  have hb : 0 < f P.b' := by
    have hh := (hc.2.2 P.b' ⟨le_rfl, hp.le⟩).1
    change 0 < xAt e P.b' - xAt (diag R P) (diag R P).1.2
    rw [xAt_lower]
    exact sub_pos.mpr hh
  have hd : f P.d' < 0 := by
    have hh := (hc.2.2 P.d' ⟨hp.le, le_rfl⟩).2
    change xAt e P.d' - xAt (diag R P) (diag R P).2.2 < 0
    rw [xAt_upper (diagonal_oriented hp)]
    exact sub_neg.mpr hh
  obtain ⟨y, hy, hz⟩ := intermediate_value_Icc' hp.le hf.continuousOn ⟨hd.le, hb.le⟩
  have heq : xAt e y = xAt (diag R P) y := sub_eq_zero.mp hz
  refine ⟨(xAt e y, y), (crossing_point he hc hy).1, ?_⟩
  exact (mem_seg_iff (diagonal_oriented hp) _).mpr ⟨hy, heq⟩

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/StepGraph.lean

namespace TriangleFreeSegments.Probes.SPFresh

abbrev StepIndex (I J : Type) := I ⊕ ((J × I) ⊕ (J × J))

def stepAdj {I J : Type} (G : SimpleGraph I) (Gs : J → SimpleGraph I)
    (H : J → J → Finset I) : StepIndex I J → StepIndex I J → Prop
  | .inl i, .inl i' => G.Adj i i'
  | .inr (.inl (p,i)), .inr (.inl (p',i')) => p=p' ∧ (Gs p).Adj i i'
  | .inr (.inl (p,i)), .inr (.inr (p',q)) => p=p' ∧ i∈H p q
  | .inr (.inr (p,q)), .inr (.inl (p',i)) => p=p' ∧ i∈H p q
  | _, _ => False

def stepGraph {I J : Type} (G : SimpleGraph I) (Gs : J → SimpleGraph I)
    (H : J → J → Finset I) : SimpleGraph (StepIndex I J) where
  Adj := stepAdj G Gs H
  symm := by
    constructor
    intro a b
    rcases a with a | (⟨p,a⟩ | ⟨p,a⟩) <;>
      rcases b with b | (⟨q,b⟩ | ⟨q,b⟩) <;> simp only [stepAdj, false_implies]
    · exact fun h => h.symm
    · rintro ⟨rfl,h⟩; exact ⟨rfl,h.symm⟩
    · rintro ⟨rfl,h⟩; exact ⟨rfl,h⟩
    · rintro ⟨rfl,h⟩; exact ⟨rfl,h⟩
  loopless := by
    constructor
    intro a
    rcases a with a | (⟨p,a⟩ | ⟨p,a⟩) <;> simp [stepAdj]

theorem stepGraph_triangleFree {I J : Type} (G : SimpleGraph I) (Gs : J → SimpleGraph I)
    (H : J → J → Finset I) (hG : G.CliqueFree 3) (hGs : ∀p,(Gs p).CliqueFree 3)
    (hH : ∀p q i j,i∈H p q → j∈H p q → ¬(Gs p).Adj i j) :
    (stepGraph G Gs H).CliqueFree 3 := by
  apply (cliqueFree_three_iff _).mpr
  intro a b c hab hac hbc
  rcases a with a | (⟨p,a⟩ | ⟨p,a⟩) <;>
    rcases b with b | (⟨q,b⟩ | ⟨q,b⟩) <;>
    rcases c with c | (⟨r,c⟩ | ⟨r,c⟩) <;>
    simp only [stepGraph, stepAdj] at hab hac hbc
  · exact (cliqueFree_three_iff G).mp hG a b c hab hac hbc
  · rcases hab with ⟨rfl,hab⟩; rcases hac with ⟨rfl,hac⟩
    exact (cliqueFree_three_iff (Gs p)).mp (hGs p) a b c hab hac hbc.2
  · rcases hab with ⟨rfl,hab⟩; rcases hac with ⟨rfl,hac⟩
    exact hH p c a b hac hbc.2 hab
  · rcases hab with ⟨rfl,hab⟩; rcases hac with ⟨rfl,hac⟩
    exact hH p b a c hab hbc.2 hac
  · rcases hab with ⟨rfl,hab⟩; rcases hac with ⟨rfl,hac⟩
    exact hH p a b c hab hac hbc.2

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/StepColors.lean

namespace TriangleFreeSegments.Probes.SPFresh

def oldIndex {I J : Type} (i : I) : StepIndex I J := .inl i
def copyIndex {I J : Type} (p : J) (i : I) : StepIndex I J := .inr (.inl (p,i))
def diagonalIndex {I J : Type} (p q : J) : StepIndex I J := .inr (.inr (p,q))

noncomputable def stepHits {I J : Type} (H : J → Finset I) (Hs : J → J → Finset I)
    (p q : J) (upper : Bool) : Finset (StepIndex I J) := by
  classical
  exact (H p).image oldIndex ∪ if upper then {diagonalIndex p q} else (Hs p q).image (copyIndex p)

theorem step_colorful {I J : Type} [Fintype I]
    (G : SimpleGraph I) (Gs : J → SimpleGraph I) (H : J → Finset I) (Hs : J → J → Finset I)
    (k : ℕ)
    (hG : ∀c (φ:I→Fin c),(∀i j,G.Adj i j→φ i≠φ j)→∃p,k≤((H p).image φ).card)
    (hGs : ∀p c (φ:I→Fin c),(∀i j,(Gs p).Adj i j→φ i≠φ j)→∃q,k≤((Hs p q).image φ).card)
    (c : ℕ) (φ : StepIndex I J → Fin c)
    (hφ : ∀i j,(stepGraph G Gs Hs).Adj i j→φ i≠φ j) :
    ∃p q b,k+1≤((stepHits H Hs p q b).image φ).card := by
  classical
  obtain ⟨p,hp⟩ := hG c (φ ∘ oldIndex) (fun i j h => hφ _ _ h)
  obtain ⟨q,hq⟩ := hGs p c (φ ∘ copyIndex p) (fun i j h => hφ _ _ ⟨rfl,h⟩)
  let X := (H p).image (φ ∘ oldIndex)
  let Y := (Hs p q).image (φ ∘ copyIndex p)
  by_cases he : X = Y
  · have hn : φ (diagonalIndex p q) ∉ X := by
      rw [he]
      rintro hm
      obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp hm
      exact hφ (copyIndex p i) (diagonalIndex p q) ⟨rfl,hi⟩ hei
    refine ⟨p,q,true,?_⟩
    have hh := color_insert_large X (φ (diagonalIndex p q)) k hp hn
    simpa [stepHits, X, Finset.image_union, Finset.image_image, Function.comp_def,
      Finset.union_comm] using hh
  · refine ⟨p,q,false,?_⟩
    have hh := color_union_large X Y k hp hq he
    simpa [stepHits, X, Y, Finset.image_union, Finset.image_image, Function.comp_def] using hh

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/PlacedCopies.lean

namespace TriangleFreeSegments.Probes.SPFresh

structure RootLayout {k : ℕ} {R : Rect} {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq I]
    (C : Configuration k R I J) (T : J → Rect) : Prop where
  bounds : ∀p, (C.pr p).a' < (T p).a ∧ (T p).a < (T p).c ∧ (T p).c < R.c ∧
    (C.pr p).b' < (T p).b ∧ (T p).b < (T p).d ∧ (T p).d < (C.pr p).d'
  empty : ∀p i, Disjoint (seg (C.e i)) (rectClosed (T p))
  dominates : ∀p i,i∈C.hits p → ∀y∈Set.Icc (C.pr p).b' (C.pr p).d',
    (T p).c < xAt (C.e i) y

variable {k : ℕ} {R : Rect} {I J : Type}
  [Fintype I] [Fintype J] [DecidableEq I]
  {C : Configuration k R I J} {T : J → Rect}
  (L : RootLayout C T) (D : ∀p,Configuration k (T p) I J)

include L in
theorem root_subset_parent (p : J) : rectClosed (T p) ⊆ probeRect R (C.pr p) := by
  intro x hx
  have h := L.bounds p
  exact ⟨⟨h.1.le.trans hx.1.1,hx.1.2.trans h.2.2.1.le⟩,
    ⟨h.2.2.2.1.le.trans hx.2.1,hx.2.2.trans h.2.2.2.2.2.le⟩⟩

include L in
theorem root_subset_inside (p : J) : rectClosed (T p) ⊆ R.inner := by
  intro x hx
  have h := L.bounds p
  have hv := C.valid p
  exact ⟨⟨(hv.1.trans h.1).trans_le hx.1.1,hx.1.2.trans_lt h.2.2.1⟩,
    ⟨(hv.2.2.1.trans h.2.2.2.1).trans_le hx.2.1,
      hx.2.2.trans_lt (h.2.2.2.2.2.trans hv.2.2.2.2)⟩⟩

theorem copy_subset_root (p : J) (i : I) : seg ((D p).e i) ⊆ rectClosed (T p) :=
  ((D p).inside i).trans (inner_subset_closed _)

theorem diagonal_subset_root (p q : J) : seg (diag (T p) ((D p).pr q)) ⊆ rectClosed (T p) := by
  apply (diagonal_subset_probe ((D p).valid q).2.1.le ((D p).valid q).2.2.2.1.le).trans
  intro x hx
  have hv := (D p).valid q
  exact ⟨⟨hv.1.le.trans hx.1.1,hx.1.2⟩,⟨hv.2.2.1.le.trans hx.2.1,hx.2.2.trans hv.2.2.2.2.le⟩⟩

include L in
theorem roots_disjoint {p q : J} (hpq : p ≠ q) : Disjoint (rectClosed (T p)) (rectClosed (T q)) :=
  (C.separated hpq).mono (root_subset_parent L p) (root_subset_parent L q)

theorem copy_diagonal_iff (p q : J) (i : I) :
    (seg ((D p).e i) ∩ seg (diag (T p) ((D p).pr q))).Nonempty ↔ i∈(D p).hits q := by
  constructor
  · intro h
    by_contra hi
    exact Set.disjoint_left.mp ((D p).misses q i hi) h.choose_spec.1
      (diagonal_subset_probe ((D p).valid q).2.1.le ((D p).valid q).2.2.2.1.le h.choose_spec.2)
  · intro hi
    exact diagonal_meets_crossing ((D p).oriented i) ((D p).crosses q i hi)
      ((D p).valid q).2.2.2.1

theorem copy_ne_diagonal (p q : J) (i : I) :
    seg ((D p).e i) ≠ seg (diag (T p) ((D p).pr q)) := by
  intro he
  have hm : (diag (T p) ((D p).pr q)).2 ∈ seg ((D p).e i) := by
    rw [he]; exact right_mem_segment _ _ _
  have hh := ((D p).inside i hm).1.2
  exact (lt_irrefl (T p).c) hh

theorem diagonals_disjoint (p : J) {q q' : J} (hq : q ≠ q') :
    Disjoint (seg (diag (T p) ((D p).pr q))) (seg (diag (T p) ((D p).pr q'))) :=
  ((D p).separated hq).mono
    (diagonal_subset_probe ((D p).valid q).2.1.le ((D p).valid q).2.2.2.1.le)
    (diagonal_subset_probe ((D p).valid q').2.1.le ((D p).valid q').2.2.2.1.le)

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/StepSegments.lean

namespace TriangleFreeSegments.Probes.SPFresh

variable {k : ℕ} {R : Rect} {I J : Type}
  [Fintype I] [Fintype J] [DecidableEq I]
  (C : Configuration k R I J) (T : J → Rect)
  (D : ∀p,Configuration k (T p) I J)

def stepEndpoints : StepIndex I J → Endpoints
  | .inl i => C.e i
  | .inr (.inl (p,i)) => (D p).e i
  | .inr (.inr (p,q)) => diag (T p) ((D p).pr q)

theorem step_oriented (a : StepIndex I J) : Oriented (stepEndpoints C T D a) := by
  rcases a with i | (⟨p,i⟩ | ⟨p,q⟩)
  · exact C.oriented i
  · exact (D p).oriented i
  · exact diagonal_oriented ((D p).valid q).2.2.2.1

theorem step_inside (L : RootLayout C T) (a : StepIndex I J) :
    seg (stepEndpoints C T D a) ⊆ R.inner := by
  rcases a with i | (⟨p,i⟩ | ⟨p,q⟩)
  · exact C.inside i
  · exact (copy_subset_root D p i).trans (root_subset_inside L p)
  · exact (diagonal_subset_root D p q).trans (root_subset_inside L p)

theorem step_distinct (L : RootLayout C T) :
    Function.Injective (fun a => seg (stepEndpoints C T D a)) := by
  intro a b he
  rcases a with i | (⟨p,i⟩ | ⟨p,q⟩) <;>
    rcases b with i' | (⟨p',i'⟩ | ⟨p',q'⟩)
  · exact congrArg Sum.inl (C.distinct he)
  · exact False.elim (disjoint_ne ((L.empty p' i).mono_right (copy_subset_root D p' i'))
      (seg_nonempty _) he)
  · exact False.elim (disjoint_ne ((L.empty p' i).mono_right (diagonal_subset_root D p' q'))
      (seg_nonempty _) he)
  · exact False.elim (disjoint_ne ((L.empty p i').mono_right (copy_subset_root D p i))
      (seg_nonempty _) he.symm)
  · by_cases hp : p=p'
    · subst p'; exact congrArg (copyIndex p) ((D p).distinct he)
    · exact False.elim (disjoint_ne ((roots_disjoint L hp).mono
        (copy_subset_root D p i) (copy_subset_root D p' i')) (seg_nonempty _) he)
  · by_cases hp : p=p'
    · subst p'; exact False.elim (copy_ne_diagonal D p q' i he)
    · exact False.elim (disjoint_ne ((roots_disjoint L hp).mono
        (copy_subset_root D p i) (diagonal_subset_root D p' q')) (seg_nonempty _) he)
  · exact False.elim (disjoint_ne ((L.empty p i').mono_right (diagonal_subset_root D p q))
      (seg_nonempty _) he.symm)
  · by_cases hp : p=p'
    · subst p'; exact False.elim (copy_ne_diagonal D p q i' he.symm)
    · exact False.elim (disjoint_ne ((roots_disjoint L hp).mono
        (diagonal_subset_root D p q) (copy_subset_root D p' i')) (seg_nonempty _) he)
  · by_cases hp : p=p'
    · subst p'
      by_cases hq : q=q'
      · subst q'; rfl
      · exact False.elim (disjoint_ne (diagonals_disjoint D p hq) (seg_nonempty _) he)
    · exact False.elim (disjoint_ne ((roots_disjoint L hp).mono
        (diagonal_subset_root D p q) (diagonal_subset_root D p' q')) (seg_nonempty _) he)

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/StepIncidence.lean

namespace TriangleFreeSegments.Probes.SPFresh

variable {k : ℕ} {R : Rect} {I J : Type}
  [Fintype I] [Fintype J] [DecidableEq I]
  (C : Configuration k R I J) (T : J → Rect)
  (D : ∀p,Configuration k (T p) I J) (L : RootLayout C T)

include L in
theorem step_graph_eq : interGraph (fun a => seg (stepEndpoints C T D a)) =
    stepGraph (interGraph (fun i => seg (C.e i)))
      (fun p => interGraph (fun i => seg ((D p).e i))) (fun p => (D p).hits) := by
  classical
  ext a b
  rcases a with i | (⟨p,i⟩ | ⟨p,q⟩) <;>
    rcases b with i' | (⟨p',i'⟩ | ⟨p',q'⟩)
  · simp [interGraph,stepEndpoints,stepGraph,stepAdj]
  · change (_ ∧ (seg (C.e i) ∩ seg ((D p').e i')).Nonempty) ↔ False
    constructor
    · rintro ⟨_,x,hx,hy⟩
      exact Set.disjoint_left.mp (L.empty p' i) hx (copy_subset_root D p' i' hy)
    · exact False.elim
  · change (_ ∧ (seg (C.e i) ∩ seg (diag (T p') ((D p').pr q'))).Nonempty) ↔ False
    constructor
    · rintro ⟨_,x,hx,hy⟩
      exact Set.disjoint_left.mp (L.empty p' i) hx (diagonal_subset_root D p' q' hy)
    · exact False.elim
  · change (_ ∧ (seg ((D p).e i) ∩ seg (C.e i')).Nonempty) ↔ False
    constructor
    · rintro ⟨_,x,hx,hy⟩
      exact Set.disjoint_left.mp (L.empty p i') hy (copy_subset_root D p i hx)
    · exact False.elim
  · by_cases hp : p=p'
    · subst p'
      simp [interGraph,stepEndpoints,stepGraph,stepAdj]
    · change (_ ∧ (seg ((D p).e i) ∩ seg ((D p').e i')).Nonempty) ↔ p=p' ∧ _
      constructor
      · rintro ⟨_,x,hx,hy⟩
        exact False.elim (Set.disjoint_left.mp (roots_disjoint L hp)
          (copy_subset_root D p i hx) (copy_subset_root D p' i' hy))
      · intro h; exact False.elim (hp h.1)
  · by_cases hp : p=p'
    · subst p'
      simpa [interGraph,stepEndpoints,stepGraph,stepAdj] using copy_diagonal_iff D p q' i
    · change (_ ∧ (seg ((D p).e i) ∩ seg (diag (T p') ((D p').pr q'))).Nonempty) ↔ p=p' ∧ _
      constructor
      · rintro ⟨_,x,hx,hy⟩
        exact False.elim (Set.disjoint_left.mp (roots_disjoint L hp)
          (copy_subset_root D p i hx) (diagonal_subset_root D p' q' hy))
      · intro h; exact False.elim (hp h.1)
  · change (_ ∧ (seg (diag (T p) ((D p).pr q)) ∩ seg (C.e i')).Nonempty) ↔ False
    constructor
    · rintro ⟨_,x,hx,hy⟩
      exact Set.disjoint_left.mp (L.empty p i') hy (diagonal_subset_root D p q hx)
    · exact False.elim
  · by_cases hp : p=p'
    · subst p'
      simpa [interGraph,stepEndpoints,stepGraph,stepAdj,Set.inter_comm] using copy_diagonal_iff D p q i'
    · change (_ ∧ (seg (diag (T p) ((D p).pr q)) ∩ seg ((D p').e i')).Nonempty) ↔ p=p' ∧ _
      constructor
      · rintro ⟨_,x,hx,hy⟩
        exact False.elim (Set.disjoint_left.mp (roots_disjoint L hp)
          (diagonal_subset_root D p q hx) (copy_subset_root D p' i' hy))
      · intro h; exact False.elim (hp h.1)
  · change (_ ∧ (seg (diag (T p) ((D p).pr q)) ∩ seg (diag (T p') ((D p').pr q'))).Nonempty) ↔ False
    constructor
    · rintro ⟨hne,x,hx,hy⟩
      by_cases hp : p=p'
      · subst p'
        have hq : q≠q' := by intro h; subst q'; exact hne rfl
        exact Set.disjoint_left.mp (diagonals_disjoint D p hq) hx hy
      · exact Set.disjoint_left.mp (roots_disjoint L hp)
          (diagonal_subset_root D p q hx) (diagonal_subset_root D p' q' hy)
    · exact False.elim

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/StepIndependent.lean

namespace TriangleFreeSegments.Probes.SPFresh

theorem stepHits_independent {I J : Type}
    (G : SimpleGraph I) (Gs : J → SimpleGraph I) (H : J → Finset I) (Hs : J → J → Finset I)
    (hH : ∀p i j,i∈H p→j∈H p→¬G.Adj i j)
    (hHs : ∀p q i j,i∈Hs p q→j∈Hs p q→¬(Gs p).Adj i j)
    (p q : J) (b : Bool) (u v : StepIndex I J)
    (hu : u∈stepHits H Hs p q b) (hv : v∈stepHits H Hs p q b) :
    ¬(stepGraph G Gs Hs).Adj u v := by
  classical
  cases b
  · simp only [stepHits, Bool.false_eq_true, ↓reduceIte, Finset.mem_union,
      Finset.mem_image] at hu hv
    rcases hu with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩ <;>
      rcases hv with ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩
    · exact hH p i j hi hj
    · simp [stepGraph,stepAdj,oldIndex,copyIndex]
    · simp [stepGraph,stepAdj,oldIndex,copyIndex]
    · intro h; exact hHs p q i j hi hj h.2
  · simp only [stepHits, ↓reduceIte, Finset.mem_union,
      Finset.mem_image, Finset.mem_singleton] at hu hv
    rcases hu with ⟨i,hi,rfl⟩ | rfl <;>
      rcases hv with ⟨j,hj,rfl⟩ | rfl
    · exact hH p i j hi hj
    · simp [stepGraph,stepAdj,oldIndex,diagonalIndex]
    · simp [stepGraph,stepAdj,oldIndex,diagonalIndex]
    · simp [stepGraph,diagonalIndex]

theorem stepHits_nonempty {I J : Type} (H : J → Finset I) (Hs : J → J → Finset I)
    (hH : ∀p,(H p).Nonempty) (p q : J) (b : Bool) : (stepHits H Hs p q b).Nonempty := by
  classical
  obtain ⟨i,hi⟩ := hH p
  exact ⟨oldIndex i,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)⟩

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/AssembleStep.lean

namespace TriangleFreeSegments.Probes.SPFresh

noncomputable def assembleStep {k : ℕ} {R : Rect} {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (C : Configuration k R I J) (T : J → Rect)
    (D : ∀p,Configuration k (T p) I J) (L : RootLayout C T)
    (pr : J → J → Bool → ProbeData)
    (hv : ∀p q b,ValidProbe R (pr p q b))
    (hc : ∀p q b i,i∈stepHits C.hits (fun p => (D p).hits) p q b →
      Crosses (stepEndpoints C T D i) R (pr p q b))
    (hm : ∀p q b i,i∉stepHits C.hits (fun p => (D p).hits) p q b →
      Disjoint (seg (stepEndpoints C T D i)) (probeRect R (pr p q b)))
    (hs : Pairwise fun j j' : J×J×Bool =>
      Disjoint (probeRect R (pr j.1 j.2.1 j.2.2)) (probeRect R (pr j'.1 j'.2.1 j'.2.2))) :
    Configuration (k+1) R (StepIndex I J) (J×J×Bool) := by
  have hH : ∀p i j,i∈C.hits p→j∈C.hits p→¬(interGraph (fun i=> seg (C.e i))).Adj i j := by
    intro p i j hi hj ha
    obtain ⟨x,hx,hy⟩ := ha.2
    exact Set.disjoint_left.mp (C.independent p i j hi hj ha.1) hx hy
  have hHs : ∀p q i j,i∈(D p).hits q→j∈(D p).hits q→
      ¬(interGraph (fun i=> seg ((D p).e i))).Adj i j := by
    intro p q i j hi hj ha
    obtain ⟨x,hx,hy⟩ := ha.2
    exact Set.disjoint_left.mp ((D p).independent q i j hi hj ha.1) hx hy
  refine { e := stepEndpoints C T D
           pr := fun j => pr j.1 j.2.1 j.2.2
           hits := fun j => stepHits C.hits (fun p => (D p).hits) j.1 j.2.1 j.2.2
           oriented := step_oriented C T D
           inside := step_inside C T D L
           distinct := step_distinct C T D L
           triangleFree := ?_
           valid := fun j => hv j.1 j.2.1 j.2.2
           hit_nonempty := fun j => stepHits_nonempty C.hits (fun p => (D p).hits)
             C.hit_nonempty j.1 j.2.1 j.2.2
           crosses := fun j => hc j.1 j.2.1 j.2.2
           misses := fun j => hm j.1 j.2.1 j.2.2
           independent := ?_
           separated := hs
           colorful := ?_ }
  · rw [step_graph_eq C T D L]
    exact stepGraph_triangleFree _ _ _ C.triangleFree (fun p => (D p).triangleFree) hHs
  · intro j i i' hi hi' hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hh := stepHits_independent _ _ C.hits (fun p => (D p).hits) hH hHs
      j.1 j.2.1 j.2.2 i i' hi hi'
    apply hh
    rw [←step_graph_eq C T D L]
    exact ⟨hne,⟨x,hx,hy⟩⟩
  · intro c φ hφ
    have hφ' : ∀i j,(stepGraph (interGraph (fun i=> seg (C.e i)))
        (fun p=>interGraph (fun i=> seg ((D p).e i))) (fun p=>(D p).hits)).Adj i j→φ i≠φ j := by
      rw [←step_graph_eq C T D L]
      exact hφ
    obtain ⟨p,q,b,h⟩ := step_colorful _ _ C.hits (fun p=>(D p).hits) k
      C.colorful (fun p=>(D p).colorful) c φ hφ'
    exact ⟨(p,q,b),h⟩

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/FiniteMargins.lean

open Filter Topology

namespace TriangleFreeSegments.Probes.SPFresh

theorem finite_strict_lower {I : Type*} (s : Finset I) (f : I → ℝ) (a : ℝ)
    (h : ∀ i ∈ s, a < f i) : ∃ b, a < b ∧ ∀ i ∈ s, b < f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨a + 1, by linarith, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨b, hab, hb⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨c, hac, hc⟩ := exists_between (lt_min hab (h i (Finset.mem_insert_self i s)))
    refine ⟨c, hac, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hc.trans_le (min_le_right _ _)
    · exact (hc.trans_le (min_le_left _ _)).trans (hb j hj)

theorem finite_strict_upper {I : Type*} (s : Finset I) (f : I → ℝ) (a : ℝ)
    (h : ∀ i ∈ s, f i < a) : ∃ b, b < a ∧ ∀ i ∈ s, f i < b := by
  obtain ⟨b, hb, hf⟩ := finite_strict_lower s (fun i => -f i) (-a)
    (fun i hi => neg_lt_neg (h i hi))
  refine ⟨-b, by linarith, ?_⟩
  intro i hi
  have := hf i hi
  linarith

theorem finite_continuous_strict {I : Type*} (s : Finset I) (f g : I → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) (hg : ∀ i ∈ s, Continuous (g i))
    (y : ℝ) (h : ∀ i ∈ s, f i y < g i y) :
    ∃ δ > 0, ∀ z, |z-y| < δ → ∀ i ∈ s, f i z < g i z := by
  have he : ∀ᶠ z in 𝓝 y, ∀ i ∈ s, f i z < g i z :=
    s.eventually_all.mpr (fun i hi =>
      ((hf i hi).continuousAt.eventually_lt (hg i hi).continuousAt (h i hi)))
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, fun z hz => hh ?_⟩
  simpa only [Real.dist_eq] using hz

/-- A common positive band width preserving arbitrary open conditions at both ends. -/
theorem thin_bands {b d : ℝ} (hbd : b < d) {P Q : ℝ → Prop}
    (hP : ∀ᶠ y in 𝓝 b, P y) (hQ : ∀ᶠ y in 𝓝 d, Q y) :
    ∃ ε > 0, b + 2*ε < d - 2*ε ∧
      (∀ y ∈ Set.Icc (b+ε) (b+2*ε), P y) ∧
      (∀ y ∈ Set.Icc (d-2*ε) (d-ε), Q y) := by
  obtain ⟨u, hu, hPu⟩ := Metric.eventually_nhds_iff.mp hP
  obtain ⟨v, hv, hQv⟩ := Metric.eventually_nhds_iff.mp hQ
  obtain ⟨ε, he, he'⟩ := exists_between
    (show (0 : ℝ) < min (u/3) (min (v/3) ((d-b)/5)) by positivity)
  have heu : ε < u/3 := he'.trans_le (min_le_left _ _)
  have hev : ε < v/3 := he'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hed : ε < (d-b)/5 := he'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, he, by linarith, ?_, ?_⟩
  · intro y hy
    apply hPu
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.1])]
    linarith [hy.2]
  · intro y hy
    apply hQv
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hy.2])]
    linarith [hy.1]

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/DiagonalBands.lean

open Filter Topology

namespace TriangleFreeSegments.Probes.SPFresh

theorem diagonal_bands {I : Type*} (e : I → Endpoints) (H : Finset I)
    (R : Rect) (P : ProbeData) (hx : P.a' < R.c) (hy : P.b' < P.d')
    (hc : ∀ i ∈ H, Crosses (e i) R P) :
    ∃ l u ε : ℝ, P.a' < l ∧ l < R.c ∧ P.a' < u ∧ u < R.c ∧ 0 < ε ∧
      P.b'+2*ε < P.d'-2*ε ∧
      (∀ y ∈ Set.Icc (P.b'+ε) (P.b'+2*ε),
        xAt (diag R P) y < l ∧ ∀ i ∈ H, l < xAt (e i) y) ∧
      (∀ y ∈ Set.Icc (P.d'-2*ε) (P.d'-ε),
        u < xAt (diag R P) y ∧ ∀ i ∈ H, xAt (e i) y < u) := by
  obtain ⟨l₀, hl₀, hlH⟩ := finite_strict_lower H (fun i => xAt (e i) P.b') P.a'
    (fun i hi => ((hc i hi).2.2 P.b' ⟨le_rfl, hy.le⟩).1)
  obtain ⟨l, hl, hl'⟩ := exists_between (lt_min hx hl₀)
  have hlR := hl'.trans_le (min_le_left _ _)
  have hlH' : ∀ i ∈ H, l < xAt (e i) P.b' :=
    fun i hi => (hl'.trans_le (min_le_right _ _)).trans (hlH i hi)
  obtain ⟨u₀, hu₀, huH⟩ := finite_strict_upper H (fun i => xAt (e i) P.d') R.c
    (fun i hi => ((hc i hi).2.2 P.d' ⟨hy.le, le_rfl⟩).2)
  obtain ⟨u, hu', hu⟩ := exists_between (max_lt hx hu₀)
  have hPu := (le_max_left _ _).trans_lt hu'
  have huH' : ∀ i ∈ H, xAt (e i) P.d' < u :=
    fun i hi => (huH i hi).trans ((le_max_right _ _).trans_lt hu')
  have hb : ∀ᶠ y in 𝓝 P.b', xAt (diag R P) y < l ∧ ∀ i ∈ H, l < xAt (e i) y := by
    have hd : xAt (diag R P) P.b' < l := by
      change xAt (diag R P) (diag R P).1.2 < l
      rw [xAt_lower]
      exact hl
    exact ((continuous_xAt (diag R P)).continuousAt.eventually_lt continuousAt_const hd).and
      (H.eventually_all.mpr (fun i hi => continuousAt_const.eventually_lt
        (continuous_xAt (e i)).continuousAt (hlH' i hi)))
  have ht : ∀ᶠ y in 𝓝 P.d', u < xAt (diag R P) y ∧ ∀ i ∈ H, xAt (e i) y < u := by
    have hd : u < xAt (diag R P) P.d' := by
      change u < xAt (diag R P) (diag R P).2.2
      rw [xAt_upper (diagonal_oriented hy)]
      exact hu
    exact (continuousAt_const.eventually_lt (continuous_xAt (diag R P)).continuousAt hd).and
      (H.eventually_all.mpr (fun i hi => (continuous_xAt (e i)).continuousAt.eventually_lt
        continuousAt_const (huH' i hi)))
  obtain ⟨ε, hε, hgap, hb', ht'⟩ := thin_bands hy hb ht
  exact ⟨l, u, ε, hl, hlR, hPu, hu, hε, hgap, hb', ht'⟩

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/ProbeTransfer.lean

namespace TriangleFreeSegments.Probes.SPFresh

theorem crosses_subband {e : Endpoints} {R T : Rect} {P Q : ProbeData}
    (h : Crosses e R P) (hb : P.b' ≤ Q.b') (hd : Q.d' ≤ P.d')
    (hr : R.c ≤ T.c)
    (hl : ∀ y ∈ Set.Icc Q.b' Q.d', Q.a' < xAt e y) : Crosses e T Q := by
  refine ⟨h.1.trans_le hb, hd.trans_lt h.2.1, ?_⟩
  intro y hy
  exact ⟨hl y hy, ((h.2.2 y ⟨hb.trans hy.1, hy.2.trans hd⟩).2).trans_le hr⟩

theorem segment_left_of_probe {e : Endpoints} {R : Rect} {P : ProbeData}
    (he : Oriented e) (hl : ∀ y ∈ Set.Icc P.b' P.d', xAt e y < P.a') :
    Disjoint (seg e) (probeRect R P) := by
  rw [Set.disjoint_left]
  intro p hs hp
  have h := hl p.2 hp.2
  rw [← ((mem_seg_iff he p).mp hs).2] at h
  exact (not_lt_of_ge hp.1.1) h

theorem misses_extended_probe {e : Endpoints} {T R : Rect} {P Q : ProbeData}
    (hi : seg e ⊆ T.inner) (hm : Disjoint (seg e) (probeRect T P))
    (ha : P.a' ≤ Q.a') (hb : P.b' ≤ Q.b') (hd : Q.d' ≤ P.d') :
    Disjoint (seg e) (probeRect R Q) := by
  rw [Set.disjoint_left]
  intro p hs hp
  apply Set.disjoint_left.mp hm hs
  exact ⟨⟨ha.trans hp.1.1, (hi hs).1.2.le⟩,
    ⟨hb.trans hp.2.1, hp.2.2.trans hd⟩⟩

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/LocalProbeSplit.lean

namespace TriangleFreeSegments.Probes.SPFresh

structure ProbeSplit {k : ℕ} {R : Rect} {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq I]
    (C : Configuration k R I J) (q : J) (S : Rect) where
  lower : ProbeData
  upper : ProbeData
  lower_left : (C.pr q).a' < lower.a' ∧ lower.a' < R.c
  upper_left : (C.pr q).a' < upper.a' ∧ upper.a' < R.c
  bands : (C.pr q).b' < lower.b' ∧ lower.b' < lower.d' ∧
    lower.d' < upper.b' ∧ upper.b' < upper.d' ∧ upper.d' < (C.pr q).d'
  hit_lower : ∀ i ∈ C.hits q, Crosses (C.e i) S lower
  hit_upper_miss : ∀ i ∈ C.hits q, Disjoint (seg (C.e i)) (probeRect S upper)
  nonhit_lower : ∀ i, i ∉ C.hits q → Disjoint (seg (C.e i)) (probeRect S lower)
  nonhit_upper : ∀ i, i ∉ C.hits q → Disjoint (seg (C.e i)) (probeRect S upper)
  diagonal_lower_miss : Disjoint (seg (diag R (C.pr q))) (probeRect S lower)
  diagonal_upper : Crosses (diag R (C.pr q)) S upper
  separated : Disjoint (probeRect S lower) (probeRect S upper)

theorem exists_probeSplit {k : ℕ} {R : Rect} {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq I]
    (C : Configuration k R I J) (q : J) (S : Rect) (hRS : R.c < S.c) :
    Nonempty (ProbeSplit C q S) := by
  have hv := C.valid q
  obtain ⟨l, u, ε, hl, hlR, hu, huR, he, hgap, hlow, hupp⟩ :=
    diagonal_bands C.e (C.hits q) R (C.pr q) hv.2.1 hv.2.2.2.1 (C.crosses q)
  let L : ProbeData := ⟨l, (C.pr q).b'+ε, (C.pr q).b'+2*ε⟩
  let U : ProbeData := ⟨u, (C.pr q).d'-2*ε, (C.pr q).d'-ε⟩
  have hLb : (C.pr q).b' < L.b' := by dsimp [L]; linarith
  have hLd : L.d' < (C.pr q).d' := by dsimp [L]; linarith
  have hUb : (C.pr q).b' < U.b' := by dsimp [U]; linarith
  have hUd : U.d' < (C.pr q).d' := by dsimp [U]; linarith
  refine ⟨{
    lower := L
    upper := U
    lower_left := ⟨hl, hlR⟩
    upper_left := ⟨hu, huR⟩
    bands := ?_
    hit_lower := ?_
    hit_upper_miss := ?_
    nonhit_lower := ?_
    nonhit_upper := ?_
    diagonal_lower_miss := ?_
    diagonal_upper := ?_
    separated := ?_ }⟩
  · dsimp [L, U]
    exact ⟨by linarith, by linarith, hgap, by linarith, by linarith⟩
  · intro i hi
    exact crosses_subband (C.crosses q i hi) hLb.le hLd.le hRS.le
      (fun y hy => (hlow y hy).2 i hi)
  · intro i hi
    exact segment_left_of_probe (C.oriented i) (fun y hy => (hupp y hy).2 i hi)
  · intro i hi
    exact misses_extended_probe (C.inside i) (C.misses q i hi) hl.le hLb.le hLd.le
  · intro i hi
    exact misses_extended_probe (C.inside i) (C.misses q i hi) hu.le hUb.le hUd.le
  · exact segment_left_of_probe (diagonal_oriented hv.2.2.2.1)
      (fun y hy => (hlow y hy).1)
  · refine ⟨hUb, hUd, ?_⟩
    intro y hy
    refine ⟨(hupp y hy).1, ?_⟩
    have hy' : y ∈ Set.Icc (C.pr q).b' (C.pr q).d' :=
      ⟨hUb.le.trans hy.1, hy.2.trans hUd.le⟩
    have hm := (mem_seg_iff (diagonal_oriented hv.2.2.2.1) (xAt (diag R (C.pr q)) y,y)).mpr
      ⟨hy', rfl⟩
    exact ((diagonal_subset_probe hv.2.1.le hv.2.2.2.1.le hm).1.2).trans_lt hRS
  · rw [Set.disjoint_left]
    intro p hp hq
    have hp' : p.2 ≤ (C.pr q).b'+2*ε := hp.2.2
    have hq' : (C.pr q).d'-2*ε ≤ p.2 := hq.2.1
    linarith

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/NewProbeGeometry.lean

namespace TriangleFreeSegments.Probes.SPFresh

variable {k : ℕ} {R : Rect} {I J : Type}
  [Fintype I] [Fintype J] [DecidableEq I]
  {C : Configuration k R I J} {T : J → Rect}
  (L : RootLayout C T) (D : ∀ p, Configuration k (T p) I J)
  (B : ∀ p q, ProbeSplit (D p) q R)

def newProbe (p q : J) (b : Bool) : ProbeData :=
  if b then (B p q).upper else (B p q).lower

theorem newProbe_left (p q : J) (b : Bool) :
    ((D p).pr q).a' < (newProbe D B p q b).a' ∧
      (newProbe D B p q b).a' < (T p).c := by
  cases b
  · exact (B p q).lower_left
  · exact (B p q).upper_left

theorem newProbe_band (p q : J) (b : Bool) :
    ((D p).pr q).b' < (newProbe D B p q b).b' ∧
      (newProbe D B p q b).b' < (newProbe D B p q b).d' ∧
      (newProbe D B p q b).d' < ((D p).pr q).d' := by
  have h := (B p q).bands
  cases b
  · exact ⟨h.1, h.2.1, h.2.2.1.trans (h.2.2.2.1.trans h.2.2.2.2)⟩
  · exact ⟨h.1.trans (h.2.1.trans h.2.2.1), h.2.2.2.1, h.2.2.2.2⟩

include L in
theorem newProbe_valid (p q : J) (b : Bool) : ValidProbe R (newProbe D B p q b) := by
  have h := L.bounds p
  have ho := C.valid p
  have hi := (D p).valid q
  have hx := newProbe_left D B p q b
  have hy := newProbe_band D B p q b
  exact ⟨ho.1.trans (h.1.trans (hi.1.trans hx.1)), hx.2.trans h.2.2.1,
    ho.2.2.1.trans (h.2.2.2.1.trans (hi.2.2.1.trans hy.1)), hy.2.1,
    hy.2.2.trans (hi.2.2.2.2.trans (h.2.2.2.2.2.trans ho.2.2.2.2))⟩

include L in
theorem newProbe_subset_parent (p q : J) (b : Bool) :
    probeRect R (newProbe D B p q b) ⊆ probeRect R (C.pr p) := by
  have h := L.bounds p
  have hi := (D p).valid q
  have hx := newProbe_left D B p q b
  have hy := newProbe_band D B p q b
  exact probe_subset_of_bounds (h.1.trans (hi.1.trans hx.1)).le le_rfl
    (h.2.2.2.1.trans (hi.2.2.1.trans hy.1)).le
    (hy.2.2.trans (hi.2.2.2.2.trans h.2.2.2.2.2)).le

include L in
theorem old_crosses_new (p q : J) (b : Bool) (i : I) (hi : i ∈ C.hits p) :
    Crosses (C.e i) R (newProbe D B p q b) := by
  have h := L.bounds p
  have hv := (D p).valid q
  have hx := newProbe_left D B p q b
  have hy := newProbe_band D B p q b
  have hb := (h.2.2.2.1.trans (hv.2.2.1.trans hy.1)).le
  have hd := (hy.2.2.trans (hv.2.2.2.2.trans h.2.2.2.2.2)).le
  apply crosses_subband (C.crosses p i hi) hb hd le_rfl
  intro y hyy
  exact hx.2.trans (L.dominates p i hi y ⟨hb.trans hyy.1, hyy.2.trans hd⟩)

include L in
theorem old_misses_new (p q : J) (b : Bool) (i : I) (hi : i ∉ C.hits p) :
    Disjoint (seg (C.e i)) (probeRect R (newProbe D B p q b)) :=
  (C.misses p i hi).mono_right (newProbe_subset_parent L D B p q b)

theorem different_inner_band {p q q' : J} (hqq : q ≠ q') (b b' : Bool) :
    Disjoint (probeRect R (newProbe D B p q b)) (probeRect R (newProbe D B p q' b')) := by
  have hb := probe_bands_disjoint ((D p).valid q).2.1.le ((D p).valid q').2.1.le
    ((D p).separated hqq)
  apply disjoint_of_band_subsets (b := ((D p).pr q).b') (d := ((D p).pr q).d')
    (b' := ((D p).pr q').b') (d' := ((D p).pr q').d') _ _ hb
  · intro x hx
    have h := newProbe_band D B p q b
    exact ⟨h.1.le.trans hx.2.1, hx.2.2.trans h.2.2.le⟩
  · intro x hx
    have h := newProbe_band D B p q' b'
    exact ⟨h.1.le.trans hx.2.1, hx.2.2.trans h.2.2.le⟩

include L in
theorem newProbe_separated : Pairwise (fun a a' : J × J × Bool =>
    Disjoint (probeRect R (newProbe D B a.1 a.2.1 a.2.2))
      (probeRect R (newProbe D B a'.1 a'.2.1 a'.2.2))) := by
  classical
  rintro ⟨p,q,b⟩ ⟨p',q',b'⟩ hne
  by_cases hp : p=p'
  · subst p'
    by_cases hq : q=q'
    · subst q'
      cases b <;> cases b'
      · exact False.elim (hne rfl)
      · exact (B p q).separated
      · exact (B p q).separated.symm
      · exact False.elim (hne rfl)
    · exact different_inner_band D B hq b b'
  · exact (C.separated hp).mono (newProbe_subset_parent L D B p q b)
      (newProbe_subset_parent L D B p' q' b')

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/NewProbeIncidence.lean

namespace TriangleFreeSegments.Probes.SPFresh

variable {k : ℕ} {R : Rect} {I J : Type}
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {C : Configuration k R I J} {T : J → Rect}
  (L : RootLayout C T) (D : ∀ p, Configuration k (T p) I J)
  (B : ∀ p q, ProbeSplit (D p) q R)

include L in
omit [DecidableEq J] in
theorem other_parent_misses_new {p p' : J} (hp : p' ≠ p) (q : J) (b : Bool)
    {Z : Set (ℝ × ℝ)} (hZ : Z ⊆ rectClosed (T p')) :
    Disjoint Z (probeRect R (newProbe D B p q b)) :=
  (C.separated hp).mono (hZ.trans (root_subset_parent L p'))
    (newProbe_subset_parent L D B p q b)

omit [DecidableEq J] in
theorem other_diagonal_misses_new {p q q' : J} (hq : q' ≠ q) (b : Bool) :
    Disjoint (seg (diag (T p) ((D p).pr q'))) (probeRect R (newProbe D B p q b)) := by
  have hb := probe_bands_disjoint ((D p).valid q').2.1.le ((D p).valid q).2.1.le
    ((D p).separated hq)
  apply disjoint_of_band_subsets (b := ((D p).pr q').b') (d := ((D p).pr q').d')
    (b' := ((D p).pr q).b') (d' := ((D p).pr q).d') _ _ hb
  · intro x hx
    exact (diagonal_subset_probe ((D p).valid q').2.1.le
      ((D p).valid q').2.2.2.1.le hx).2
  · intro x hx
    have h := newProbe_band D B p q b
    exact ⟨h.1.le.trans hx.2.1, hx.2.2.trans h.2.2.le⟩

include L in
omit [DecidableEq J] in
theorem step_crosses_new (p q : J) (b : Bool) (a : StepIndex I J)
    (ha : a ∈ stepHits C.hits (fun p => (D p).hits) p q b) :
    Crosses (stepEndpoints C T D a) R (newProbe D B p q b) := by
  rcases a with i | (⟨p',i⟩ | ⟨p',q'⟩)
  · have hi : i ∈ C.hits p := by
      cases b <;> simpa [stepHits, oldIndex, copyIndex, diagonalIndex] using ha
    exact old_crosses_new L D B p q b i hi
  · cases b
    · have hi : i ∈ (D p).hits q ∧ p = p' := by
        simpa [stepHits, oldIndex, copyIndex, diagonalIndex] using ha
      rcases hi with ⟨hi, hp⟩
      subst p'
      exact (B p q).hit_lower i hi
    · simp [stepHits, oldIndex, diagonalIndex] at ha
  · cases b
    · simp [stepHits, oldIndex, copyIndex] at ha
    · have hi : p'=p ∧ q'=q := by
        simpa [stepHits, oldIndex, copyIndex, diagonalIndex] using ha
      rcases hi with ⟨hp, hq⟩
      subst p'
      subst q'
      exact (B p q).diagonal_upper

include L in
theorem step_misses_new (p q : J) (b : Bool) (a : StepIndex I J)
    (ha : a ∉ stepHits C.hits (fun p => (D p).hits) p q b) :
    Disjoint (seg (stepEndpoints C T D a)) (probeRect R (newProbe D B p q b)) := by
  rcases a with i | (⟨p',i⟩ | ⟨p',q'⟩)
  · have hi : i ∉ C.hits p := by
      cases b <;> simpa [stepHits, oldIndex, copyIndex, diagonalIndex] using ha
    exact old_misses_new L D B p q b i hi
  · by_cases hp : p'=p
    · subst p'
      cases b
      · have hi : i ∉ (D p).hits q := by
          simpa [stepHits, oldIndex, copyIndex, diagonalIndex] using ha
        exact (B p q).nonhit_lower i hi
      · by_cases hi : i ∈ (D p).hits q
        · exact (B p q).hit_upper_miss i hi
        · exact (B p q).nonhit_upper i hi
    · exact other_parent_misses_new L D B hp q b (copy_subset_root D p' i)
  · by_cases hp : p'=p
    · subst p'
      by_cases hq : q'=q
      · subst q'
        cases b
        · exact (B p q).diagonal_lower_miss
        · simp [stepHits, oldIndex, diagonalIndex] at ha
      · exact other_diagonal_misses_new D B hq b
    · exact other_parent_misses_new L D B hp q b (diagonal_subset_root D p' q')

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/AffineBounds.lean

namespace TriangleFreeSegments.Probes.SPFresh

theorem xAt_sub (e : Endpoints) (y z : ℝ) :
    xAt e y - xAt e z = (y-z)*((e.2.1-e.1.1)/(e.2.2-e.1.2)) := by
  unfold xAt
  ring

theorem xAt_lower_bound (e : Endpoints) {b d a y : ℝ}
    (hb : a < xAt e b) (hd : a < xAt e d) (hy : y ∈ Set.Icc b d) :
    a < xAt e y := by
  by_cases hs : 0 ≤ (e.2.1-e.1.1)/(e.2.2-e.1.2)
  · have h := mul_nonneg (sub_nonneg.mpr hy.1) hs
    rw [← xAt_sub] at h
    linarith
  · have h := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hy.2) (le_of_not_ge hs)
    rw [← xAt_sub] at h
    linarith

theorem xAt_upper_bound (e : Endpoints) {b d a y : ℝ}
    (hb : xAt e b < a) (hd : xAt e d < a) (hy : y ∈ Set.Icc b d) :
    xAt e y < a := by
  by_cases hs : 0 ≤ (e.2.1-e.1.1)/(e.2.2-e.1.2)
  · have h := mul_nonneg (sub_nonneg.mpr hy.2) hs
    rw [← xAt_sub] at h
    linarith
  · have h := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hy.1) (le_of_not_ge hs)
    rw [← xAt_sub] at h
    linarith

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/EmptyRoot.lean

namespace TriangleFreeSegments.Probes.SPFresh

theorem empty_root {I : Type*} [DecidableEq I] (e : I → Endpoints)
    (H : Finset I) (R : Rect) (P : ProbeData)
    (hx : P.a' < R.c) (hy : P.b' < P.d')
    (he : ∀ i, Oriented (e i)) (hc : ∀ i ∈ H, Crosses (e i) R P)
    (hm : ∀ i, i ∉ H → Disjoint (seg (e i)) (probeRect R P)) :
    ∃ T : Rect, (P.a' < T.a ∧ T.a < T.c ∧ T.c < R.c) ∧
      (P.b' < T.b ∧ T.b < T.d ∧ T.d < P.d') ∧
      (∀ i, Disjoint (seg (e i)) (Set.Icc T.a T.c ×ˢ Set.Icc T.b T.d)) ∧
      (∀ i ∈ H, ∀ y ∈ Set.Icc P.b' P.d', T.c < xAt (e i) y) := by
  obtain ⟨c, hpc, hc'⟩ := finite_strict_lower H
    (fun i => min (xAt (e i) P.b') (xAt (e i) P.d')) P.a'
    (fun i hi => lt_min ((hc i hi).2.2 P.b' ⟨le_rfl, hy.le⟩).1
      ((hc i hi).2.2 P.d' ⟨hy.le, le_rfl⟩).1)
  obtain ⟨v, hpv, hvc⟩ := exists_between (lt_min hx hpc)
  obtain ⟨u, hpu, huv⟩ := exists_between hpv
  obtain ⟨b, hpb, hbd⟩ := exists_between hy
  obtain ⟨d, hbd', hdp⟩ := exists_between hbd
  have hvR : v < R.c := hvc.trans_le (min_le_left _ _)
  have hdom : ∀ i ∈ H, ∀ y ∈ Set.Icc P.b' P.d', v < xAt (e i) y := by
    intro i hi y hyy
    have hvi : v < min (xAt (e i) P.b') (xAt (e i) P.d') :=
      (hvc.trans_le (min_le_right _ _)).trans (hc' i hi)
    exact xAt_lower_bound (e i) (hvi.trans_le (min_le_left _ _))
      (hvi.trans_le (min_le_right _ _)) hyy
  refine ⟨⟨u, v, b, d⟩, ⟨hpu, huv, hvR⟩, ⟨hpb, hbd', hdp⟩, ?_, hdom⟩
  intro i
  rw [Set.disjoint_left]
  intro p hseg hbox
  have hpband : p.2 ∈ Set.Icc P.b' P.d' :=
    ⟨hpb.le.trans hbox.2.1, hbox.2.2.trans hdp.le⟩
  by_cases hi : i ∈ H
  · have hh := hdom i hi p.2 hpband
    have heq := ((mem_seg_iff (he i) p).mp hseg).2
    have hle : p.1 ≤ v := hbox.1.2
    rw [← heq] at hh
    exact (not_lt_of_ge hle) hh
  · apply Set.disjoint_left.mp (hm i hi) hseg
    exact ⟨⟨hpu.le.trans hbox.1.1, hbox.1.2.trans hvR.le⟩, hpband⟩

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/ChooseRoots.lean

namespace TriangleFreeSegments.Probes.SPFresh

theorem choose_roots {k : ℕ} {R : Rect} {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq I] (C : Configuration k R I J) :
    ∃T : J → Rect,RootLayout C T := by
  classical
  have hex := fun p => empty_root C.e (C.hits p) R (C.pr p)
    (C.valid p).2.1 (C.valid p).2.2.2.1 C.oriented (C.crosses p) (C.misses p)
  choose T hb hv he hd using hex
  refine ⟨T,⟨?_,he,hd⟩⟩
  intro p
  exact ⟨(hb p).1,(hb p).2.1,(hb p).2.2,(hv p).1,(hv p).2.1,(hv p).2.2⟩

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/BaseConfiguration.lean

namespace TriangleFreeSegments.Probes.SPFresh

noncomputable def baseConfiguration (R : Rect) (hx : R.a < R.c) (hy : R.b < R.d) :
    Configuration 1 R (Fin 1) (Fin 1) := by
  let e : Endpoints := (((R.a+R.c)/2,(3*R.b+R.d)/4),((R.a+R.c)/2,(R.b+3*R.d)/4))
  let P : ProbeData := ⟨(3*R.a+R.c)/4,(5*R.b+3*R.d)/8,(3*R.b+5*R.d)/8⟩
  have ho : Oriented e := by dsimp [Oriented,e]; linarith
  have heval : ∀y,xAt e y=(R.a+R.c)/2 := by intro y; simp [xAt,e]
  refine { e := fun _ => e
           pr := fun _ => P
           hits := fun _ => Finset.univ
           oriented := fun _ => ho
           inside := ?_
           distinct := ?_
           triangleFree := ?_
           valid := ?_
           hit_nonempty := ?_
           crosses := ?_
           misses := ?_
           independent := ?_
           separated := ?_
           colorful := ?_ }
  · intro i p hp
    obtain ⟨hp,hpx⟩ := (mem_seg_iff ho p).mp hp
    rw [heval] at hpx
    change (R.a < p.1 ∧ p.1 < R.c) ∧ (R.b < p.2 ∧ p.2 < R.d)
    dsimp [e] at hp
    constructor <;> constructor <;> linarith [hp.1,hp.2]
  · intro i j _; exact Subsingleton.elim i j
  · apply (cliqueFree_three_iff _).mpr
    intro a b c hab
    exact False.elim (hab.1 (Subsingleton.elim a b))
  · intro j
    dsimp [ValidProbe,P]
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> linarith
  · intro j; exact ⟨0,Finset.mem_univ _⟩
  · intro j i _
    refine ⟨?_,?_,?_⟩
    · dsimp [e,P]; linarith
    · dsimp [e,P]; linarith
    · intro y _; rw [heval]; dsimp [P]; constructor <;> linarith
  · intro j i hi; exact False.elim (hi (Finset.mem_univ _))
  · intro j i i' _ _ h; exact False.elim (h (Subsingleton.elim i i'))
  · intro j j' h; exact False.elim (h (Subsingleton.elim j j'))
  · intro c φ _
    refine ⟨0,?_⟩
    simp

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/Reindex.lean

namespace TriangleFreeSegments.Probes.SPFresh

noncomputable def Configuration.reindex {k : ℕ} {R : Rect} {I J I' J' : Type}
    [Fintype I] [Fintype J] [DecidableEq I] [Fintype I'] [Fintype J'] [DecidableEq I']
    (C : Configuration k R I J) (f : I' ≃ I) (g : J' ≃ J) : Configuration k R I' J' where
  e := C.e ∘ f
  pr := C.pr ∘ g
  hits j := (C.hits (g j)).map f.symm.toEmbedding
  oriented i := C.oriented (f i)
  inside i := C.inside (f i)
  distinct := C.distinct.comp f.injective
  triangleFree := by
    apply (cliqueFree_three_iff _).mpr
    intro a b c hab hac hbc
    apply (cliqueFree_three_iff _).mp C.triangleFree (f a) (f b) (f c)
    · exact ⟨fun h => hab.1 (f.injective h), hab.2⟩
    · exact ⟨fun h => hac.1 (f.injective h), hac.2⟩
    · exact ⟨fun h => hbc.1 (f.injective h), hbc.2⟩
  valid j := C.valid (g j)
  hit_nonempty j := (C.hit_nonempty (g j)).map
  crosses := by
    intro j i hi
    exact C.crosses (g j) (f i) (by simpa using hi)
  misses := by
    intro j i hi
    exact C.misses (g j) (f i) (by simpa using hi)
  independent := by
    intro j i i' hi hi' hne
    exact C.independent (g j) (f i) (f i') (by simpa using hi) (by simpa using hi')
      (fun h => hne (f.injective h))
  separated := by
    intro j j' hne
    exact C.separated (fun h => hne (g.injective h))
  colorful := by
    intro c φ hφ
    obtain ⟨j,hj⟩ := C.colorful c (φ ∘ f.symm) (by
      intro i i' h
      apply hφ
      exact ⟨fun he => h.1 (f.symm.injective he), by simpa using h.2⟩)
    refine ⟨g.symm j, ?_⟩
    simpa only [Equiv.apply_symm_apply, Finset.map_eq_image, Finset.image_image, Equiv.coe_toEmbedding,
      Function.comp_def] using hj

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/RecursiveConfiguration.lean

namespace TriangleFreeSegments.Probes.SPFresh

theorem configurations (n : ℕ) : ∃N M : ℕ,∀R : Rect,R.a<R.c→R.b<R.d→
    Nonempty (Configuration (n+1) R (Fin N) (Fin M)) := by
  classical
  induction n with
  | zero =>
    exact ⟨1,1,fun R hx hy=>⟨baseConfiguration R hx hy⟩⟩
  | succ n ih =>
    obtain ⟨N,M,ih⟩ := ih
    let I := StepIndex (Fin N) (Fin M)
    let J := Fin M × Fin M × Bool
    refine ⟨Fintype.card I,Fintype.card J,?_⟩
    intro R hx hy
    obtain ⟨C⟩ := ih R hx hy
    obtain ⟨T,L⟩ := choose_roots C
    have hD : ∀p,Nonempty (Configuration (n+1) (T p) (Fin N) (Fin M)) :=
      fun p=>ih (T p) (L.bounds p).2.1 (L.bounds p).2.2.2.2.1
    let D := fun p=>(hD p).some
    let B := fun p q=>(exists_probeSplit (D p) q R (L.bounds p).2.2.1).some
    let E := assembleStep C T D L (newProbe D B) (newProbe_valid L D B)
      (step_crosses_new L D B) (step_misses_new L D B) (newProbe_separated L D B)
    exact ⟨E.reindex (Fintype.equivFin I).symm (Fintype.equivFin J).symm⟩

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/ChromaticConclusion.lean

namespace TriangleFreeSegments.Probes.SPFresh

theorem configuration_chromatic {k : ℕ} {R : Rect} {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq I] (C : Configuration (k+1) R I J) :
    (k : ℕ∞) < (interGraph (fun i=> seg (C.e i))).chromaticNumber := by
  by_contra h
  have hc := SimpleGraph.chromaticNumber_le_iff_colorable.mp (le_of_not_gt h)
  obtain ⟨φ⟩ := hc
  obtain ⟨j,hj⟩ := C.colorful k φ (fun _ _ h=>φ.valid h)
  have hh := Finset.card_le_univ ((C.hits j).image φ)
  simp only [Fintype.card_fin] at hh
  omega

theorem configuration_root {k : ℕ} {R : Rect} {N M : ℕ}
    (C : Configuration (k+1) R (Fin N) (Fin M)) :
    ∃ (N : ℕ) (e : Fin N → (ℝ × ℝ) × (ℝ × ℝ)),
      (∀ i, (e i).1 ≠ (e i).2) ∧
      Function.Injective (fun i => seg (e i)) ∧
      (interGraph (fun i => seg (e i))).CliqueFree 3 ∧
      (k : ℕ∞) < (interGraph (fun i => seg (e i))).chromaticNumber := by
  exact ⟨N,C.e,(fun i=>oriented_ne (C.oriented i)),C.distinct,C.triangleFree,
    configuration_chromatic C⟩

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/NativeConclusion.lean

namespace TriangleFreeSegments.Probes.SPFresh

theorem native_theorem_1 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : ℕ) (e : Fin N → (ℝ × ℝ) × (ℝ × ℝ)),
      (∀ i, (e i).1 ≠ (e i).2) ∧
      Function.Injective (fun i => seg (e i)) ∧
      (interGraph (fun i => seg (e i))).CliqueFree 3 ∧
      (k : ℕ∞) < (interGraph (fun i => seg (e i))).chromaticNumber := by
  cases k with
  | zero => omega
  | succ k =>
    obtain ⟨N,M,h⟩ := configurations (k+1)
    obtain ⟨C⟩ := h ⟨0,1,0,1⟩ (by norm_num) (by norm_num)
    exact configuration_root C

end TriangleFreeSegments.Probes.SPFresh

-- Complete module: SPProof/FinalRoot.lean

namespace TriangleFreeSegments.Probes

theorem theorem_1 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : ℕ) (e : Fin N → (ℝ × ℝ) × (ℝ × ℝ)),
      (∀ i, (e i).1 ≠ (e i).2) ∧
      Function.Injective (fun i => seg (e i)) ∧
      (interGraph (fun i => seg (e i))).CliqueFree 3 ∧
      (k : ℕ∞) < (interGraph (fun i => seg (e i))).chromaticNumber := by
  exact SPFresh.native_theorem_1 k hk

end TriangleFreeSegments.Probes


open TriangleFreeSegments.Probes
open scoped BigOperators
theorem solution (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : ℕ) (e : Fin N → (ℝ × ℝ) × (ℝ × ℝ)),
      (∀ i, (e i).1 ≠ (e i).2) ∧
      Function.Injective (fun i => seg (e i)) ∧
      (interGraph (fun i => seg (e i))).CliqueFree 3 ∧
      (k : ℕ∞) < (interGraph (fun i => seg (e i))).chromaticNumber := by
  exact TriangleFreeSegments.Probes.theorem_1 k hk
