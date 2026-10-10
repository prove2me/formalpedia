-- Prove2me | solution 1 for PersistClust.Count.alg_diagram_death_pair
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T18:05:31.677991+00:00
-- url     : https://prove2.me/submissions/42870c52-dcac-417a-aa5f-ada4a601e1a8

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_AlgBarcode
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count
open Classical

/-!
# Death slice: `alg_diagram_death_pair` (ID ee075464)

For all real levels `d < b`, the multiplicity of the off-diagonal point `(b, d)` in the
analytic 0-th persistence diagram `ripsDiagram Dm g δ = mult (ripsRank Dm g δ)` of the
upper-star Rips filtration (Eq. (3) of RR-6968) equals the multiplicity of `(b, d)` in
the combinatorial barcode `ripsBarcode g Dm δ σ` produced by the elder-rule sweep of
Procedure 1 with merge threshold `τ = +∞`: both count the merge events in which a
component whose highest-`g` vertex has `g`-value `b` is absorbed at level `d` into an
older (higher-`g`) component — i.e. the elder-rule pairs with birth `b` and death `d`.

The master identity is

    mult(b, d) = #comps(G_{>d}, maxg = b) − #comps(G_{≥d}, maxg = b) = barcode(b, d),

where `G_{>d}` (resp. `G_{≥d}`) is the Rips graph with vertex set `{ i | g i > d }`
(resp. `{ i | g i ≥ d }`) and the inf-over-`ε` in `mult` is monotone-constant for small
`ε` via the bars-in-windows formula: a bar `[d', b']` covers the window `[d + ε, b − ε]`
iff `d' ≤ d` and `b ≤ b'`.
-/

/-! ## Proof steps (private lemmas) -/

/-- A sample `ε` is grid-good for the real pair `(b, d)` when no grade value `g i` lies
in the punctured windows `(b − ε, b + ε) ∖ {b}` or `(d − ε, d + ε) ∖ {d}`: the rank grid
is then constant around `b ± ε` and `d ± ε`, and a bar covers the window
`[d + ε, b − ε]` iff it pairs birth `b` with death `d`. -/
private def gridGood {n : ℕ} (g : Fin n → ℝ) (b d ε : ℝ) : Prop :=
  (∀ i : Fin n, b - ε < g i ∧ g i < b + ε → g i = b) ∧
    (∀ i : Fin n, d - ε < g i ∧ g i < d + ε → g i = d)

/-- **Strong** grid goodness: no grade value lies in the *closed* punctured windows
`[b − ε, b + ε] ∖ {b}` or `[d − ε, d + ε] ∖ {d}`. This is the hypothesis the
box-counting step (B) and the mult evaluation (M) actually need: the bracket's birth
window is the half-open `[b − ε, b + ε)` and its death window the half-open
`(d − ε, d + ε]`, so boundary grades would sneak extra bars into the count. The
canonical sample `ε₀BD` satisfies the strong version. -/
private def gridGoodC {n : ℕ} (g : Fin n → ℝ) (b d ε : ℝ) : Prop :=
  (∀ i : Fin n, b - ε ≤ g i ∧ g i ≤ b + ε → g i = b) ∧
    (∀ i : Fin n, d - ε ≤ g i ∧ g i ≤ d + ε → g i = d)

/-! ### Set equalities at a strong-grid sample

At a strong-grid sample `ε` the four stage sets of the rank grid reduce to the exact
levels: `{i | b − ε ≤ g i} = {i | b ≤ g i}` etc. These are the two-level analogs of the
immortal slice's `windowMem` lemma. -/

private lemma gridGoodC_set_blo {n : ℕ} (g : Fin n → ℝ) {b d ε : ℝ} (hpos : 0 < ε)
    (hg : gridGoodC g b d ε) :
    {i : Fin n | b - ε ≤ g i} = {i : Fin n | b ≤ g i} := by
  obtain ⟨h1, -⟩ := hg
  ext i
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hlt
    have hlt' : g i < b := not_le.mp hlt
    have := h1 i ⟨h, by linarith [hpos, hlt']⟩
    linarith [hlt', this]
  · intro h; linarith [hpos]

private lemma gridGoodC_set_bhi {n : ℕ} (g : Fin n → ℝ) {b d ε : ℝ} (hpos : 0 < ε)
    (hg : gridGoodC g b d ε) :
    {i : Fin n | b + ε ≤ g i} = {i : Fin n | b < g i} := by
  obtain ⟨h1, -⟩ := hg
  ext i
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h; linarith [hpos]
  · intro h
    by_contra hcon
    have hcon' : g i < b + ε := not_le.mp hcon
    have := h1 i ⟨by linarith [h, hpos], by linarith [hcon']⟩
    linarith [h, this]

private lemma gridGoodC_set_dhi {n : ℕ} (g : Fin n → ℝ) {b d ε : ℝ} (hpos : 0 < ε)
    (hg : gridGoodC g b d ε) :
    {i : Fin n | d + ε ≤ g i} = {i : Fin n | d < g i} := by
  obtain ⟨-, h2⟩ := hg
  ext i
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h; linarith [hpos]
  · intro h
    by_contra hcon
    have hcon' : g i < d + ε := not_le.mp hcon
    have := h2 i ⟨by linarith [h, hpos], by linarith [hcon']⟩
    linarith [h, this]

private lemma gridGoodC_set_dlo {n : ℕ} (g : Fin n → ℝ) {b d ε : ℝ} (hpos : 0 < ε)
    (hg : gridGoodC g b d ε) :
    {i : Fin n | d - ε ≤ g i} = {i : Fin n | d ≤ g i} := by
  obtain ⟨-, h2⟩ := hg
  ext i
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hlt
    have hlt' : g i < d := not_le.mp hlt
    have := h2 i ⟨h, by linarith [hpos, hlt']⟩
    linarith [hlt', this]
  · intro h; linarith [hpos]

/-! ### Analytic primitives (shared with the two-level `mult` evaluation) -/

namespace AlgDp

/-- `L g s i` is the induced-subgraph vertex predicate `s ≤ g i`. -/
abbrev L {n : ℕ} (g : Fin n → ℝ) (s : ℝ) (i : Fin n) : Prop := s ≤ g i

/-- `classAt` is the connected component of `i` in the Rips graph induced on `L^t`. -/
abbrev classAt {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (t : ℝ)
    (i : Fin n) : Set (Fin n) := {j | ripsJoined Dm g δ t i j}

/-- The image of `L^s` under the component map at level `t` (the rank's counting set). -/
abbrev imgAt {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (s t : ℝ) :
    Set (Set (Fin n)) := (fun i => classAt g Dm δ t i) '' {i | L g s i}

/-- Connectedness in the full Rips graph. -/
abbrev fullConn {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i j : Fin n) : Prop :=
  Relation.ReflTransGen (ripsGraph Dm δ).Adj i j

/-- The full Rips-graph component of `i`. -/
abbrev fullComp {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i : Fin n) : Set (Fin n) :=
  {j | fullConn Dm δ i j}

/-- All full Rips-graph components. -/
abbrev fullComps {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) : Set (Set (Fin n)) :=
  (fun i => fullComp Dm δ i) '' Set.univ

/-- A component has max-grade exactly `b`. -/
def maxgIs {n : ℕ} (g : Fin n → ℝ) (b : ℝ) (C : Set (Fin n)) : Prop :=
  (∃ i ∈ C, g i = b) ∧ (∀ j ∈ C, (g j : ℝ) ≤ b)

lemma rtg_mono {α : Type*} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b)
    {a b : α} (hrt : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hrt with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (h _ _ hstep))

lemma Adj_symm {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i j : Fin n)
    (h : (ripsGraph Dm δ).Adj i j) : (ripsGraph Dm δ).Adj j i := by
  rw [ripsGraph, SimpleGraph.fromRel] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

lemma ripsStep_symm {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (t : ℝ)
    (a b : Fin n) : (t ≤ g a ∧ t ≤ g b ∧ (ripsGraph Dm δ).Adj a b) →
    (t ≤ g b ∧ t ≤ g a ∧ (ripsGraph Dm δ).Adj b a) :=
  fun h => ⟨h.2.1, h.1, Adj_symm Dm δ a b h.2.2⟩

lemma rtg_reverse {α : Type*} {r : α → α → Prop} (hsymm : ∀ a b, r a b → r b a)
    {a b : α} (hrt : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction hrt with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (hsymm _ _ hstep)) ih

lemma ripsJoined_symm {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (t : ℝ)
    {i j : Fin n} (hj : L g t j) (h : ripsJoined Dm g δ t i j) :
    ripsJoined Dm g δ t j i :=
  ⟨hj, rtg_reverse (fun _ _ h => ⟨h.2.1, h.1, Adj_symm Dm δ _ _ h.2.2⟩) h.2⟩

lemma ripsJoined_mem_self {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) {i : Fin n} (hi : L g t i) : i ∈ classAt g Dm δ t i :=
  ⟨hi, Relation.ReflTransGen.refl⟩

lemma ripsJoined_trans {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (t : ℝ)
    {i j k : Fin n} (hij : ripsJoined Dm g δ t i j) (hjk : ripsJoined Dm g δ t j k) :
    ripsJoined Dm g δ t i k :=
  ⟨hij.1, Relation.ReflTransGen.trans hij.2 hjk.2⟩

lemma L_of_rtg {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (t : ℝ)
    {a b : Fin n} (ha : L g t a)
    (hrt : Relation.ReflTransGen (fun x y => t ≤ g x ∧ t ≤ g y ∧ (ripsGraph Dm δ).Adj x y) a b) :
    L g t b := by
  induction hrt with
  | refl => exact ha
  | tail _ hstep _ => exact hstep.2.1

lemma classAt_eq_of_mem {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) {i y : Fin n} (hi : i ∈ classAt g Dm δ t y) :
    classAt g Dm δ t i = classAt g Dm δ t y := by
  obtain ⟨hy, hrt⟩ := hi
  have hiL : L g t i := L_of_rtg g Dm δ t hy hrt
  ext j
  constructor
  · intro hij
    exact ⟨hy, Relation.ReflTransGen.trans hrt hij.2⟩
  · intro hjy
    exact ripsJoined_trans g Dm δ t (ripsJoined_symm g Dm δ t hiL ⟨hy, hrt⟩) hjy

lemma ripsJoined_eq_fullConn {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) (hlow : ∀ a : Fin n, L g t a) (i j : Fin n) :
    ripsJoined Dm g δ t i j ↔ fullConn Dm δ i j := by
  constructor
  · intro h
    exact rtg_mono (fun _ _ ha => ha.2.2) h.2
  · intro h
    exact ⟨hlow i, rtg_mono (fun a b ha => ⟨hlow a, hlow b, ha⟩) h⟩

lemma classAt_eq_fullComp {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) (hlow : ∀ a : Fin n, L g t a) (i : Fin n) :
    classAt g Dm δ t i = fullComp Dm δ i := by
  ext j; exact ripsJoined_eq_fullConn g Dm δ t hlow i j

lemma ripsRank_eq {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (s t : ℝ) :
    ripsRank Dm g δ s t = (imgAt g Dm δ s t).encard := by
  simp only [ripsRank, rankFn, imgAt, L]

lemma imgAt_mono {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) {a a' t : ℝ}
    (h : a ≤ a') : imgAt g Dm δ a' t ⊆ imgAt g Dm δ a t := by
  rintro C ⟨x, hxLa, rfl⟩
  exact ⟨x, h.trans hxLa, rfl⟩

lemma meets_iff {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t a : ℝ) (hta : t ≤ a) {y : Fin n} :
    classAt g Dm δ t y ∈ imgAt g Dm δ a t ↔ ∃ i ∈ classAt g Dm δ t y, a ≤ g i := by
  constructor
  · rintro ⟨x, hxLa, hx⟩
    refine ⟨x, ?_, hxLa⟩
    rw [← hx]
    exact ripsJoined_mem_self g Dm δ t (hta.trans hxLa)
  · rintro ⟨i, himem, hgi⟩
    exact ⟨i, hgi, classAt_eq_of_mem g Dm δ t himem⟩

lemma fullConn_symm {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) {i j : Fin n}
    (h : fullConn Dm δ i j) : fullConn Dm δ j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (Adj_symm Dm δ _ _ hstep)) ih

lemma fullConn_refl {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i : Fin n) :
    fullConn Dm δ i i := Relation.ReflTransGen.refl

lemma fullComp_eq_of_mem {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) {i y : Fin n}
    (hi : i ∈ fullComp Dm δ y) : fullComp Dm δ i = fullComp Dm δ y := by
  have hi' : fullConn Dm δ y i := hi
  ext j
  constructor
  · intro hij
    exact Relation.ReflTransGen.trans hi' hij
  · intro hjy
    have hjy' : fullConn Dm δ y j := hjy
    exact Relation.ReflTransGen.trans (fullConn_symm Dm δ hi') hjy'

lemma classAt_subset_fullComp {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) (i : Fin n) : classAt g Dm δ t i ⊆ fullComp Dm δ i := by
  intro j hj
  exact rtg_mono (fun _ _ ha => ha.2.2) hj.2

lemma diff_encard {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (b ε t : ℝ) (hε : 0 < ε) :
    (imgAt g Dm δ (b - ε) t).encard - (imgAt g Dm δ (b + ε) t).encard
      = (imgAt g Dm δ (b - ε) t \ imgAt g Dm δ (b + ε) t).encard := by
  have hsub := imgAt_mono (t := t) g Dm δ (show b - ε ≤ b + ε by linarith)
  exact (Set.encard_sdiff hsub (Set.toFinite _)).symm

/-! ### The two-level grid sample

For the death pair `(b, d)` the rank grid must avoid grade values near both endpoints.
The sample `ε₀BD g b d` is built from the nonzero gaps `|g c − b|` and `|g c − d|`
(capped by `(b − d)/4` so that the sampled window stays inside the `mult` interval).

-/

noncomputable def gapsBD {n : ℕ} (g : Fin n → ℝ) (b d : ℝ) : Finset ℝ :=
  ((Finset.univ.image (fun c : Fin n => |g c - b|)) ∪
    (Finset.univ.image (fun c : Fin n => |g c - d|))).filter (fun x => x ≠ 0)

noncomputable def ε₀BD {n : ℕ} (g : Fin n → ℝ) (b d : ℝ) : ℝ :=
  if h : (gapsBD g b d).Nonempty then
    min ((gapsBD g b d).min' h / 2) ((b - d) / 4)
  else (b - d) / 4

lemma ε₀BD_le_quarter {n : ℕ} (g : Fin n → ℝ) (b d : ℝ) :
    ε₀BD g b d ≤ (b - d) / 4 := by
  unfold ε₀BD
  split_ifs with h
  · exact min_le_right _ _
  · exact le_refl _

lemma gapsBD_min'_pos {n : ℕ} (g : Fin n → ℝ) (b d : ℝ)
    (h : (gapsBD g b d).Nonempty) : (0:ℝ) < (gapsBD g b d).min' h := by
  have hmem := (gapsBD g b d).min'_mem h
  obtain ⟨himg, hne⟩ := Finset.mem_filter.mp hmem
  rcases Finset.mem_union.mp himg with hb | hd
  · obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hb
    rw [← hc] at hne ⊢
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
  · obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hd
    rw [← hc] at hne ⊢
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)

lemma ε₀BD_pos {n : ℕ} (g : Fin n → ℝ) (b d : ℝ) (hbd : d < b) : 0 < ε₀BD g b d := by
  have hq : 0 < (b - d) / 4 := by linarith
  unfold ε₀BD
  split_ifs with h
  · have hminpos := gapsBD_min'_pos g b d h
    exact lt_min (by linarith) hq
  · exact hq

lemma ε₀BD_lt_half {n : ℕ} (g : Fin n → ℝ) (b d : ℝ) (hbd : d < b) :
    ε₀BD g b d < (b - d) / 2 := by
  have hq := ε₀BD_le_quarter g b d
  linarith

lemma ε₀BD_gridGood {n : ℕ} (g : Fin n → ℝ) (b d : ℝ) (hbd : d < b) :
    gridGood g b d (ε₀BD g b d) := by
  constructor
  · intro i hwin
    by_contra hne
    have habs_lt : |g i - b| < ε₀BD g b d :=
      abs_sub_lt_iff.mpr ⟨by linarith [hwin.2], by linarith [hwin.1]⟩
    have hmem : |g i - b| ∈ gapsBD g b d := by
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      · intro h0; exact hne (sub_eq_zero.mp (abs_eq_zero.mp h0))
    have hne' : (gapsBD g b d).Nonempty := ⟨_, hmem⟩
    have heps2 : ε₀BD g b d ≤ |g i - b| / 2 := by
      unfold ε₀BD
      rw [dif_pos hne']
      have hmin := (gapsBD g b d).min'_le _ hmem
      have : min ((gapsBD g b d).min' hne' / 2) ((b - d) / 4)
          ≤ (gapsBD g b d).min' hne' / 2 := min_le_left _ _
      linarith
    linarith [habs_lt, heps2, abs_nonneg (g i - b)]
  · intro i hwin
    by_contra hne
    have habs_lt : |g i - d| < ε₀BD g b d :=
      abs_sub_lt_iff.mpr ⟨by linarith [hwin.2], by linarith [hwin.1]⟩
    have hmem : |g i - d| ∈ gapsBD g b d := by
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      · intro h0; exact hne (sub_eq_zero.mp (abs_eq_zero.mp h0))
    have hne' : (gapsBD g b d).Nonempty := ⟨_, hmem⟩
    have heps2 : ε₀BD g b d ≤ |g i - d| / 2 := by
      unfold ε₀BD
      rw [dif_pos hne']
      have hmin := (gapsBD g b d).min'_le _ hmem
      have h2 : min ((gapsBD g b d).min' hne' / 2) ((b - d) / 4)
          ≤ (gapsBD g b d).min' hne' / 2 := min_le_left _ _
      linarith
    linarith [habs_lt, heps2, abs_nonneg (g i - d)]

/-- Strong grid goodness of the canonical sample: any grade value at distance ≤ `ε₀BD`
from `b` or `d` **is** that very level (all nonzero gaps exceed `ε₀BD`). -/
lemma ε₀BD_gridGoodC {n : ℕ} (g : Fin n → ℝ) (b d : ℝ) (hbd : d < b) :
    gridGoodC g b d (ε₀BD g b d) := by
  constructor
  · intro i hwin
    by_contra hne
    have habs_le : |g i - b| ≤ ε₀BD g b d := abs_le.mpr ⟨by linarith [hwin.1], by linarith [hwin.2]⟩
    have hmem : |g i - b| ∈ gapsBD g b d := by
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      · intro h0; exact hne (sub_eq_zero.mp (abs_eq_zero.mp h0))
    have hne' : (gapsBD g b d).Nonempty := ⟨_, hmem⟩
    have heps : ε₀BD g b d < |g i - b| := by
      unfold ε₀BD
      rw [dif_pos hne']
      have hmin := (gapsBD g b d).min'_le _ hmem
      calc min ((gapsBD g b d).min' hne' / 2) ((b - d) / 4)
          ≤ (gapsBD g b d).min' hne' / 2 := min_le_left _ _
        _ < (gapsBD g b d).min' hne' := by
            have := gapsBD_min'_pos g b d hne'; linarith
        _ ≤ |g i - b| := hmin
    linarith [habs_le, heps]
  · intro i hwin
    by_contra hne
    have habs_le : |g i - d| ≤ ε₀BD g b d := abs_le.mpr ⟨by linarith [hwin.1], by linarith [hwin.2]⟩
    have hmem : |g i - d| ∈ gapsBD g b d := by
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      · intro h0; exact hne (sub_eq_zero.mp (abs_eq_zero.mp h0))
    have hne' : (gapsBD g b d).Nonempty := ⟨_, hmem⟩
    have heps : ε₀BD g b d < |g i - d| := by
      unfold ε₀BD
      rw [dif_pos hne']
      have hmin := (gapsBD g b d).min'_le _ hmem
      calc min ((gapsBD g b d).min' hne' / 2) ((b - d) / 4)
          ≤ (gapsBD g b d).min' hne' / 2 := min_le_left _ _
        _ < (gapsBD g b d).min' hne' := by
            have := gapsBD_min'_pos g b d hne'; linarith
        _ ≤ |g i - d| := hmin
    linarith [habs_le, heps]

end AlgDp

open AlgDp

/-- Step R1a — rank grid-constancy (upper endpoint). The Rips rank `ripsRank Dm g δ s t`
depends on the upper threshold `s` only through the vertex set `{i | s ≤ g i}`: if
`s` and `s'` induce the same set, the ranks agree at every lower threshold `t`.
(Ranks change only at grade values `g i`, which are finite.) -/
private theorem alg_death_pair_step_rank_const_upper
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (b d : ℝ) (hbd : d < b)
    {s s' : ℝ} (hs : {i : Fin n | s ≤ g i} = {i : Fin n | s' ≤ g i}) (t : ℝ) :
    ripsRank Dm g δ s t = ripsRank Dm g δ s' t := by
  -- `ripsRank Dm g δ s t = ((fun x => {y | ripsJoined … t x y}) '' {i | s ≤ g i}).encard`,
  -- which depends on `s` only through the set `{i | s ≤ g i}`.
  simp only [ripsRank, rankFn]
  rw [hs]

/-- Step R1b — rank grid-constancy (lower endpoint). The Rips rank `ripsRank Dm g δ s t`
depends on the lower threshold `t` only through the vertex set `{i | t ≤ g i}`: if
`t` and `t'` induce the same set, the ranks agree at every upper threshold `s`
(the `ripsJoined` relation is pointwise equivalent under the two levels). -/
private theorem alg_death_pair_step_rank_const_lower
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (b d : ℝ) (hbd : d < b)
    (s : ℝ) {t t' : ℝ} (ht : {i : Fin n | t ≤ g i} = {i : Fin n | t' ≤ g i}) :
    ripsRank Dm g δ s t = ripsRank Dm g δ s t' := by
  have hset : ∀ i : Fin n, t ≤ g i ↔ t' ≤ g i := by
    intro i
    constructor
    · intro h
      have : i ∈ ({i : Fin n | t' ≤ g i} : Set (Fin n)) := by rw [← ht]; exact h
      exact this
    · intro h
      have : i ∈ ({i : Fin n | t ≤ g i} : Set (Fin n)) := by rw [ht]; exact h
      exact this
  -- The `ripsJoined` relation is pointwise equivalent for `t` and `t'`.
  have hrel : ∀ a b : Fin n,
      (t ≤ g a ∧ t ≤ g b ∧ (ripsGraph Dm δ).Adj a b) ↔
        (t' ≤ g a ∧ t' ≤ g b ∧ (ripsGraph Dm δ).Adj a b) := by
    intro a b; rw [hset a, hset b]
  have rtg_mono : ∀ {r p : Fin n → Fin n → Prop},
      (∀ a b, r a b → p a b) → ∀ {a b}, Relation.ReflTransGen r a b →
        Relation.ReflTransGen p a b := by
    intro r p h a b hrt
    induction hrt with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (h _ _ hstep))
  have hji : ∀ i j : Fin n, ripsJoined Dm g δ t i j ↔ ripsJoined Dm g δ t' i j := by
    intro i j
    constructor
    · rintro ⟨hi, hrt⟩
      exact ⟨(hset i).mp hi, rtg_mono (fun a b h => (hrel a b).mp h) hrt⟩
    · rintro ⟨hi, hrt⟩
      exact ⟨(hset i).mpr hi, rtg_mono (fun a b h => (hrel a b).mpr h) hrt⟩
  have hfun : (fun x => {y | ripsJoined Dm g δ t x y}) =
      (fun x => {y | ripsJoined Dm g δ t' x y}) := by
    funext x; ext y; exact hji x y
  simp only [ripsRank, rankFn]
  rw [hfun]

/-- The rank bracket is constant across strong-grid samples: at any strong-grid `ε` the
four stage sets collapse to the exact levels `{b ≤ g}`, `{b < g}`, `{d < g}`, `{d ≤ g}`,
so two strong-grid samples give the same bracket (rank grid-constancy R1a/R1b). -/
private lemma alg_death_pair_bracket_const_good
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (b d : ℝ) (hbd : d < b)
    {ε₁ ε₂ : ℝ} (hpos₁ : 0 < ε₁) (hpos₂ : 0 < ε₂)
    (hg₁ : gridGoodC g b d ε₁) (hg₂ : gridGoodC g b d ε₂) :
    (ripsRank Dm g δ (b - ε₁) (d + ε₁) - ripsRank Dm g δ (b + ε₁) (d + ε₁)) -
      (ripsRank Dm g δ (b - ε₁) (d - ε₁) - ripsRank Dm g δ (b + ε₁) (d - ε₁))
      = (ripsRank Dm g δ (b - ε₂) (d + ε₂) - ripsRank Dm g δ (b + ε₂) (d + ε₂)) -
        (ripsRank Dm g δ (b - ε₂) (d - ε₂) - ripsRank Dm g δ (b + ε₂) (d - ε₂)) := by
  have hbl₁ := gridGoodC_set_blo g hpos₁ hg₁
  have hbl₂ := gridGoodC_set_blo g hpos₂ hg₂
  have hbh₁ := gridGoodC_set_bhi g hpos₁ hg₁
  have hbh₂ := gridGoodC_set_bhi g hpos₂ hg₂
  have hdh₁ := gridGoodC_set_dhi g hpos₁ hg₁
  have hdh₂ := gridGoodC_set_dhi g hpos₂ hg₂
  have hdl₁ := gridGoodC_set_dlo g hpos₁ hg₁
  have hdl₂ := gridGoodC_set_dlo g hpos₂ hg₂
  have e1 : ripsRank Dm g δ (b - ε₁) (d + ε₁) = ripsRank Dm g δ (b - ε₂) (d + ε₂) := by
    rw [alg_death_pair_step_rank_const_upper n g Dm hDm δ b d hbd
          (hbl₁.trans hbl₂.symm) (d + ε₁)]
    rw [alg_death_pair_step_rank_const_lower n g Dm hDm δ b d hbd (b - ε₂)
          (hdh₁.trans hdh₂.symm)]
  have e2 : ripsRank Dm g δ (b + ε₁) (d + ε₁) = ripsRank Dm g δ (b + ε₂) (d + ε₂) := by
    rw [alg_death_pair_step_rank_const_upper n g Dm hDm δ b d hbd
          (hbh₁.trans hbh₂.symm) (d + ε₁)]
    rw [alg_death_pair_step_rank_const_lower n g Dm hDm δ b d hbd (b + ε₂)
          (hdh₁.trans hdh₂.symm)]
  have e3 : ripsRank Dm g δ (b - ε₁) (d - ε₁) = ripsRank Dm g δ (b - ε₂) (d - ε₂) := by
    rw [alg_death_pair_step_rank_const_upper n g Dm hDm δ b d hbd
          (hbl₁.trans hbl₂.symm) (d - ε₁)]
    rw [alg_death_pair_step_rank_const_lower n g Dm hDm δ b d hbd (b - ε₂)
          (hdl₁.trans hdl₂.symm)]
  have e4 : ripsRank Dm g δ (b + ε₁) (d - ε₁) = ripsRank Dm g δ (b + ε₂) (d - ε₂) := by
    rw [alg_death_pair_step_rank_const_upper n g Dm hDm δ b d hbd
          (hbh₁.trans hbh₂.symm) (d - ε₁)]
    rw [alg_death_pair_step_rank_const_lower n g Dm hDm δ b d hbd (b + ε₂)
          (hdl₁.trans hdl₂.symm)]
  rw [e1, e2, e3, e4]

/-! ### Sweep-prefix machinery for the death slice (namespace `DpB`)

Both the box-counting step (B) and the minimality bound (M−) follow from a single prefix
analysis of the elder-rule sweep.  Split the processing order at the two levels `d + ε` and
`d − ε`.  While the vertices with grades in `[d − ε, d + ε)` are processed, the number of
grade-`b` entries lost is exactly the bracket `B(ε)` (each lost entry is a bar whose birth
lies in the birth window and whose death lies in the death window), and the accumulated
deaths at `(b, d)` are precisely those grade-`b` losses that happen at the level `d` itself.
Hence `acc(b, d) ≤ B(ε)`, with equality when `ε` is strong-grid good (then the middle chunk
is exactly the grade-`d` vertices and the birth window is exactly `{b}`). -/

namespace DpB

variable {n : ℕ}

/-- Connectivity in the subgraph of the Rips graph induced on the processed set `P`. -/
def connIn (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (P : Set (Fin n)) (i j : Fin n) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ (ripsGraph Dm δ).Adj a b) i j

lemma connIn_mono {Dm : Fin n → Fin n → ℝ} {δ : ℝ} {P P' : Set (Fin n)}
    (hsub : P ⊆ P') {a b : Fin n} (h : connIn Dm δ P a b) : connIn Dm δ P' a b :=
  rtg_mono (fun _ _ hxy => ⟨hsub hxy.1, hsub hxy.2.1, hxy.2.2⟩) h

lemma connIn_single {Dm : Fin n → Fin n → ℝ} {δ : ℝ} {P : Set (Fin n)} {a b : Fin n}
    (ha : a ∈ P) (hb : b ∈ P) (hadj : (ripsGraph Dm δ).Adj a b) : connIn Dm δ P a b :=
  Relation.ReflTransGen.single ⟨ha, hb, hadj⟩

lemma connIn_symm {Dm : Fin n → Fin n → ℝ} {δ : ℝ} {P : Set (Fin n)} {a b : Fin n}
    (h : connIn Dm δ P a b) : connIn Dm δ P b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single
      ⟨hstep.2.1, hstep.1, Adj_symm Dm δ _ _ hstep.2.2⟩) ih

lemma connIn_trans {Dm : Fin n → Fin n → ℝ} {δ : ℝ} {P : Set (Fin n)} {a b c : Fin n}
    (hab : connIn Dm δ P a b) (hbc : connIn Dm δ P b c) : connIn Dm δ P a c :=
  Relation.ReflTransGen.trans hab hbc

/-- The sweep invariant for an arbitrary processed prefix `P`, with connectivity measured
*inside* `P` (the processed induced subgraph), which is what lets us count components of the
prefix graph.  Clauses: (1) labels are defined exactly on `P`; (2) labels of `P` point to
roots; (3) roots are elders w.r.t. the processing order; (4) adjacent processed vertices share
a label; (5) a labelled vertex is connected to its root within `P`. -/
def SweepInvP (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (lab : UFState n) (P : Set (Fin n)) : Prop :=
  (∀ v, (lab v).isSome ↔ v ∈ P) ∧
  (∀ v r, lab v = some r → lab r = some r) ∧
  (∀ v r, lab v = some r → σ.symm r ≥ σ.symm v) ∧
  (∀ u v, (ripsGraph Dm δ).Adj u v → lab u = lab v ∨ ¬(lab u).isSome ∨ ¬(lab v).isSome) ∧
  (∀ v r, lab v = some r → connIn Dm δ P r v)

lemma init_invP (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n) :
    SweepInvP g Dm δ σ (fun _ => none) (∅ : Set (Fin n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v; simp
  · intro v r h; exact absurd h (by simp)
  · intro v r h; exact absurd h (by simp)
  · intro u v _; exact Or.inr (Or.inl (by simp))
  · intro v r h; exact absurd h (by simp)

/-! #### `firstProcessed` facts -/

lemma firstProcessed_mem (σ : Fin n ≃ Fin n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (i₀ : Fin n) : firstProcessed σ S i₀ ∈ S := by
  rw [firstProcessed, dif_pos hS]
  obtain ⟨y, hyS, hy⟩ := Finset.mem_image.mp (Finset.max'_mem _ (hS.image σ.symm))
  rw [← hy, Equiv.apply_symm_apply]
  exact hyS

lemma firstProcessed_max (σ : Fin n ≃ Fin n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (i₀ : Fin n) (q : Fin n) (hq : q ∈ S) :
    σ.symm q ≤ σ.symm (firstProcessed σ S i₀) := by
  have hmemq : σ.symm q ∈ S.image σ.symm := Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hcongr : (S.image σ.symm).max' (hS.image σ.symm) =
      (S.image σ.symm).max' ⟨σ.symm q, hmemq⟩ :=
    congrArg (Finset.max' (S.image σ.symm)) (Subsingleton.elim _ _)
  rw [firstProcessed, dif_pos hS, Equiv.symm_apply_apply, hcongr]
  exact Finset.le_max' (S.image σ.symm) (σ.symm q) hmemq

lemma g_le_of_symm_le {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hσ : IsSortOrder g σ) {x y : Fin n} (h : σ.symm x ≤ σ.symm y) : g x ≤ g y := by
  have hm := hσ h
  rw [Function.comp] at hm
  rw [← Equiv.apply_symm_apply σ x, ← Equiv.apply_symm_apply σ y]
  exact hm

lemma barStep_S_mem {n : ℕ} (lab : UFState n) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i j : Fin n)
    (hj : j ∈ Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)) :
    j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome := (Finset.mem_filter.mp hj).2

lemma graphAdj_iff {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i j : Fin n) :
    (ripsGraph Dm δ).Adj i j ↔ i ≠ j ∧ (Dm i j ≤ δ ∨ Dm j i ≤ δ) := by
  simp [ripsGraph, SimpleGraph.fromRel]

lemma graphAdj_of_dm {n : ℕ} (Dm : Fin n → Fin n → ℝ) (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ)
    (a b : Fin n) (hne : a ≠ b) (h : Dm a b ≤ δ) : (ripsGraph Dm δ).Adj a b := by
  rw [graphAdj_iff Dm δ]
  exact ⟨hne, Or.inl h⟩

lemma root_getD {n : ℕ} (lab : UFState n) (hptr : ∀ v r, lab v = some r → lab r = some r)
    (j r : Fin n) (hr : lab j = some r) :
    (lab j).getD j = r ∧ lab ((lab j).getD j) = some ((lab j).getD j) := by
  rw [hr]
  refine ⟨rfl, ?_⟩
  simpa only [Option.getD_some] using hptr j r hr

/-! #### One-step preservation of the prefix invariant -/

lemma barStep_invP {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i)
    (σ : Fin n ≃ Fin n) (st : UFState n × ((EReal × EReal) → ℕ∞)) (P : Set (Fin n)) (i : Fin n)
    (hinv : SweepInvP g Dm δ σ st.1 P) (hiP : i ∉ P)
    (horder : ∀ v ∈ P, σ.symm i ≤ σ.symm v) :
    SweepInvP g Dm δ σ (barStep g Dm δ σ st i).1 (insert i P) := by
  obtain ⟨hmem, hptr, helder, hedge, hcomp⟩ := hinv
  rw [barStep]
  set Sf : Finset (Fin n) :=
    Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (st.1 j).isSome) with hSf
  by_cases hS : Sf = ∅
  · -- no processed neighbour: `i` seeds a new entry
    rw [if_pos hS]; simp only [Prod.fst]
    constructor
    · intro v
      rw [Function.update_apply]
      by_cases hv : v = i
      · rw [if_pos hv, hv]
        simp [hv, Set.mem_insert_iff]
      · rw [if_neg hv]
        rw [hmem v]
        simp [hv, Set.mem_insert_iff]
    constructor
    · intro v r hv
      rw [Function.update_apply] at hv
      by_cases hv' : v = i
      · rw [if_pos hv'] at hv
        injection hv with he
        rw [← he]
        rw [Function.update_apply, if_pos rfl]
      · rw [if_neg hv'] at hv
        rw [Function.update_apply]
        by_cases hr : r = i
        · rw [if_pos hr, ← hr]
        · rw [if_neg hr]
          exact hptr v r hv
    constructor
    · intro v r hv
      rw [Function.update_apply] at hv
      by_cases hv' : v = i
      · rw [if_pos hv'] at hv
        injection hv with he
        rw [hv', he]
      · rw [if_neg hv'] at hv
        exact helder v r hv
    constructor
    · intro u v huv
      rw [Function.update_apply, Function.update_apply]
      by_cases hu : u = i
      · rw [if_pos hu]
        by_cases hv : v = i
        · rw [if_pos hv]; exact Or.inl rfl
        · rw [if_neg hv]
          rw [hu] at huv
          have hvP : v ∉ P := by
            intro hvP
            have hvSf : v ∈ Sf := by
              rw [hSf, Finset.mem_filter]
              have hadj : Dm i v ≤ δ := by
                rcases (graphAdj_iff Dm δ i v).mp huv with ⟨_, h⟩
                rcases h with h | h
                · exact h
                · rw [hDm]; exact h
              exact ⟨Finset.mem_univ v, hv, hadj, (hmem v).mpr hvP⟩
            rw [hS] at hvSf
            exact (Finset.notMem_empty v) hvSf
          have hvn : st.1 v = none := by
            cases hh : st.1 v with
            | none => rfl
            | some r => exact absurd ((hmem v).mp (by simp [hh])) hvP
          right; right; simp [hvn]
      · by_cases hv : v = i
        · rw [if_neg hu, if_pos hv]
          rw [hv] at huv
          have huP : u ∉ P := by
            intro huP
            have huSf : u ∈ Sf := by
              rw [hSf, Finset.mem_filter]
              have hadj : Dm i u ≤ δ := by
                rcases (graphAdj_iff Dm δ u i).mp huv with ⟨_, h⟩
                rcases h with h | h
                · rw [hDm]; exact h
                · exact h
              exact ⟨Finset.mem_univ u, hu, hadj, (hmem u).mpr huP⟩
            rw [hS] at huSf
            exact (Finset.notMem_empty u) huSf
          have hun : st.1 u = none := by
            cases hh : st.1 u with
            | none => rfl
            | some r => exact absurd ((hmem u).mp (by simp [hh])) huP
          right; left; simp [hun]
        · rw [if_neg hu, if_neg hv]
          rcases hedge u v huv with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
    · intro v r hv
      rw [Function.update_apply] at hv
      by_cases hv' : v = i
      · rw [if_pos hv'] at hv
        injection hv with he
        rw [hv', ← he]
        exact Relation.ReflTransGen.refl
      · rw [if_neg hv'] at hv
        exact connIn_mono (fun x hx => Or.inr hx) (hcomp v r hv)
  · -- merge step
    rw [if_neg hS]; simp only [Prod.fst]
    set root : Fin n → Fin n := fun j => (st.1 j).getD j with hroot
    set ri : Fin n := root (firstProcessed σ Sf i) with hri
    set M : Finset (Fin n) := insert ri (Sf.image root) with hM
    set R : Fin n := firstProcessed σ M ri with hR
    set lab2 : UFState n := fun v =>
      if v = i then some R
      else match st.1 v with
        | some r => if r ∈ M then some R else some r
        | none => none with hlab2
    change SweepInvP g Dm δ σ lab2 (insert i P)
    have hSne : Sf.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    have hMne : M.Nonempty := ⟨ri, by rw [hM]; exact Finset.mem_insert_self _ _⟩
    have hRM : R ∈ M := by rw [hR]; exact firstProcessed_mem σ M hMne ri
    have hRmax : ∀ q ∈ M, σ.symm q ≤ σ.symm R := by
      intro q hq; rw [hR]; exact firstProcessed_max σ M hMne ri q hq
    have hroot_of : ∀ j, (st.1 j).isSome → root j = (st.1 j).getD j := fun j _ => rfl
    have hroot_mem_M : ∀ j ∈ Sf, root j ∈ M := by
      intro j hj; rw [hM]; exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    have hroot_root : ∀ j, (st.1 j).isSome → st.1 (root j) = some (root j) := by
      intro j hj
      have hsome : ∃ r, st.1 j = some r := Option.isSome_iff_exists.mp hj
      obtain ⟨r, hr⟩ := hsome
      have : root j = r := by rw [hroot_of j hj, hr]; rfl
      rw [this]
      exact hptr j r hr
    have hroot_P : ∀ j ∈ Sf, root j ∈ P := by
      intro j hj
      have hj' := barStep_S_mem st.1 Dm δ i j hj
      have hsj : (st.1 j).isSome := hj'.2.2
      exact (hmem (root j)).mp (by rw [hroot_root j hsj]; rfl)
    have hM_P : ∀ q ∈ M, q ∈ P := by
      intro q hq
      rw [hM] at hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · rw [hri]
        exact hroot_P _ (firstProcessed_mem σ Sf hSne i)
      · obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp hq
        rw [← hjq]; exact hroot_P j hj
    have hconn_i_M : ∀ q ∈ M, connIn Dm δ (insert i P) q i := by
      intro q hq
      rw [hM] at hq
      rcases Finset.mem_insert.mp hq with hqi | hqg
      · have hj0 : firstProcessed σ Sf i ∈ Sf := firstProcessed_mem σ Sf hSne i
        obtain ⟨hjne, hdmj, hsj⟩ := barStep_S_mem st.1 Dm δ i _ hj0
        obtain ⟨r0, hr0lab⟩ := Option.isSome_iff_exists.mp hsj
        have hrootj : root (firstProcessed σ Sf i) = r0 := by
          simp [hroot_of (firstProcessed σ Sf i) hsj, hr0lab]
        rw [hqi, hri, hrootj]
        have hc1 : connIn Dm δ P r0 (firstProcessed σ Sf i) :=
          hcomp (firstProcessed σ Sf i) r0 hr0lab
        have hjP : (firstProcessed σ Sf i) ∈ P :=
          (hmem (firstProcessed σ Sf i)).mp (by simpa using hsj)
        have hadj : (ripsGraph Dm δ).Adj (firstProcessed σ Sf i) i :=
          graphAdj_of_dm Dm hDm δ _ i hjne (hDm _ _ ▸ hdmj)
        exact connIn_trans (connIn_mono (fun x hx => Or.inr hx) hc1)
          (connIn_single (Or.inr hjP) (Or.inl rfl) hadj)
      · obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp hqg
        obtain ⟨hjne, hdmj, hsj⟩ := barStep_S_mem st.1 Dm δ i j hj
        obtain ⟨r0, hr0lab⟩ := Option.isSome_iff_exists.mp hsj
        have hrootj : root j = r0 := by simp [hroot_of j hsj, hr0lab]
        rw [← hjq, hrootj]
        have hc1 : connIn Dm δ P r0 j := hcomp j r0 hr0lab
        have hjP : j ∈ P := (hmem j).mp (by simpa using hsj)
        have hadj : (ripsGraph Dm δ).Adj j i :=
          graphAdj_of_dm Dm hDm δ j i hjne (hDm j i ▸ hdmj)
        exact connIn_trans (connIn_mono (fun x hx => Or.inr hx) hc1)
          (connIn_single (Or.inr hjP) (Or.inl rfl) hadj)
    have hrRob : R ≠ i := fun hh => hiP (hh ▸ hM_P R hRM)
    have hrootRootM : ∀ q ∈ M, st.1 q = some q := by
      intro q hq
      rw [hM] at hq
      rcases Finset.mem_insert.mp hq with hqi | hqg
      · rw [hqi, hri]
        obtain ⟨_, _, hsj⟩ := barStep_S_mem st.1 Dm δ i _
          (firstProcessed_mem σ Sf hSne i)
        exact hroot_root _ hsj
      · obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp hqg
        rw [← hjq]
        obtain ⟨_, _, hsj⟩ := barStep_S_mem st.1 Dm δ i j hj
        exact hroot_root j hsj
    have hlab2_i : lab2 i = some R := by rw [hlab2]; simp
    have hlab2_ne : ∀ v, v ≠ i → lab2 v =
        (match st.1 v with | some r => if r ∈ M then some R else some r | none => none) := by
      intro v hv; rw [hlab2]; simp [hv]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v
      by_cases hv : v = i
      · rw [hv, hlab2_i]; simp [hiP]
      · cases h : st.1 v with
        | none =>
          rw [hlab2_ne v hv, h]
          have hnp : v ∉ P := by
            intro hvp
            have hs1 := (hmem v).mpr hvp
            rw [h] at hs1
            simp at hs1
          simp [hv, Set.mem_insert_iff, hnp]
        | some r0 =>
          have hvp : v ∈ P := (hmem v).mp (by simp [h])
          have hl2 : lab2 v = (if r0 ∈ M then some R else some r0) := by
            simp [hlab2_ne v hv, h]
          by_cases hr : r0 ∈ M
          · rw [hl2, if_pos hr]
            simp only [Option.isSome_some, true_iff]
            simp [Set.mem_insert_iff, hM_P r0 hr, hvp]
          · rw [hl2, if_neg hr]
            simp only [Option.isSome_some, true_iff]
            simp [Set.mem_insert_iff, hvp]
    · intro v r hv
      by_cases hv' : v = i
      · rw [hv'] at hv; rw [hlab2_i] at hv
        injection hv with hvR
        rw [← hvR]
        have hl2R : lab2 R = (if R ∈ M then some R else some R) := by
          rw [hlab2_ne R hrRob, hrootRootM R hRM]
        rw [hl2R]; simp [hRM]
      · cases h : st.1 v with
        | none => simp [hlab2_ne v hv', h] at hv
        | some r0 =>
          have hl2 : lab2 v = (if r0 ∈ M then some R else some r0) := by
            simp [hlab2_ne v hv', h]
          by_cases hr : r0 ∈ M
          · rw [hl2, if_pos hr] at hv
            injection hv with hvR
            rw [← hvR]
            have hl2R : lab2 R = (if R ∈ M then some R else some R) := by
              rw [hlab2_ne R hrRob, hrootRootM R hRM]
            rw [hl2R]; simp [hRM]
          · rw [hl2, if_neg hr] at hv
            injection hv with hvR
            have hr0is : (st.1 r0).isSome = true := by rw [hptr v r0 h, Option.isSome_some]
            have hr0ne : r0 ≠ i := by
              intro hh; rw [hh] at hr0is; exact hiP ((hmem i).mp hr0is)
            rw [← hvR, hlab2_ne r0 hr0ne, hptr v r0 h]
            simp [hr]
    · intro v r hv
      by_cases hv' : v = i
      · rw [hv'] at hv; rw [hlab2_i] at hv
        injection hv with hvR
        rw [← hvR, hv']; exact horder R (hM_P R hRM)
      · cases h : st.1 v with
        | none => simp [hlab2_ne v hv', h] at hv
        | some r0 =>
          have hl2 : lab2 v = (if r0 ∈ M then some R else some r0) := by
            simp [hlab2_ne v hv', h]
          by_cases hr : r0 ∈ M
          · rw [hl2, if_pos hr] at hv
            injection hv with hvR
            rw [← hvR]
            exact le_trans (helder v r0 h) (hRmax r0 hr)
          · rw [hl2, if_neg hr] at hv
            injection hv with hvR
            rw [← hvR]; exact helder v r0 h
    · intro u v huv
      by_cases hu : u = i
      · rw [hu] at huv; rw [hu]
        by_cases hv : v = i
        · rw [hv, hlab2_i]; exact Or.inl rfl
        · by_cases hvP : v ∈ P
          · have hs : (st.1 v).isSome = true := (hmem v).mpr hvP
            obtain ⟨r0, hr0⟩ := (Option.isSome_iff_exists.mp hs)
            have hrootv : root v = r0 := by rw [hroot_of v hs, hr0]; rfl
            have hvSf : v ∈ Sf := by
              rw [hSf, Finset.mem_filter]
              have hdj : Dm i v ≤ δ := by
                rcases (graphAdj_iff Dm δ i v).mp huv with ⟨_, h⟩
                rcases h with h | h
                · exact h
                · rw [hDm]; exact h
              exact ⟨Finset.mem_univ v, hv, hdj, hs⟩
            have hce : st.1 v = some (root v) := by rw [hrootv]; exact hr0
            have hl2 : lab2 v = (if root v ∈ M then some R else some (root v)) := by
              simp [hlab2_ne v hv, hce]
            have hvR : lab2 v = some R := by
              rw [hl2, if_pos (hroot_mem_M v hvSf)]
            rw [hlab2_i, hvR]; exact Or.inl rfl
          · have hvn : st.1 v = none := by
              cases hh : st.1 v with
              | none => rfl
              | some r => exact absurd ((hmem v).mp (by simp [hh])) hvP
            rw [hlab2_i, hlab2_ne v hv, hvn]
            exact Or.inr (Or.inr (by simp))
      · by_cases hv : v = i
        · rw [hv] at huv; rw [hv]
          by_cases huP : u ∈ P
          · have hs : (st.1 u).isSome = true := (hmem u).mpr huP
            obtain ⟨r0, hr0⟩ := (Option.isSome_iff_exists.mp hs)
            have hrootu : root u = r0 := by rw [hroot_of u hs, hr0]; rfl
            have huSf : u ∈ Sf := by
              rw [hSf, Finset.mem_filter]
              have hdj : Dm i u ≤ δ := by
                rcases (graphAdj_iff Dm δ u i).mp huv with ⟨_, h⟩
                rcases h with h | h
                · rw [hDm]; exact h
                · exact h
              exact ⟨Finset.mem_univ u, hu, hdj, hs⟩
            have hce : st.1 u = some (root u) := by rw [hrootu]; exact hr0
            have hl2 : lab2 u = (if root u ∈ M then some R else some (root u)) := by
              simp [hlab2_ne u hu, hce]
            have huR : lab2 u = some R := by
              rw [hl2, if_pos (hroot_mem_M u huSf)]
            rw [huR, hlab2_i]; exact Or.inl rfl
          · have hun : st.1 u = none := by
              cases hh : st.1 u with
              | none => rfl
              | some r => exact absurd ((hmem u).mp (by simp [hh])) huP
            rw [hlab2_ne u hu, hun, hlab2_i]
            exact Or.inr (Or.inl (by simp))
        · have hisSome_lab2 : ∀ w : Fin n, w ≠ i →
              ((lab2 w).isSome = true ↔ (st.1 w).isSome = true) := by
            intro w hw; rw [hlab2_ne w hw]
            cases h : st.1 w with
            | none => simp [h]
            | some r => by_cases hr : r ∈ M <;> simp [hr, Option.isSome_some]
          rcases hedge u v huv with h | h | h
          · exact Or.inl (by rw [hlab2_ne u hu, hlab2_ne v hv, h])
          · exact Or.inr (Or.inl (fun h2 => h ((hisSome_lab2 u hu).mp h2)))
          · exact Or.inr (Or.inr (fun h2 => h ((hisSome_lab2 v hv).mp h2)))
    · intro v r hv
      by_cases hv' : v = i
      · rw [hv'] at hv; rw [hlab2_i] at hv
        injection hv with hvR
        rw [hv', ← hvR]; exact hconn_i_M R hRM
      · cases h : st.1 v with
        | none => simp [hlab2_ne v hv', h] at hv
        | some r0 =>
          have hl2 : lab2 v = (if r0 ∈ M then some R else some r0) := by
            simp [hlab2_ne v hv', h]
          by_cases hr : r0 ∈ M
          · rw [hl2, if_pos hr] at hv
            injection hv with hvR
            rw [← hvR]
            exact connIn_trans
              (connIn_trans (hconn_i_M R hRM) (connIn_symm (hconn_i_M r0 hr)))
              (connIn_mono (fun x hx => Or.inr hx) (hcomp v r0 h))
          · rw [hl2, if_neg hr] at hv
            injection hv with hvR
            rw [← hvR]; exact connIn_mono (fun x hx => Or.inr hx) (hcomp v r0 h)

/-! #### Fold over a sorted prefix -/

lemma finRange_pairwise_gt (n : ℕ) :
    (List.finRange n).Pairwise (fun a b : Fin n => (a : ℕ) < (b : ℕ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Pairwise.map Fin.castSucc (fun a b h => h) ih
    · simp
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      rw [hb]
      obtain ⟨a', _, rfl⟩ := List.mem_map.mp ha
      exact Fin.castSucc_lt_last a'

lemma sweep_fold {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (σ : Fin n ≃ Fin n) (l : List (Fin n))
    (hdec : l.Pairwise (fun a b : Fin n => σ.symm a > σ.symm b))
    (st : UFState n × ((EReal × EReal) → ℕ∞)) (P0 : Set (Fin n))
    (h0 : SweepInvP g Dm δ σ st.1 P0)
    (hPa : ∀ a ∈ P0, ∀ b ∈ l, (σ.symm a : Fin n) > σ.symm b) :
    SweepInvP g Dm δ σ (l.foldl (fun st i => barStep g Dm δ σ st i) st).1
      (P0 ∪ (l.toFinset : Set (Fin n))) := by
  induction l generalizing st P0 with
  | nil => simpa using h0
  | cons i rest ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hdec
    have hset : P0 ∪ (↑(i :: rest).toFinset : Set (Fin n))
        = insert i P0 ∪ (↑rest.toFinset : Set (Fin n)) := by
      simp [List.toFinset_cons, Set.union_insert, Set.insert_union]
    rw [List.foldl_cons, hset]
    have hiP : i ∉ P0 := by
      intro hi
      exact absurd (hPa i hi i (by simp)) (lt_irrefl _)
    refine ih hrest (barStep g Dm δ σ st i) (insert i P0)
      (barStep_invP g Dm δ hDm σ st P0 i h0 hiP
        (fun v hv => le_of_lt (hPa v hv i (by simp)))) ?_
    intro a ha b hb
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hhead b hb
    · exact lt_trans (hhead b hb) (hPa a ha i (by simp))

lemma sweep_order_pairwise {n : ℕ} (σ : Fin n ≃ Fin n) :
    (((List.finRange n).reverse).map σ).Pairwise
      (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
  rw [List.pairwise_map]
  simp only [Equiv.symm_apply_apply]
  rw [List.finRange_reverse, List.pairwise_map]
  exact (finRange_pairwise_gt n).imp (fun {a b} h => Fin.rev_lt_rev.mpr h)

/-! #### Fold-splitting support (checkpoints of the sweep)

The sweep list `L := ((List.finRange n).reverse.map σ)` lists all vertices in grade
order (grades weakly decrease along it).  We split it at grade thresholds to reach the
two checkpoint states: after all vertices of grade `> d` (the `Φ⁺` checkpoint) and
after all vertices of grade `≥ d` (the `Φ⁻` checkpoint). -/

/-- Every vertex occurs in the sweep list. -/
lemma L_mem {n : ℕ} (σ : Fin n ≃ Fin n) (v : Fin n) :
    v ∈ ((List.finRange n).reverse.map σ) := by
  refine List.mem_map.mpr ⟨σ.symm v, ?_, ?_⟩
  · exact List.mem_reverse.mpr (List.mem_finRange _)
  · simp [Equiv.apply_symm_apply]

/-- The full sweep is one fold over the sweep list. -/
lemma barRun_as_fold {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) :
    barRun g Dm δ σ
      = ((List.finRange n).reverse.map σ).foldl
          (fun st i => barStep g Dm δ σ st i) ((fun _ => none), (fun _ => 0)) := by
  have hf := (List.foldl_map (f := (σ : Fin n → Fin n))
    (g := fun (st : UFState n × ((EReal × EReal) → ℕ∞)) (i : Fin n) =>
      barStep g Dm δ σ st i)
    (l := (List.finRange n).reverse)
    (init := ((fun _ => none), (fun _ => 0)))).symm
  unfold barRun
  exact hf

/-- Strictly higher grades are processed strictly earlier (larger `σ.symm`). -/
lemma symm_lt_of_g_lt {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ)
    {a b : Fin n} (h : g b < g a) : σ.symm b < σ.symm a := by
  by_contra hcon
  have hle : σ.symm a ≤ σ.symm b := not_lt.mp hcon
  have hm := hσ hle
  have hma : (g ∘ ⇑σ) (σ.symm a) = g a := by
    rw [Function.comp_apply, Equiv.apply_symm_apply]
  have hmb : (g ∘ ⇑σ) (σ.symm b) = g b := by
    rw [Function.comp_apply, Equiv.apply_symm_apply]
  rw [hma, hmb] at hm
  linarith

/-- Grades weakly decrease along the sweep list. -/
lemma L_pairwise_ge {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    (((List.finRange n).reverse.map σ).Pairwise (fun a b : Fin n => g b ≤ g a)) :=
  (sweep_order_pairwise σ).imp
    (fun {_ _} h => g_le_of_symm_le g σ hσ (le_of_lt h))

/-- Split a list whose `key` values weakly decrease along it at a threshold: the upper
chunk collects the entries `≥ thr`, the lower chunk the entries `< thr`, and both chunks
again have weakly decreasing keys. -/
lemma rsplit {α : Type*} {β : Type*} [LinearOrder β] (l : List α) (key : α → β) (thr : β)
    (h : l.Pairwise (fun a b : α => key b ≤ key a)) :
    ∃ l₁ l₂ : List α, l = l₁ ++ l₂ ∧ (∀ x ∈ l₁, thr ≤ key x) ∧ (∀ y ∈ l₂, key y < thr)
      ∧ l₁.Pairwise (fun a b : α => key b ≤ key a)
      ∧ l₂.Pairwise (fun a b : α => key b ≤ key a) := by
  induction l with
  | nil => exact ⟨[], [], rfl, by simp, by simp, by simp⟩
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    by_cases hp : thr ≤ key a
    · obtain ⟨l₁, l₂, heq, h1, h2, -⟩ := ih ht
      refine ⟨a :: l₁, l₂, by rw [heq]; exact List.cons_append, ?_, h2, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hp
        · exact h1 x hx
      · have hfull : List.Pairwise (fun a b : α => key b ≤ key a) (a :: t) := h
        rw [show a :: t = (a :: l₁) ++ l₂ by rw [heq]; exact List.cons_append] at hfull
        exact ((List.pairwise_append.mp hfull).1)
      · have hfull : List.Pairwise (fun a b : α => key b ≤ key a) (a :: t) := h
        rw [show a :: t = (a :: l₁) ++ l₂ by rw [heq]; exact List.cons_append] at hfull
        exact ((List.pairwise_append.mp hfull).2.1)
    · have hkey : key a < thr := not_le.mp hp
      have hall : ∀ y ∈ t, key y < thr := by
        intro y hy
        have := ha y hy
        exact lt_of_le_of_lt this hkey
      refine ⟨[], a :: t, rfl, by simp, fun y hy => ?_, by simp, h⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hkey
      · exact hall y hy

/-- Strict variant: the upper chunk collects the entries strictly above the threshold. -/
lemma rsplit_strict {α : Type*} {β : Type*} [LinearOrder β] (l : List α) (key : α → β)
    (thr : β) (h : l.Pairwise (fun a b : α => key b ≤ key a)) :
    ∃ l₁ l₂ : List α, l = l₁ ++ l₂ ∧ (∀ x ∈ l₁, thr < key x) ∧ (∀ y ∈ l₂, key y ≤ thr)
      ∧ l₁.Pairwise (fun a b : α => key b ≤ key a)
      ∧ l₂.Pairwise (fun a b : α => key b ≤ key a) := by
  induction l with
  | nil => exact ⟨[], [], rfl, by simp, by simp, by simp⟩
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    by_cases hp : thr < key a
    · obtain ⟨l₁, l₂, heq, h1, h2, -⟩ := ih ht
      refine ⟨a :: l₁, l₂, by rw [heq]; exact List.cons_append, ?_, h2, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hp
        · exact h1 x hx
      · have hfull : List.Pairwise (fun a b : α => key b ≤ key a) (a :: t) := h
        rw [show a :: t = (a :: l₁) ++ l₂ by rw [heq]; exact List.cons_append] at hfull
        exact ((List.pairwise_append.mp hfull).1)
      · have hfull : List.Pairwise (fun a b : α => key b ≤ key a) (a :: t) := h
        rw [show a :: t = (a :: l₁) ++ l₂ by rw [heq]; exact List.cons_append] at hfull
        exact ((List.pairwise_append.mp hfull).2.1)
    · have hkey : key a ≤ thr := not_lt.mp hp
      have hall : ∀ y ∈ t, key y ≤ thr := by
        intro y hy
        exact (ha y hy).trans hkey
      refine ⟨[], a :: t, rfl, by simp, fun y hy => ?_, by simp, h⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hkey
      · exact hall y hy

/-! #### Components of the induced subgraph, and the root↔component bijection -/

/-- The component of `i` in the subgraph of the Rips graph induced on `P`. -/
def compIn {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (P : Set (Fin n)) (i : Fin n) :
    Set (Fin n) := {j | connIn Dm δ P i j}

/-- All components of the Rips graph induced on `P`. -/
def compsIn {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (P : Set (Fin n)) :
    Set (Set (Fin n)) := (fun i : Fin n => compIn Dm δ P i) '' P

lemma connIn_refl {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (P : Set (Fin n)) (i : Fin n) :
    connIn Dm δ P i i := Relation.ReflTransGen.refl

/-- Connected vertices have equal components (within the induced subgraph). -/
lemma compIn_eq_of_mem {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) {P : Set (Fin n)}
    {i j : Fin n} (h : connIn Dm δ P i j) : compIn Dm δ P i = compIn Dm δ P j := by
  ext k
  constructor
  · intro hik
    exact Relation.ReflTransGen.trans (connIn_symm h) hik
  · intro hjk
    exact Relation.ReflTransGen.trans h hjk

/-- At an invariant state, vertices of `P` connected inside `P` share a label. -/
lemma lab_constantP {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (lab : UFState n) (P : Set (Fin n))
    (hinv : SweepInvP g Dm δ σ lab P) {u v : Fin n} (h : connIn Dm δ P u v) :
    lab u = lab v := by
  induction h with
  | refl => rfl
  | tail hprev hstep ih =>
    obtain ⟨hprevP, hcurP, hadj⟩ := hstep
    rcases hinv.2.2.2.1 _ _ hadj with heq | hn1 | hn2
    · rw [← heq, ih]
    · exact absurd ((hinv.1 _).mpr hprevP) hn1
    · exact absurd ((hinv.1 _).mpr hcurP) hn2

/-- At an invariant state, every label is an elder: `g v ≤ g r`. -/
lemma lab_elderP {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) (lab : UFState n) (P : Set (Fin n))
    (hinv : SweepInvP g Dm δ σ lab P) {v r : Fin n} (hv : lab v = some r) : g v ≤ g r :=
  g_le_of_symm_le g σ hσ (hinv.2.2.1 v r hv)

/-- The component of a root `r` of an invariant state has maximum grade `g r`. -/
lemma compIn_maxgIs {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) (lab : UFState n) (P : Set (Fin n))
    (hinv : SweepInvP g Dm δ σ lab P) {r : Fin n} (hrr : lab r = some r) :
    maxgIs g (g r) (compIn Dm δ P r) := by
  refine ⟨⟨r, connIn_refl Dm δ P r, rfl⟩, ?_⟩
  intro j hj
  have hjr : lab j = lab r :=
    (lab_constantP g Dm δ σ lab P hinv hj).symm
  rw [← hjr] at hrr
  exact lab_elderP g Dm δ σ hσ lab P hinv hrr

/-- Pick the root of a component of the induced subgraph on `P`. -/
noncomputable def compRootP {n : ℕ} (hn : 0 < n) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (P : Set (Fin n)) (lab : UFState n) (C : Set (Fin n)) : Fin n :=
  if h : ∃ u, u ∈ P ∧ compIn Dm δ P u = C then (lab (Classical.choose h)).getD (Classical.choose h)
  else ⟨0, hn⟩

/-- **The root↔component bijection.**  At any invariant state, the map `r ↦ compIn r`
is a bijection from the roots onto `compsIn P`; consequently, for every component
predicate `Ψ` the number of roots whose component satisfies `Ψ` equals the number of
components satisfying `Ψ`. -/
lemma encard_roots_eq_comps {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) (lab : UFState n) (P : Set (Fin n))
    (hinv : SweepInvP g Dm δ σ lab P) (Ψ : Set (Fin n) → Prop) :
    ({r : Fin n | lab r = some r ∧ Ψ (compIn Dm δ P r)} : Set (Fin n)).encard
      = ({C ∈ compsIn Dm δ P | Ψ C} : Set (Set (Fin n))).encard := by
  classical
  set A : Set (Fin n) := {r : Fin n | lab r = some r ∧ Ψ (compIn Dm δ P r)} with hA
  set B : Set (Set (Fin n)) := {C ∈ compsIn Dm δ P | Ψ C} with hB
  have hAm : ∀ r : Fin n, r ∈ A ↔ lab r = some r ∧ Ψ (compIn Dm δ P r) := by
    intro r; simp [hA]
  have hBm : ∀ C : Set (Fin n), C ∈ B ↔ C ∈ compsIn Dm δ P ∧ Ψ C := by
    intro C; simp [hB]
  -- every root lies in `P`, so `compIn` maps roots into `compsIn`
  have hrootP : ∀ r : Fin n, lab r = some r → r ∈ P := by
    intro r hr
    exact (hinv.1 r).mp (by rw [hr]; rfl)
  have himg : ∀ r : Fin n, r ∈ A → compIn Dm δ P r ∈ B := by
    intro r hr
    obtain ⟨hrr, hΨ⟩ := (hAm r).mp hr
    exact (hBm _).mpr ⟨⟨r, hrootP r hrr, rfl⟩, hΨ⟩
  -- injection `A → B` (via the component map)
  have h1 : A.encard ≤ B.encard :=
    Set.encard_le_encard_of_injOn (f := fun r : Fin n => compIn Dm δ P r)
      (fun r hr => himg r hr)
      (by intro r₁ hr₁ r₂ hr₂ heq
          have heq' : compIn Dm δ P r₁ = compIn Dm δ P r₂ := heq
          have hr₂mem : r₂ ∈ compIn Dm δ P r₁ := by rw [heq']; exact connIn_refl Dm δ P r₂
          have hlab : lab r₁ = lab r₂ := lab_constantP g Dm δ σ lab P hinv hr₂mem
          obtain ⟨hrr₁, -⟩ := (hAm r₁).mp hr₁
          obtain ⟨hrr₂, -⟩ := (hAm r₂).mp hr₂
          rw [hrr₁, hrr₂] at hlab
          exact Option.some.inj hlab)
  -- injection `B → A` via `compRootP`
  have hspec : ∀ C ∈ B, compRootP hn Dm δ P lab C ∈ A ∧ compIn Dm δ P (compRootP hn Dm δ P lab C) = C := by
    intro C hC
    obtain ⟨hCcomps, hΨ⟩ := (hBm C).mp hC
    obtain ⟨u, huP, huC⟩ := hCcomps
    have hex : ∃ u, u ∈ P ∧ compIn Dm δ P u = C := ⟨u, huP, huC⟩
    have hu0 := Classical.choose_spec hex
    have hcr : compRootP hn Dm δ P lab C = (lab (Classical.choose hex)).getD (Classical.choose hex) := by
      rw [compRootP, dif_pos hex]
    have hsome : ∃ r, lab (Classical.choose hex) = some r := by
      have := (hinv.1 (Classical.choose hex)).mpr hu0.1
      exact Option.isSome_iff_exists.mp this
    obtain ⟨r0, hr0⟩ := hsome
    have hget : (lab (Classical.choose hex)).getD (Classical.choose hex) = r0 := by
      rw [hr0]; rfl
    have hptr0 : lab r0 = some r0 := hinv.2.1 _ r0 hr0
    have hconn : connIn Dm δ P r0 (Classical.choose hex) := hinv.2.2.2.2 _ r0 hr0
    have hcompeq : compIn Dm δ P r0 = C := (compIn_eq_of_mem Dm δ hconn).trans hu0.2
    rw [hcr, hget]
    refine ⟨(hAm _).mpr ⟨hptr0, by rw [hcompeq]; exact hΨ⟩, hcompeq⟩
  have h2 : B.encard ≤ A.encard :=
    Set.encard_le_encard_of_injOn (f := compRootP hn Dm δ P lab)
      (fun C hC => (hspec C hC).1)
      (by intro C₁ hC₁ C₂ hC₂ heq
          rw [← (hspec C₁ hC₁).2, heq, (hspec C₂ hC₂).2])
  exact le_antisymm h1 h2

/-! #### Per-step accumulator / root analysis

The sweep is a fold of `barStep`; each step either leaves the accumulator unchanged
(peak: no live neighbour) or adds, at the points `((g r, g i))` for the dying roots `r`,
one unit of mass. -/

/-- A death recorded at `((b, d))` requires the death level `g i` to equal `d`; hence a
step at a vertex whose grade is not `d` leaves the accumulator at `((b, d))` unchanged. -/
lemma step_acc_ne {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (st : UFState n × ((EReal × EReal) → ℕ∞)) (i : Fin n)
    (b d : ℝ) (hgi : g i ≠ d) :
    (barStep g Dm δ σ st i).2 ((b : EReal), (d : EReal)) = st.2 ((b : EReal), (d : EReal)) := by
  rw [barStep]
  set lab := st.1 with hlab
  set acc := st.2 with hacc
  set Sf : Finset (Fin n) :=
    Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) with hSf
  by_cases hS : Sf = ∅
  · rw [if_pos hS]
  · rw [if_neg hS]
    set root : Fin n → Fin n := fun j => (lab j).getD j with hroot
    set ri : Fin n := root (firstProcessed σ Sf i) with hri
    set M : Finset (Fin n) := insert ri (Sf.image root) with hM
    set R : Fin n := firstProcessed σ M ri with hR
    set dying : Finset (Fin n) :=
      (M.erase R).filter (fun r => (g i : EReal) < (g r : EReal)) with hdying
    set acc2 : EReal × EReal → ℕ∞ :=
      fun p => acc p + dying.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then 1 else 0)
        with hacc2
    show acc2 ((b : EReal), (d : EReal)) = acc ((b : EReal), (d : EReal))
    have hsum : dying.sum
        (fun r => if ((b : EReal), (d : EReal)) = ((g r : EReal), (g i : EReal))
            then (1 : ℕ∞) else 0) = 0 := by
      refine Finset.sum_eq_zero fun r _ => if_neg fun h => hgi ?_
      exact (EReal.coe_injective ((Prod.ext_iff.mp h).2)).symm
    simp only [hacc2]
    rw [hsum, add_zero]

/-- Sum of indicators over a finset equals the cardinality of the filtered set. -/
lemma sum_indicator_card {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    s.sum (fun r => if P r then (1 : ℕ∞) else 0) = ((s.filter P).card : ℕ∞) := by
  rw [Finset.sum_ite]
  rw [Finset.sum_const, Finset.sum_const]
  simp [nsmul_eq_mul]

/-- The pointwise per-step telescope: processing a vertex of grade `d` at an invariant
state, the accumulator at `((b, d))` gains exactly as much mass as the number of
grade-`b` roots that die in the step.  Hence `acc((b,d)) + #(grade-`b` roots)` is
invariant along the whole sweep. -/
lemma step_telescope {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) (st : UFState n × ((EReal × EReal) → ℕ∞))
    (P : Set (Fin n)) (i : Fin n) (hinv : SweepInvP g Dm δ σ st.1 P) (hiP : i ∉ P)
    {b d : ℝ} (hbd : d < b) (hgi : g i = d) :
    (barStep g Dm δ σ st i).2 ((b : EReal), (d : EReal))
      + ({r : Fin n | (barStep g Dm δ σ st i).1 r = some r ∧ g r = b}).encard
    = st.2 ((b : EReal), (d : EReal))
      + ({r : Fin n | st.1 r = some r ∧ g r = b}).encard := by
  classical
  rw [barStep]
  set lab := st.1 with hlab
  set acc := st.2 with hacc
  set Sf : Finset (Fin n) :=
    Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) with hSf
  obtain ⟨hmem, hptr, helder, hedge, hcomp⟩ := hinv
  have hlabnone : lab i = none := by
    cases hh : lab i with
    | none => rfl
    | some r => exact absurd ((hmem i).mp (by simp [hh])) hiP
  by_cases hS : Sf = ∅
  · -- peak step: new root `i` of grade `d ≠ b`; accumulator unchanged
    rw [if_pos hS]
    have hset : {r : Fin n | (Function.update lab i (some i)) r = some r ∧ g r = b}
        = {r : Fin n | lab r = some r ∧ g r = b} := by
      ext r
      by_cases hr : r = i
      · subst hr
        have hne : ¬ (d = b) := ne_of_lt hbd
        simp only [Set.mem_setOf_eq, Function.update_self, hgi, hlabnone]
        constructor
        · rintro ⟨-, hgb⟩; exact absurd hgb hne
        · rintro ⟨-, hgb⟩; exact absurd hgb hne
      · simp only [Set.mem_setOf_eq, Function.update_of_ne hr]
    show acc ((b : EReal), (d : EReal))
      + ({r : Fin n | (Function.update lab i (some i)) r = some r ∧ g r = b}).encard
      = acc ((b : EReal), (d : EReal)) + ({r : Fin n | lab r = some r ∧ g r = b}).encard
    rw [hset]
  · -- merge step
    rw [if_neg hS]
    simp only [Prod.snd, Prod.fst]
    set root : Fin n → Fin n := fun j => (lab j).getD j with hroot
    set ri : Fin n := root (firstProcessed σ Sf i) with hri
    set M : Finset (Fin n) := insert ri (Sf.image root) with hM
    set R : Fin n := firstProcessed σ M ri with hR
    set lab2 : UFState n := fun v =>
      if v = i then some R
      else match lab v with
        | some r => if r ∈ M then some R else some r
        | none => none with hlab2
    set dying : Finset (Fin n) :=
      (M.erase R).filter (fun r => (g i : EReal) < (g r : EReal)) with hdying
    set acc2 : EReal × EReal → ℕ∞ :=
      fun p => acc p + dying.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then 1 else 0)
        with hacc2
    have hSne : Sf.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    have hMne : M.Nonempty := ⟨ri, by rw [hM]; exact Finset.mem_insert_self _ _⟩
    have hRM : R ∈ M := by rw [hR]; exact firstProcessed_mem σ M hMne ri
    have hSf_some : ∀ j ∈ Sf, (lab j).isSome := by
      intro j hj; exact ((Finset.mem_filter.mp hj).2).2.2
    have hroot_val : ∀ j ∈ Sf, ∃ r, lab j = some r ∧ root j = r := by
      intro j hj
      obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp (hSf_some j hj)
      exact ⟨r0, hr0, by simp [hroot, hr0]⟩
    have hMroot : ∀ q ∈ M, lab q = some q := by
      intro q hq
      rw [hM] at hq
      rcases Finset.mem_insert.mp hq with hq | hq
      · rw [hq, hri]
        have hfpS : firstProcessed σ Sf i ∈ Sf := firstProcessed_mem σ Sf hSne i
        obtain ⟨r0, hr0lab, hr0r⟩ := hroot_val _ hfpS
        rw [hr0r]
        exact hptr _ r0 hr0lab
      · obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp hq
        rw [← hjq]
        obtain ⟨r0, hr0lab, hr0r⟩ := hroot_val j hj
        rw [hr0r]
        exact hptr j r0 hr0lab
    have hM_P : ∀ q ∈ M, q ∈ P := by
      intro q hq
      have hr := hMroot q hq
      exact (hmem q).mp (by rw [hr]; rfl)
    have hRi : R ≠ i := fun hh => hiP (hh ▸ hM_P R hRM)
    have hRroot : lab R = some R := hMroot R hRM
    -- finite-set encoding of "grade-`b` roots"
    set brootsF : UFState n → Finset (Fin n) :=
      fun L => Finset.univ.filter (fun r => L r = some r ∧ g r = b) with hbrootsF
    set DiedB : Finset (Fin n) := (M.erase R).filter (fun r => g r = b) with hDiedB
    have hF4 : ∀ L : UFState n,
        ({r : Fin n | L r = some r ∧ g r = b}).encard = ((brootsF L).card : ℕ∞) := by
      intro L
      have hset : ({r : Fin n | L r = some r ∧ g r = b} : Set (Fin n)).toFinset = brootsF L := by
        ext r; simp [hbrootsF, Finset.mem_filter]
      rw [Set.encard_eq_coe_toFinset_card, hset]
    -- membership forms
    have hmemB : ∀ (L : UFState n) (v : Fin n),
        v ∈ brootsF L ↔ (L v = some v ∧ g v = b) := by
      intro L v
      simp only [hbrootsF, Finset.mem_filter, Finset.mem_univ, true_and]
    have hmemD : ∀ v : Fin n, v ∈ DiedB ↔ (v ≠ R ∧ v ∈ M ∧ g v = b) := by
      intro v
      simp only [hDiedB, Finset.mem_filter, Finset.mem_erase, and_assoc]
    -- match reductions
    have hred_none : (match (none : Option (Fin n)) with
          | some q => if q ∈ M then some R else some q
          | none => none) = none := by
      simp
    have hred_some : ∀ u : Fin n,
        (match (some u : Option (Fin n)) with
          | some q => if q ∈ M then some R else some q
          | none => none) = (if u ∈ M then some R else some u) := by
      intro u; simp
    -- `lab2` keeps `v` as its own root iff `v`'s root is itself and `v` is neither a merged
    -- root that died nor a mere member of `M`; the survivor `R` is the sole exception.
    have hl2char : ∀ v : Fin n, v ≠ i →
        (lab2 v = some v ↔ (lab v = some v ∧ (v ∉ M ∨ v = R))) := by
      intro v hv
      have hx : lab2 v = match lab v with
          | some q => if q ∈ M then some R else some q
          | none => none := by
        simp only [hlab2, if_neg hv]
      constructor
      · intro heq
        rw [hx] at heq
        by_cases hl : lab v = none
        · rw [hl, hred_none] at heq
          exact absurd heq.symm (Option.some_ne_none v)
        · obtain ⟨q, hq⟩ : ∃ q, lab v = some q := by
            cases hh : lab v with
            | none => exact absurd hh hl
            | some q => exact ⟨q, rfl⟩
          rw [hq, hred_some q] at heq
          by_cases hqM : q ∈ M
          · rw [if_pos hqM] at heq
            have hRv : R = v := Option.some.inj heq
            have h1 : lab v = some R := by rw [← hRv, ← hRroot]
            exact ⟨by rw [h1, hRv], Or.inr hRv.symm⟩
          · rw [if_neg hqM] at heq
            have hqv : q = v := Option.some.inj heq
            rw [hqv] at hq hqM
            exact ⟨hq, Or.inl hqM⟩
      · rintro ⟨hlabb, hcond⟩
        have hredv : (match lab v with
            | some q => if q ∈ M then some R else some q
            | none => none) = (if v ∈ M then some R else some v) := by
          simp [hlabb]
        rw [hx, hredv]
        rcases hcond with hnotM | hRe
        · rw [if_neg hnotM]
        · have hvM : v ∈ M := by rw [hRe]; exact hRM
          rw [if_pos hvM, hRe]
    -- (F1): the grade-`b` roots after the step are those before, minus the dying ones
    have hF1 : brootsF lab2 = brootsF lab \ DiedB := by
      ext r
      rw [hmemB lab2 r, Finset.mem_sdiff, hmemB lab r, hmemD r]
      by_cases hri2 : r = i
      · have hgrb : ¬ (g r = b) := by
          rw [hri2, hgi]; exact ne_of_lt hbd
        exact ⟨fun h => absurd h.2 hgrb, fun h => absurd h.1.2 hgrb⟩
      · rw [hl2char r hri2]
        constructor
        · rintro ⟨⟨hlabb, hcond⟩, hgb⟩
          refine ⟨⟨hlabb, hgb⟩, ?_⟩
          rintro ⟨hrne, hrM, _⟩
          rcases hcond with hnotM | hRe
          · exact hnotM hrM
          · exact hrne hRe
        · rintro ⟨⟨hlabb, hgb⟩, hneg⟩
          refine ⟨⟨hlabb, ?_⟩, hgb⟩
          by_contra hcon
          push_neg at hcon
          exact hneg ⟨hcon.2, hcon.1, hgb⟩
    have hF2 : DiedB ⊆ brootsF lab := by
      intro r hr
      obtain ⟨hm, hgb⟩ := Finset.mem_filter.mp hr
      obtain ⟨hrne, hrM⟩ := Finset.mem_erase.mp hm
      rw [hmemB]
      exact ⟨hMroot r hrM, hgb⟩
    -- (F3): the accumulator gain at `((b,d))` is the number of dying grade-`b` roots
    have hF3 : dying.sum
        (fun r => if ((b : EReal), (d : EReal)) = ((g r : EReal), (g i : EReal))
            then (1 : ℕ∞) else 0)
        = ((DiedB.card : ℕ∞)) := by
      have hcond : ∀ r : Fin n, ((b : EReal), (d : EReal)) = ((g r : EReal), (g i : EReal))
          ↔ g r = b := by
        intro r
        constructor
        · intro h; exact (EReal.coe_injective ((Prod.ext_iff.mp h).1)).symm
        · intro hr; rw [hr, hgi]
      have hsum1 : dying.sum
          (fun r => if ((b : EReal), (d : EReal)) = ((g r : EReal), (g i : EReal))
              then (1 : ℕ∞) else 0)
          = dying.sum (fun r => if g r = b then (1 : ℕ∞) else 0) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [if_congr (hcond r) rfl rfl]
      have hfil : dying.filter (fun r => g r = b) = DiedB := by
        rw [hdying, hDiedB, Finset.filter_filter]
        refine Finset.filter_congr fun r _ => ?_
        constructor
        · rintro ⟨-, hgb⟩; exact hgb
        · intro hgb
          exact ⟨by rw [hgi, hgb]; exact EReal.coe_lt_coe_iff.mpr hbd, hgb⟩
      rw [hsum1, sum_indicator_card, hfil]
    -- assemble
    have hcard : ((brootsF lab).card : ℕ∞)
        = ((brootsF lab2).card : ℕ∞) + ((DiedB.card : ℕ∞)) := by
      rw [hF1, ← Nat.cast_add, Finset.card_sdiff_add_card_eq_card hF2]
    show acc2 ((b : EReal), (d : EReal))
      + ({r : Fin n | lab2 r = some r ∧ g r = b}).encard
      = acc ((b : EReal), (d : EReal)) + ({r : Fin n | lab r = some r ∧ g r = b}).encard
    have haccval : acc2 ((b : EReal), (d : EReal))
        = acc ((b : EReal), (d : EReal)) + ((DiedB.card : ℕ∞)) := by
      simp only [hacc2]
      rw [hF3]
    rw [haccval, hF4 lab2, hF4 lab, hcard, add_assoc,
      add_comm ((DiedB.card : ℕ∞)) ((brootsF lab2).card : ℕ∞)]
/-- The `lab2` root-characterization used by the per-step telescopes: after a merge step,
`lab2` keeps `v` as its own root iff `v` was its own root and is neither a merged root that
died nor a mere member of `M`; the surviving elder `R` is the sole exception. -/
lemma lab2_root_iff {n : ℕ} (lab2 lab : UFState n) (M : Finset (Fin n)) (R i : Fin n)
    (hlab2 : lab2 = fun v => if v = i then some R
      else match lab v with
        | some r => if r ∈ M then some R else some r
        | none => none)
    (hMroot : ∀ q ∈ M, lab q = some q) (hRM : R ∈ M) {v : Fin n} (hv : v ≠ i) :
    (lab2 v = some v ↔ (lab v = some v ∧ (v ∉ M ∨ v = R))) := by
  have hRroot : lab R = some R := hMroot R hRM
  have hred_none : (match (none : Option (Fin n)) with
        | some q => if q ∈ M then some R else some q
        | none => none) = none := by simp
  have hred_some : ∀ q : Fin n,
      (match (some q : Option (Fin n)) with
        | some q => if q ∈ M then some R else some q
        | none => none) = (if q ∈ M then some R else some q) := by
    intro q; simp
  have hx : lab2 v = match lab v with
      | some q => if q ∈ M then some R else some q
      | none => none := by
    simp only [hlab2, if_neg hv]
  constructor
  · intro heq
    rw [hx] at heq
    by_cases hl : lab v = none
    · rw [hl, hred_none] at heq
      exact absurd heq.symm (Option.some_ne_none v)
    · obtain ⟨q, hq⟩ : ∃ q, lab v = some q := by
        cases hh : lab v with
        | none => exact absurd hh hl
        | some q => exact ⟨q, rfl⟩
      rw [hq, hred_some q] at heq
      by_cases hqM : q ∈ M
      · rw [if_pos hqM] at heq
        have hRv : R = v := Option.some.inj heq
        have h1 : lab v = some R := by rw [← hRv, ← hRroot]
        exact ⟨by rw [h1, hRv], Or.inr hRv.symm⟩
      · rw [if_neg hqM] at heq
        have hqv : q = v := Option.some.inj heq
        rw [hqv] at hq hqM
        exact ⟨hq, Or.inl hqM⟩
  · rintro ⟨hlabb, hcond⟩
    have hredv : (match lab v with
        | some q => if q ∈ M then some R else some q
        | none => none) = (if v ∈ M then some R else some v) := by
      simp [hlabb]
    rw [hx, hredv]
    rcases hcond with hnotM | hRe
    · rw [if_neg hnotM]
    · have hvM : v ∈ M := by rw [hRe]; exact hRM
      rw [if_pos hvM, hRe]

/-- Number of roots of grade exactly `b`. -/
noncomputable def broots {n : ℕ} (g : Fin n → ℝ) (b : ℝ)
    (st : UFState n × ((EReal × EReal) → ℕ∞)) : ℕ∞ :=
  ({r : Fin n | st.1 r = some r ∧ g r = b}).encard

/-- Folding `barStep` over a list all of whose grades differ from `d` leaves the
accumulator at `((b,d))` unchanged. -/
lemma foldl_acc_ne {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (b d : ℝ) (l : List (Fin n)) (hl : ∀ i ∈ l, g i ≠ d)
    (s : UFState n × ((EReal × EReal) → ℕ∞)) :
    (l.foldl (fun st i => barStep g Dm δ σ st i) s).2 ((b : EReal), (d : EReal))
      = s.2 ((b : EReal), (d : EReal)) := by
  induction l generalizing s with
  | nil => simp [List.foldl_nil]
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih (fun j hj => hl j (List.mem_cons.mpr (Or.inr hj))) (barStep g Dm δ σ s i),
      step_acc_ne g Dm δ σ s i b d (hl i (by simp))]

/-- Folding `barStep` over a prefix all of whose grades equal `d`: the accumulator at
`((b,d))` gains exactly the drop in the number of grade-`b` roots. -/
lemma foldl_bd {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ)
    {b d : ℝ} (hbd : d < b) (l : List (Fin n)) (hl : ∀ i ∈ l, g i = d)
    (st : UFState n × ((EReal × EReal) → ℕ∞)) (P0 : Set (Fin n))
    (h0 : SweepInvP g Dm δ σ st.1 P0)
    (hPa : ∀ a ∈ P0, ∀ v ∈ l, (σ.symm a : Fin n) > σ.symm v)
    (hdec : l.Pairwise (fun a v : Fin n => (σ.symm a : Fin n) > σ.symm v)) :
    SweepInvP g Dm δ σ (l.foldl (fun st i => barStep g Dm δ σ st i) st).1
        (P0 ∪ ((l.toFinset : Set (Fin n))))
      ∧ (l.foldl (fun st i => barStep g Dm δ σ st i) st).2 ((b : EReal), (d : EReal))
          + broots g b (l.foldl (fun st i => barStep g Dm δ σ st i) st)
        = st.2 ((b : EReal), (d : EReal)) + broots g b st := by
  induction l generalizing st P0 with
  | nil => simpa using h0
  | cons i rest ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hdec
    have hset : P0 ∪ (↑(i :: rest).toFinset : Set (Fin n))
        = insert i P0 ∪ (↑rest.toFinset : Set (Fin n)) := by
      simp [List.toFinset_cons, Set.union_insert, Set.insert_union]
    rw [List.foldl_cons]
    have hiP : i ∉ P0 := by
      intro hi
      exact absurd (hPa i hi i (by simp)) (lt_irrefl _)
    have hinv' : SweepInvP g Dm δ σ (barStep g Dm δ σ st i).1 (insert i P0) :=
      barStep_invP g Dm δ hDm σ st P0 i h0 hiP
        (fun v hv => le_of_lt (hPa v hv i (by simp)))
    have hstep := step_telescope g Dm δ σ hσ st P0 i h0 hiP hbd (hl i (by simp))
    have hih := ih (fun j hj => hl j (List.mem_cons.mpr (Or.inr hj)))
      (barStep g Dm δ σ st i) (insert i P0)
      hinv'
      (fun a ha v hv => by
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact hhead v hv
        · exact lt_trans (hhead v hv) (hPa a ha i (by simp)))
      hrest
    refine ⟨?_, ?_⟩
    · rw [hset]; exact hih.1
    · rw [hih.2]; exact hstep

/-- At an invariant state, a root `r` spans exactly the components with maximum grade `g r`;
so `maxgIs g b (compIn r) ↔ g r = b` for roots `r`. -/
lemma maxgIs_compIn_iff {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) {P : Set (Fin n)} {lab : UFState n}
    (hinv : SweepInvP g Dm δ σ lab P) {r : Fin n} (hrr : lab r = some r) {b : ℝ} :
    maxgIs g b (compIn Dm δ P r) ↔ g r = b := by
  constructor
  · rintro ⟨⟨i, hiC, hib⟩, hall⟩
    have hgr_le_b : g r ≤ b := hall r (connIn_refl Dm δ P r)
    have hb_le_gr : b ≤ g r := by
      have hlab : lab i = lab r := (lab_constantP g Dm δ σ lab P hinv hiC).symm
      rw [hrr] at hlab
      rw [← hib]
      exact lab_elderP g Dm δ σ hσ lab P hinv hlab
    linarith
  · intro hgb
    have := compIn_maxgIs g Dm δ σ hσ lab P hinv hrr
    rwa [hgb] at this

/-- The strict-upper chunk of the sweep list at `d` collects exactly the vertices of grade
`> d`. -/
lemma chunk_set_above {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n) {d : ℝ}
    {A B : List (Fin n)} (hAB : ((List.finRange n).reverse.map σ) = A ++ B)
    (hAc : ∀ x ∈ A, d < g x) (hBc : ∀ x ∈ B, g x ≤ d) :
    ((A.toFinset : Set (Fin n))) = {v : Fin n | d < g v} := by
  ext v
  simp only [Finset.mem_coe, List.mem_toFinset]
  constructor
  · exact fun hv => hAc v hv
  · intro hgv
    have hvL : v ∈ ((List.finRange n).reverse.map σ) := L_mem σ v
    rw [hAB] at hvL
    rcases List.mem_append.mp hvL with hA | hB
    · exact hA
    · exact absurd hgv (not_lt.mpr (hBc v hB))

/-- The weak-upper chunk of the sweep list at `d` collects exactly the vertices of grade
`≥ d`. -/
lemma chunk_set_above_eq {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n) {d : ℝ}
    {A B : List (Fin n)} (hAB : ((List.finRange n).reverse.map σ) = A ++ B)
    (hAc : ∀ x ∈ A, d ≤ g x) (hBc : ∀ y ∈ B, g y < d) :
    ((A.toFinset : Set (Fin n))) = {v : Fin n | d ≤ g v} := by
  ext v
  simp only [Finset.mem_coe, List.mem_toFinset]
  constructor
  · exact fun hv => hAc v hv
  · intro hgv
    have hvL : v ∈ ((List.finRange n).reverse.map σ) := L_mem σ v
    rw [hAB] at hvL
    rcases List.mem_append.mp hvL with hA | hB
    · exact hA
    · exact absurd hgv (not_le.mpr (hBc v hB))

/-- **Master checkpoint identity (sweep side).**  For real `d < b`, the accumulator of the
full sweep at `((b, d))` plus the number of `G_{≥d}`-components with maximum grade `b`
equals the number of `G_{>d}`-components with maximum grade `b`.  This is the elder-rule
master identity `barcode(b,d) = #comps(G_{>d}, maxg=b) − #comps(G_{≥d}, maxg=b)`. -/
theorem barRun_acc_eq_Vdrop {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ)
    (hn : 0 < n) {b d : ℝ} (hbd : d < b) :
    (barRun g Dm δ σ).2 ((b : EReal), (d : EReal))
      + ({C ∈ compsIn Dm δ ({v : Fin n | d ≤ g v}) | maxgIs g b C} : Set (Set (Fin n))).encard
      = ({C ∈ compsIn Dm δ ({v : Fin n | d < g v}) | maxgIs g b C} : Set (Set (Fin n))).encard := by
  classical
  set L : List (Fin n) := (List.finRange n).reverse.map σ with hL
  have hLpw : L.Pairwise (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
    rw [hL]; exact sweep_order_pairwise σ
  have hLg : L.Pairwise (fun a b : Fin n => g b ≤ g a) := by
    rw [hL]; exact L_pairwise_ge g σ hσ
  obtain ⟨A, B, hAB, hAc, hBc, hBp⟩ := rsplit_strict L g d hLg
  obtain ⟨Ld, Llo, hBL, hLdc, hLloc, hLlOp⟩ := rsplit B g d hBp.2
  have hAB' : L = (A ++ Ld) ++ Llo := by rw [hAB, hBL, List.append_assoc]
  have hAB'' : ((List.finRange n).reverse.map σ) = (A ++ Ld) ++ Llo := hAB'
  -- chunk pairwise-σ
  have hdecA : A.Pairwise (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
    have h := hLpw; rw [hAB] at h; exact (List.pairwise_append.mp h).1
  have hdecADd : (A ++ Ld).Pairwise (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
    have h := hLpw; rw [hAB'] at h; exact (List.pairwise_append.mp h).1
  have hdecLd : Ld.Pairwise (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
    have h := hLpw; rw [hAB] at h
    have hB := (List.pairwise_append.mp h).2.1
    rw [hBL] at hB; exact (List.pairwise_append.mp hB).1
  -- chunk set-equalities
  have hsetA : ((A.toFinset : Set (Fin n))) = {v : Fin n | d < g v} :=
    chunk_set_above g σ hAB hAc hBc
  have hA'c : ∀ x ∈ A ++ Ld, d ≤ g x := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact le_of_lt (hAc x h)
    · exact hLdc x h
  have hsetADd : (((A ++ Ld).toFinset : Set (Fin n))) = {v : Fin n | d ≤ g v} :=
    chunk_set_above_eq g σ hAB' hA'c hLloc
  -- fold states
  set s0 : UFState n × ((EReal × EReal) → ℕ∞) := ((fun _ => none), (fun _ => 0)) with hs0
  set sP : UFState n × ((EReal × EReal) → ℕ∞) :=
    A.foldl (fun st i => barStep g Dm δ σ st i) s0 with hsP
  set sQ : UFState n × ((EReal × EReal) → ℕ∞) :=
    (A ++ Ld).foldl (fun st i => barStep g Dm δ σ st i) s0 with hsQ
  have hsQ_eq : sQ = Ld.foldl (fun st i => barStep g Dm δ σ st i) sP := by
    rw [hsQ, hsP, List.foldl_append]
  -- invariants at the checkpoints
  have hinvP : SweepInvP g Dm δ σ sP.1 ({v : Fin n | d < g v}) := by
    have h := sweep_fold g Dm δ hDm σ A hdecA s0 ∅ (init_invP g Dm δ σ)
      (by intro a ha; simp at ha)
    rw [Set.empty_union, hsetA] at h
    exact h
  have hinvQ : SweepInvP g Dm δ σ sQ.1 ({v : Fin n | d ≤ g v}) := by
    have h := sweep_fold g Dm δ hDm σ (A ++ Ld) hdecADd s0 ∅ (init_invP g Dm δ σ)
      (by intro a ha; simp at ha)
    rw [Set.empty_union, hsetADd] at h
    exact h
  -- grade-`d` condition and order condition for the middle chunk
  have hLd : ∀ i ∈ Ld, g i = d := by
    intro i hi
    have hiB : i ∈ B := by rw [hBL]; exact List.mem_append_left Llo hi
    exact le_antisymm (hBc i hiB) (hLdc i hi)
  have hPaLd : ∀ a ∈ ({v : Fin n | d < g v} : Set (Fin n)), ∀ v ∈ Ld,
      (σ.symm a : Fin n) > σ.symm v := by
    intro a ha v hv
    exact symm_lt_of_g_lt g σ hσ (by rw [hLd v hv]; exact ha)
  -- accumulator facts
  have haccP : sP.2 ((b : EReal), (d : EReal)) = 0 := by
    rw [hsP]
    rw [foldl_acc_ne g Dm δ σ b d A (fun i hi => ne_of_gt (hAc i hi)) s0]
  have htelesc := foldl_bd g Dm δ hDm σ hσ hbd Ld hLd sP ({v : Fin n | d < g v})
    hinvP hPaLd hdecLd
  have ht2 : sQ.2 ((b : EReal), (d : EReal)) + broots g b sQ
      = broots g b sP := by
    rw [hsQ_eq]
    rw [htelesc.2, haccP, zero_add]
  have hbar : barRun g Dm δ σ = Llo.foldl (fun st i => barStep g Dm δ σ st i) sQ := by
    rw [barRun_as_fold]
    rw [hAB'', List.foldl_append, hsQ]
  have haccLlo : (Llo.foldl (fun st i => barStep g Dm δ σ st i) sQ).2 ((b : EReal), (d : EReal))
      = sQ.2 ((b : EReal), (d : EReal)) :=
    foldl_acc_ne g Dm δ σ b d Llo (fun i hi => ne_of_lt (hLloc i hi)) sQ
  -- bijection at both checkpoints
  have hbioP : broots g b sP
      = ({C ∈ compsIn Dm δ ({v : Fin n | d < g v}) | maxgIs g b C} : Set (Set (Fin n))).encard := by
    have hset : {r : Fin n | sP.1 r = some r ∧ g r = b}
        = {r : Fin n | sP.1 r = some r
            ∧ maxgIs g b (compIn Dm δ ({v : Fin n | d < g v}) r)} := by
      ext r
      constructor
      · rintro ⟨hrr, hgb⟩
        exact ⟨hrr, (maxgIs_compIn_iff g Dm δ σ hσ hinvP hrr).mpr hgb⟩
      · rintro ⟨hrr, hmax⟩
        exact ⟨hrr, (maxgIs_compIn_iff g Dm δ σ hσ hinvP hrr).mp hmax⟩
    unfold broots
    rw [hset]
    exact encard_roots_eq_comps hn g Dm δ σ hσ sP.1 ({v : Fin n | d < g v}) hinvP
      (fun C => maxgIs g b C)
  have hbioQ : broots g b sQ
      = ({C ∈ compsIn Dm δ ({v : Fin n | d ≤ g v}) | maxgIs g b C} : Set (Set (Fin n))).encard := by
    have hset : {r : Fin n | sQ.1 r = some r ∧ g r = b}
        = {r : Fin n | sQ.1 r = some r
            ∧ maxgIs g b (compIn Dm δ ({v : Fin n | d ≤ g v}) r)} := by
      ext r
      constructor
      · rintro ⟨hrr, hgb⟩
        exact ⟨hrr, (maxgIs_compIn_iff g Dm δ σ hσ hinvQ hrr).mpr hgb⟩
      · rintro ⟨hrr, hmax⟩
        exact ⟨hrr, (maxgIs_compIn_iff g Dm δ σ hσ hinvQ hrr).mp hmax⟩
    unfold broots
    rw [hset]
    exact encard_roots_eq_comps hn g Dm δ σ hσ sQ.1 ({v : Fin n | d ≤ g v}) hinvQ
      (fun C => maxgIs g b C)
  rw [hbar, haccLlo, ← hbioQ, ← hbioP]
  exact ht2

/-! #### Analytic bridge: rank windows = component windows -/

/-- The `classAt` class of a vertex in `L^t` is its induced-subgraph component. -/
lemma classAt_eq_compIn {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) {i : Fin n} (hie : t ≤ g i) :
    classAt g Dm δ t i = compIn Dm δ ({v : Fin n | t ≤ g v} : Set (Fin n)) i := by
  ext j
  constructor
  · rintro ⟨-, hrt⟩
    exact rtg_mono (fun a b h => ⟨h.1, h.2.1, h.2.2⟩) hrt
  · intro hrt
    exact ⟨hie, rtg_mono (fun a b h => ⟨h.1, h.2.1, h.2.2⟩) hrt⟩

/-- `imgAt` is the image of the level-`t` components over the vertices of grade `≥ s`. -/
lemma imgAt_eq_compsInImage {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    {s t : ℝ} (hst : t ≤ s) :
    imgAt g Dm δ s t
      = (fun i : Fin n => compIn Dm δ ({v : Fin n | t ≤ g v} : Set (Fin n)) i) ''
          {i : Fin n | s ≤ g i} := by
  ext C
  constructor
  · rintro ⟨i, hi, hieq⟩
    refine ⟨i, hi, ?_⟩
    change compIn Dm δ ({v : Fin n | t ≤ g v} : Set (Fin n)) i = C
    rw [← classAt_eq_compIn g Dm δ t (hst.trans hi)]
    exact hieq
  · rintro ⟨i, hi, hieq⟩
    refine ⟨i, hi, ?_⟩
    change classAt g Dm δ t i = C
    rw [classAt_eq_compIn g Dm δ t (hst.trans hi)]
    exact hieq

/-- For a level-`t` component, membership in `imgAt lo t` is exactly having a vertex of
grade `≥ lo`. -/
lemma compsIn_mem_imgAt {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    {t a : ℝ} (hta : t ≤ a) {C : Set (Fin n)}
    (hC : C ∈ compsIn Dm δ ({v : Fin n | t ≤ g v} : Set (Fin n))) :
    C ∈ imgAt g Dm δ a t ↔ ∃ i ∈ C, a ≤ g i := by
  obtain ⟨y, hy, hyC⟩ := hC
  have hyg : t ≤ g y := hy
  have hcy : classAt g Dm δ t y = C := by
    rw [classAt_eq_compIn g Dm δ t hyg]
    exact hyC
  rw [← hcy]
  exact meets_iff g Dm δ t a hta

/-- The rank-window difference is the set of level-`t` components whose maximum grade lies
in `[lo, hi)`: it has a vertex of grade `≥ lo` and none of grade `≥ hi`. -/
lemma compsIn_diff {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    {t lo hi : ℝ} (htlo : t ≤ lo) (hthi : t ≤ hi) :
    ((imgAt g Dm δ lo t \ imgAt g Dm δ hi t) : Set (Set (Fin n)))
      = {C ∈ compsIn Dm δ ({v : Fin n | t ≤ g v} : Set (Fin n))
          | (∃ i ∈ C, lo ≤ g i) ∧ (∀ j ∈ C, ¬ hi ≤ g j)} := by
  ext C
  constructor
  · intro hL
    have hlo : C ∈ imgAt g Dm δ lo t := hL.1
    have hhi : C ∉ imgAt g Dm δ hi t := hL.2
    have hcomp : C ∈ compsIn Dm δ ({v : Fin n | t ≤ g v} : Set (Fin n)) := by
      rw [imgAt_eq_compsInImage g Dm δ htlo] at hlo
      exact Set.image_mono (by intro v hv; exact le_trans htlo hv) hlo
    refine ⟨hcomp, (compsIn_mem_imgAt g Dm δ htlo hcomp).mp hlo, fun j hj hle =>
      hhi ((compsIn_mem_imgAt g Dm δ hthi hcomp).mpr ⟨j, hj, hle⟩)⟩
  · rintro ⟨hcomp, hlo, hhi⟩
    refine ⟨(compsIn_mem_imgAt g Dm δ htlo hcomp).mpr hlo, fun hmem => ?_⟩
    obtain ⟨j, hj, hle⟩ := (compsIn_mem_imgAt g Dm δ hthi hcomp).mp hmem
    exact hhi j hj hle

/-- A window condition characterises the maximum grade when no grade other than `b` lies
in `[lo, hi]`. -/
lemma windowCond_iff_maxgIs {n : ℕ} (g : Fin n → ℝ) (C : Set (Fin n))
    {b lo hi : ℝ} (hlob : lo ≤ b) (hbhi : b < hi)
    (hgw : ∀ i : Fin n, lo ≤ g i ∧ g i ≤ hi → g i = b) :
    ((∃ i ∈ C, lo ≤ g i) ∧ (∀ j ∈ C, ¬ hi ≤ g j)) ↔ maxgIs g b C := by
  constructor
  · rintro ⟨⟨i, hiC, hgi⟩, hhi⟩
    refine ⟨?_, ?_⟩
    · refine ⟨i, hiC, ?_⟩
      exact hgw i ⟨hgi, le_of_lt (not_le.mp (hhi i hiC))⟩
    · intro j hj
      exact le_of_not_gt (fun hgt : b < g j =>
        absurd (hgw j ⟨le_trans hlob (le_of_lt hgt), le_of_lt (not_le.mp (hhi j hj))⟩)
          (fun heq : g j = b => by rw [heq] at hgt; exact lt_irrefl b hgt))
  · rintro ⟨⟨i, hiC, hib⟩, hall⟩
    refine ⟨?_, ?_⟩
    · refine ⟨i, hiC, ?_⟩
      rw [hib]
      exact hlob
    · intro j hj hle
      exact absurd (lt_of_le_of_lt (le_trans hle (hall j hj)) hbhi) (lt_irrefl hi)

/-- At a strong-grid sample, the rank-window difference at any level `t ≤ b − ε` is
exactly the set of level-`t` components with maximum grade `b`. -/
lemma compsIn_diff_maxgC {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    {b ε t : ℝ} (hpos : 0 < ε) (htlo : t ≤ b - ε) (hthi : t ≤ b + ε)
    (hgw : ∀ i : Fin n, b - ε ≤ g i ∧ g i ≤ b + ε → g i = b) :
    ((imgAt g Dm δ (b - ε) t \ imgAt g Dm δ (b + ε) t) : Set (Set (Fin n)))
      = {C ∈ compsIn Dm δ ({v : Fin n | t ≤ g v} : Set (Fin n)) | maxgIs g b C} := by
  rw [compsIn_diff g Dm δ htlo hthi]
  ext C
  simp only [Set.mem_setOf_eq, and_assoc, windowCond_iff_maxgIs g C (by linarith) (by linarith) hgw]

/-- A weakly smaller tolerance keeps grid goodness. -/
lemma gridGoodC_mono {n : ℕ} (g : Fin n → ℝ) {b d ε ε₀ : ℝ} (hε : ε ≤ ε₀)
    (h₀ : gridGoodC g b d ε₀) : gridGoodC g b d ε := by
  obtain ⟨h1, h2⟩ := h₀
  constructor
  · intro i hwin
    exact h1 i ⟨by linarith, by linarith⟩
  · intro i hwin
    exact h2 i ⟨by linarith, by linarith⟩

/-- A step at a vertex outside the death window leaves the window-accumulator sum
unchanged. -/
lemma step_wpts_ne {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (blo bhi dlo dhi : ℝ)
    (Wpts : Finset (EReal × EReal))
    (hW : ∀ r j : Fin n, ((g r : EReal), (g j : EReal)) ∈ Wpts
      ↔ (blo ≤ g r ∧ g r < bhi ∧ dlo ≤ g j ∧ g j < dhi))
    (st : UFState n × ((EReal × EReal) → ℕ∞)) (i : Fin n)
    (hgi : ¬ (dlo ≤ g i ∧ g i < dhi)) :
    ∑ p ∈ Wpts, (barStep g Dm δ σ st i).2 p = ∑ p ∈ Wpts, st.2 p := by
  rw [barStep]
  set lab := st.1 with hlab
  set acc := st.2 with hacc
  set Sf : Finset (Fin n) :=
    Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) with hSf
  by_cases hS : Sf = ∅
  · rw [if_pos hS]
  · rw [if_neg hS]
    simp only [Prod.snd]
    set root : Fin n → Fin n := fun j => (lab j).getD j with hroot
    set ri : Fin n := root (firstProcessed σ Sf i) with hri
    set M : Finset (Fin n) := insert ri (Sf.image root) with hM
    set R : Fin n := firstProcessed σ M ri with hR
    set dying : Finset (Fin n) :=
      (M.erase R).filter (fun r => (g i : EReal) < (g r : EReal)) with hdying
    set acc2 : EReal × EReal → ℕ∞ :=
      fun p => acc p + dying.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then 1 else 0)
        with hacc2
    show (∑ p ∈ Wpts, acc2 p) = (∑ p ∈ Wpts, acc p)
    simp only [hacc2, Finset.sum_add_distrib]
    have hinner : ∀ pt : EReal × EReal,
        ∑ p ∈ Wpts, (if p = pt then (1 : ℕ∞) else 0) = (if pt ∈ Wpts then (1 : ℕ∞) else 0) := by
      intro pt
      rw [sum_indicator_card]
      by_cases hpt : pt ∈ Wpts
      · have hfil : Wpts.filter (fun p => p = pt) = {pt} := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨-, hpp⟩; exact hpp
          · intro hpp; exact ⟨by rw [hpp]; exact hpt, hpp⟩
        rw [hfil, Finset.card_singleton, if_pos hpt]; simp
      · have hfil : Wpts.filter (fun p => p = pt) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x hx hxp
          exact hpt (hxp ▸ hx)
        rw [hfil, Finset.card_empty, if_neg hpt]; simp
    have hzero : (∑ p ∈ Wpts, dying.sum
        (fun r => if p = ((g r : EReal), (g i : EReal)) then (1 : ℕ∞) else 0)) = 0 := by
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_zero]
      intro r _
      rw [hinner ((g r : EReal), (g i : EReal))]
      exact if_neg (fun hcond => hgi ((hW r i).mp hcond).2.2)
    rw [hzero, add_zero]

/-- Folding over a list whose vertices all lie outside the death window leaves the
window-accumulator sum unchanged. -/
lemma foldl_wpts_ne {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (blo bhi dlo dhi : ℝ)
    (Wpts : Finset (EReal × EReal))
    (hW : ∀ r j : Fin n, ((g r : EReal), (g j : EReal)) ∈ Wpts
      ↔ (blo ≤ g r ∧ g r < bhi ∧ dlo ≤ g j ∧ g j < dhi))
    (l : List (Fin n))
    (hl : ∀ i ∈ l, ¬ (dlo ≤ g i ∧ g i < dhi))
    (s : UFState n × ((EReal × EReal) → ℕ∞)) :
    ∑ p ∈ Wpts, (l.foldl (fun st i => barStep g Dm δ σ st i) s).2 p = ∑ p ∈ Wpts, s.2 p := by
  induction l generalizing s with
  | nil => simp [List.foldl_nil]
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih (fun j hj => hl j (List.mem_cons.mpr (Or.inr hj))) (barStep g Dm δ σ s i)]
    exact step_wpts_ne g Dm δ σ blo bhi dlo dhi Wpts hW s i (hl i (by simp))

/-- For a root `r`, being a window-grade vertex is equivalent to its component satisfying
the window condition. -/
lemma wroof_irr {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) {P : Set (Fin n)} {lab : UFState n}
    (hinv : SweepInvP g Dm δ σ lab P) {r : Fin n} (hrr : lab r = some r) {blo bhi : ℝ} :
    (blo ≤ g r ∧ g r < bhi) ↔
      ((∃ i ∈ compIn Dm δ P r, blo ≤ g i) ∧ (∀ j ∈ compIn Dm δ P r, ¬ bhi ≤ g j)) := by
  constructor
  · rintro ⟨hb1, hb2⟩
    refine ⟨⟨r, connIn_refl Dm δ P r, hb1⟩, fun j hj hle => ?_⟩
    have hjlab : lab j = some r := (lab_constantP g Dm δ σ lab P hinv hj).symm.trans hrr
    exact absurd (hle.trans (lab_elderP g Dm δ σ hσ lab P hinv hjlab)) (not_le.mpr hb2)
  · rintro ⟨⟨i, hiC, hbl⟩, hup⟩
    refine ⟨?_, ?_⟩
    · have hilab : lab i = some r := (lab_constantP g Dm δ σ lab P hinv hiC).symm.trans hrr
      exact le_trans hbl (lab_elderP g Dm δ σ hσ lab P hinv hilab)
    · exact not_le.mp (hup r (connIn_refl Dm δ P r))

/-- The number of window-grade roots equals the number of window-condition components. -/
lemma roots_window_eq {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) {P : Set (Fin n)} {lab : UFState n}
    (hinv : SweepInvP g Dm δ σ lab P) {blo bhi : ℝ} :
    ({r : Fin n | lab r = some r ∧ blo ≤ g r ∧ g r < bhi} : Set (Fin n)).encard
      = ({C ∈ compsIn Dm δ P | (∃ i ∈ C, blo ≤ g i) ∧ (∀ j ∈ C, ¬ bhi ≤ g j)}
          : Set (Set (Fin n))).encard := by
  classical
  have hset : {r : Fin n | lab r = some r ∧ blo ≤ g r ∧ g r < bhi}
      = {r : Fin n | lab r = some r
          ∧ ((∃ i ∈ compIn Dm δ P r, blo ≤ g i) ∧ (∀ j ∈ compIn Dm δ P r, ¬ bhi ≤ g j))} := by
    ext r
    constructor
    · rintro ⟨hrr, ⟨hb1, hb2⟩⟩
      exact ⟨hrr, (wroof_irr g Dm δ σ hσ hinv hrr).mp ⟨hb1, hb2⟩⟩
    · rintro ⟨hrr, hcond⟩
      exact ⟨hrr, (wroof_irr g Dm δ σ hσ hinv hrr).mpr hcond⟩
  rw [hset]
  exact encard_roots_eq_comps hn g Dm δ σ hσ lab P hinv
    (fun C => (∃ i ∈ C, blo ≤ g i) ∧ (∀ j ∈ C, ¬ bhi ≤ g j))

/-- The window per-step telescope: processing a vertex whose grade lies in the death
window `[dlo, dhi)`, the total accumulator mass over the window points `Wpts` gains
exactly as much as the number of `W`-grade roots (grades in `[blo, bhi)`) that die in the
step.  Hence `Σ_{p ∈ Wpts} acc(p) + #(W-grade roots)` is invariant along the sweep, as
long as every processed vertex has grade in `[dlo, dhi)`. -/
lemma step_W_telescope {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) (st : UFState n × ((EReal × EReal) → ℕ∞))
    (P : Set (Fin n)) (i : Fin n) (hinv : SweepInvP g Dm δ σ st.1 P) (hiP : i ∉ P)
    {blo bhi dlo dhi : ℝ} (hgap : dhi ≤ blo) (hgiW : dlo ≤ g i ∧ g i < dhi)
    (Wpts : Finset (EReal × EReal))
    (hW : ∀ r j : Fin n,
        ((g r : EReal), (g j : EReal)) ∈ Wpts
          ↔ (blo ≤ g r ∧ g r < bhi ∧ dlo ≤ g j ∧ g j < dhi)) :
    ∑ p ∈ Wpts, (barStep g Dm δ σ st i).2 p
      + ({r : Fin n | (barStep g Dm δ σ st i).1 r = some r ∧ blo ≤ g r ∧ g r < bhi}).encard
    = ∑ p ∈ Wpts, st.2 p
      + ({r : Fin n | st.1 r = some r ∧ blo ≤ g r ∧ g r < bhi}).encard := by
  classical
  rw [barStep]
  set lab := st.1 with hlab
  set acc := st.2 with hacc
  set Sf : Finset (Fin n) :=
    Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) with hSf
  obtain ⟨hmem, hptr, helder, hedge, hcomp⟩ := hinv
  have hlabnone : lab i = none := by
    cases hh : lab i with
    | none => rfl
    | some r => exact absurd ((hmem i).mp (by simp [hh])) hiP
  by_cases hS : Sf = ∅
  · -- peak step: the new root has grade `g i`, outside `[blo, bhi)`; accumulator unchanged
    rw [if_pos hS]
    have hgiBlo : g i < blo := lt_of_lt_of_le hgiW.2 hgap
    have hgi_out : ¬ (blo ≤ g i ∧ g i < bhi) := fun hp => absurd hgiBlo (not_lt.mpr hp.1)
    have hsetW : {r : Fin n | (Function.update lab i (some i)) r = some r ∧ blo ≤ g r ∧ g r < bhi}
        = {r : Fin n | lab r = some r ∧ blo ≤ g r ∧ g r < bhi} := by
      ext r
      by_cases hr : r = i
      · subst hr
        simp only [Set.mem_setOf_eq, Function.update_self, hlabnone, hgi_out]
        exact ⟨fun h => False.elim h.2, fun h => False.elim h.2⟩
      · simp only [Set.mem_setOf_eq, Function.update_of_ne hr]
    show (∑ p ∈ Wpts, acc p)
      + ({r : Fin n | (Function.update lab i (some i)) r = some r ∧ blo ≤ g r ∧ g r < bhi}).encard
      = (∑ p ∈ Wpts, acc p) + ({r : Fin n | lab r = some r ∧ blo ≤ g r ∧ g r < bhi}).encard
    rw [hsetW]
  · -- merge step
    rw [if_neg hS]
    simp only [Prod.snd, Prod.fst]
    set root : Fin n → Fin n := fun j => (lab j).getD j with hroot
    set ri : Fin n := root (firstProcessed σ Sf i) with hri
    set M : Finset (Fin n) := insert ri (Sf.image root) with hM
    set R : Fin n := firstProcessed σ M ri with hR
    set lab2 : UFState n := fun v =>
      if v = i then some R
      else match lab v with
        | some r => if r ∈ M then some R else some r
        | none => none with hlab2
    set dying : Finset (Fin n) :=
      (M.erase R).filter (fun r => (g i : EReal) < (g r : EReal)) with hdying
    set acc2 : EReal × EReal → ℕ∞ :=
      fun p => acc p + dying.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then 1 else 0)
        with hacc2
    have hSne : Sf.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    have hMne : M.Nonempty := ⟨ri, by rw [hM]; exact Finset.mem_insert_self _ _⟩
    have hRM : R ∈ M := by rw [hR]; exact firstProcessed_mem σ M hMne ri
    have hSf_some : ∀ j ∈ Sf, (lab j).isSome := by
      intro j hj; exact ((Finset.mem_filter.mp hj).2).2.2
    have hroot_val : ∀ j ∈ Sf, ∃ r, lab j = some r ∧ root j = r := by
      intro j hj
      obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp (hSf_some j hj)
      exact ⟨r0, hr0, by simp [hroot, hr0]⟩
    have hMroot : ∀ q ∈ M, lab q = some q := by
      intro q hq
      rw [hM] at hq
      rcases Finset.mem_insert.mp hq with hq | hq
      · rw [hq, hri]
        have hfpS : firstProcessed σ Sf i ∈ Sf := firstProcessed_mem σ Sf hSne i
        obtain ⟨r0, hr0lab, hr0r⟩ := hroot_val _ hfpS
        rw [hr0r]
        exact hptr _ r0 hr0lab
      · obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp hq
        rw [← hjq]
        obtain ⟨r0, hr0lab, hr0r⟩ := hroot_val j hj
        rw [hr0r]
        exact hptr j r0 hr0lab
    have hM_P : ∀ q ∈ M, q ∈ P := by
      intro q hq
      have hr := hMroot q hq
      exact (hmem q).mp (by rw [hr]; rfl)
    have hRi : R ≠ i := fun hh => hiP (hh ▸ hM_P R hRM)
    have hgiBlo : g i < blo := lt_of_lt_of_le hgiW.2 hgap
    have hl2c : ∀ v : Fin n, v ≠ i →
        (lab2 v = some v ↔ (lab v = some v ∧ (v ∉ M ∨ v = R))) :=
      fun v hv => lab2_root_iff lab2 lab M R i hlab2 hMroot hRM hv
    set WrootsF : UFState n → Finset (Fin n) :=
      fun L => Finset.univ.filter (fun r => L r = some r ∧ blo ≤ g r ∧ g r < bhi) with hWrootsF
    set DiedW : Finset (Fin n) := (M.erase R).filter (fun r => blo ≤ g r ∧ g r < bhi)
      with hDiedW
    have hmemW : ∀ (L : UFState n) (v : Fin n),
        v ∈ WrootsF L ↔ (L v = some v ∧ blo ≤ g v ∧ g v < bhi) := by
      intro L v
      simp only [hWrootsF, Finset.mem_filter, Finset.mem_univ, true_and]
    have hmemDW : ∀ v : Fin n, v ∈ DiedW ↔ (v ≠ R ∧ v ∈ M ∧ blo ≤ g v ∧ g v < bhi) := by
      intro v
      simp only [hDiedW, Finset.mem_filter, Finset.mem_erase, and_assoc]
    have hF4W : ∀ L : UFState n,
        ({r : Fin n | L r = some r ∧ blo ≤ g r ∧ g r < bhi}).encard
          = ((WrootsF L).card : ℕ∞) := by
      intro L
      have hset : ({r : Fin n | L r = some r ∧ blo ≤ g r ∧ g r < bhi} : Set (Fin n)).toFinset
          = WrootsF L := by
        ext r; simp [hWrootsF, Finset.mem_filter]
      rw [Set.encard_eq_coe_toFinset_card, hset]
    have hF1W : WrootsF lab2 = WrootsF lab \ DiedW := by
      ext r
      rw [hmemW lab2 r, Finset.mem_sdiff, hmemW lab r, hmemDW r]
      by_cases hri2 : r = i
      · have hgrb : ¬ (blo ≤ g r ∧ g r < bhi) := by
          rw [hri2]
          exact fun hp => absurd hgiBlo (not_lt.mpr hp.1)
        exact ⟨fun h => absurd h.2 hgrb, fun h => absurd h.1.2 hgrb⟩
      · rw [hl2c r hri2]
        constructor
        · rintro ⟨⟨hlabb, hcond⟩, hgb⟩
          refine ⟨⟨hlabb, hgb⟩, ?_⟩
          rintro ⟨hrne, hrM, _⟩
          rcases hcond with hnotM | hRe
          · exact hnotM hrM
          · exact hrne hRe
        · rintro ⟨⟨hlabb, hgb⟩, hneg⟩
          refine ⟨⟨hlabb, ?_⟩, hgb⟩
          by_contra hcon
          push_neg at hcon
          exact hneg ⟨hcon.2, hcon.1, hgb⟩
    have hF2W : DiedW ⊆ WrootsF lab := by
      intro r hr
      obtain ⟨hm, hgb⟩ := Finset.mem_filter.mp hr
      obtain ⟨hrne, hrM⟩ := Finset.mem_erase.mp hm
      rw [hmemW]
      exact ⟨hMroot r hrM, hgb⟩
    -- (F3W): window-accumulator gain = number of dying window-grade roots
    have hinner : ∀ pt : EReal × EReal,
        ∑ p ∈ Wpts, (if p = pt then (1 : ℕ∞) else 0) = (if pt ∈ Wpts then (1 : ℕ∞) else 0) := by
      intro pt
      rw [sum_indicator_card]
      by_cases hpt : pt ∈ Wpts
      · have hfil : Wpts.filter (fun p => p = pt) = {pt} := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨-, hpp⟩; exact hpp
          · intro hpp; exact ⟨by rw [hpp]; exact hpt, hpp⟩
        rw [hfil, Finset.card_singleton, if_pos hpt]; simp
      · have hfil : Wpts.filter (fun p => p = pt) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x hx hxp
          exact hpt (hxp ▸ hx)
        rw [hfil, Finset.card_empty, if_neg hpt]; simp
    have hper : ∀ r : Fin n, ((g r : EReal), (g i : EReal)) ∈ Wpts ↔ (blo ≤ g r ∧ g r < bhi) := by
      intro r
      rw [hW r i]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hgiW.1, hgiW.2⟩
    have hfiltrW : dying.filter (fun r => blo ≤ g r ∧ g r < bhi) = DiedW := by
      rw [hdying, hDiedW, Finset.filter_filter]
      refine Finset.filter_congr fun r _ => ?_
      constructor
      · rintro ⟨-, hgb⟩; exact hgb
      · intro hp
        exact ⟨EReal.coe_lt_coe_iff.mpr (lt_of_lt_of_le hgiBlo hp.1), hp⟩
    have hF3W : ∑ p ∈ Wpts,
        dying.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then (1 : ℕ∞) else 0)
        = ((DiedW.card : ℕ∞)) := by
      rw [Finset.sum_comm]
      calc ∑ y ∈ dying, ∑ x ∈ Wpts, (if x = ((g y : EReal), (g i : EReal)) then (1 : ℕ∞) else 0)
          = ∑ y ∈ dying, (if ((g y : EReal), (g i : EReal)) ∈ Wpts then (1 : ℕ∞) else 0) :=
            Finset.sum_congr rfl fun r _ => hinner _
        _ = ∑ y ∈ dying, (if blo ≤ g y ∧ g y < bhi then (1 : ℕ∞) else 0) :=
            Finset.sum_congr rfl fun r _ => if_congr (hper r) rfl rfl
        _ = ((dying.filter (fun r => blo ≤ g r ∧ g r < bhi)).card : ℕ∞) :=
            sum_indicator_card dying _
        _ = ((DiedW.card : ℕ∞)) := by rw [hfiltrW]
    -- assemble
    have hcardW : ((WrootsF lab).card : ℕ∞)
        = ((WrootsF lab2).card : ℕ∞) + ((DiedW.card : ℕ∞)) := by
      rw [hF1W, ← Nat.cast_add, Finset.card_sdiff_add_card_eq_card hF2W]
    have haccvalW : (∑ p ∈ Wpts, acc2 p)
        = (∑ p ∈ Wpts, acc p) + ((DiedW.card : ℕ∞)) := by
      simp only [hacc2, Finset.sum_add_distrib]
      rw [hF3W]
    show (∑ p ∈ Wpts, acc2 p)
      + ({r : Fin n | lab2 r = some r ∧ blo ≤ g r ∧ g r < bhi}).encard
      = (∑ p ∈ Wpts, acc p)
        + ({r : Fin n | lab r = some r ∧ blo ≤ g r ∧ g r < bhi}).encard
    rw [haccvalW, hF4W lab2, hF4W lab, hcardW, add_assoc,
      add_comm ((DiedW.card : ℕ∞)) ((WrootsF lab2).card : ℕ∞)]
/-- Number of roots with grade in the half-open window `[blo, bhi)`. -/
noncomputable def wroots {n : ℕ} (g : Fin n → ℝ) (blo bhi : ℝ)
    (st : UFState n × ((EReal × EReal) → ℕ∞)) : ℕ∞ :=
  ({r : Fin n | st.1 r = some r ∧ blo ≤ g r ∧ g r < bhi}).encard

/-- Folding over a prefix whose vertices all lie in the death window preserves
`window-accumulator sum + window-grade roots`. -/
lemma foldl_Wbd {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ)
    {blo bhi dlo dhi : ℝ} (hgap : dhi ≤ blo) (l : List (Fin n))
    (hl : ∀ i ∈ l, dlo ≤ g i ∧ g i < dhi)
    (Wpts : Finset (EReal × EReal))
    (hW : ∀ r j : Fin n, ((g r : EReal), (g j : EReal)) ∈ Wpts
      ↔ (blo ≤ g r ∧ g r < bhi ∧ dlo ≤ g j ∧ g j < dhi))
    (st : UFState n × ((EReal × EReal) → ℕ∞)) (P0 : Set (Fin n))
    (h0 : SweepInvP g Dm δ σ st.1 P0)
    (hPa : ∀ a ∈ P0, ∀ v ∈ l, (σ.symm a : Fin n) > σ.symm v)
    (hdec : l.Pairwise (fun a v : Fin n => (σ.symm a : Fin n) > σ.symm v)) :
    SweepInvP g Dm δ σ (l.foldl (fun st i => barStep g Dm δ σ st i) st).1
        (P0 ∪ ((l.toFinset : Set (Fin n))))
      ∧ (∑ p ∈ Wpts, (l.foldl (fun st i => barStep g Dm δ σ st i) st).2 p)
          + wroots g blo bhi (l.foldl (fun st i => barStep g Dm δ σ st i) st)
        = (∑ p ∈ Wpts, st.2 p) + wroots g blo bhi st := by
  induction l generalizing st P0 with
  | nil => simpa using h0
  | cons i rest ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hdec
    have hset : P0 ∪ (↑(i :: rest).toFinset : Set (Fin n))
        = insert i P0 ∪ (↑rest.toFinset : Set (Fin n)) := by
      simp [List.toFinset_cons, Set.union_insert, Set.insert_union]
    rw [List.foldl_cons]
    have hiP : i ∉ P0 := by
      intro hi
      exact absurd (hPa i hi i (by simp)) (lt_irrefl _)
    have hinv' : SweepInvP g Dm δ σ (barStep g Dm δ σ st i).1 (insert i P0) :=
      barStep_invP g Dm δ hDm σ st P0 i h0 hiP
        (fun v hv => le_of_lt (hPa v hv i (by simp)))
    have hstep := step_W_telescope g Dm δ σ hσ st P0 i h0 hiP hgap (hl i (by simp)) Wpts hW
    have hih := ih (fun j hj => hl j (List.mem_cons.mpr (Or.inr hj)))
      (barStep g Dm δ σ st i) (insert i P0)
      hinv'
      (fun a ha v hv => by
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact hhead v hv
        · exact lt_trans (hhead v hv) (hPa a ha i (by simp)))
      hrest
    refine ⟨?_, ?_⟩
    · rw [hset]; exact hih.1
    · rw [hih.2]; exact hstep

/-- A step never decreases the window-accumulator sum. -/
lemma step_wpts_mono {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (st : UFState n × ((EReal × EReal) → ℕ∞)) (i : Fin n)
    (Wpts : Finset (EReal × EReal)) :
    (∑ p ∈ Wpts, st.2 p) ≤ ∑ p ∈ Wpts, (barStep g Dm δ σ st i).2 p := by
  rw [barStep]
  set lab := st.1 with hlab
  set acc := st.2 with hacc
  set Sf : Finset (Fin n) :=
    Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) with hSf
  by_cases hS : Sf = ∅
  · rw [if_pos hS]
  · rw [if_neg hS]
    simp only [Prod.snd]
    set root : Fin n → Fin n := fun j => (lab j).getD j with hroot
    set ri : Fin n := root (firstProcessed σ Sf i) with hri
    set M : Finset (Fin n) := insert ri (Sf.image root) with hM
    set R : Fin n := firstProcessed σ M ri with hR
    set dying : Finset (Fin n) :=
      (M.erase R).filter (fun r => (g i : EReal) < (g r : EReal)) with hdying
    set acc2 : EReal × EReal → ℕ∞ :=
      fun p => acc p + dying.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then 1 else 0)
        with hacc2
    show (∑ p ∈ Wpts, acc p) ≤ ∑ p ∈ Wpts, acc2 p
    simp only [hacc2, Finset.sum_add_distrib]
    exact le_self_add

/-- Folding never decreases the window-accumulator sum. -/
lemma foldl_wpts_mono {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (l : List (Fin n))
    (Wpts : Finset (EReal × EReal)) (s : UFState n × ((EReal × EReal) → ℕ∞)) :
    (∑ p ∈ Wpts, s.2 p) ≤ ∑ p ∈ Wpts, (l.foldl (fun st i => barStep g Dm δ σ st i) s).2 p := by
  induction l generalizing s with
  | nil => simp [List.foldl_nil]
  | cons i rest ih =>
    simp only [List.foldl_cons]
    exact le_trans (step_wpts_mono g Dm δ σ s i Wpts) (ih (barStep g Dm δ σ s i))

/-- Tie-broken grade order on the index set: by grade, then by index. This is a decidable
linear order, so `Finset.sort` produces a list of all vertices in nondecreasing grade. -/
private def gradeOrd {n : ℕ} (g : Fin n → ℝ) (a b : Fin n) : Prop :=
  g a < g b ∨ (g a = g b ∧ a ≤ b)

/-- Every grade function admits a sort order: sort the vertices by `(grade, index)` and
read off the permutation. Needed because `barRun` requires a `σ`, while the sample-
minimality statement (M−) is σ-free. -/
theorem exists_isSortOrder {n : ℕ} (g : Fin n → ℝ) :
    ∃ σ : Fin n ≃ Fin n, IsSortOrder g σ := by
  classical
  haveI hdec : DecidableRel (gradeOrd g) := fun a b => by unfold gradeOrd; infer_instance
  haveI htrans : IsTrans (Fin n) (gradeOrd g) := ⟨fun a b c h1 h2 => by
    rcases h1 with hlt | ⟨heq, hab⟩
    · rcases h2 with hlt2 | ⟨heq2, hbc⟩
      · exact Or.inl (lt_trans hlt hlt2)
      · exact Or.inl (lt_of_lt_of_le hlt (le_of_eq heq2))
    · rcases h2 with hlt2 | ⟨heq2, hbc⟩
      · exact Or.inl (lt_of_le_of_lt (le_of_eq heq) hlt2)
      · exact Or.inr ⟨heq.trans heq2, le_trans hab hbc⟩⟩
  haveI hanti : Std.Antisymm (gradeOrd g) := ⟨fun a b h1 h2 => by
    rcases h1 with hlt | ⟨heq, hab⟩
    · rcases h2 with hlt2 | ⟨heq2, hba⟩
      · linarith
      · linarith
    · rcases h2 with hlt2 | ⟨heq2, hba⟩
      · linarith
      · exact le_antisymm hab hba⟩
  haveI htotal : Std.Total (gradeOrd g) := ⟨fun a b => by
    rcases lt_trichotomy (g a) (g b) with hlt | heq | hgt
    · exact Or.inl (Or.inl hlt)
    · rcases le_total a b with hab | hba
      · exact Or.inl (Or.inr ⟨heq, hab⟩)
      · exact Or.inr (Or.inr ⟨heq.symm, hba⟩)
    · exact Or.inr (Or.inl hgt)⟩
  set L : List (Fin n) := Finset.sort Finset.univ (gradeOrd g) with hLdef
  have hLpw : L.Pairwise (gradeOrd g) := Finset.pairwise_sort Finset.univ (gradeOrd g)
  have hLnd : L.Nodup := Finset.sort_nodup Finset.univ (gradeOrd g)
  have hLtf : L.toFinset = Finset.univ := Finset.sort_toFinset Finset.univ (gradeOrd g)
  have hlen : L.length = n := by
    have h1 : L.length = (Finset.univ : Finset (Fin n)).card := by
      rw [← hLtf, List.toFinset_card_of_nodup hLnd]
    rw [h1]; simp
  have f_inj : Function.Injective (fun (k : Fin n) => L.get (Fin.cast hlen.symm k)) := by
    intro k1 k2 h
    have h := (List.Nodup.get_inj_iff hLnd).mp h
    exact Fin.cast_injective hlen.symm h
  have f_surj : Function.Surjective (fun (k : Fin n) => L.get (Fin.cast hlen.symm k)) :=
    Finite.injective_iff_surjective.mp f_inj
  refine ⟨Equiv.ofBijective _ ⟨f_inj, f_surj⟩, ?_⟩
  intro k1 k2 hkk
  show g (L.get (Fin.cast hlen.symm k1)) ≤ g (L.get (Fin.cast hlen.symm k2))
  by_cases heqk : k1 = k2
  · rw [heqk]
  · have hlt : k1 < k2 := lt_of_le_of_ne hkk heqk
    have hlt' : (Fin.cast hlen.symm k1 : Fin L.length) < Fin.cast hlen.symm k2 :=
      (Fin.cast_lt_cast hlen.symm).mpr hlt
    rcases hLpw.rel_get_of_lt hlt' with hltg | ⟨heqg, -⟩
    · exact le_of_lt hltg
    · exact le_of_eq heqg

end DpB

open DpB

/-! ### Helpers for step B -/

/-- The number of grade-`b` roots never exceeds the number of vertices. -/
theorem broots_le_card {n : ℕ} (g : Fin n → ℝ) (b : ℝ)
    (st : UFState n × ((EReal × EReal) → ℕ∞)) : broots g b st ≤ (n : ℕ∞) := by
  unfold broots
  calc ({r : Fin n | st.1 r = some r ∧ g r = b} : Set (Fin n)).encard
      ≤ (Set.univ : Set (Fin n)).encard := Set.encard_le_encard (fun r _ => Set.mem_univ r)
    _ = (n : ℕ∞) := by rw [Set.encard_univ]; simp

/-- Component sets are always finite (their count is at most the number of vertices). -/
lemma compSet_ne_top {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (P : Set (Fin n)) (Ψ : Set (Fin n) → Prop) :
    ({C ∈ compsIn Dm δ P | Ψ C} : Set (Set (Fin n))).encard ≠ (⊤ : ℕ∞) := by
  refine ne_top_of_le_ne_top (ENat.coe_lt_top n).ne ?_
  calc ({C ∈ compsIn Dm δ P | Ψ C} : Set (Set (Fin n))).encard
      ≤ (compsIn Dm δ P).encard := Set.encard_le_encard (fun C hm => hm.1)
    _ = ((fun i : Fin n => compIn Dm δ P i) '' P).encard := by rw [compsIn]
    _ ≤ P.encard := Set.encard_image_le _ _
    _ ≤ (Set.univ : Set (Fin n)).encard := Set.encard_le_encard (fun r _ => Set.mem_univ r)
    _ = (n : ℕ∞) := by rw [Set.encard_univ]; simp

/-- The number of grade-`b` roots is finite. -/
theorem broots_ne_top {n : ℕ} (g : Fin n → ℝ) (b : ℝ)
    (st : UFState n × ((EReal × EReal) → ℕ∞)) : broots g b st ≠ (⊤ : ℕ∞) :=
  ne_top_of_le_ne_top (ENat.coe_lt_top n).ne (broots_le_card g b st)

/-- For a real death coordinate `d`, the immortal contribution to the combinatorial
barcode at `((b, d))` vanishes: immortal points are `((g r : EReal), ⊥)` and `⊥` is not
a real coercion. Hence `ripsBarcode (b, d)` is the accumulated off-diagonal mass
`(barRun …).2 ((b, d))`. -/
private lemma alg_death_pair_barcode_real_no_immortal
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (b d : ℝ) :
    ripsBarcode g Dm δ σ ((b : EReal), (d : EReal)) =
      (barRun g Dm δ σ).2 ((b : EReal), (d : EReal)) := by
  have h0 : (Finset.univ.filter (fun r => (barRun g Dm δ σ).1 r = some r)).sum
      (fun r => if ((b : EReal), (d : EReal)) = ((g r : EReal), ⊥) then (1 : ℕ∞) else 0)
      = 0 := by
    refine Finset.sum_eq_zero fun r _ => if_neg fun h => ?_
    exact EReal.coe_ne_bot d (Prod.ext_iff.mp h).2
  simp only [ripsBarcode]
  rw [h0, add_zero]

/-- The rank bracket rewrites as a difference of window-set encards: the inclusion-
exclusion of component counts

    (imgAt (b − ε) (d + ε) \ imgAt (b + ε) (d + ε)).encard
      − (imgAt (b − ε) (d − ε) \ imgAt (b + ε) (d − ε)).encard,

the two components-counting sets being the level-`(d + ε)` and level-`(d − ε)` classes
whose max grade lies in the window `[b − ε, b + ε)`. -/
private lemma alg_death_pair_bracket_diff_encard
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (b d : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (ripsRank Dm g δ (b - ε) (d + ε) - ripsRank Dm g δ (b + ε) (d + ε)) -
      (ripsRank Dm g δ (b - ε) (d - ε) - ripsRank Dm g δ (b + ε) (d - ε))
      = ((imgAt g Dm δ (b - ε) (d + ε) \ imgAt g Dm δ (b + ε) (d + ε)).encard -
          (imgAt g Dm δ (b - ε) (d - ε) \ imgAt g Dm δ (b + ε) (d - ε)).encard) := by
  rw [ripsRank_eq, ripsRank_eq, ripsRank_eq, ripsRank_eq,
    diff_encard g Dm δ b ε (d + ε) hε, diff_encard g Dm δ b ε (d - ε) hε]

/-- Step B — box-counting identity (bars-in-windows). At every grid-good sample `ε`
the combinatorial barcode multiplicity `ripsBarcode g Dm δ σ (b, d)` equals the rank
bracket, because a finite bar `[d', b']` covers the window `[d + ε, b − ε]` iff
`d' ≤ d < b ≤ b'`, i.e. the bar pairs birth `b` with death `d`; by the sweep invariant (S)
the recorded pairs biject the merge events of components whose max-grade is `b`. -/
private theorem alg_death_pair_step_box_counting
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (hσ : IsSortOrder g σ) (b d : ℝ) (hbd : d < b) {ε : ℝ}
    (hε : 0 < ε) (hεlt : ε < (b - d) / 2) (hgood : gridGoodC g b d ε) :
    ripsBarcode g Dm δ σ ((b : EReal), (d : EReal)) =
      (ripsRank Dm g δ (b - ε) (d + ε) - ripsRank Dm g δ (b + ε) (d + ε)) -
        (ripsRank Dm g δ (b - ε) (d - ε) - ripsRank Dm g δ (b + ε) (d - ε)) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have hbar0 : ripsBarcode g Dm δ σ ((b : EReal), (d : EReal)) = 0 := by
      rw [alg_death_pair_barcode_real_no_immortal 0 g Dm δ σ b d]
      simp [barRun]
    have hrk : ∀ s t : ℝ, ripsRank Dm g δ s t = 0 := by
      intro s t
      simp only [ripsRank, rankFn, imgAt, L]
      have hE : ({x | s ≤ g x} : Set (Fin 0)) = ∅ := by
        ext x; exact x.elim0
      rw [hE, Set.image_empty]
      simp
    have hrank0 : (ripsRank Dm g δ (b - ε) (d + ε) - ripsRank Dm g δ (b + ε) (d + ε)) -
        (ripsRank Dm g δ (b - ε) (d - ε) - ripsRank Dm g δ (b + ε) (d - ε)) = 0 := by
      rw [hrk]; simp
    rw [hbar0, hrank0]
  · have hgw : ∀ i : Fin n, b - ε ≤ g i ∧ g i ≤ b + ε → g i = b := hgood.1
    have hgwP : ({C ∈ compsIn Dm δ ({v : Fin n | d ≤ g v}) | maxgIs g b C}
        : Set (Set (Fin n))).encard ≠ (⊤ : ℕ∞) :=
      compSet_ne_top g Dm δ ({v : Fin n | d ≤ g v}) (maxgIs g b)
    have hbr : (ripsRank Dm g δ (b - ε) (d + ε) - ripsRank Dm g δ (b + ε) (d + ε)) -
        (ripsRank Dm g δ (b - ε) (d - ε) - ripsRank Dm g δ (b + ε) (d - ε))
        = ({C ∈ compsIn Dm δ ({v : Fin n | d < g v}) | maxgIs g b C}
              : Set (Set (Fin n))).encard
          - ({C ∈ compsIn Dm δ ({v : Fin n | d ≤ g v}) | maxgIs g b C}
              : Set (Set (Fin n))).encard := by
      rw [alg_death_pair_bracket_diff_encard n g Dm δ b d hε]
      rw [compsIn_diff_maxgC g Dm δ hε (by linarith) (by linarith) hgw]
      rw [gridGoodC_set_dhi g hε hgood]
      rw [compsIn_diff_maxgC g Dm δ hε (by linarith) (by linarith) hgw]
      rw [gridGoodC_set_dlo g hε hgood]
    have hmaster := barRun_acc_eq_Vdrop g Dm δ hDm σ hσ hn hbd
    have hsub : (barRun g Dm δ σ).2 ((b : EReal), (d : EReal))
        = ({C ∈ compsIn Dm δ ({v : Fin n | d < g v}) | maxgIs g b C}
              : Set (Set (Fin n))).encard
          - ({C ∈ compsIn Dm δ ({v : Fin n | d ≤ g v}) | maxgIs g b C}
              : Set (Set (Fin n))).encard := by
      apply le_antisymm
      · exact ENat.le_sub_of_add_le_right hgwP hmaster.le
      · rw [tsub_le_iff_right]
        exact hmaster.ge
    rw [alg_death_pair_barcode_real_no_immortal n g Dm δ σ b d]
    exact hsub.trans hbr.symm

/-- The number of window-grade roots never exceeds the number of vertices. -/
theorem wroots_le_card {n : ℕ} (g : Fin n → ℝ) (blo bhi : ℝ)
    (st : UFState n × ((EReal × EReal) → ℕ∞)) : wroots g blo bhi st ≤ (n : ℕ∞) := by
  unfold wroots
  calc ({r : Fin n | st.1 r = some r ∧ blo ≤ g r ∧ g r < bhi} : Set (Fin n)).encard
      ≤ (Set.univ : Set (Fin n)).encard := Set.encard_le_encard (fun r _ => Set.mem_univ r)
    _ = (n : ℕ∞) := by rw [Set.encard_univ]; simp

/-- Window-grade roots are finite, so cancellation in `ℕ∞` is valid. -/
theorem wroots_ne_top {n : ℕ} (g : Fin n → ℝ) (blo bhi : ℝ)
    (st : UFState n × ((EReal × EReal) → ℕ∞)) : wroots g blo bhi st ≠ (⊤ : ℕ∞) :=
  ne_top_of_le_ne_top (ENat.coe_lt_top n).ne (wroots_le_card g blo bhi st)

/-- Step M−, hard case (`n > 0`): the full sweep chain. For any sample `ε` in
`Ioo 0 ((b−d)/2)` the bracket at `ε₀BD` is the off-diagonal barcode mass, which is at
most the window-accumulator sum at the checkpoint after processing the vertices of
grade `≥ d − ε`, which equals the bracket at `ε`. -/
private theorem aux_hard_case
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (b d : ℝ) (hbd : d < b)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) (hn : 0 < n)
    (ε : ℝ) (hεp : 0 < ε) (hεlt : ε < (b - d) / 2) :
    (ripsRank Dm g δ (b - ε₀BD g b d) (d + ε₀BD g b d)
        - ripsRank Dm g δ (b + ε₀BD g b d) (d + ε₀BD g b d))
      - (ripsRank Dm g δ (b - ε₀BD g b d) (d - ε₀BD g b d)
        - ripsRank Dm g δ (b + ε₀BD g b d) (d - ε₀BD g b d)) ≤
    (ripsRank Dm g δ (b - ε) (d + ε) - ripsRank Dm g δ (b + ε) (d + ε))
      - (ripsRank Dm g δ (b - ε) (d - ε) - ripsRank Dm g δ (b + ε) (d - ε)) := by
  classical
  have hgap : d + ε ≤ b - ε := by linarith
  -- recorded window pairs plus the query point `(b, d)`
  set Brts : Finset EReal :=
    (Finset.univ.filter (fun r : Fin n => b - ε ≤ g r ∧ g r < b + ε)).image
      (fun r : Fin n => (g r : EReal)) with hBrts
  set Dths : Finset EReal :=
    (Finset.univ.filter (fun i : Fin n => d - ε ≤ g i ∧ g i < d + ε)).image
      (fun i : Fin n => (g i : EReal)) with hDths
  set Wpts : Finset (EReal × EReal) :=
    insert ((b : EReal), (d : EReal)) (Brts ×ˢ Dths) with hWpts
  have hW : ∀ r j : Fin n, ((g r : EReal), (g j : EReal)) ∈ Wpts
      ↔ (b - ε ≤ g r ∧ g r < b + ε ∧ d - ε ≤ g j ∧ g j < d + ε) := by
    intro r j
    constructor
    · intro h
      rcases Finset.mem_insert.mp h with heq | hprod
      · -- the query point itself lies in both windows
        obtain ⟨h1, h2⟩ := Prod.ext_iff.mp heq
        rw [EReal.coe_eq_coe_iff] at h1 h2
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      · -- a recorded window pair `(g r, g j)`
        rw [Finset.mem_product] at hprod
        obtain ⟨r', hr', hrre⟩ := Finset.mem_image.mp hprod.1
        have hrb := (Finset.mem_filter.mp hr').2
        have hgrr : g r' = g r := EReal.coe_eq_coe_iff.mp hrre
        obtain ⟨j', hj', hjre⟩ := Finset.mem_image.mp hprod.2
        have hjb := (Finset.mem_filter.mp hj').2
        have hgjj : g j' = g j := EReal.coe_eq_coe_iff.mp hjre
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine Finset.mem_insert.mpr (Or.inr (Finset.mem_product.mpr ⟨?_, ?_⟩))
      · exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, ⟨h1, h2⟩⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨h3, h4⟩⟩, rfl⟩
  -- split the sweep list into the high, middle and low chunks
  set L : List (Fin n) := (List.finRange n).reverse.map σ with hL
  have hLpw : L.Pairwise (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
    rw [hL]; exact sweep_order_pairwise σ
  have hLg : L.Pairwise (fun a b : Fin n => g b ≤ g a) := by
    rw [hL]; exact L_pairwise_ge g σ hσ
  obtain ⟨C, Dch, hCD, hCc, hDc, hDp⟩ := rsplit L g (d + ε) hLg
  obtain ⟨Mid, Lo, hMl, hMc, hLoc, hLop⟩ := rsplit Dch g (d - ε) hDp.2
  have hFull : L = (C ++ Mid) ++ Lo := by rw [hCD, hMl, List.append_assoc]
  have hFull' : ((List.finRange n).reverse.map σ) = (C ++ Mid) ++ Lo := hFull
  -- σ-order pairwise on the relevant chunks
  have hdecC : C.Pairwise (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
    have h := hLpw; rw [hCD] at h; exact (List.pairwise_append.mp h).1
  have hdecCM : (C ++ Mid).Pairwise (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
    have h := hLpw; rw [hFull] at h; exact (List.pairwise_append.mp h).1
  have hdecM : Mid.Pairwise (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
    have h := hLpw; rw [hCD] at h
    have hD := (List.pairwise_append.mp h).2.1
    rw [hMl] at hD; exact (List.pairwise_append.mp hD).1
  -- chunk set equalities
  have hsetC : ((C.toFinset : Set (Fin n))) = {v : Fin n | d + ε ≤ g v} :=
    chunk_set_above_eq g σ hCD (fun x hx => hCc x hx) (fun y hy => hDc y hy)
  have hsetCM : (((C ++ Mid).toFinset : Set (Fin n))) = {v : Fin n | d - ε ≤ g v} := by
    refine chunk_set_above_eq g σ hFull (fun x hx => ?_) (fun y hy => hLoc y hy)
    rcases List.mem_append.mp hx with h | h
    · exact le_trans (by linarith) (hCc x h)
    · exact hMc x h
  -- the cross-chunk order: a high-grade vertex is processed before any middle-grade one
  have hPaM : ∀ a ∈ ({v : Fin n | d + ε ≤ g v} : Set (Fin n)), ∀ v ∈ Mid,
      (σ.symm a : Fin n) > σ.symm v := by
    intro a ha v hv
    have hvD : v ∈ Dch := by rw [hMl]; exact List.mem_append_left Lo hv
    exact symm_lt_of_g_lt g σ hσ (lt_of_lt_of_le (hDc v hvD) ha)
  -- checkpoint states
  set s0 : UFState n × ((EReal × EReal) → ℕ∞) := ((fun _ => none), (fun _ => 0)) with hs0
  set sHi : UFState n × ((EReal × EReal) → ℕ∞) :=
    C.foldl (fun st i => barStep g Dm δ σ st i) s0 with hsHi
  set sLo : UFState n × ((EReal × EReal) → ℕ∞) :=
    (C ++ Mid).foldl (fun st i => barStep g Dm δ σ st i) s0 with hsLo
  have hsLo_eq : sLo = Mid.foldl (fun st i => barStep g Dm δ σ st i) sHi := by
    rw [hsLo, hsHi, List.foldl_append]
  -- invariants at the two checkpoints
  have hinvHi : SweepInvP g Dm δ σ sHi.1 ({v : Fin n | d + ε ≤ g v}) := by
    have h := sweep_fold g Dm δ hDm σ C hdecC s0 ∅ (init_invP g Dm δ σ)
      (by intro a ha; exact absurd ha (by simp))
    rw [Set.empty_union, hsetC] at h
    exact h
  have hinvLo : SweepInvP g Dm δ σ sLo.1 ({v : Fin n | d - ε ≤ g v}) := by
    have h := sweep_fold g Dm δ hDm σ (C ++ Mid) hdecCM s0 ∅ (init_invP g Dm δ σ)
      (by intro a ha; exact absurd ha (by simp))
    rw [Set.empty_union, hsetCM] at h
    exact h
  -- the window-accumulator sum is `0` at the high checkpoint
  have hW0 : ∑ p ∈ Wpts, s0.2 p = 0 := by
    rw [hs0]; exact Finset.sum_eq_zero fun p _ => rfl
  have hWsumHi : ∑ p ∈ Wpts, sHi.2 p = 0 := by
    have h := foldl_wpts_ne g Dm δ σ (b - ε) (b + ε) (d - ε) (d + ε) Wpts hW C
      (fun i hi hcond => absurd hcond.2 (not_lt.mpr (hCc i hi))) s0
    rw [← hsHi] at h; rw [h]; exact hW0
  -- the middle-chunk telescope
  have hMidWin : ∀ i ∈ Mid, d - ε ≤ g i ∧ g i < d + ε := by
    intro i hi
    have hiD : i ∈ Dch := by rw [hMl]; exact List.mem_append_left Lo hi
    exact ⟨hMc i hi, hDc i hiD⟩
  have htel := foldl_Wbd g Dm δ hDm σ hσ hgap Mid hMidWin Wpts hW sHi
      ({v : Fin n | d + ε ≤ g v}) hinvHi hPaM hdecM
  have hkey1 : (∑ p ∈ Wpts, sLo.2 p) + wroots g (b - ε) (b + ε) sLo
      = wroots g (b - ε) (b + ε) sHi := by
    rw [hsLo_eq, htel.2, hWsumHi, zero_add]
  -- window-roots biject window-condition components
  have hwrHi : wroots g (b - ε) (b + ε) sHi
      = ({C ∈ compsIn Dm δ ({v : Fin n | d + ε ≤ g v} : Set (Fin n))
          | (∃ i ∈ C, b - ε ≤ g i) ∧ (∀ j ∈ C, ¬ b + ε ≤ g j)} : Set (Set (Fin n))).encard :=
    roots_window_eq hn g Dm δ σ hσ hinvHi
  have hwrLo : wroots g (b - ε) (b + ε) sLo
      = ({C ∈ compsIn Dm δ ({v : Fin n | d - ε ≤ g v} : Set (Fin n))
          | (∃ i ∈ C, b - ε ≤ g i) ∧ (∀ j ∈ C, ¬ b + ε ≤ g j)} : Set (Set (Fin n))).encard :=
    roots_window_eq hn g Dm δ σ hσ hinvLo
  -- the bracket at `ε` is the difference of the two window-root counts
  have hbrε : (ripsRank Dm g δ (b - ε) (d + ε) - ripsRank Dm g δ (b + ε) (d + ε))
      - (ripsRank Dm g δ (b - ε) (d - ε) - ripsRank Dm g δ (b + ε) (d - ε))
      = wroots g (b - ε) (b + ε) sHi - wroots g (b - ε) (b + ε) sLo := by
    rw [alg_death_pair_bracket_diff_encard n g Dm δ b d hεp]
    rw [compsIn_diff g Dm δ (by linarith : d + ε ≤ b - ε) (by linarith : d + ε ≤ b + ε)]
    rw [compsIn_diff g Dm δ (by linarith : d - ε ≤ b - ε) (by linarith : d - ε ≤ b + ε)]
    rw [← hwrHi, ← hwrLo]
  -- `(b, d)` lies in the window, so the barcode mass at `(b, d)` is at most the window sum
  have hbd_mem : ((b : EReal), (d : EReal)) ∈ Wpts := by
    rw [hWpts]
    exact Finset.mem_insert_self _ _
  have hsingle : sLo.2 ((b : EReal), (d : EReal)) ≤ ∑ p ∈ Wpts, sLo.2 p := by
    have he : ((b : EReal), (d : EReal)) ∉ Wpts.erase ((b : EReal), (d : EReal)) := by
      rw [hWpts]
      intro h
      exact (Finset.mem_erase.mp h).1 rfl
    rw [← Finset.insert_erase hbd_mem, Finset.sum_insert he]
    exact le_self_add
  -- assemble: `bracket(ε₀BD) = ripsBarcode = acc(sLo) ≤ Wsum(sLo) = bracket(ε)`
  have hneLo : wroots g (b - ε) (b + ε) sLo ≠ (⊤ : ℕ∞) := wroots_ne_top g (b - ε) (b + ε) sLo
  have hkey : sLo.2 ((b : EReal), (d : EReal)) + wroots g (b - ε) (b + ε) sLo
      ≤ wroots g (b - ε) (b + ε) sHi := by
    calc sLo.2 ((b : EReal), (d : EReal)) + wroots g (b - ε) (b + ε) sLo
      ≤ (∑ p ∈ Wpts, sLo.2 p) + wroots g (b - ε) (b + ε) sLo :=
        add_le_add hsingle le_rfl
      _ = wroots g (b - ε) (b + ε) sHi := hkey1
  have hbar0 : ripsBarcode g Dm δ σ ((b : EReal), (d : EReal))
      = (barRun g Dm δ σ).2 ((b : EReal), (d : EReal)) :=
    alg_death_pair_barcode_real_no_immortal n g Dm δ σ b d
  have hB := alg_death_pair_step_box_counting n g Dm hDm δ σ hσ b d hbd
    (ε₀BD_pos g b d hbd) (ε₀BD_lt_half g b d hbd) (ε₀BD_gridGoodC g b d hbd)
  have hbar : barRun g Dm δ σ = Lo.foldl (fun st i => barStep g Dm δ σ st i) sLo := by
    rw [barRun_as_fold, hFull', List.foldl_append, ← hsLo]
  have haccLo : (barRun g Dm δ σ).2 ((b : EReal), (d : EReal)) = sLo.2 ((b : EReal), (d : EReal)) := by
    rw [hbar]
    exact foldl_acc_ne g Dm δ σ b d Lo (fun i hi => ne_of_lt (by have := hLoc i hi; linarith)) sLo
  calc (ripsRank Dm g δ (b - ε₀BD g b d) (d + ε₀BD g b d)
      - ripsRank Dm g δ (b + ε₀BD g b d) (d + ε₀BD g b d))
    - (ripsRank Dm g δ (b - ε₀BD g b d) (d - ε₀BD g b d)
      - ripsRank Dm g δ (b + ε₀BD g b d) (d - ε₀BD g b d))
    = (barRun g Dm δ σ).2 ((b : EReal), (d : EReal)) := hB.symm.trans hbar0
  _ = sLo.2 ((b : EReal), (d : EReal)) := haccLo
  _ ≤ wroots g (b - ε) (b + ε) sHi - wroots g (b - ε) (b + ε) sLo :=
    ENat.le_sub_of_add_le_right hneLo hkey
  _ = (ripsRank Dm g δ (b - ε) (d + ε) - ripsRank Dm g δ (b + ε) (d + ε))
    - (ripsRank Dm g δ (b - ε) (d - ε) - ripsRank Dm g δ (b + ε) (d - ε)) := hbrε.symm

/-- Step M− — sample minimality (the deep one-sided bound). Every sample `ε` in the
`mult` interval `Ioo 0 ((b − d) / 2)` dominates the bracket at the grid sample `ε₀BD`:
the window `[d + ε, b − ε]]` always contains the exact pair `(b, d)` (a bar covers the
window iff it pairs birth `b` with death `d`), so the bracket is minimal precisely at
grid-good samples. This is the two-level analog of the immortal-slice lower bound. -/
private theorem alg_death_pair_step_mult_bracket_ge
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (b d : ℝ) (hbd : d < b)
    (ε : ℝ) (hε : ε ∈ Set.Ioo 0 ((b - d) / 2)) :
    (ripsRank Dm g δ (b - ε₀BD g b d) (d + ε₀BD g b d)
        - ripsRank Dm g δ (b + ε₀BD g b d) (d + ε₀BD g b d))
      - (ripsRank Dm g δ (b - ε₀BD g b d) (d - ε₀BD g b d)
        - ripsRank Dm g δ (b + ε₀BD g b d) (d - ε₀BD g b d)) ≤
    (ripsRank Dm g δ (b - ε) (d + ε) - ripsRank Dm g δ (b + ε) (d + ε))
      - (ripsRank Dm g δ (b - ε) (d - ε) - ripsRank Dm g δ (b + ε) (d - ε)) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- `n = 0`: every stage set is empty, so every `ripsRank` is `0`.
    subst hn0
    have hrk : ∀ s t : ℝ, ripsRank Dm g δ s t = 0 := by
      intro s t
      simp only [ripsRank, rankFn, imgAt, L]
      have hE : ({x | s ≤ g x} : Set (Fin 0)) = ∅ := by ext x; exact x.elim0
      rw [hE, Set.image_empty]
      simp
    -- all four `ripsRank` terms are `0`, so both sides of the goal are `0`.
    simp only [hrk]
    simp
  · -- `n > 0`: the bracket at every sample dominates the bracket at the grid sample
    -- `ε₀BD` (uniformly in `ε`, since `compsIn_diff` needs no grid-goodness).
    obtain ⟨σ, hσ⟩ := exists_isSortOrder g
    exact aux_hard_case n g Dm hDm δ b d hbd σ hσ hn ε hε.1 hε.2

/-- Step M — mult evaluation. For real `(b, d)` with `d < b` the analytic multiplicity
`mult (b, d)` equals the rank bracket at the grid sample `ε₀BD` (which is positive,
below the half-gap, and grid-good): the bracket counts bars covering the window
`[d + ε₀, b − ε₀]` and is minimal at grid-good samples, by the sample-minimality bound
(M−). -/
private theorem alg_death_pair_step_mult_eval
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (b d : ℝ) (hbd : d < b) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < (b - d) / 2 ∧ gridGoodC g b d ε₀ ∧
      mult (ripsRank Dm g δ) ((b : EReal), (d : EReal)) =
        (ripsRank Dm g δ (b - ε₀) (d + ε₀) - ripsRank Dm g δ (b + ε₀) (d + ε₀)) -
          (ripsRank Dm g δ (b - ε₀) (d - ε₀) - ripsRank Dm g δ (b + ε₀) (d - ε₀)) := by
  refine ⟨ε₀BD g b d, ε₀BD_pos g b d hbd, ε₀BD_lt_half g b d hbd,
    ε₀BD_gridGoodC g b d hbd, ?_⟩
  -- Unfold `mult`: the birth coordinate `b` is real (neither `⊥` nor `⊤`), the death
  -- coordinate `d` is real and strictly below `b`, so the death branch applies.
  have htr : ((b : EReal)).toReal = b := EReal.toReal_coe b
  have htrd : ((d : EReal)).toReal = d := EReal.toReal_coe d
  have hlt : ((d : EReal)) < ((b : EReal)) := EReal.coe_lt_coe_iff.mpr hbd
  simp only [mult, Prod.fst, Prod.snd]
  -- `simp` closes the `⊥`/`⊤` branches via the `coe_ne_bot`/`coe_ne_top` simp lemmas,
  -- leaving the `if ((d:EReal)) < ((b:EReal)) then ⨅ … else 0` death branch.
  rw [if_pos hlt, htr, htrd]
  refine le_antisymm ?_ ?_
  · -- upper: the infimum is below any sample value, in particular at `ε₀BD`.
    have hmem : ε₀BD g b d ∈ Set.Ioo 0 ((b - d) / 2) :=
      ⟨ε₀BD_pos g b d hbd, ε₀BD_lt_half g b d hbd⟩
    exact iInf_le_of_le (ε₀BD g b d) (iInf_le_of_le hmem (le_refl _))
  · -- lower: every sample dominates the grid sample (step M−).
    refine le_iInf fun ε => le_iInf fun hmem =>
      alg_death_pair_step_mult_bracket_ge n g Dm hDm δ b d hbd ε hmem

/-! ### Private support machinery (accumulator invariant for the `barStep` sweep) -/

/-- The accumulator invariant. After any prefix of the `barRun` fold, the accumulated
off-diagonal multiplicity is nonzero only at points `((g r : EReal), (g i : EReal))`
with `g i < g r` — real birth/death levels, death strictly below birth. -/
private def accSupport {n : ℕ} (g : Fin n → ℝ) (acc : EReal × EReal → ℕ∞) : Prop :=
  ∀ p, acc p ≠ 0 →
    ∃ r : Fin n, p.1 = (g r : EReal) ∧
      ∃ i : Fin n, p.2 = (g i : EReal) ∧ (g i : EReal) < (g r : EReal)

/-- In ℕ∞, `a + b ≠ 0` splits into `a ≠ 0 ∨ b ≠ 0`. -/
private lemma add_ne_zero_split {a b : ℕ∞} (h : a + b ≠ 0) : a ≠ 0 ∨ b ≠ 0 := by
  rcases _root_.em (a = 0) with ha | ha
  · exact Or.inr fun hb => h (by rw [ha, hb]; rfl)
  · exact Or.inl ha

/-- The empty accumulator trivially satisfies the invariant. -/
private lemma init_support {n : ℕ} (g : Fin n → ℝ) : accSupport g (fun _ => 0) := by
  intro _ hp
  exact absurd rfl hp

/-- A sum of death-point indicators that is nonzero contains a death point
`((g r : EReal), (g i : EReal))`. -/
private lemma sum_indicator_death {n : ℕ} (g : Fin n → ℝ) (s : Finset (Fin n)) (i : Fin n)
    (p : EReal × EReal)
    (hsum : s.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then (1 : ℕ∞) else 0) ≠ 0) :
    ∃ r ∈ s, p = ((g r : EReal), (g i : EReal)) := by
  have hf : ∀ a ∈ s, 0 ≤ (if p = ((g a : EReal), (g i : EReal)) then (1 : ℕ∞) else 0) := by
    intro a _
    split_ifs <;> simp
  have h3 : ¬ ∀ a ∈ s, (if p = ((g a : EReal), (g i : EReal)) then (1 : ℕ∞) else 0) = 0 :=
    fun hall => hsum ((Finset.sum_eq_zero_iff_of_nonneg hf).mpr hall)
  push Not at h3
  obtain ⟨r, hr_mem, hr_ne⟩ := h3
  refine ⟨r, hr_mem, ?_⟩
  by_contra hne
  rw [if_neg hne] at hr_ne
  exact hr_ne rfl

/-- One `barStep` preserves the accumulator invariant: it either leaves the accumulator
untouched (no neighbour is already alive) or adds indicator masses at the death points
`((g r : EReal), (g i : EReal))` with `g i < g r` (the `dying` filter). -/
private lemma barStep_support {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (st : UFState n × ((EReal × EReal) → ℕ∞)) (i : Fin n)
    (h : accSupport g st.2) :
    accSupport g (barStep g Dm δ σ st i).2 := by
  simp only [barStep]
  split_ifs with hS
  · -- no neighbour alive yet: accumulator unchanged.
    exact h
  · -- merge step: accumulator gains `dying.sum (indicator …)`.
    intro p hp
    rcases add_ne_zero_split hp with hacc | hsum
    · exact h p hacc
    · -- a death pair `((g r), (g i))` was recorded by some dying root `r`.
      obtain ⟨r, hr_mem, hr_p⟩ := sum_indicator_death g _ i p hsum
      obtain ⟨hr1, hr2⟩ := Prod.ext_iff.mp hr_p
      have hlt : (g i : EReal) < (g r : EReal) := (Finset.mem_filter.mp hr_mem).2
      exact ⟨r, hr1, i, hr2, hlt⟩

/-- Folding `barStep` over any list preserves the invariant. -/
private lemma foldl_support {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (l : List (Fin n))
    (init : UFState n × ((EReal × EReal) → ℕ∞)) (h : accSupport g init.2) :
    accSupport g (l.foldl (fun st k => barStep g Dm δ σ st (σ k)) init).2 := by
  induction l generalizing init with
  | nil => simp only [List.foldl_nil]; exact h
  | cons k ks ih =>
    simp only [List.foldl_cons]
    exact ih _ (barStep_support g Dm δ σ _ (σ k) h)

/-- The full `barRun` accumulator satisfies the invariant. -/
private lemma barRun_support {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) : accSupport g (barRun g Dm δ σ).2 := by
  simp only [barRun]
  exact foldl_support g Dm δ σ _ _ (init_support g)
/-- Step O — off-grid zero cases.
 If `d ≥ b` (diagonal or below) then both sides are zero,
so the identity holds trivially: the analytic `mult` takes the `else 0` branch, and the
combinatorial barcode has mass only at points with death strictly below birth (real
deaths) or at immortal points `((g r : EReal), ⊥)`, neither of which can be `((b, d))`
with `b ≤ d` real. (The non-grid sub-case is absorbed by `d < b` being a
hypothesis of the main theorem.) -/
private theorem alg_death_pair_step_off_grid_zero
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (hσ : IsSortOrder g σ) (b d : ℝ) (hbd : ¬d < b) :
    ripsDiagram Dm g δ ((b : EReal), (d : EReal)) = 0 ∧
      ripsBarcode g Dm δ σ ((b : EReal), (d : EReal)) = 0 := by
  refine ⟨?_, ?_⟩
  · -- analytic side: `mult` is `0` when `¬ d < b`.
    show mult (ripsRank Dm g δ) ((b : EReal), (d : EReal)) = 0
    simp [mult, hbd]
  · -- combinatorial side: no recorded pair and no immortal point can equal `((b, d))`.
    by_contra hne
    simp only [ripsBarcode] at hne
    have himm : (Finset.univ.filter (fun r => (barRun g Dm δ σ).1 r = some r)).sum
        (fun r => if ((b : EReal), (d : EReal)) = ((g r : EReal), ⊥) then (1 : ℕ∞) else 0)
          = 0 := by
      refine Finset.sum_eq_zero fun r _ => if_neg fun hpr => ?_
      exact EReal.coe_ne_bot d (Prod.ext_iff.mp hpr).2
    rw [himm, add_zero] at hne
    obtain ⟨r, hr1, i, hi2, hlt⟩ := barRun_support g Dm δ σ _ hne
    have h1 : (b : EReal) = (g r : EReal) := hr1
    have h2 : (d : EReal) = (g i : EReal) := hi2
    exact hbd (EReal.coe_lt_coe_iff.mp (by rw [h2, h1]; exact hlt))

/-! ## Main theorem -/

theorem solution
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (hσ : IsSortOrder g σ) (b d : ℝ) (hbd : d < b) :
    ripsDiagram Dm g δ ((b : EReal), (d : EReal)) =
      ripsBarcode g Dm δ σ ((b : EReal), (d : EReal)) := by
  -- `ripsDiagram = mult (ripsRank …)`. Evaluate the analytic side at a grid-good sample
  -- (step M) and the combinatorial side at the same sample (step B); transitivity gives
  -- the identity. The off-grid cases (`¬ d < b`) are handled by `alg_death_pair_step_off_grid_zero`.
  obtain ⟨ε₀, hpos, hlt, hgood, hM⟩ :=
    alg_death_pair_step_mult_eval n g Dm hDm δ b d hbd
  have hB :=
    alg_death_pair_step_box_counting n g Dm hDm δ σ hσ b d hbd hpos hlt hgood
  show mult (ripsRank Dm g δ) ((b : EReal), (d : EReal)) = _
  exact hM.trans hB.symm
