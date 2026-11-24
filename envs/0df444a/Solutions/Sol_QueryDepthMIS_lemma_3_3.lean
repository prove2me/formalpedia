-- Prove2me | solution 1 for QueryDepthMIS.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T12:37:43.151637+00:00
-- url     : https://prove2.me/submissions/d44db0c0-904e-4488-8bf9-da371c7c0d34

import Mathlib
import Definitions.Def_NoSignalPA_uniformExp
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_QueryDepthMIS_TwoHopBound
import Definitions.Def_QueryDepthMIS_aliveSet
import Definitions.Def_QueryDepthMIS_condProb
import Definitions.Def_QueryDepthMIS_maxDegOn
import Definitions.Def_QueryDepthMIS_oneHopEvent
import Definitions.Def_QueryDepthMIS_queryDepth
import Definitions.Def_QueryDepthMIS_rank
import Definitions.Def_QueryDepthMIS_twoHopEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QDM
open QueryDepthMIS RGMISFast

section scan
variable {V : Type*} [LinearOrder V]

lemma scanOrder_mk (r : V → ℕ) (l : List V) (hl : (l : Multiset V).Nodup) :
    scanOrder r ⟨(l : Multiset V), hl⟩ =
      ((l.map (fun w => toLex (r w, w))).insertionSort (· ≤ ·)).map (fun p => (ofLex p).2) := by
  rfl

lemma scanOrder_spec (r : V → ℕ) (hr : Function.Injective r) (s : Finset V) :
    (scanOrder r s).Pairwise (fun a b => r a < r b) ∧ (scanOrder r s).Nodup ∧
      (scanOrder r s).length = s.card := by
  rcases s with ⟨m, hm⟩
  induction m using Quot.ind with
  | mk l =>
    have hl : l.Nodup := hm
    change List.Pairwise (fun a b => r a < r b) (scanOrder r ⟨(l : Multiset V), hl⟩) ∧
      (scanOrder r ⟨(l : Multiset V), hl⟩).Nodup ∧
      (scanOrder r ⟨(l : Multiset V), hl⟩).length = (⟨(l : Multiset V), hl⟩ : Finset V).card
    rw [scanOrder_mk r l hl]
    set f : V → Lex (ℕ × V) := fun w => toLex (r w, w) with hf
    have hfi : Function.Injective f := by
      intro a b h; simp [hf] at h; exact h.2
    have hperm := List.perm_insertionSort (· ≤ ·) (l.map f)
    have hnd : (List.insertionSort (· ≤ ·) (l.map f)).Nodup :=
      hperm.nodup_iff.2 (hl.map hfi)
    have hpw := List.pairwise_insertionSort (· ≤ ·) (l.map f)
    have hg : ((List.insertionSort (· ≤ ·) (l.map f)).map (fun p => (ofLex p).2)) =
        (List.insertionSort (· ≤ ·) (l.map f)).map (fun p => (ofLex p).2) := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      have := hpw.and hnd
      refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.and hpw (List.nodup_iff_pairwise_ne.mp hnd))
      intro a b ha hb ⟨hab, hne⟩
      have ha' : a ∈ l.map f := hperm.subset ha
      have hb' : b ∈ l.map f := hperm.subset hb
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha'
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb'
      simp only [hf, ofLex_toLex]
      have hxy : x ≠ y := fun h => hne (by rw [h])
      rcases (Prod.Lex.le_iff).1 hab with h | ⟨h1, -⟩
      · exact h
      · exact absurd (hr h1) hxy
    · refine List.Nodup.map_on ?_ hnd
      intro a ha b hb hab
      have ha' : a ∈ l.map f := hperm.subset ha
      have hb' : b ∈ l.map f := hperm.subset hb
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha'
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb'
      simp only [hf, ofLex_toLex] at hab
      rw [hab]
    · simp only [List.length_map, hperm.length_eq]
      rfl

lemma scanOrder_eq_of_pairwise (r : V → ℕ) (l : List V)
    (hl : l.Pairwise (fun a b => r a < r b)) : scanOrder r l.toFinset = l := by
  have hnd : l.Nodup := by
    refine List.Pairwise.imp ?_ hl
    intro a b h e; rw [e] at h; exact lt_irrefl _ h
  have hnd' : (l : Multiset V).Nodup := Multiset.coe_nodup.2 hnd
  have : l.toFinset = ⟨(l : Multiset V), hnd'⟩ := by
    ext x; simp
  rw [this, scanOrder_mk r l hnd']
  have hs : List.Pairwise (· ≤ ·) (l.map (fun w => toLex (r w, w))) := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ hl
    intro a b h
    exact (Prod.Lex.le_iff).2 (Or.inl h)
  rw [List.Pairwise.insertionSort_eq hs, List.map_map]
  conv_rhs => rw [← List.map_id l]
  rfl

end scan

section greedy
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma inMIS_iff (r : V → ℕ) (v : V) :
    inMIS G r v = true ↔ ∀ w, G.Adj v w → r w < r v → inMIS G r w = false := by
  rw [inMIS_eq]
  simp only [List.all_eq_true, List.mem_attach, true_implies, Bool.not_eq_eq_eq_not,
    Bool.not_true, Subtype.forall, mem_lowerNbrs]
  constructor
  · intro h w hw hlt; exact h w ⟨hw, hlt⟩
  · intro h w hw; exact h w hw.1 hw.2

lemma not_inMIS_iff (r : V → ℕ) (v : V) :
    inMIS G r v = false ↔ ∃ w, G.Adj v w ∧ r w < r v ∧ inMIS G r w = true := by
  rw [← Bool.not_eq_true, inMIS_iff]
  push Not
  simp

lemma le_tau_iff (r : V → ℕ) (v : V) (t : ℕ) :
    t ≤ tau G r v ↔ ∀ x, (x = v ∨ G.Adj v x) → inMIS G r x = true → t ≤ r x := by
  unfold tau
  rw [Finset.le_min'_iff]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_insert,
    SimpleGraph.mem_neighborFinset, forall_exists_index, and_imp]
  constructor
  · intro h x hx hm
    exact h _ x hx hm rfl
  · intro h y x hx hm hy
    rw [← hy]; exact h x hx hm

lemma tau_le_of (r : V → ℕ) (v x : V) (hx : x = v ∨ G.Adj v x) (hm : inMIS G r x = true) :
    tau G r v ≤ r x := by
  unfold tau
  apply Finset.min'_le
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_insert,
    SimpleGraph.mem_neighborFinset]
  exact ⟨x, ⟨hx, hm⟩, rfl⟩

lemma tau_le_self (r : V → ℕ) (v : V) : tau G r v ≤ r v := by
  cases h : inMIS G r v
  · obtain ⟨w, hw, hlt, hm⟩ := (not_inMIS_iff G r v).1 h
    exact (tau_le_of G r v w (Or.inr hw) hm).trans hlt.le
  · exact tau_le_of G r v v (Or.inl rfl) h

lemma inMIS_of_le_tau (r : V → ℕ) (v : V) (h : r v ≤ tau G r v) : inMIS G r v = true := by
  by_contra hc
  rw [Bool.not_eq_true, not_inMIS_iff] at hc
  obtain ⟨w, hw, hlt, hm⟩ := hc
  have := tau_le_of G r v w (Or.inr hw) hm
  omega

lemma tau_eq_self_of_inMIS (r : V → ℕ) (v : V) (h : inMIS G r v = true) :
    tau G r v = r v := by
  apply le_antisymm (tau_le_self G r v)
  rw [le_tau_iff]
  intro x hx hm
  rcases hx with rfl | hx
  · exact le_rfl
  · by_contra hc
    push Not at hc
    have := (inMIS_iff G r v).1 h x hx hc
    rw [this] at hm; exact Bool.false_ne_true hm

lemma tau_le_of_adj_alive (r : V → ℕ) (v x : V) (hadj : G.Adj v x) (hx : r x ≤ tau G r x) :
    tau G r v ≤ r x :=
  tau_le_of G r v x (Or.inr hadj) (inMIS_of_le_tau G r x hx)

end greedy

section rankfacts
variable {V : Type*} [Fintype V]

lemma rank_pos (ω : Perm V) (v : V) : 1 ≤ rank ω v := by simp [rank]

lemma rank_le (ω : Perm V) (v : V) : rank ω v ≤ Fintype.card V := by
  simp only [rank]; have := (ω v).isLt; omega

lemma rank_injective (ω : Perm V) : Function.Injective (rank ω) := by
  intro a b h; simp only [rank, add_left_inj] at h; exact ω.injective (Fin.ext h)

/-- the vertex at (1-based) position `p` -/
lemma exists_rank_eq (ω : Perm V) (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ Fintype.card V) :
    ∃ v, rank ω v = p := by
  refine ⟨ω.symm ⟨p - 1, by omega⟩, ?_⟩
  simp [rank]; omega

end rankfacts

section locality
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `ω'` agrees with `ω` on all positions `≤ k` of `ω`. -/
def AgreeLE (k : ℕ) (ω ω' : Perm V) : Prop := ∀ v, rank ω v ≤ k → rank ω' v = rank ω v

lemma AgreeLE.symm_le {k : ℕ} {ω ω' : Perm V} (h : AgreeLE k ω ω') {v : V}
    (hv : rank ω' v ≤ k) : rank ω v = rank ω' v := by
  obtain ⟨u, hu⟩ := exists_rank_eq ω (rank ω' v) (rank_pos _ _) (rank_le _ _)
  have := h u (hu ▸ hv)
  rw [hu] at this
  have huv := rank_injective ω' this
  subst huv; exact hu

lemma AgreeLE.symm {k : ℕ} {ω ω' : Perm V} (h : AgreeLE k ω ω') : AgreeLE k ω' ω :=
  fun _ hv => h.symm_le hv

lemma AgreeLE.mono {k k' : ℕ} {ω ω' : Perm V} (h : AgreeLE k ω ω') (hk : k' ≤ k) :
    AgreeLE k' ω ω' := fun v hv => h v (hv.trans hk)

lemma inMIS_congr {k : ℕ} {ω ω' : Perm V} (h : AgreeLE k ω ω') :
    ∀ v, rank ω v ≤ k → inMIS G (rank ω) v = inMIS G (rank ω') v := by
  intro v
  induction hn : rank ω v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    intro hv
    have hrv := h v (hn ▸ hv)
    apply Bool.eq_iff_iff.2
    rw [inMIS_iff, inMIS_iff]
    constructor
    · intro H w hw hlt
      have hw' : rank ω' w ≤ k := by omega
      have e := h.symm_le hw'
      have := H w hw (by omega)
      rw [← ih (rank ω w) (by omega) w rfl (by omega), this]
    · intro H w hw hlt
      have e := h w (by omega)
      have := H w hw (by omega)
      rw [ih (rank ω w) (by omega) w rfl (by omega), this]

lemma le_tau_congr {k : ℕ} {ω ω' : Perm V} (h : AgreeLE k ω ω') (v : V) {t : ℕ}
    (ht : t ≤ k + 1) :
    t ≤ tau G (rank ω) v ↔ t ≤ tau G (rank ω') v := by
  rw [le_tau_iff, le_tau_iff]
  constructor
  · intro H x hx hm
    by_contra hc; push Not at hc
    have hx' : rank ω' x ≤ k := by omega
    have e := h.symm_le hx'
    rw [← inMIS_congr G h x (by omega)] at hm
    have := H x hx hm; omega
  · intro H x hx hm
    by_contra hc; push Not at hc
    have e := h x (by omega)
    rw [inMIS_congr G h x (by omega)] at hm
    have := H x hx hm; omega

end locality

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QDM
open QueryDepthMIS RGMISFast

section expose
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `ω` agrees with `ω₀` on the positions `S` (positions of `ω₀`). -/
def Agree (S : Finset ℕ) (ω₀ ω : Perm V) : Prop := ∀ v, rank ω₀ v ∈ S → rank ω v = rank ω₀ v

instance (S : Finset ℕ) (ω₀ : Perm V) : DecidablePred (Agree S ω₀) := by
  intro ω; unfold Agree; infer_instance

/-- the class of permutations agreeing with `ω₀` on `S` -/
def cls (S : Finset ℕ) (ω₀ : Perm V) : Finset (Perm V) := Finset.univ.filter (Agree S ω₀)

lemma mem_cls {S : Finset ℕ} {ω₀ ω : Perm V} : ω ∈ cls S ω₀ ↔ Agree S ω₀ ω := by
  simp [cls]

lemma Agree.refl (S : Finset ℕ) (ω : Perm V) : Agree S ω ω := fun _ _ => rfl

lemma self_mem_cls (S : Finset ℕ) (ω : Perm V) : ω ∈ cls S ω := mem_cls.2 (Agree.refl S ω)

lemma Agree.symm {S : Finset ℕ} {ω₀ ω : Perm V} (h : Agree S ω₀ ω) : Agree S ω ω₀ := by
  intro v hv
  obtain ⟨u, hu⟩ := exists_rank_eq ω₀ (rank ω v) (rank_pos _ _) (rank_le _ _)
  have := h u (hu ▸ hv)
  rw [hu] at this
  have huv := rank_injective ω this
  subst huv; exact hu

lemma Agree.mem_iff {S : Finset ℕ} {ω₀ ω : Perm V} (h : Agree S ω₀ ω) (v : V) :
    rank ω v ∈ S ↔ rank ω₀ v ∈ S := by
  constructor
  · intro hv; rw [h.symm v hv]; exact hv
  · intro hv; rw [h v hv]; exact hv

lemma Agree.trans {S : Finset ℕ} {ω₁ ω₂ ω₃ : Perm V} (h₁ : Agree S ω₁ ω₂) (h₂ : Agree S ω₂ ω₃) :
    Agree S ω₁ ω₃ := by
  intro v hv
  rw [h₂ v ((h₁.mem_iff v).2 hv), h₁ v hv]

lemma Agree.mono {S S' : Finset ℕ} (hS : S ⊆ S') {ω₀ ω : Perm V} (h : Agree S' ω₀ ω) :
    Agree S ω₀ ω := fun v hv => h v (hS hv)

lemma cls_eq_of_mem {S : Finset ℕ} {ω₀ ω : Perm V} (h : ω ∈ cls S ω₀) : cls S ω = cls S ω₀ := by
  ext ω'
  simp only [mem_cls] at h ⊢
  exact ⟨fun h' => h.trans h', fun h' => (mem_cls.1 (mem_cls.2 h)).symm.trans h'⟩

lemma cls_subset {S S' : Finset ℕ} (hS : S ⊆ S') {ω₀ ω : Perm V} (h : ω ∈ cls S ω₀) :
    cls S' ω ⊆ cls S ω₀ := by
  intro ω' h'
  rw [mem_cls] at h h' ⊢
  exact h.trans (h'.mono hS)

/-- exposed vertices -/
def exposedV (S : Finset ℕ) (ω : Perm V) : Finset V := Finset.univ.filter (fun v => rank ω v ∈ S)

lemma card_exposedV (S : Finset ℕ) (ω : Perm V) :
    (exposedV S ω).card = (S.filter (fun p => 1 ≤ p ∧ p ≤ Fintype.card V)).card := by
  apply Finset.card_bij (fun v _ => rank ω v)
  · intro v hv
    simp only [exposedV, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_filter]
    exact ⟨hv, rank_pos _ _, rank_le _ _⟩
  · intro a _ b _ h; exact rank_injective ω h
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨v, hv⟩ := exists_rank_eq ω p hp.2.1 hp.2.2
    exact ⟨v, by simp [exposedV, hv, hp.1], hv⟩

/-- number of positions of `S` within `[1, n]` -/
def nExp (V : Type*) [Fintype V] (S : Finset ℕ) : ℕ :=
  (S.filter (fun p => 1 ≤ p ∧ p ≤ Fintype.card V)).card

lemma card_cls (S : Finset ℕ) (ω₀ : Perm V) :
    (cls S ω₀).card = (Fintype.card V - nExp V S).factorial := by
  classical
  -- bijection with permutations of V fixing exposed vertices
  let p : V → Prop := fun v => rank ω₀ v ∉ S
  have e1 : {ω // ω ∈ cls S ω₀} ≃ {f : Equiv.Perm V // ∀ a, ¬p a → f a = a} :=
    { toFun := fun ω => ⟨ω.1.trans ω₀.symm, by
        intro a ha
        have := (mem_cls.1 ω.2) a (by simpa [p] using ha)
        simp only [Equiv.trans_apply]
        rw [Equiv.symm_apply_eq]
        simp only [rank, add_left_inj] at this
        exact Fin.ext this⟩
      invFun := fun f => ⟨f.1.trans ω₀, by
        rw [mem_cls]
        intro v hv
        have := f.2 v (by simpa [p] using hv)
        simp [rank, this]⟩
      left_inv := by intro ω; ext; simp
      right_inv := by intro f; ext; simp }
  have h1 := Fintype.card_congr (e1.trans (Equiv.Perm.subtypeEquivSubtypePerm p).symm)
  rw [Fintype.card_coe] at h1
  rw [h1, Fintype.card_perm]
  congr 1
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter p) = Finset.univ \ exposedV S ω₀ := by
    ext v; simp [p, exposedV]
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    card_exposedV]
  try rfl

lemma condProb_eq (E : Perm V → Prop) [DecidablePred E] (S : Finset ℕ) (ω₀ : Perm V) :
    condProb E S ω₀ = (((cls S ω₀).filter E).card : ℝ) / ((cls S ω₀).card : ℝ) := by
  unfold condProb
  congr 2
  · congr 1; ext ω; simp [cls, Agree]

lemma cls_card_pos (S : Finset ℕ) (ω₀ : Perm V) : 0 < (cls S ω₀).card :=
  Finset.card_pos.2 ⟨ω₀, self_mem_cls S ω₀⟩

/-- the tower property -/
lemma sum_condProb_tower (E : Perm V → Prop) [DecidablePred E] {S S' : Finset ℕ}
    (hS : S ⊆ S') (ω₀ : Perm V) :
    ∑ ω ∈ cls S ω₀, condProb E S' ω = (((cls S ω₀).filter E).card : ℝ) := by
  classical
  set c : ℕ := (Fintype.card V - nExp V S').factorial with hc
  have hcpos : (0 : ℝ) < c := by rw [hc]; exact_mod_cast Nat.factorial_pos _
  have h1 : ∀ ω, condProb E S' ω = (((cls S' ω).filter E).card : ℝ) / c := by
    intro ω; rw [condProb_eq, card_cls]
  simp_rw [h1, ← Finset.sum_div]
  rw [div_eq_iff hcpos.ne']
  -- double counting
  have h2 : ∑ ω ∈ cls S ω₀, (((cls S' ω).filter E).card : ℝ) =
      ∑ ω' ∈ (cls S ω₀).filter E, ((cls S' ω').card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    rw [Finset.sum_comm' (t' := (cls S ω₀).filter E) (s' := fun ω' => cls S' ω')]
    intro ω ω'
    simp only [Finset.mem_filter, mem_cls]
    constructor
    · rintro ⟨hω, h', hE⟩
      exact ⟨h'.symm, hω.trans (h'.mono hS), hE⟩
    · rintro ⟨h', hω', hE⟩
      exact ⟨hω'.trans (h'.mono hS), h'.symm, hE⟩
  rw [h2]
  simp_rw [card_cls]
  rw [Finset.sum_const, nsmul_eq_mul]

lemma condProb_tower (E : Perm V → Prop) [DecidablePred E] {S S' : Finset ℕ}
    (hS : S ⊆ S') (ω₀ : Perm V) :
    condProb E S ω₀ = (∑ ω ∈ cls S ω₀, condProb E S' ω) / ((cls S ω₀).card : ℝ) := by
  rw [sum_condProb_tower E hS, condProb_eq]

lemma condProb_congr (E : Perm V → Prop) {S : Finset ℕ} {ω ω' : Perm V} (h : ω' ∈ cls S ω) :
    condProb E S ω' = condProb E S ω := by
  classical
  rw [condProb_eq, condProb_eq, cls_eq_of_mem h]

lemma condProb_nonneg (E : Perm V → Prop) (S : Finset ℕ) (ω : Perm V) : 0 ≤ condProb E S ω := by
  classical
  rw [condProb_eq]; positivity

lemma condProb_le_one (E : Perm V → Prop) (S : Finset ℕ) (ω : Perm V) : condProb E S ω ≤ 1 := by
  classical
  rw [condProb_eq, div_le_one (by exact_mod_cast cls_card_pos S ω)]
  exact_mod_cast Finset.card_filter_le _ _

lemma condProb_mono {E F : Perm V → Prop} (hEF : ∀ ω, E ω → F ω) (S : Finset ℕ) (ω : Perm V) :
    condProb E S ω ≤ condProb F S ω := by
  classical
  rw [condProb_eq, condProb_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun ω hω => by
    simp only [Finset.mem_filter] at hω ⊢; exact ⟨hω.1, hEF _ hω.2⟩)

/-- an event determined by the exposed positions -/
lemma condProb_of_determined (E : Perm V → Prop) [DecidablePred E] (S : Finset ℕ) (ω₀ : Perm V)
    (hE : ∀ ω ∈ cls S ω₀, (E ω ↔ E ω₀)) :
    condProb E S ω₀ = if E ω₀ then 1 else 0 := by
  classical
  rw [condProb_eq]
  split_ifs with h
  · rw [Finset.filter_true_of_mem (fun ω hω => (hE ω hω).2 h), div_self]
    exact_mod_cast (cls_card_pos S ω₀).ne'
  · rw [Finset.filter_false_of_mem (fun ω hω hE' => h ((hE ω hω).1 hE'))]
    simp

/-- the position index (0-based) of a 1-based position -/
def posIdx (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V) : Fin (Fintype.card V) :=
  ⟨p - 1, by omega⟩

/-- put vertex `x` at 1-based position `p` by a swap -/
def put (ω : Perm V) (x : V) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V) : Perm V :=
  ω.trans (Equiv.swap (ω x) (posIdx p hp))

lemma rank_put_self (ω : Perm V) (x : V) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V) :
    rank (put ω x p hp) x = p := by
  simp only [put, rank, Equiv.trans_apply, Equiv.swap_apply_left, posIdx]; omega

lemma rank_put_of_ne (ω : Perm V) (x : V) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V) (v : V)
    (h1 : v ≠ x) (h2 : rank ω v ≠ p) : rank (put ω x p hp) v = rank ω v := by
  simp only [put, rank, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne]
  · intro h; exact h1 (ω.injective h)
  · intro h; apply h2; simp [rank, h, posIdx]; omega

lemma put_mem_cls {S : Finset ℕ} (ω₀ : Perm V) (x : V) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ Fintype.card V) (hpS : p ∉ S) (hx : rank ω₀ x ∉ S) :
    put ω₀ x p hp ∈ cls S ω₀ := by
  rw [mem_cls]
  intro v hv
  apply rank_put_of_ne
  · rintro rfl; exact hx hv
  · intro h; rw [h] at hv; exact hpS hv

/-- unexposed vertices -/
def unexp (S : Finset ℕ) (ω : Perm V) : Finset V := Finset.univ.filter (fun v => rank ω v ∉ S)

lemma card_unexp (S : Finset ℕ) (ω : Perm V) :
    (unexp S ω).card = Fintype.card V - nExp V S := by
  have : unexp S ω = Finset.univ \ exposedV S ω := by ext v; simp [unexp, exposedV]
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_exposedV]
  rfl

lemma unexp_congr {S : Finset ℕ} {ω₀ ω : Perm V} (h : ω ∈ cls S ω₀) : unexp S ω = unexp S ω₀ := by
  ext v; simp [unexp, (mem_cls.1 h).mem_iff v]

/-- the class of `ω` refined by position `p` is the set of class members with `x` at `p` -/
lemma cls_insert_put {S : Finset ℕ} (ω₀ : Perm V) (x : V) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ Fintype.card V) (hpS : p ∉ S) (hx : rank ω₀ x ∉ S) :
    cls (insert p S) (put ω₀ x p hp) = (cls S ω₀).filter (fun ω => rank ω x = p) := by
  ext ω
  simp only [Finset.mem_filter, mem_cls]
  have hput := mem_cls.1 (put_mem_cls ω₀ x p hp hpS hx)
  constructor
  · intro h
    refine ⟨hput.trans (h.mono (Finset.subset_insert _ _)), ?_⟩
    have := h x (by rw [rank_put_self]; exact Finset.mem_insert_self _ _)
    rw [this, rank_put_self]
  · rintro ⟨h1, h2⟩
    intro v hv
    rw [Finset.mem_insert] at hv
    rcases hv with hv | hv
    · have hvx : v = x := rank_injective _ (hv.trans (rank_put_self ω₀ x p hp).symm)
      subst hvx
      rw [h2, rank_put_self]
    · have := (hput.mem_iff v).1 hv
      rw [h1 v this, hput v this]

/-- vertex at position `p` -/
def vAt (ω : Perm V) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V) : V := ω.symm (posIdx p hp)

lemma rank_vAt (ω : Perm V) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V) : rank ω (vAt ω p hp) = p := by
  simp only [vAt, rank, Equiv.apply_symm_apply, posIdx]; omega

lemma vAt_eq_iff (ω : Perm V) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V) (x : V) :
    vAt ω p hp = x ↔ rank ω x = p := by
  constructor
  · rintro rfl; exact rank_vAt ω p hp
  · intro h; exact rank_injective ω ((rank_vAt ω p hp).trans h.symm)

lemma sum_cls_step {S : Finset ℕ} (ω₀ : Perm V) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V)
    (hpS : p ∉ S) (f : Perm V → ℝ) (hf : ∀ ω ω', Agree (insert p S) ω ω' → f ω' = f ω) :
    ∑ ω ∈ cls S ω₀, f ω =
      ((Fintype.card V - nExp V (insert p S)).factorial : ℝ) *
        ∑ x ∈ unexp S ω₀, f (put ω₀ x p hp) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun ω => vAt ω p hp) (t := unexp S ω₀)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' : rank ω₀ x ∉ S := by simpa [unexp] using hx
    have hfib : (cls S ω₀).filter (fun ω => vAt ω p hp = x) =
        cls (insert p S) (put ω₀ x p hp) := by
      rw [cls_insert_put ω₀ x p hp hpS hx']
      congr 1; ext ω; exact vAt_eq_iff ω p hp x
    rw [hfib]
    rw [Finset.sum_congr rfl (fun ω hω => hf _ _ (mem_cls.1 hω)), Finset.sum_const, card_cls,
      nsmul_eq_mul]
  · intro ω hω
    simp only [unexp, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← (mem_cls.1 hω).mem_iff, rank_vAt]; exact hpS

lemma card_cls_step {S : Finset ℕ} (ω₀ : Perm V) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V)
    (hpS : p ∉ S) :
    ((cls S ω₀).card : ℝ) =
      ((Fintype.card V - nExp V (insert p S)).factorial : ℝ) * ((unexp S ω₀).card : ℝ) := by
  have := sum_cls_step ω₀ p hp hpS (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  simpa using this

lemma unexp_nonempty_of {S : Finset ℕ} (ω₀ : Perm V) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V)
    (hpS : p ∉ S) : (unexp S ω₀).Nonempty :=
  ⟨vAt ω₀ p hp, by simp [unexp, rank_vAt, hpS]⟩

/-- one exposure step: average over the vertex placed at position `p` -/
lemma avg_cls_step {S : Finset ℕ} (ω₀ : Perm V) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ Fintype.card V)
    (hpS : p ∉ S) (f : Perm V → ℝ) (hf : ∀ ω ω', Agree (insert p S) ω ω' → f ω' = f ω) :
    (∑ ω ∈ cls S ω₀, f ω) / ((cls S ω₀).card : ℝ) =
      (∑ x ∈ unexp S ω₀, f (put ω₀ x p hp)) / ((unexp S ω₀).card : ℝ) := by
  rw [sum_cls_step ω₀ p hp hpS f hf, card_cls_step ω₀ p hp hpS]
  have h1 : (0 : ℝ) < ((Fintype.card V - nExp V (insert p S)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  field_simp

lemma condProb_step (E : Perm V → Prop) {S : Finset ℕ} (ω₀ : Perm V) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ Fintype.card V) (hpS : p ∉ S) :
    condProb E S ω₀ =
      (∑ x ∈ unexp S ω₀, condProb E (insert p S) (put ω₀ x p hp)) / ((unexp S ω₀).card : ℝ) := by
  classical
  rw [condProb_tower E (Finset.subset_insert p S) ω₀]
  exact avg_cls_step ω₀ p hp hpS _ (fun ω ω' h => condProb_congr E (mem_cls.2 h))

/-- The basic one-step bound: if only vertices in `B` can be placed at `p` without killing `E`,
then the probability is at most `|B|/|U|` times the maximum over those placements. -/
lemma condProb_step_le (E : Perm V → Prop) {S : Finset ℕ} (ω₀ : Perm V) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ Fintype.card V) (hpS : p ∉ S) (B : Finset V) (M : ℝ) (hM : 0 ≤ M)
    (hB : ∀ x ∈ unexp S ω₀, x ∉ B → condProb E (insert p S) (put ω₀ x p hp) = 0)
    (hBM : ∀ x ∈ unexp S ω₀, x ∈ B → condProb E (insert p S) (put ω₀ x p hp) ≤ M) :
    condProb E S ω₀ ≤ ((B ∩ unexp S ω₀).card : ℝ) / ((unexp S ω₀).card : ℝ) * M := by
  rw [condProb_step E ω₀ p hp hpS, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ∑ x ∈ unexp S ω₀, condProb E (insert p S) (put ω₀ x p hp)
      = ∑ x ∈ unexp S ω₀, (if x ∈ B then condProb E (insert p S) (put ω₀ x p hp) else 0) := by
        apply Finset.sum_congr rfl; intro x hx
        split_ifs with h
        · rfl
        · exact hB x hx h
    _ ≤ ∑ x ∈ unexp S ω₀, (if x ∈ B then M else 0) := by
        apply Finset.sum_le_sum; intro x hx
        split_ifs with h
        · exact hBM x hx h
        · exact le_rfl
    _ = ((B ∩ unexp S ω₀).card : ℝ) * M := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        congr 3
        ext x; simp [and_comm]

/-- conditional expectation given the positions `S` of `ω₀` -/
noncomputable def cexp (f : Perm V → ℝ) (S : Finset ℕ) (ω₀ : Perm V) : ℝ :=
  (∑ ω ∈ cls S ω₀, f ω) / ((cls S ω₀).card : ℝ)

lemma cexp_congr (f : Perm V → ℝ) {S : Finset ℕ} {ω ω' : Perm V} (h : ω' ∈ cls S ω) :
    cexp f S ω' = cexp f S ω := by
  unfold cexp; rw [cls_eq_of_mem h]

lemma sum_cexp_tower (f : Perm V → ℝ) {S S' : Finset ℕ} (hS : S ⊆ S') (ω₀ : Perm V) :
    ∑ ω ∈ cls S ω₀, cexp f S' ω = ∑ ω ∈ cls S ω₀, f ω := by
  classical
  set c : ℕ := (Fintype.card V - nExp V S').factorial with hc
  have hcpos : (0 : ℝ) < c := by rw [hc]; exact_mod_cast Nat.factorial_pos _
  have h1 : ∀ ω, cexp f S' ω = (∑ ω' ∈ cls S' ω, f ω') / c := by
    intro ω; rw [cexp, card_cls]
  simp_rw [h1, ← Finset.sum_div]
  rw [div_eq_iff hcpos.ne']
  have h2 : ∑ ω ∈ cls S ω₀, ∑ ω' ∈ cls S' ω, f ω' =
      ∑ ω' ∈ cls S ω₀, ∑ ω ∈ cls S' ω', f ω' := by
    rw [Finset.sum_comm' (t' := cls S ω₀) (s' := fun ω' => cls S' ω')]
    intro ω ω'
    simp only [mem_cls]
    constructor
    · rintro ⟨hω, h'⟩
      exact ⟨h'.symm, hω.trans (h'.mono hS)⟩
    · rintro ⟨h', hω'⟩
      exact ⟨hω'.trans (h'.mono hS), h'.symm⟩
  rw [h2]
  simp_rw [Finset.sum_const, card_cls, nsmul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro x _; ring

lemma cexp_tower (f : Perm V → ℝ) {S S' : Finset ℕ} (hS : S ⊆ S') (ω₀ : Perm V) :
    cexp f S ω₀ = cexp (cexp f S') S ω₀ := by
  rw [cexp, cexp, sum_cexp_tower f hS ω₀]

lemma cexp_step (f : Perm V → ℝ) {S : Finset ℕ} (ω₀ : Perm V) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ Fintype.card V) (hpS : p ∉ S) :
    cexp f S ω₀ =
      (∑ x ∈ unexp S ω₀, cexp f (insert p S) (put ω₀ x p hp)) / ((unexp S ω₀).card : ℝ) := by
  rw [cexp_tower f (Finset.subset_insert p S) ω₀]
  exact avg_cls_step ω₀ p hp hpS _ (fun ω ω' h => cexp_congr f (mem_cls.2 h))

lemma cexp_of_determined (f : Perm V → ℝ) (S : Finset ℕ) (ω₀ : Perm V)
    (hf : ∀ ω ∈ cls S ω₀, f ω = f ω₀) : cexp f S ω₀ = f ω₀ := by
  unfold cexp
  rw [Finset.sum_congr rfl hf, Finset.sum_const, nsmul_eq_mul]
  have : ((cls S ω₀).card : ℝ) ≠ 0 := by exact_mod_cast (cls_card_pos S ω₀).ne'
  field_simp

lemma cexp_mono {f g : Perm V → ℝ} (hfg : ∀ ω, f ω ≤ g ω) (S : Finset ℕ) (ω₀ : Perm V) :
    cexp f S ω₀ ≤ cexp g S ω₀ := by
  unfold cexp
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun ω _ => hfg ω)

lemma condProb_eq_cexp (E : Perm V → Prop) [DecidablePred E] (S : Finset ℕ) (ω₀ : Perm V) :
    condProb E S ω₀ = cexp (fun ω => if E ω then 1 else 0) S ω₀ := by
  rw [condProb_eq, cexp, Finset.sum_boole]

lemma cls_empty (ω₀ : Perm V) : cls ∅ ω₀ = Finset.univ := by
  ext ω; simp [mem_cls, Agree]

lemma coinProb_eq_condProb (E : Perm V → Prop) (ω₀ : Perm V) :
    PunctSketch.coinProb E = condProb E ∅ ω₀ := by
  classical
  rw [condProb_eq, cls_empty, PunctSketch.coinProb, Finset.card_univ]

lemma uniformExp_eq_cexp (f : Perm V → ℝ) (ω₀ : Perm V) :
    NoSignalPA.uniformExp f = cexp f ∅ ω₀ := by
  rw [NoSignalPA.uniformExp, cexp, cls_empty, Finset.card_univ]

end expose

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM
open QueryDepthMIS RGMISFast

section general
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma condProb_eq_zero (E : Perm V → Prop) (S : Finset ℕ) (ω₀ : Perm V)
    (h : ∀ ω ∈ cls S ω₀, ¬ E ω) : condProb E S ω₀ = 0 := by
  classical
  rw [condProb_eq, Finset.filter_false_of_mem h]; simp

lemma condProb_union_le {ι : Type*} (s : Finset ι) (E : ι → Perm V → Prop) (S : Finset ℕ)
    (ω₀ : Perm V) :
    condProb (fun ω => ∃ i ∈ s, E i ω) S ω₀ ≤ ∑ i ∈ s, condProb (E i) S ω₀ := by
  classical
  simp_rw [condProb_eq]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (cls S ω₀).filter (fun ω => ∃ i ∈ s, E i ω) =
      s.biUnion (fun i => (cls S ω₀).filter (E i)) := by
    ext ω; simp only [Finset.mem_filter, Finset.mem_biUnion]; tauto
  rw [this]
  exact_mod_cast Finset.card_biUnion_le

lemma condProb_compl (E : Perm V → Prop) (S : Finset ℕ) (ω₀ : Perm V) :
    condProb (fun ω => ¬ E ω) S ω₀ = 1 - condProb E S ω₀ := by
  classical
  rw [condProb_eq, condProb_eq]
  have hpos : ((cls S ω₀).card : ℝ) ≠ 0 := by exact_mod_cast (cls_card_pos S ω₀).ne'
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos]
  rw [add_comm]
  exact_mod_cast Finset.card_filter_add_card_filter_not _

lemma Icc_insert (i : ℕ) : insert (i + 1) (Finset.Icc 1 i) = Finset.Icc 1 (i + 1) := by
  ext x; simp; omega

end general

section deg
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma agreeLE_of_agree {i : ℕ} {ω ω' : Perm V} (h : Agree (Finset.Icc 1 i) ω ω') :
    AgreeLE i ω ω' := by
  intro v hv
  exact h v (by simp [hv, rank_pos])

/-- alive at time `i+1` is determined by the first `i` positions -/
lemma alive_congr {i : ℕ} {ω ω' : Perm V} (h : Agree (Finset.Icc 1 i) ω ω') (v : V) :
    i + 1 ≤ tau G (rank ω) v ↔ i + 1 ≤ tau G (rank ω') v :=
  le_tau_congr G (agreeLE_of_agree h) v le_rfl

/-- the event for the degree reduction at a fixed vertex `u` -/
def degEv (t : ℕ) (d : ℝ) (u : V) (ω : Perm V) : Prop :=
  t + 1 ≤ rank ω u ∧ t + 1 ≤ tau G (rank ω) u ∧
    d ≤ ((Finset.univ.filter (fun w => G.Adj u w ∧ t + 1 ≤ rank ω w ∧
      t + 1 ≤ tau G (rank ω) w)).card : ℝ)

lemma degEv_bound (t : ℕ) (ht : t ≤ Fintype.card V) (d : ℝ) (hd : 0 ≤ d) (u : V) :
    ∀ k i, i + k = t → ∀ ω : Perm V,
      condProb (degEv G t d u) (Finset.Icc 1 i) ω ≤
        Real.exp (-(k : ℝ) * d / Fintype.card V) := by
  intro k
  induction k with
  | zero =>
    intro i _ ω
    simpa using condProb_le_one _ _ _
  | succ k ih =>
    intro i hik ω
    have hp : 1 ≤ i + 1 ∧ i + 1 ≤ Fintype.card V := ⟨by omega, by omega⟩
    have hpS : i + 1 ∉ Finset.Icc 1 i := by simp
    set n := Fintype.card V with hn
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    -- good set
    set B : Finset V := Finset.univ.filter
      (fun x => x ≠ u ∧ ¬ (G.Adj u x ∧ i + 1 ≤ tau G (rank ω) x)) with hB
    by_cases hex : ∃ ω' ∈ cls (Finset.Icc 1 i) ω, degEv G t d u ω'
    · obtain ⟨ω', hω', hE⟩ := hex
      have hstep := condProb_step_le (degEv G t d u) ω (i + 1) hp hpS B
        (Real.exp (-(k : ℝ) * d / n)) (Real.exp_pos _).le ?_ ?_
      · refine hstep.trans ?_
        -- counting
        set W := Finset.univ.filter (fun w => G.Adj u w ∧ t + 1 ≤ rank ω' w ∧
          t + 1 ≤ tau G (rank ω') w) with hW
        have hWsub : W ⊆ unexp (Finset.Icc 1 i) ω \ (B ∩ unexp (Finset.Icc 1 i) ω) := by
          intro w hw
          simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          have hwu : w ∈ unexp (Finset.Icc 1 i) ω := by
            rw [← unexp_congr hω']
            simp [unexp]; omega
          simp only [Finset.mem_sdiff, Finset.mem_inter, hwu, true_and, and_true, hB,
            Finset.mem_filter, Finset.mem_univ, not_and, not_not]
          intro _ h
          apply h hw.1
          rw [alive_congr G (mem_cls.1 hω') w]
          omega
        have hcard := Finset.card_le_card hWsub
        rw [Finset.card_sdiff_of_subset Finset.inter_subset_right] at hcard
        have hm : 0 < (unexp (Finset.Icc 1 i) ω).card :=
          Finset.card_pos.2 (unexp_nonempty_of ω (i + 1) hp hpS)
        have hmle : (unexp (Finset.Icc 1 i) ω).card ≤ n := by
          rw [hn]; exact Finset.card_le_univ _
        have hWd : d ≤ (W.card : ℝ) := hE.2.2
        have hle : (B ∩ unexp (Finset.Icc 1 i) ω).card ≤ (unexp (Finset.Icc 1 i) ω).card :=
          Finset.card_le_card Finset.inter_subset_right
        have hratio : ((B ∩ unexp (Finset.Icc 1 i) ω).card : ℝ) /
            ((unexp (Finset.Icc 1 i) ω).card : ℝ) ≤ Real.exp (-d / n) := by
          have hmR : (0 : ℝ) < (unexp (Finset.Icc 1 i) ω).card := by exact_mod_cast hm
          rw [div_le_iff₀ hmR]
          have h1 : ((B ∩ unexp (Finset.Icc 1 i) ω).card : ℝ) ≤
              ((unexp (Finset.Icc 1 i) ω).card : ℝ) - d := by
            have : (((unexp (Finset.Icc 1 i) ω).card - (B ∩ unexp (Finset.Icc 1 i) ω).card :
              ℕ) : ℝ) = ((unexp (Finset.Icc 1 i) ω).card : ℝ) -
                ((B ∩ unexp (Finset.Icc 1 i) ω).card : ℝ) := by
              rw [Nat.cast_sub hle]
            have h2 : (W.card : ℝ) ≤ (((unexp (Finset.Icc 1 i) ω).card -
                (B ∩ unexp (Finset.Icc 1 i) ω).card : ℕ) : ℝ) := by exact_mod_cast hcard
            linarith
          have h3 : ((unexp (Finset.Icc 1 i) ω).card : ℝ) - d ≤
              ((unexp (Finset.Icc 1 i) ω).card : ℝ) * (1 - d / n) := by
            have hmn : ((unexp (Finset.Icc 1 i) ω).card : ℝ) ≤ n := by exact_mod_cast hmle
            have : ((unexp (Finset.Icc 1 i) ω).card : ℝ) * (d / n) ≤ d := by
              rw [mul_div_assoc', div_le_iff₀ hnpos]; nlinarith
            nlinarith
          have h4 : 1 - d / n ≤ Real.exp (-d / n) := by
            have := Real.add_one_le_exp (-d / n); rw [neg_div] at this ⊢; linarith
          nlinarith
        calc ((B ∩ unexp (Finset.Icc 1 i) ω).card : ℝ) /
              ((unexp (Finset.Icc 1 i) ω).card : ℝ) * Real.exp (-(k : ℝ) * d / n)
            ≤ Real.exp (-d / n) * Real.exp (-(k : ℝ) * d / n) :=
              mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le
          _ = Real.exp (-((k + 1 : ℕ) : ℝ) * d / n) := by
              rw [← Real.exp_add]; congr 1; push_cast; ring
      · -- bad placements kill the event
        intro x hx hxB
        rw [Icc_insert]
        apply condProb_eq_zero
        intro ω'' hω'' hE''
        have hput := put_mem_cls (S := Finset.Icc 1 i) ω x (i + 1) hp hpS
          (by simpa [unexp] using hx)
        have hag : Agree (Finset.Icc 1 (i + 1)) (put ω x (i + 1) hp) ω'' := mem_cls.1 hω''
        have hxr : rank ω'' x = i + 1 := by
          rw [hag x (by rw [rank_put_self]; simp), rank_put_self]
        have hxB' : x = u ∨ (G.Adj u x ∧ i + 1 ≤ tau G (rank ω) x) := by
          by_contra hc
          push Not at hc
          exact hxB (by
            simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hc.1, fun h => absurd h.2 (not_le.2 (hc.2 h.1))⟩)
        rcases hxB' with rfl | ⟨hadj, halive⟩
        · have := hE''.1; omega
        · -- x is alive at i+1, so it joins the MIS and kills u
          have hag2 : Agree (Finset.Icc 1 i) ω ω'' :=
            (mem_cls.1 hput).trans (hag.mono (by intro y; simp; omega))
          rw [alive_congr G hag2 x, ← hxr] at halive
          have := tau_le_of_adj_alive G (rank ω'') u x hadj halive
          have := hE''.2.1; omega
      · intro x hx _
        rw [Icc_insert]
        exact ih (i + 1) (by omega) _
    · push Not at hex
      rw [condProb_eq_zero _ _ _ hex]
      exact (Real.exp_pos _).le

theorem lemma_2_9_part1 (t : ℕ) (ht1 : 1 ≤ t) (ht : t < Fintype.card V) (d : ℝ) (hd : 0 < d) :
    PunctSketch.coinProb (fun ω : Perm V =>
        d ≤ (maxDegOn G (aliveSet G (rank ω) (t + 1) (Fintype.card V)) : ℝ)) ≤
      (Fintype.card V : ℝ) * Real.exp (-((t : ℝ) * d) / (Fintype.card V : ℝ)) := by
  classical
  obtain ⟨ω₀⟩ : Nonempty (Perm V) := ⟨Fintype.equivFin V⟩
  rw [coinProb_eq_condProb _ ω₀]
  have hsub : ∀ ω : Perm V, d ≤ (maxDegOn G (aliveSet G (rank ω) (t + 1)
      (Fintype.card V)) : ℝ) → ∃ u ∈ (Finset.univ : Finset V), degEv G t d u ω := by
    intro ω h
    set U := aliveSet G (rank ω) (t + 1) (Fintype.card V)
    have hne : U.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h0 : maxDegOn G U = 0 := by unfold maxDegOn; rw [hne]; rfl
      rw [h0] at h; simp at h; linarith
    obtain ⟨u, hu, hmax⟩ := Finset.exists_mem_eq_sup U hne
      (fun v => (U.filter (fun w => G.Adj v w)).card)
    refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [U, aliveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨hu.1, hu.2.2, ?_⟩
    have h1 : (maxDegOn G U : ℝ) = ((U.filter (fun w => G.Adj u w)).card : ℝ) := by
      unfold maxDegOn; rw [hmax]
    rw [h1] at h
    refine h.trans ?_
    exact_mod_cast Finset.card_le_card (by
      intro w hw
      simp only [U, aliveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact ⟨hw.2, hw.1.1, hw.1.2.2⟩)
  refine (condProb_mono hsub _ _).trans ((condProb_union_le _ _ _ _).trans ?_)
  have hb : ∀ u ∈ (Finset.univ : Finset V), condProb (degEv G t d u) ∅ ω₀ ≤
      Real.exp (-((t : ℝ) * d) / (Fintype.card V : ℝ)) := by
    intro u _
    have := degEv_bound G t ht.le d hd.le u t 0 (by omega) ω₀
    have e : Finset.Icc 1 0 = (∅ : Finset ℕ) := by simp
    rw [e] at this
    convert this using 2
    ring
  refine (Finset.sum_le_sum hb).trans ?_
  simp

theorem lemma_2_9_part2 (t : ℕ) (ht1 : 1 ≤ t) (ht : t < Fintype.card V) :
    1 - 1 / (Fintype.card V : ℝ) ^ 7 ≤
      PunctSketch.coinProb (fun ω : Perm V =>
        (maxDegOn G (aliveSet G (rank ω) (t + 1) (Fintype.card V)) : ℝ) ≤
          8 * (Fintype.card V : ℝ) * Real.log (Fintype.card V : ℝ) / (t : ℝ)) := by
  classical
  obtain ⟨ω₀⟩ : Nonempty (Perm V) := ⟨Fintype.equivFin V⟩
  have hn2 : 2 ≤ Fintype.card V := by omega
  have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn2
  have htR : (0 : ℝ) < t := by exact_mod_cast ht1
  have hlog : 0 < Real.log (Fintype.card V) := Real.log_pos (by linarith)
  have hdpos : 0 < 8 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) / t := by positivity
  have h1 := lemma_2_9_part1 G t ht1 ht _ hdpos
  have hval : (Fintype.card V : ℝ) * Real.exp (-((t : ℝ) *
      (8 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) / t)) / Fintype.card V) =
      1 / (Fintype.card V : ℝ) ^ 7 := by
    have : -((t : ℝ) * (8 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) / t)) /
        Fintype.card V = -8 * Real.log (Fintype.card V) := by
      field_simp
    rw [this, show (-8 : ℝ) * Real.log (Fintype.card V) =
        Real.log ((Fintype.card V : ℝ) ^ (-8 : ℤ)) by
      rw [Real.log_zpow]; push_cast; ring, Real.exp_log (by positivity)]
    rw [zpow_neg, zpow_ofNat]
    field_simp
  rw [hval] at h1
  rw [coinProb_eq_condProb _ ω₀] at h1 ⊢
  have h2 := condProb_mono (S := ∅) (ω := ω₀)
    (E := fun ω : Perm V => ¬ (8 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) / t ≤
      (maxDegOn G (aliveSet G (rank ω) (t + 1) (Fintype.card V)) : ℝ)))
    (F := fun ω : Perm V => (maxDegOn G (aliveSet G (rank ω) (t + 1) (Fintype.card V)) : ℝ) ≤
      8 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) / t)
    (fun ω h => by push Not at h; exact h.le)
  rw [condProb_compl] at h2
  linarith

end deg

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM
open QueryDepthMIS RGMISFast

section gmax

/-- `max_{D ≤ d} e^{-kD/n} D / n'` -/
noncomputable def gmax (n n' : ℝ) (k d : ℕ) : ℝ :=
  (Finset.range (d + 1)).sup' ⟨0, by simp⟩
    (fun D => Real.exp (-(k : ℝ) * D / n) * D / n')

lemma le_gmax (n n' : ℝ) (k : ℕ) {D d : ℕ} (hD : D ≤ d) :
    Real.exp (-(k : ℝ) * D / n) * D / n' ≤ gmax n n' k d :=
  Finset.le_sup' (fun D : ℕ => Real.exp (-(k : ℝ) * D / n) * D / n')
    (by simp; omega)

lemma gmax_mono (n n' : ℝ) (k : ℕ) {d d' : ℕ} (h : d ≤ d') : gmax n n' k d ≤ gmax n n' k d' := by
  unfold gmax
  apply Finset.sup'_le
  intro D hD
  apply le_gmax; simp at hD; omega

lemma exp_mul_gmax {n n' : ℝ} (hn : 0 < n) (hn' : 0 < n') (k d : ℕ) :
    Real.exp (-(d : ℝ) / n) * gmax n n' k d ≤ gmax n n' (k + 1) d := by
  obtain ⟨D, hD, hDe⟩ := Finset.exists_mem_eq_sup' ((⟨0, by simp⟩ : (Finset.range (d + 1)).Nonempty))
    (fun D : ℕ => Real.exp (-(k : ℝ) * D / n) * D / n')
  unfold gmax at *
  rw [hDe]
  have hDd : D ≤ d := by simp at hD; omega
  refine le_trans ?_ (le_gmax n n' (k + 1) hDd)
  have h1 : Real.exp (-(d : ℝ) / n) ≤ Real.exp (-(D : ℝ) / n) := by
    apply Real.exp_le_exp.2
    have : (D : ℝ) ≤ d := by exact_mod_cast hDd
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right this hn.le
  have h2 : 0 ≤ Real.exp (-(k : ℝ) * D / n) * D / n' := by positivity
  calc Real.exp (-(d : ℝ) / n) * (Real.exp (-(k : ℝ) * D / n) * D / n')
      ≤ Real.exp (-(D : ℝ) / n) * (Real.exp (-(k : ℝ) * D / n) * D / n') :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = Real.exp (-((k + 1 : ℕ) : ℝ) * D / n) * D / n' := by
        rw [mul_div_assoc', ← mul_assoc, ← Real.exp_add]
        congr 3; push_cast; ring

lemma mul_exp_neg_le (y : ℝ) : y * Real.exp (-y) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (y - 1)
  have hpos := Real.exp_pos (-y)
  calc y * Real.exp (-y) ≤ Real.exp (y - 1) * Real.exp (-y) := by
        apply mul_le_mul_of_nonneg_right _ hpos.le; linarith
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

lemma gmax_le {n n' : ℝ} (hn : 0 < n) (hn' : 0 < n') {k : ℕ} (hk : 1 ≤ k) (d : ℕ) :
    gmax n n' k d ≤ n / (Real.exp 1 * k * n') := by
  unfold gmax
  apply Finset.sup'_le
  intro D _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := mul_exp_neg_le ((k : ℝ) * D / n)
  rw [Real.exp_neg 1] at h
  have e : Real.exp (-(k : ℝ) * D / n) * D / n' =
      ((k : ℝ) * D / n * Real.exp (-((k : ℝ) * D / n))) * (n / (k * n')) := by
    field_simp
  rw [e]
  calc ((k : ℝ) * D / n * Real.exp (-((k : ℝ) * D / n))) * (n / (k * n'))
      ≤ (Real.exp 1)⁻¹ * (n / (k * n')) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = n / (Real.exp 1 * k * n') := by field_simp

end gmax

section hop
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma agreeLE_of_agree_sub {k : ℕ} {X : Finset ℕ} (hX : ∀ q, 1 ≤ q → q ≤ k → q ∈ X)
    {ω ω' : Perm V} (h : Agree X ω ω') : AgreeLE k ω ω' := by
  intro v hv
  exact h v (hX _ (rank_pos _ _) hv)

/-- active neighbours of `a` satisfying `Φ`: unexposed (w.r.t. `X`) neighbours alive at time `c` -/
def actSetΦ (Φ : V → Prop) [DecidablePred Φ] (ω : Perm V) (a : V) (X : Finset ℕ) (c : ℕ) :
    Finset V :=
  Finset.univ.filter (fun w => G.Adj a w ∧ Φ w ∧ rank ω w ∉ X ∧ c ≤ tau G (rank ω) w)

/-- active neighbours of `a`: unexposed (w.r.t. `X`) neighbours alive at time `c` -/
def actSet (ω : Perm V) (a : V) (X : Finset ℕ) (c : ℕ) : Finset V :=
  Finset.univ.filter (fun w => G.Adj a w ∧ rank ω w ∉ X ∧ c ≤ tau G (rank ω) w)

/-- the hop event with a target filter `Φ` -/
def hopEv (Φ : V → Prop) (P₁ : Finset ℕ) (p₁ p₂ : ℕ) (ω : Perm V) : Prop :=
  ∃ u v : V, rank ω u = p₁ ∧ rank ω v = p₂ ∧ G.Adj u v ∧ Φ v ∧
    P₁.sup id + 1 ≤ RGMISFast.tau G (rank ω) u ∧ P₁.sup id + 1 ≤ RGMISFast.tau G (rank ω) v

/-- the current time in the one-hop induction: the smallest remaining protected position,
or `max P₁ + 1` -/
def curT (t₁ : ℕ) (R : Finset ℕ) : ℕ := (insert (t₁ + 1) R).min' (Finset.insert_nonempty _ _)

lemma curT_le (t₁ : ℕ) (R : Finset ℕ) : curT t₁ R ≤ t₁ + 1 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

lemma curT_le_of_mem {t₁ : ℕ} {R : Finset ℕ} {q : ℕ} (hq : q ∈ R) : curT t₁ R ≤ q :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem hq)

lemma le_curT {t₁ : ℕ} {R : Finset ℕ} {c : ℕ} (h1 : c ≤ t₁ + 1) (h2 : ∀ q ∈ R, c ≤ q) :
    c ≤ curT t₁ R := by
  apply Finset.le_min'
  intro y hy
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact h1
  · exact h2 y hy

/-- Setting of the one-hop lemma. -/
structure HopSetting (P₁ S : Finset ℕ) (p₁ p₂ : ℕ) : Prop where
  hp₁S : p₁ ∈ S
  hdisj : Disjoint P₁ S
  hp₂S : p₂ ∉ S
  hp₂P : p₂ ∉ P₁
  hp₂n : 1 ≤ p₂ ∧ p₂ ≤ Fintype.card V
  hPn : ∀ q ∈ P₁, 1 ≤ q ∧ q ≤ Fintype.card V
  hfill : ∀ q, 1 ≤ q → q ≤ P₁.sup id → q ∉ P₁ → q ∈ S

lemma le_sup_id {P : Finset ℕ} {q : ℕ} (h : q ∈ P) : q ≤ P.sup id := Finset.le_sup (f := id) h

/-- positions before the current time are exposed -/
lemma exposed_before {P₁ S R : Finset ℕ} {p₁ p₂ : ℕ} (hs : HopSetting (V := V) P₁ S p₁ p₂)
    (hR : R ⊆ P₁) (hord : ∀ x ∈ P₁ \ R, ∀ y ∈ R, x < y) :
    ∀ q, 1 ≤ q → q ≤ curT (P₁.sup id) R - 1 → q ∈ S ∪ (P₁ \ R) := by
  intro q hq1 hq2
  have hc := curT_le (P₁.sup id) R
  by_cases hqP : q ∈ P₁
  · apply Finset.mem_union_right
    rw [Finset.mem_sdiff]
    refine ⟨hqP, fun hqR => ?_⟩
    have := curT_le_of_mem (t₁ := P₁.sup id) hqR
    omega
  · exact Finset.mem_union_left _ (hs.hfill q hq1 (by omega) hqP)

theorem hop_core (Φ : V → Prop) [DecidablePred Φ] {P₁ S : Finset ℕ} {p₁ p₂ : ℕ} (hs : HopSetting (V := V) P₁ S p₁ p₂)
    (a : V) (ω₀ : Perm V) (ha : rank ω₀ a = p₁) (n' : ℝ)
    (hn' : 0 < n') (hn'le : n' ≤ (Fintype.card V - nExp V (S ∪ P₁) : ℕ)) :
    ∀ k (R : Finset ℕ), R ⊆ P₁ → R.card = k → (∀ x ∈ P₁ \ R, ∀ y ∈ R, x < y) →
    ∀ ω ∈ cls S ω₀, condProb (hopEv G Φ P₁ p₁ p₂) (S ∪ (P₁ \ R)) ω ≤
      gmax (Fintype.card V) n' k (actSetΦ G Φ ω a (S ∪ (P₁ \ R)) (curT (P₁.sup id) R)).card := by
  classical
  have hnpos : (0 : ℝ) < Fintype.card V := by
    have := hs.hp₂n; have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  intro k
  induction k with
  | zero =>
    intro R hR hk hord ω hω
    have hR0 : R = ∅ := Finset.card_eq_zero.1 hk
    subst hR0
    simp only [Finset.sdiff_empty]
    have hc : curT (P₁.sup id) ∅ = P₁.sup id + 1 := by simp [curT]
    rw [hc]
    have ha' : rank ω a = p₁ := by rw [(mem_cls.1 hω) a (ha ▸ hs.hp₁S), ha]
    have hp₂X : p₂ ∉ S ∪ P₁ := by simp [hs.hp₂S, hs.hp₂P]
    have hstep := condProb_step_le (hopEv G Φ P₁ p₁ p₂) ω p₂ hs.hp₂n hp₂X
      (actSetΦ G Φ ω a (S ∪ P₁) (P₁.sup id + 1)) 1 zero_le_one ?_ ?_
    · refine hstep.trans ?_
      rw [mul_one]
      refine le_trans ?_ (le_gmax _ _ 0 le_rfl)
      simp only [CharP.cast_eq_zero, neg_zero, zero_mul, zero_div, Real.exp_zero, one_mul]
      have hU : ((unexp (S ∪ P₁) ω).card : ℝ) = ((Fintype.card V - nExp V (S ∪ P₁) : ℕ) : ℝ) := by
        rw [card_unexp]
      rw [hU]
      have h1 : ((actSetΦ G Φ ω a (S ∪ P₁) (P₁.sup id + 1) ∩ unexp (S ∪ P₁) ω).card : ℝ) ≤
          (actSetΦ G Φ ω a (S ∪ P₁) (P₁.sup id + 1)).card := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_left
      calc ((actSetΦ G Φ ω a (S ∪ P₁) (P₁.sup id + 1) ∩ unexp (S ∪ P₁) ω).card : ℝ) /
            ((Fintype.card V - nExp V (S ∪ P₁) : ℕ) : ℝ)
          ≤ (actSetΦ G Φ ω a (S ∪ P₁) (P₁.sup id + 1)).card / n' := by
            apply div_le_div₀ (by positivity) h1 hn' hn'le
        _ = _ := rfl
    · intro x hx hxB
      apply condProb_eq_zero
      intro ω' hω' hE
      obtain ⟨u, v, hu, hv, hadj, hΦ, hu1, hv1⟩ := hE
      have hag : Agree (insert p₂ (S ∪ P₁)) (put ω x p₂ hs.hp₂n) ω' := mem_cls.1 hω'
      have hxr : rank ω' x = p₂ := by
        rw [hag x (by rw [rank_put_self]; simp), rank_put_self]
      have hvx : v = x := rank_injective ω' (hv.trans hxr.symm)
      subst hvx
      have hag0 : Agree (S ∪ P₁) ω ω' :=
        (mem_cls.1 (put_mem_cls ω v p₂ hs.hp₂n hp₂X (by simpa [unexp] using hx))).trans
          (hag.mono (Finset.subset_insert _ _))
      have hua : u = a := by
        apply rank_injective ω'
        rw [hu, hag0 a (by rw [ha']; simp [hs.hp₁S]), ha']
      subst hua
      apply hxB
      simp only [actSetΦ, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hadj, hΦ, by simpa [unexp] using hx, ?_⟩
      have hle := agreeLE_of_agree_sub (k := P₁.sup id)
        (fun q hq1 hq2 => by
          by_cases hqP : q ∈ P₁
          · exact Finset.mem_union_right _ hqP
          · exact Finset.mem_union_left _ (hs.hfill q hq1 hq2 hqP)) hag0
      exact (le_tau_congr G hle v le_rfl).2 hv1
    · intro x _ _
      exact condProb_le_one _ _ _
  | succ k ih =>
    intro R hR hk hord ω hω
    have hRne : R.Nonempty := Finset.card_pos.1 (by omega)
    set q := R.min' hRne with hq
    have hqR : q ∈ R := Finset.min'_mem R hRne
    have hqP : q ∈ P₁ := hR hqR
    have hqn := hs.hPn q hqP
    have hqX : q ∉ S ∪ (P₁ \ R) := by
      simp only [Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not]
      exact ⟨Finset.disjoint_left.1 hs.hdisj hqP, fun _ => hqR⟩
    set R' := R.erase q with hR'
    have hins : insert q (S ∪ (P₁ \ R)) = S ∪ (P₁ \ R') := by
      ext y
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, hR', Finset.mem_erase]
      constructor
      · rintro (rfl | h | ⟨h1, h2⟩)
        · exact Or.inr ⟨hqP, fun h => h.1 rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, fun h => h2 h.2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inr (Or.inl h)
        · by_cases hyq : y = q
          · exact Or.inl hyq
          · exact Or.inr (Or.inr ⟨h1, fun h => h2 ⟨hyq, h⟩⟩)
    have hcur : curT (P₁.sup id) R = q := by
      apply le_antisymm (curT_le_of_mem hqR)
      apply le_curT
      · have := le_sup_id hqP; omega
      · intro y hy; exact Finset.min'_le R y hy
    have ha' : rank ω a = p₁ := by rw [(mem_cls.1 hω) a (ha ▸ hs.hp₁S), ha]
    obtain ⟨A, hA⟩ : ∃ A, A = actSetΦ G Φ ω a (S ∪ (P₁ \ R)) q := ⟨_, rfl⟩
    -- good set: everything except the active neighbours of `a`
    obtain ⟨B, hB⟩ : ∃ B : Finset V, B = Finset.univ.filter (fun x => x ∉ A) := ⟨_, rfl⟩
    have hstep := condProb_step_le (hopEv G Φ P₁ p₁ p₂) ω q hqn hqX B
      (gmax (Fintype.card V) n' k A.card) ?_ ?_ ?_
    · rw [hcur, ← hA]
      refine hstep.trans ?_
      have hAU : A ⊆ unexp (S ∪ (P₁ \ R)) ω := by
        intro w hw; simp only [hA, actSetΦ, Finset.mem_filter] at hw
        simp only [unexp, Finset.mem_filter, Finset.mem_univ, true_and]; exact hw.2.2.2.1
      have hBU : B ∩ unexp (S ∪ (P₁ \ R)) ω = unexp (S ∪ (P₁ \ R)) ω \ A := by
        ext w; rw [hB]; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_sdiff]; tauto
      rw [hBU, Finset.card_sdiff_of_subset hAU]
      have hm : 0 < (unexp (S ∪ (P₁ \ R)) ω).card :=
        Finset.card_pos.2 (unexp_nonempty_of ω q hqn hqX)
      have hmle : (unexp (S ∪ (P₁ \ R)) ω).card ≤ Fintype.card V := Finset.card_le_univ _
      have hAle := Finset.card_le_card hAU
      have hratio : (((unexp (S ∪ (P₁ \ R)) ω).card - A.card : ℕ) : ℝ) /
          ((unexp (S ∪ (P₁ \ R)) ω).card : ℝ) ≤ Real.exp (-(A.card : ℝ) / Fintype.card V) := by
        rw [Nat.cast_sub hAle]
        have hmR : (0 : ℝ) < (unexp (S ∪ (P₁ \ R)) ω).card := by exact_mod_cast hm
        have hmnR : ((unexp (S ∪ (P₁ \ R)) ω).card : ℝ) ≤ Fintype.card V := by exact_mod_cast hmle
        rw [sub_div, div_self hmR.ne']
        have h1 : (A.card : ℝ) / Fintype.card V ≤ (A.card : ℝ) / (unexp (S ∪ (P₁ \ R)) ω).card :=
          div_le_div_of_nonneg_left (by positivity) hmR hmnR
        have h2 := Real.add_one_le_exp (-(A.card : ℝ) / Fintype.card V)
        rw [neg_div] at h2 ⊢
        linarith
      have hg0 : 0 ≤ gmax (Fintype.card V) n' k A.card := by
        refine le_trans ?_ (le_gmax (Fintype.card V : ℝ) n' k (D := 0) (Nat.zero_le _))
        simp
      calc (((unexp (S ∪ (P₁ \ R)) ω).card - A.card : ℕ) : ℝ) /
            ((unexp (S ∪ (P₁ \ R)) ω).card : ℝ) * gmax (Fintype.card V) n' k A.card
          ≤ Real.exp (-(A.card : ℝ) / Fintype.card V) * gmax (Fintype.card V) n' k A.card :=
            mul_le_mul_of_nonneg_right hratio hg0
        _ ≤ gmax (Fintype.card V) n' (k + 1) A.card := exp_mul_gmax hnpos hn' k A.card
    · refine le_trans ?_ (le_gmax (Fintype.card V : ℝ) n' k (D := 0) (Nat.zero_le _))
      simp
    · -- placing an active neighbour kills `a`
      intro x hx hxB
      rw [hins]
      apply condProb_eq_zero
      intro ω' hω' hE
      obtain ⟨u, v, hu, hv, hadj, hΦ, hu1, hv1⟩ := hE
      have hxA : x ∈ A := by
        by_contra hc; apply hxB; rw [hB]; simp only [Finset.mem_filter, Finset.mem_univ,
          true_and]; exact hc
      rw [hA] at hxA
      simp only [actSetΦ, Finset.mem_filter, Finset.mem_univ, true_and] at hxA
      have hag : Agree (S ∪ (P₁ \ R')) (put ω x q hqn) ω' := mem_cls.1 hω'
      have hput := put_mem_cls ω x q hqn hqX (by simpa [unexp] using hx)
      have hag0 : Agree (S ∪ (P₁ \ R)) ω ω' :=
        (mem_cls.1 hput).trans (hag.mono (by rw [← hins]; exact Finset.subset_insert _ _))
      have hxr : rank ω' x = q := by
        rw [hag x (by rw [rank_put_self, ← hins]; simp), rank_put_self]
      have hua : u = a := by
        apply rank_injective ω'
        rw [hu, hag0 a (by rw [ha']; simp [hs.hp₁S]), ha']
      subst hua
      -- x is alive at time q in ω'
      have hle := agreeLE_of_agree_sub (k := q - 1) (fun y hy1 hy2 => by
        have := exposed_before hs hR hord y hy1 (by rw [hcur]; exact hy2)
        exact this) hag0
      have hxalive : q ≤ tau G (rank ω') x := by
        rw [← le_tau_congr G hle x (by omega)]; exact hxA.2.2.2
      rw [← hxr] at hxalive
      have := tau_le_of_adj_alive G (rank ω') u x hxA.1 hxalive
      have := le_sup_id hqP
      omega
    · -- surviving placements: induction hypothesis and monotonicity of the active set
      intro x hx _
      rw [hins]
      have hput := put_mem_cls ω x q hqn hqX (by simpa [unexp] using hx)
      have hputS : put ω x q hqn ∈ cls S ω₀ := by
        have h1 : cls (S ∪ (P₁ \ R)) ω ⊆ cls S ω₀ := by
          intro ω'' h''
          rw [mem_cls] at h'' ⊢
          exact (mem_cls.1 hω).trans (h''.mono Finset.subset_union_left)
        exact h1 hput
      have hR'sub : R' ⊆ P₁ := (Finset.erase_subset _ _).trans hR
      have hR'card : R'.card = k := by rw [hR', Finset.card_erase_of_mem hqR]; omega
      have hord' : ∀ x ∈ P₁ \ R', ∀ y ∈ R', x < y := by
        intro x' hx' y hy
        simp only [hR', Finset.mem_sdiff, Finset.mem_erase, not_and] at hx' hy
        by_cases hx'q : x' = q
        · subst hx'q
          exact lt_of_le_of_ne (Finset.min'_le R y hy.2) (fun h => hy.1 h.symm)
        · exact hord x' (by simp [hx'.1]; exact fun h => hx'.2 hx'q h) y hy.2
      refine (ih R' hR'sub hR'card hord' _ hputS).trans (gmax_mono _ _ _ ?_)
      rw [hA]
      -- active set shrinks
      apply Finset.card_le_card
      intro w hw
      simp only [actSetΦ, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      have hagq : Agree (S ∪ (P₁ \ R)) ω (put ω x q hqn) := mem_cls.1 hput
      refine ⟨hw.1, hw.2.1, ?_, ?_⟩
      · intro hmem
        apply hw.2.2.1
        rw [← hins]
        exact Finset.mem_insert_of_mem ((hagq.mem_iff w).2 hmem)
      · have hcq : q + 1 ≤ curT (P₁.sup id) R' := by
          apply le_curT
          · have := le_sup_id hqP; omega
          · intro y hy
            simp only [hR', Finset.mem_erase] at hy
            exact lt_of_le_of_ne (Finset.min'_le R y hy.2) (fun h => hy.1 h.symm)
        have hle := agreeLE_of_agree_sub (k := q - 1) (fun y hy1 hy2 => by
          exact exposed_before hs hR hord y hy1 (by rw [hcur]; exact hy2)) hagq
        rw [le_tau_congr G hle w (by omega)]
        omega

lemma nExp_le_floor (X : Finset ℕ) (β : ℝ) (hβ : 0 ≤ β)
    (h : ∀ q ∈ X, (q : ℝ) ≤ β * Fintype.card V) :
    (nExp V X : ℝ) ≤ β * Fintype.card V := by
  have hsub : X.filter (fun p => 1 ≤ p ∧ p ≤ Fintype.card V) ⊆
      Finset.Icc 1 ⌊β * Fintype.card V⌋₊ := by
    intro q hq
    simp only [Finset.mem_filter] at hq
    simp only [Finset.mem_Icc]
    exact ⟨hq.2.1, Nat.le_floor (h q hq.1)⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  calc (nExp V X : ℝ) ≤ (⌊β * Fintype.card V⌋₊ : ℝ) := by exact_mod_cast this
    _ ≤ β * Fintype.card V := Nat.floor_le (by positivity)

lemma nExp_le_card (V : Type*) [Fintype V] (X : Finset ℕ) : nExp V X ≤ Fintype.card V := by
  unfold nExp
  calc (X.filter (fun p => 1 ≤ p ∧ p ≤ Fintype.card V)).card ≤ (Finset.Icc 1 (Fintype.card V)).card :=
        Finset.card_le_card (by intro q hq; simp at hq ⊢; omega)
    _ = Fintype.card V := by simp

theorem lemma_3_2_proof (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 0.1)
    (hn2 : 2 ≤ Fintype.card V) (P₁ : Finset ℕ) (hP₁ : P₁.Nonempty) (p₁ p₂ : ℕ)
    (hP₁p₁ : ∀ x ∈ P₁, x < p₁) (hp₁₂ : p₁ < p₂) (hp₂β : (p₂ : ℝ) < β * (Fintype.card V : ℝ))
    (S : Finset ℕ) (hSβ : ∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) ≤ β * (Fintype.card V : ℝ))
    (hp₁S : p₁ ∈ S) (hfill : ∀ q, 1 ≤ q → q ≤ P₁.sup id → q ∉ P₁ → q ∈ S)
    (hSP : ∀ q ∈ S, q ∉ P₁ ∧ q ≠ p₂) (hP₁pos : ∀ x ∈ P₁, 1 ≤ x) (ω₀ : Perm V) :
    condProb (oneHopEvent G P₁ p₁ p₂) S ω₀ ≤
      1 / (Real.exp 1 * (P₁.card : ℝ) * (1 - β)) := by
  have hnR : (0 : ℝ) < Fintype.card V := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  have hp₁1 := (hSβ p₁ hp₁S).1
  have hp₂n : (p₂ : ℝ) ≤ Fintype.card V := by nlinarith
  have hp₂n' : p₂ ≤ Fintype.card V := by exact_mod_cast hp₂n
  have hs : HopSetting (V := V) P₁ S p₁ p₂ :=
    { hp₁S := hp₁S
      hdisj := Finset.disjoint_left.2 (fun x hx hxS => (hSP x hxS).1 hx)
      hp₂S := fun h => (hSP p₂ h).2 rfl
      hp₂P := fun h => by have := hP₁p₁ p₂ h; omega
      hp₂n := ⟨by omega, hp₂n'⟩
      hPn := fun q hq => ⟨hP₁pos q hq, by have := hP₁p₁ q hq; omega⟩
      hfill := hfill }
  obtain ⟨a, ha⟩ := exists_rank_eq ω₀ p₁ hp₁1 (by omega)
  have hn'pos : 0 < (1 - β) * Fintype.card V := by
    apply mul_pos (by norm_num at hβ1 ⊢; linarith) hnR
  have hn'le : (1 - β) * Fintype.card V ≤ ((Fintype.card V - nExp V (S ∪ P₁) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (nExp_le_card V _)]
    have := nExp_le_floor (V := V) (S ∪ P₁) β hβ0.le (by
      intro q hq
      rcases Finset.mem_union.1 hq with hq | hq
      · exact (hSβ q hq).2
      · have := hP₁p₁ q hq
        have h2 : (q : ℝ) < p₁ := by exact_mod_cast this
        have h3 := (hSβ p₁ hp₁S).2
        linarith)
    linarith
  have h := hop_core G (fun _ => True) hs a ω₀ ha ((1 - β) * Fintype.card V) hn'pos hn'le
    P₁.card P₁ le_rfl rfl (by simp) ω₀ (self_mem_cls _ _)
  rw [Finset.sdiff_self, Finset.union_empty] at h
  have hmono : condProb (oneHopEvent G P₁ p₁ p₂) S ω₀ ≤
      condProb (hopEv G (fun _ => True) P₁ p₁ p₂) S ω₀ :=
    condProb_mono (fun ω ⟨u, v, h1, h2, h3, h4, h5⟩ => ⟨u, v, h1, h2, h3, trivial, h4, h5⟩) _ _
  refine hmono.trans ?_
  refine h.trans ((gmax_le hnR hn'pos (Finset.card_pos.2 hP₁) _).trans (le_of_eq ?_))
  field_simp

end hop

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM
open QueryDepthMIS RGMISFast

section stage
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- exposed set after `j` stages of the sorted list `L` -/
def stX (S : Finset ℕ) (L : List ℕ) (j : ℕ) : Finset ℕ := S ∪ (L.take j).toFinset

lemma stX_zero (S : Finset ℕ) (L : List ℕ) : stX S L 0 = S := by simp [stX]

lemma stX_mono (S : Finset ℕ) (L : List ℕ) {i j : ℕ} (h : i ≤ j) : stX S L i ⊆ stX S L j := by
  intro q hq
  simp only [stX, Finset.mem_union, List.mem_toFinset] at hq ⊢
  rcases hq with hq | hq
  · exact Or.inl hq
  · exact Or.inr ((List.take_subset_take_left L h) hq)

lemma stX_succ (S : Finset ℕ) (L : List ℕ) (j : ℕ) (hj : j < L.length) :
    insert (L[j]) (stX S L j) = stX S L (j + 1) := by
  ext q
  simp only [stX, Finset.mem_insert, Finset.mem_union, List.mem_toFinset]
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, List.mem_append, List.mem_singleton]
  tauto

/-- The generic potential bound along a list of exposures. -/
theorem condProb_le_potential (E : Perm V → Prop) (S : Finset ℕ) (L : List ℕ)
    (hLv : ∀ q ∈ L, 1 ≤ q ∧ q ≤ Fintype.card V)
    (hLnew : ∀ j (hj : j < L.length), L[j] ∉ stX S L j)
    (Ω : Finset (Perm V)) (hΩ : ∀ j (hj : j < L.length), ∀ ω ∈ Ω, ∀ x ∈ unexp (stX S L j) ω,
      put ω x L[j] (hLv _ (List.getElem_mem hj)) ∈ Ω)
    (good : ℕ → Perm V → Finset V) (H : ℕ → Perm V → ℝ)
    (hterm : ∀ ω ∈ Ω, condProb E (stX S L L.length) ω ≤ H L.length ω)
    (hbad : ∀ j (hj : j < L.length), ∀ ω ∈ Ω, ∀ x ∈ unexp (stX S L j) ω, x ∉ good j ω →
      condProb E (stX S L (j + 1)) (put ω x L[j] (hLv _ (List.getElem_mem hj))) = 0)
    (hsuper : ∀ j (hj : j < L.length), ∀ ω ∈ Ω,
      (∑ x ∈ unexp (stX S L j) ω ∩ good j ω,
          H (j + 1) (put ω x L[j] (hLv _ (List.getElem_mem hj)))) /
        ((unexp (stX S L j) ω).card : ℝ) ≤ H j ω) :
    ∀ ω ∈ Ω, condProb E S ω ≤ H 0 ω := by
  classical
  -- downward induction on the stage
  have key : ∀ k, ∀ j, j + k = L.length → ∀ ω ∈ Ω, condProb E (stX S L j) ω ≤ H j ω := by
    intro k
    induction k with
    | zero => intro j hj ω hω; rw [show j = L.length by omega]; exact hterm ω hω
    | succ k ih =>
      intro j hjk ω hω
      have hj : j < L.length := by omega
      have hp := hLv _ (List.getElem_mem hj)
      rw [condProb_step E ω L[j] hp (hLnew j hj), stX_succ S L j hj]
      refine le_trans ?_ (hsuper j hj ω hω)
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [← Finset.sum_filter_add_sum_filter_not (unexp (stX S L j) ω) (fun x => x ∈ good j ω)]
      have h0 : ∑ x ∈ (unexp (stX S L j) ω).filter (fun x => x ∉ good j ω),
          condProb E (stX S L (j + 1)) (put ω x L[j] hp) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Finset.mem_filter] at hx
        exact hbad j hj ω hω x hx.1 hx.2
      rw [h0, add_zero, Finset.filter_mem_eq_inter]
      apply Finset.sum_le_sum
      intro x hx
      exact ih (j + 1) (by omega) _ (hΩ j hj ω hω x (Finset.mem_inter.1 hx).1)
  have := key L.length 0 (by omega)
  simpa [stX_zero] using this

end stage

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM
open QueryDepthMIS RGMISFast

section twohop
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Setting of the two-hop lemma. -/
structure THS (P₁ P₂ S : Finset ℕ) (p₁ p₂ p₃ : ℕ) : Prop where
  hp₁S : p₁ ∈ S
  hP₁S : Disjoint P₁ S
  hP₂S : Disjoint P₂ S
  hP₁₂ : ∀ x ∈ P₁, ∀ y ∈ P₂, x < y
  hP₁p₁ : ∀ x ∈ P₁, x < p₁
  hP₂p₁ : ∀ y ∈ P₂, y < p₁
  hp₁₂ : p₁ < p₂
  hp₂₃ : p₂ < p₃
  hp₂S : p₂ ∉ S
  hp₃S : p₃ ∉ S
  hp₃n : p₃ ≤ Fintype.card V
  hPpos : ∀ q ∈ P₁ ∪ P₂, 1 ≤ q
  hfill : ∀ q, 1 ≤ q → q ≤ P₂.sup id → q ∉ P₁ → q ∉ P₂ → q ∈ S
  hP₁ne : P₁.Nonempty
  hP₂ne : P₂.Nonempty

lemma condProb_mono_cls {V : Type*} [Fintype V] [DecidableEq V] {E F : Perm V → Prop}
    (S : Finset ℕ) (ω₀ : Perm V) (hEF : ∀ ω ∈ cls S ω₀, E ω → F ω) :
    condProb E S ω₀ ≤ condProb F S ω₀ := by
  classical
  rw [condProb_eq, condProb_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun ω hω => by
    simp only [Finset.mem_filter] at hω ⊢; exact ⟨hω.1, hEF _ hω.1 hω.2⟩)

variable {P₁ P₂ S : Finset ℕ} {p₁ p₂ p₃ : ℕ}

lemma THS.p₂n (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) : 1 ≤ p₂ ∧ p₂ ≤ Fintype.card V := by
  have := hs.hp₁₂; have := hs.hp₂₃; have := hs.hp₃n; constructor <;> omega

lemma THS.t₁_lt (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) : ∀ y ∈ P₂, P₁.sup id < y := by
  intro y hy
  have : P₁.sup id ∈ P₁ ∨ P₁.sup id = 0 := by
    obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup P₁ hs.hP₁ne id
    exact Or.inl (by rw [hxe]; exact hx)
  rcases this with h | h
  · exact hs.hP₁₂ _ h y hy
  · have := hs.hPpos y (Finset.mem_union_right _ hy); omega

lemma THS.fill₁ (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) :
    ∀ q, 1 ≤ q → q ≤ P₁.sup id → q ∉ P₁ → q ∈ S := by
  intro q hq1 hq2 hq3
  obtain ⟨y, hy⟩ := hs.hP₂ne
  have := hs.t₁_lt y hy
  apply hs.hfill q hq1 (le_trans (by omega) (le_sup_id hy)) hq3
  intro hq; have := hs.t₁_lt q hq; omega

/-- Phase 2: after `b` is placed at `p₂`, the rest is a restricted one-hop event. -/
theorem phase2_bound (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) (ω : Perm V)
    (ha : rank ω a = p₁) (n' : ℝ) (hn' : 0 < n')
    (hn'le : n' ≤ (Fintype.card V - nExp V (insert p₂ (S ∪ P₁) ∪ P₂) : ℕ))
    (b : V) (hb : b ∈ unexp (S ∪ P₁) ω) :
    condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃) (insert p₂ (S ∪ P₁)) (put ω b p₂ hs.p₂n) ≤
      gmax (Fintype.card V) n' P₂.card
        (actSetΦ G (fun w => ¬ G.Adj a w) ω b (S ∪ P₁) (P₁.sup id + 1)).card := by
  classical
  set ω₂ := put ω b p₂ hs.p₂n with hω₂
  have hp₂X : p₂ ∉ S ∪ P₁ := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hs.hp₂S, fun h => by have := hs.hP₁p₁ p₂ h; have := hs.hp₁₂; omega⟩
  have hbX : rank ω b ∉ S ∪ P₁ := by simpa [unexp] using hb
  have hω₂cls : ω₂ ∈ cls (S ∪ P₁) ω := put_mem_cls ω b p₂ hs.p₂n hp₂X hbX
  have hb₂ : rank ω₂ b = p₂ := rank_put_self ω b p₂ hs.p₂n
  have ha₂ : rank ω₂ a = p₁ := by
    rw [(mem_cls.1 hω₂cls) a (by rw [ha]; simp [hs.hp₁S]), ha]
  have hset : HopSetting (V := V) P₂ (insert p₂ (S ∪ P₁)) p₂ p₃ :=
    { hp₁S := Finset.mem_insert_self _ _
      hdisj := by
        rw [Finset.disjoint_left]
        intro y hy hyX
        simp only [Finset.mem_insert, Finset.mem_union] at hyX
        rcases hyX with h | h | h
        · have := hs.hP₂p₁ y hy; have := hs.hp₁₂; omega
        · exact Finset.disjoint_left.1 hs.hP₂S hy h
        · have := hs.hP₁₂ y h y hy; omega
      hp₂S := by
        simp only [Finset.mem_insert, Finset.mem_union, not_or]
        refine ⟨by have := hs.hp₂₃; omega, hs.hp₃S, fun h => ?_⟩
        have := hs.hP₁p₁ p₃ h; have := hs.hp₁₂; have := hs.hp₂₃; omega
      hp₂P := fun h => by have := hs.hP₂p₁ p₃ h; have := hs.hp₁₂; have := hs.hp₂₃; omega
      hp₂n := ⟨by have := hs.hp₁₂; have := hs.hp₂₃; omega, hs.hp₃n⟩
      hPn := fun q hq => ⟨hs.hPpos q (Finset.mem_union_right _ hq),
        by have := hs.hP₂p₁ q hq; have := hs.hp₁₂; have := hs.hp₂₃; have := hs.hp₃n; omega⟩
      hfill := by
        intro q hq1 hq2 hq3
        by_cases hqP : q ∈ P₁
        · simp [hqP]
        · simp [hs.hfill q hq1 hq2 hqP hq3] }
  have hcore := hop_core G (fun w => ¬ G.Adj a w) hset b ω₂ hb₂ n' hn' hn'le P₂.card P₂
    le_rfl rfl (by simp) ω₂ (self_mem_cls _ _)
  rw [Finset.sdiff_self, Finset.union_empty] at hcore
  have hmono : condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃) (insert p₂ (S ∪ P₁)) ω₂ ≤
      condProb (hopEv G (fun w => ¬ G.Adj a w) P₂ p₂ p₃) (insert p₂ (S ∪ P₁)) ω₂ := by
    apply condProb_mono_cls
    intro ω' hω' hE
    obtain ⟨u, v, w, hu, hv, hw, hind, hu1, hv1, hw1⟩ := hE
    have hua : u = a := by
      apply rank_injective ω'
      rw [hu, (mem_cls.1 hω') a (by rw [ha₂]; simp [hs.hp₁S]), ha₂]
    subst hua
    refine ⟨v, w, hv, hw, ?_, ?_, hv1, hw1⟩
    · exact (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hind.1).2).1
    · have := hind.2 0 2 (by simp) (by simp) (by norm_num) (by norm_num)
      simpa using this
  refine hmono.trans (hcore.trans (gmax_mono _ _ _ (Finset.card_le_card ?_)))
  -- the restricted active set at the start of phase 2 is contained in the one at time t₁+1
  intro w hw
  simp only [actSetΦ, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  refine ⟨hw.1, hw.2.1, fun h => hw.2.2.1 (Finset.mem_insert_of_mem
    (((mem_cls.1 hω₂cls).mem_iff w).2 h)), ?_⟩
  have hcur : P₁.sup id + 1 ≤ curT (P₂.sup id) P₂ := by
    apply le_curT
    · obtain ⟨y, hy⟩ := hs.hP₂ne; have := hs.t₁_lt y hy; have := le_sup_id hy; omega
    · intro y hy; exact hs.t₁_lt y hy
  have hle := agreeLE_of_agree_sub (k := P₁.sup id) (X := S ∪ P₁) (fun q hq1 hq2 => by
    by_cases hqP : q ∈ P₁
    · exact Finset.mem_union_right _ hqP
    · exact Finset.mem_union_left _ (hs.fill₁ q hq1 hq2 hqP)) (mem_cls.1 hω₂cls)
  rw [le_tau_congr G hle w le_rfl]
  omega

/-- End of phase 1: expose `p₂`. -/
theorem phase1_end (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) (ω : Perm V)
    (ha : rank ω a = p₁) (n' : ℝ) (hn' : 0 < n')
    (hn'le : n' ≤ (Fintype.card V - nExp V (insert p₂ (S ∪ P₁) ∪ P₂) : ℕ)) :
    condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃) (S ∪ P₁) ω ≤
      (∑ b ∈ actSet G ω a (S ∪ P₁) (P₁.sup id + 1),
        gmax (Fintype.card V) n' P₂.card
          (actSetΦ G (fun w => ¬ G.Adj a w) ω b (S ∪ P₁) (P₁.sup id + 1)).card) /
        ((unexp (S ∪ P₁) ω).card : ℝ) := by
  classical
  have hp₂X : p₂ ∉ S ∪ P₁ := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hs.hp₂S, fun h => by have := hs.hP₁p₁ p₂ h; have := hs.hp₁₂; omega⟩
  rw [condProb_step _ ω p₂ hs.p₂n hp₂X]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsub : actSet G ω a (S ∪ P₁) (P₁.sup id + 1) ⊆ unexp (S ∪ P₁) ω := by
    intro w hw; simp only [actSet, Finset.mem_filter] at hw
    simp only [unexp, Finset.mem_filter, Finset.mem_univ, true_and]; exact hw.2.2.1
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_le_sum
    intro b hb
    exact phase2_bound G hs a ω ha n' hn' hn'le b (hsub hb)
  · intro b hbU hbA
    apply condProb_eq_zero
    intro ω' hω' hE
    obtain ⟨u, v, w, hu, hv, hw, hind, hu1, hv1, hw1⟩ := hE
    have hbX : rank ω b ∉ S ∪ P₁ := by simpa [unexp] using hbU
    have hput := put_mem_cls ω b p₂ hs.p₂n hp₂X hbX
    have hag : Agree (insert p₂ (S ∪ P₁)) (put ω b p₂ hs.p₂n) ω' := mem_cls.1 hω'
    have hag0 : Agree (S ∪ P₁) ω ω' :=
      (mem_cls.1 hput).trans (hag.mono (Finset.subset_insert _ _))
    have hbr : rank ω' b = p₂ := by
      rw [hag b (by rw [rank_put_self]; simp), rank_put_self]
    have hvb : v = b := rank_injective ω' (hv.trans hbr.symm)
    have hua : u = a := by
      apply rank_injective ω'
      rw [hu, hag0 a (by rw [ha]; simp [hs.hp₁S]), ha]
    subst hvb hua
    apply hbA
    simp only [actSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(List.isChain_cons_cons.1 hind.1).1, hbX, ?_⟩
    have hle := agreeLE_of_agree_sub (k := P₁.sup id) (X := S ∪ P₁) (fun q hq1 hq2 => by
      by_cases hqP : q ∈ P₁
      · exact Finset.mem_union_right _ hqP
      · exact Finset.mem_union_left _ (hs.fill₁ q hq1 hq2 hqP)) hag0
    rw [le_tau_congr G hle v le_rfl]
    have : P₁.sup id ≤ P₂.sup id := by
      obtain ⟨y, hy⟩ := hs.hP₂ne; have := hs.t₁_lt y hy; have := le_sup_id hy; omega
    omega

end twohop

section sortedfacts

lemma sorted_mem_take_of_lt {L : List ℕ} (hL : L.SortedLT) {q : ℕ} (hq : q ∈ L) {j : ℕ}
    (hj : j < L.length) (hlt : q < L[j]) : q ∈ L.take j := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
  have hij : i < j := by
    by_contra h; push Not at h
    have := (hL.getElem_le_getElem_iff (hi := hj) (hj := hi)).2 h
    omega
  rw [List.mem_iff_getElem]
  refine ⟨i, by simp; omega, ?_⟩
  simp

lemma sorted_lt_of_mem_take {L : List ℕ} (hL : L.SortedLT) {q : ℕ} {j : ℕ} (hj : j < L.length)
    (hq : q ∈ L.take j) : q < L[j] := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
  simp only [List.length_take] at hi
  simp only [List.getElem_take]
  exact hL.getElem_lt_getElem_of_lt (by omega)

lemma sorted_getElem_not_mem_take {L : List ℕ} (hL : L.SortedLT) {j : ℕ} (hj : j < L.length) :
    L[j] ∉ L.take j := fun h => lt_irrefl _ (sorted_lt_of_mem_take hL hj h)

end sortedfacts

section phase1
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- current time at stage `j` of phase 1 -/
def curJ (P₁ : Finset ℕ) (j : ℕ) : ℕ := (P₁.sort).getD j (P₁.sup id + 1)

/-- active neighbours of `a` at stage `j` -/
def AJ (P₁ S : Finset ℕ) (a : V) (j : ℕ) (ω : Perm V) : Finset V :=
  actSet G ω a (stX S P₁.sort j) (curJ P₁ j)

/-- active distance-two neighbours of `u` (not adjacent to `a`) at stage `j` -/
def N2J (P₁ S : Finset ℕ) (a : V) (j : ℕ) (u : V) (ω : Perm V) : Finset V :=
  actSetΦ G (fun w => ¬ G.Adj a w) ω u (stX S P₁.sort j) (curJ P₁ j)

/-- candidates at stage `j` with threshold `θℓ` -/
noncomputable def candJ (P₁ S : Finset ℕ) (a : V) (θℓ : ℝ) (j : ℕ) (ω : Perm V) : Finset V :=
  (AJ G P₁ S a j ω).filter (fun u => θℓ ≤ ((N2J G P₁ S a j u ω).card : ℝ))

variable {P₁ P₂ S : Finset ℕ} {p₁ p₂ p₃ : ℕ}

lemma curJ_lt (P₁ : Finset ℕ) {j : ℕ} (hj : j < P₁.card) :
    curJ P₁ j = (P₁.sort)[j]'(by rw [Finset.length_sort]; exact hj) := by
  unfold curJ
  rw [List.getD_eq_getElem]

lemma curJ_card (P₁ : Finset ℕ) : curJ P₁ P₁.card = P₁.sup id + 1 := by
  unfold curJ
  rw [List.getD_eq_default]
  rw [Finset.length_sort]

lemma curJ_le (P₁ : Finset ℕ) (j : ℕ) (hj : j ≤ P₁.card) : curJ P₁ j ≤ P₁.sup id + 1 := by
  rcases Nat.lt_or_ge j P₁.card with h | h
  · rw [curJ_lt P₁ h]
    have : (P₁.sort)[j]'(by rw [Finset.length_sort]; exact h) ∈ P₁ := by
      rw [← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem _
    have := le_sup_id this; omega
  · rw [show j = P₁.card by omega, curJ_card]

lemma curJ_mono (P₁ : Finset ℕ) {j : ℕ} (hj : j < P₁.card) : curJ P₁ j < curJ P₁ (j + 1) := by
  rw [curJ_lt P₁ hj]
  rcases Nat.lt_or_ge (j + 1) P₁.card with h | h
  · rw [curJ_lt P₁ h]
    exact (Finset.sortedLT_sort P₁).getElem_lt_getElem_of_lt (by omega)
  · rw [show j + 1 = P₁.card by omega, curJ_card]
    have : (P₁.sort)[j]'(by rw [Finset.length_sort]; exact hj) ∈ P₁ := by
      rw [← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem _
    have := le_sup_id this; omega

lemma curJ_mono' (P₁ : Finset ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P₁.card) :
    curJ P₁ i ≤ curJ P₁ j := by
  induction j with
  | zero => rw [show i = 0 by omega]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact (ih (by omega) (by omega)).trans (curJ_mono P₁ (by omega)).le

/-- all positions before the current time are exposed -/
lemma exposed_before_J (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) {j : ℕ} (hj : j ≤ P₁.card) :
    ∀ q, 1 ≤ q → q ≤ curJ P₁ j - 1 → q ∈ stX S P₁.sort j := by
  intro q hq1 hq2
  have hc := curJ_le P₁ j hj
  by_cases hqP : q ∈ P₁
  · simp only [stX, Finset.mem_union, List.mem_toFinset]
    right
    rcases Nat.lt_or_ge j P₁.card with h | h
    · rw [curJ_lt P₁ h] at hq2
      have hpos : 1 ≤ (P₁.sort)[j]'(by rw [Finset.length_sort]; exact h) := by
        apply hs.hPpos; apply Finset.mem_union_left
        rw [← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem _
      exact sorted_mem_take_of_lt (Finset.sortedLT_sort P₁) ((Finset.mem_sort _).2 hqP)
        (by rw [Finset.length_sort]; exact h) (by omega)
    · rw [show j = P₁.card by omega, ← Finset.length_sort (· ≤ ·), List.take_length]
      exact (Finset.mem_sort _).2 hqP
  · exact Finset.mem_union_left _ (hs.fill₁ q hq1 (by omega) hqP)

lemma stX_card (S P₁ : Finset ℕ) : stX S P₁.sort P₁.card = S ∪ P₁ := by
  unfold stX
  have : P₁.sort.take P₁.card = P₁.sort := by
    rw [List.take_of_length_le]; rw [Finset.length_sort]
  rw [this, Finset.sort_toFinset]

lemma sortJ_not_mem (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) {j : ℕ} (hj : j < P₁.sort.length) :
    (P₁.sort)[j] ∉ stX S P₁.sort j := by
  simp only [stX, Finset.mem_union, List.mem_toFinset, not_or]
  constructor
  · exact Finset.disjoint_left.1 hs.hP₁S ((Finset.mem_sort _).1 (List.getElem_mem _))
  · exact sorted_getElem_not_mem_take (Finset.sortedLT_sort P₁) hj

lemma sortJ_valid (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) :
    ∀ q ∈ P₁.sort, 1 ≤ q ∧ q ≤ Fintype.card V := by
  intro q hq
  rw [Finset.mem_sort] at hq
  exact ⟨hs.hPpos q (Finset.mem_union_left _ hq), by
    have := hs.hP₁p₁ q hq; have := hs.hp₁₂; have := hs.hp₂₃; have := hs.hp₃n; omega⟩

/-- invariance of active sets under the class of the exposed positions -/
lemma actSetΦ_congr (Φ : V → Prop) [DecidablePred Φ] {X : Finset ℕ} {c : ℕ}
    (hX : ∀ q, 1 ≤ q → q ≤ c - 1 → q ∈ X) {ω ω' : Perm V} (h : ω' ∈ cls X ω) (u : V) :
    actSetΦ G Φ ω' u X c = actSetΦ G Φ ω u X c := by
  ext w
  simp only [actSetΦ, Finset.mem_filter, Finset.mem_univ, true_and]
  have hle := agreeLE_of_agree_sub hX (mem_cls.1 h)
  rw [(mem_cls.1 h).mem_iff w, le_tau_congr G hle w (by omega)]

lemma actSet_congr {X : Finset ℕ} {c : ℕ}
    (hX : ∀ q, 1 ≤ q → q ≤ c - 1 → q ∈ X) {ω ω' : Perm V} (h : ω' ∈ cls X ω) (u : V) :
    actSet G ω' u X c = actSet G ω u X c := by
  ext w
  simp only [actSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hle := agreeLE_of_agree_sub hX (mem_cls.1 h)
  rw [(mem_cls.1 h).mem_iff w, le_tau_congr G hle w (by omega)]

/-- monotonicity of active sets: later stage, later class member -/
lemma actSetΦ_anti (Φ : V → Prop) [DecidablePred Φ] {X X' : Finset ℕ} {c c' : ℕ}
    (hXX : X ⊆ X') (hcc : c ≤ c') (hX : ∀ q, 1 ≤ q → q ≤ c - 1 → q ∈ X)
    {ω ω' : Perm V} (h : ω' ∈ cls X ω) (u : V) :
    actSetΦ G Φ ω' u X' c' ⊆ actSetΦ G Φ ω u X c := by
  intro w hw
  simp only [actSetΦ, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  have hle := agreeLE_of_agree_sub hX (mem_cls.1 h)
  refine ⟨hw.1, hw.2.1, fun hm => hw.2.2.1 (hXX (((mem_cls.1 h).mem_iff w).2 hm)), ?_⟩
  rw [le_tau_congr G hle w (by omega)]
  omega

lemma actSet_anti {X X' : Finset ℕ} {c c' : ℕ}
    (hXX : X ⊆ X') (hcc : c ≤ c') (hX : ∀ q, 1 ≤ q → q ≤ c - 1 → q ∈ X)
    {ω ω' : Perm V} (h : ω' ∈ cls X ω) (u : V) :
    actSet G ω' u X' c' ⊆ actSet G ω u X c := by
  intro w hw
  simp only [actSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  have hle := agreeLE_of_agree_sub hX (mem_cls.1 h)
  refine ⟨hw.1, fun hm => hw.2.1 (hXX (((mem_cls.1 h).mem_iff w).2 hm)), ?_⟩
  rw [le_tau_congr G hle w (by omega)]
  omega

end phase1

section numerics

lemma exp_tenth_le : Real.exp (1/10) ≤ 83/75 := by
  by_contra h
  push Not at h
  have h1 : (83/75 : ℝ)^10 < (Real.exp (1/10))^10 := by
    apply pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at h1
  norm_num at h1
  have := Real.exp_one_lt_d9
  linarith

lemma exp_half_le : Real.exp (1/2) ≤ 5/3 := by
  by_contra h
  push Not at h
  have h1 : (5/3 : ℝ)^2 < (Real.exp (1/2))^2 := by
    apply pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at h1
  norm_num at h1
  have := Real.exp_one_lt_d9
  linarith

lemma exp_3_25_ge : (28/25 : ℝ) ≤ Real.exp (3/25) := by
  have h := Real.add_one_le_exp (3/50)
  have h2 : Real.exp (3/25) = Real.exp (3/50) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  nlinarith [Real.exp_pos (3/50)]

lemma exp_9_20_ge : (3/2 : ℝ) ≤ Real.exp (9/20) := by
  have h := Real.add_one_le_exp (9/160)
  have h2 : Real.exp (9/20) = Real.exp (9/160) ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  have h3 : (1 + 9/160 : ℝ) ^ 8 ≤ Real.exp (9/160) ^ 8 := by
    apply pow_le_pow_left₀ (by norm_num); linarith
  have h4 : (3/2 : ℝ) ≤ (1 + 9/160) ^ 8 := by norm_num
  linarith

/-- `y e^{-y}` is increasing on `[0, μ]` for `μ ≤ 1` -/
lemma mul_exp_neg_le_of_le {y μ : ℝ} (hy : 0 ≤ y) (hyμ : y ≤ μ) (hμ : μ ≤ 1) :
    y * Real.exp (-y) ≤ μ * Real.exp (-μ) := by
  have hμ0 : 0 ≤ μ := hy.trans hyμ
  rcases eq_or_lt_of_le hμ0 with h0 | hpos
  · subst h0; have : y = 0 := le_antisymm hyμ hy; subst this; simp
  have h1 : y ≤ μ * (1 + (y - μ)) := by nlinarith
  have h2 : 1 + (y - μ) ≤ Real.exp (y - μ) := by have := Real.add_one_le_exp (y - μ); linarith
  have h3 : y ≤ μ * Real.exp (y - μ) := h1.trans (mul_le_mul_of_nonneg_left h2 hpos.le)
  have h4 : Real.exp (y - μ) * Real.exp (-y) = Real.exp (-μ) := by rw [← Real.exp_add]; ring_nf
  calc y * Real.exp (-y) ≤ μ * Real.exp (y - μ) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = μ * Real.exp (-μ) := by rw [mul_assoc, h4]

end numerics

section phase1b
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {P₁ P₂ S : Finset ℕ} {p₁ p₂ p₃ : ℕ}

/-- placing `x` at the `j`-th protected position -/
def stPut (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) {j : ℕ} (hj : j < P₁.sort.length)
    (ω : Perm V) (x : V) : Perm V :=
  put ω x (P₁.sort)[j] (sortJ_valid hs _ (List.getElem_mem hj))

lemma stage_put_mem (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) {j : ℕ} (hj : j < P₁.sort.length)
    (ω : Perm V) (x : V) (hx : x ∈ unexp (stX S P₁.sort j) ω) :
    stPut hs hj ω x ∈ cls (stX S P₁.sort j) ω :=
  put_mem_cls ω x _ _ (sortJ_not_mem hs hj) (by simpa [unexp] using hx)

lemma lenJ (P₁ : Finset ℕ) : P₁.sort.length = P₁.card := Finset.length_sort _

lemma curJ_eq_get (P₁ : Finset ℕ) {j : ℕ} (hj : j < P₁.sort.length) :
    curJ P₁ j = (P₁.sort)[j] := by
  rw [curJ_lt P₁ (by rw [← lenJ]; exact hj)]

lemma AJ_congr (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ P₁.card) {ω ω' : Perm V} (h : ω' ∈ cls (stX S P₁.sort j) ω) :
    AJ G P₁ S a i ω' = AJ G P₁ S a i ω := by
  unfold AJ
  apply actSet_congr G (exposed_before_J hs (by omega))
  rw [mem_cls] at h ⊢
  exact h.mono (stX_mono S _ hij)

lemma N2J_congr (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ P₁.card) {ω ω' : Perm V} (h : ω' ∈ cls (stX S P₁.sort j) ω) (u : V) :
    N2J G P₁ S a i u ω' = N2J G P₁ S a i u ω := by
  unfold N2J
  apply actSetΦ_congr G _ (exposed_before_J hs (by omega))
  rw [mem_cls] at h ⊢
  exact h.mono (stX_mono S _ hij)

lemma AJ_anti_stage (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ P₁.card) (ω : Perm V) : AJ G P₁ S a j ω ⊆ AJ G P₁ S a i ω := by
  unfold AJ
  exact actSet_anti G (stX_mono S _ hij) (curJ_mono' P₁ hij hj)
    (exposed_before_J hs (by omega)) (self_mem_cls _ ω) a

lemma AJ_step (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) {j : ℕ} (hj : j < P₁.sort.length)
    {ω ω' : Perm V} (h : ω' ∈ cls (stX S P₁.sort j) ω) :
    AJ G P₁ S a (j + 1) ω' ⊆ AJ G P₁ S a j ω := by
  have hj' : j < P₁.card := by rw [← lenJ]; exact hj
  unfold AJ
  exact actSet_anti G (stX_mono S _ (Nat.le_succ j)) (curJ_mono P₁ hj').le
    (exposed_before_J hs hj'.le) h a

lemma N2J_step (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) {j : ℕ} (hj : j < P₁.sort.length)
    {ω ω' : Perm V} (h : ω' ∈ cls (stX S P₁.sort j) ω) (u : V) :
    N2J G P₁ S a (j + 1) u ω' ⊆ N2J G P₁ S a j u ω := by
  have hj' : j < P₁.card := by rw [← lenJ]; exact hj
  unfold N2J
  exact actSetΦ_anti G _ (stX_mono S _ (Nat.le_succ j)) (curJ_mono P₁ hj').le
    (exposed_before_J hs hj'.le) h u

/-- placing an alive neighbour of `u` at the current position kills `u` -/
lemma kill_at_stage (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) {j : ℕ} (hj : j < P₁.sort.length)
    (ω : Perm V) (x : V) (hx : x ∈ unexp (stX S P₁.sort j) ω)
    (hxa : curJ P₁ j ≤ tau G (rank ω) x) (u : V) (hux : G.Adj u x)
    (ω' : Perm V)
    (hω' : ω' ∈ cls (stX S P₁.sort (j + 1))
      (stPut hs hj ω x)) :
    tau G (rank ω') u ≤ curJ P₁ j := by
  have hj' : j < P₁.card := by rw [← lenJ]; exact hj
  have hput := stage_put_mem hs hj ω x hx
  have hag : Agree (stX S P₁.sort j) ω ω' :=
    (mem_cls.1 hput).trans ((mem_cls.1 hω').mono (stX_mono S _ (Nat.le_succ j)))
  have hxr : rank ω' x = curJ P₁ j := by
    rw [(mem_cls.1 hω') x (by rw [stPut, rank_put_self, ← stX_succ S _ j hj]; simp), stPut, rank_put_self,
      curJ_eq_get P₁ hj]
  have hle := agreeLE_of_agree_sub (exposed_before_J hs hj'.le) hag
  have hxa' : rank ω' x ≤ tau G (rank ω') x := by
    rw [hxr, ← le_tau_congr G hle x (by omega)]; exact hxa
  have := tau_le_of_adj_alive G (rank ω') u x hux hxa'
  omega

lemma kill_a_stage (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) {j : ℕ}
    (hj : j < P₁.sort.length) (ω : Perm V) (ha : rank ω a = p₁) (x : V)
    (hx : x ∈ unexp (stX S P₁.sort j) ω) (hxA : x ∈ AJ G P₁ S a j ω) :
    condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃) (stX S P₁.sort (j + 1))
      (stPut hs hj ω x) = 0 := by
  have hj' : j < P₁.card := by rw [← lenJ]; exact hj
  apply condProb_eq_zero
  intro ω' hω' hE
  obtain ⟨u, v, w, hu, hv, hw, hind, hu1, hv1, hw1⟩ := hE
  simp only [AJ, actSet, Finset.mem_filter, Finset.mem_univ, true_and] at hxA
  have hput := stage_put_mem hs hj ω x hx
  have hag : Agree (stX S P₁.sort j) ω ω' :=
    (mem_cls.1 hput).trans ((mem_cls.1 hω').mono (stX_mono S _ (Nat.le_succ j)))
  have hua : u = a := by
    apply rank_injective ω'
    rw [hu, hag a (by rw [ha]; simp [stX, hs.hp₁S]), ha]
  subst hua
  have := kill_at_stage G hs hj ω x hx hxA.2.2 u hxA.1 ω' hω'
  have := curJ_le P₁ j hj'.le
  have : curJ P₁ j ≤ P₁.sup id := by
    rw [curJ_eq_get P₁ hj]
    exact le_sup_id ((Finset.mem_sort _).1 (List.getElem_mem _))
  omega

lemma candJ_step (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) (θℓ : ℝ) {j : ℕ}
    (hj : j < P₁.sort.length) {ω ω' : Perm V} (h : ω' ∈ cls (stX S P₁.sort j) ω) :
    candJ G P₁ S a θℓ (j + 1) ω' ⊆ candJ G P₁ S a θℓ j ω := by
  intro u hu
  simp only [candJ, Finset.mem_filter] at hu ⊢
  refine ⟨AJ_step G hs a hj h hu.1, hu.2.trans ?_⟩
  exact_mod_cast Finset.card_le_card (N2J_step G hs a hj h u)

lemma candJ_sub_AJ (a : V) (θℓ : ℝ) (j : ℕ) (ω : Perm V) :
    candJ G P₁ S a θℓ j ω ⊆ AJ G P₁ S a j ω := Finset.filter_subset _ _

/-- the key decay of candidates under the conditioned process -/
lemma candJ_decay (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) (θℓ : ℝ) {j : ℕ}
    (hj : j < P₁.sort.length) (ω : Perm V) :
    (∑ x ∈ unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω,
        ((candJ G P₁ S a θℓ (j + 1) (stPut hs hj ω x)).card : ℝ)) ≤
      ((candJ G P₁ S a θℓ j ω).card : ℝ) *
        (((unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω).card : ℝ) - θℓ) := by
  classical
  obtain ⟨Gd, hGd⟩ : ∃ Gd : Finset V,
      Gd = unexp (stX S (P₁.sort (· ≤ ·)) j) ω \ AJ G P₁ S a j ω := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Finset V, C = candJ G P₁ S a θℓ j ω := ⟨_, rfl⟩
  rw [← hGd, ← hC]
  have h1 : ∀ x ∈ Gd, ((candJ G P₁ S a θℓ (j + 1) (stPut hs hj ω x)).card : ℝ) =
      ∑ u ∈ C, if u ∈ candJ G P₁ S a θℓ (j + 1) (stPut hs hj ω x) then (1 : ℝ) else 0 := by
    intro x hx
    rw [Finset.sum_boole]
    congr 1
    rw [hGd] at hx
    have hsub := candJ_step G hs a θℓ hj (stage_put_mem hs hj ω x (Finset.mem_sdiff.1 hx).1)
    rw [Finset.filter_mem_eq_inter, hC, Finset.inter_eq_right.2 hsub]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  rw [show ((C.card : ℝ) * ((Gd.card : ℝ) - θℓ)) =
    ∑ u ∈ C, ((Gd.card : ℝ) - θℓ) by rw [Finset.sum_const, nsmul_eq_mul]]
  apply Finset.sum_le_sum
  intro u hu
  rw [hC] at hu
  simp only [candJ, Finset.mem_filter] at hu
  -- the distance-two neighbours of `u` are all good and each kills `u`
  have hN2sub : N2J G P₁ S a j u ω ⊆ Gd := by
    intro w hw
    simp only [N2J, actSetΦ, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [hGd]
    simp only [Finset.mem_sdiff, unexp, Finset.mem_filter, Finset.mem_univ, true_and, AJ,
      actSet, not_and]
    exact ⟨hw.2.2.1, fun h => absurd h hw.2.1⟩
  have hkill : ∀ x ∈ N2J G P₁ S a j u ω,
      u ∉ candJ G P₁ S a θℓ (j + 1) (stPut hs hj ω x) := by
    intro x hx hu'
    simp only [N2J, actSetΦ, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hxU : x ∈ unexp (stX S P₁.sort j) ω := by simp [unexp, hx.2.2.1]
    simp only [candJ, AJ, actSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu'
    have := kill_at_stage G hs hj ω x hxU hx.2.2.2 u hx.1 _ (self_mem_cls _ _)
    have := curJ_mono P₁ (by rw [← lenJ]; exact hj) (j := j)
    have := hu'.1.2.2
    omega
  calc ∑ x ∈ Gd, (if u ∈ candJ G P₁ S a θℓ (j + 1) (stPut hs hj ω x) then (1 : ℝ) else 0)
      ≤ ∑ x ∈ Gd \ N2J G P₁ S a j u ω, (1 : ℝ) := by
        rw [← Finset.sum_sdiff hN2sub]
        have : ∑ x ∈ N2J G P₁ S a j u ω, (if u ∈ candJ G P₁ S a θℓ (j + 1)
            (stPut hs hj ω x) then (1 : ℝ) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro x hx; rw [if_neg (hkill x hx)]
        rw [this, add_zero]
        apply Finset.sum_le_sum; intro x _; split_ifs <;> norm_num
    _ = (Gd.card : ℝ) - (N2J G P₁ S a j u ω).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_sdiff_of_subset hN2sub,
          Nat.cast_sub (Finset.card_le_card hN2sub)]
    _ ≤ (Gd.card : ℝ) - θℓ := by linarith [hu.2]

end phase1b

section pointwise

/-- The pointwise inequality at the end of phase 1. -/
lemma twohop_pointwise (n : ℝ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 1000 ≤ ℓ) (D f dk Λ : ℝ)
    (hf0 : 0 ≤ f) (hfD : f ≤ D) (hDk : D ≤ dk) (hΛ1 : (ℓ : ℝ) * D / n ≤ Λ)
    (hΛ2 : (((ℓ / 10 : ℕ) : ℝ) + 1) * dk / n + ((ℓ : ℝ) - ((ℓ / 10 : ℕ) : ℝ) - 1) * D / n ≤ Λ) :
    Real.exp (-Λ) * ((5/6) * D + f / 6) ≤
      n / (Real.exp 1 * ℓ) * ((1 - 1/250) + (1/250) * ((ℓ / ((17/20) * n)) *
        (if dk < (6/5) * n / ℓ then f else 0))) := by
  have hℓR : (1000 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have hD0 : 0 ≤ D := hf0.trans hfD
  set base := n / (Real.exp 1 * ℓ) with hbase
  have hbase_pos : 0 < base := by positivity
  set y := (ℓ : ℝ) * D / n with hy
  have hy0 : 0 ≤ y := by positivity
  have hDy : D = n / ℓ * y := by rw [hy]; field_simp
  have hLHS : (5/6) * D + f / 6 ≤ D := by linarith
  have he1 : Real.exp (-Λ) * D ≤ Real.exp (-y) * D :=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hD0
  have hcommon : Real.exp (-y) * D ≤ base := by
    rw [hDy, hbase]
    have := mul_exp_neg_le y
    rw [Real.exp_neg 1] at this
    calc Real.exp (-y) * (n / ℓ * y) = n / ℓ * (y * Real.exp (-y)) := by ring
      _ ≤ n / ℓ * (Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_left this (by positivity)
      _ = n / (Real.exp 1 * ℓ) := by field_simp
  have hX0 : 0 ≤ (ℓ / ((17/20) * n)) * (if dk < (6/5) * n / ℓ then f else 0) := by
    apply mul_nonneg (by positivity); split_ifs <;> linarith
  have hRHS : base * (1 - 1/250) ≤ base * ((1 - 1/250) + (1/250) *
      ((ℓ / ((17/20) * n)) * (if dk < (6/5) * n / ℓ then f else 0))) := by
    apply mul_le_mul_of_nonneg_left _ hbase_pos.le; nlinarith
  have hfin : Real.exp (-Λ) * ((5/6) * D + f / 6) ≤ Real.exp (-Λ) * D :=
    mul_le_mul_of_nonneg_left hLHS (Real.exp_pos _).le
  by_cases hA : y < 9/10
  · -- small final degree
    refine hfin.trans (he1.trans ?_)
    refine le_trans ?_ hRHS
    rw [hDy, hbase]
    have h1 := mul_exp_neg_le_of_le hy0 hA.le (by norm_num : (9/10 : ℝ) ≤ 1)
    have h2 : (9/10 : ℝ) * Real.exp (-(9/10)) ≤ (1 - 1/250) * Real.exp (-1) := by
      have := exp_tenth_le
      have e : Real.exp (-(9/10)) = Real.exp (1/10) * Real.exp (-1) := by
        rw [← Real.exp_add]; norm_num
      rw [e]
      have := Real.exp_pos (-1)
      nlinarith
    rw [Real.exp_neg 1] at h2
    calc Real.exp (-y) * (n / ℓ * y) = n / ℓ * (y * Real.exp (-y)) := by ring
      _ ≤ n / ℓ * ((1 - 1/250) * (Real.exp 1)⁻¹) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = n / (Real.exp 1 * ℓ) * (1 - 1/250) := by field_simp
  push Not at hA
  by_cases hB : (6/5) * n / ℓ ≤ dk
  · -- large early degree
    refine hfin.trans ?_
    refine le_trans ?_ hRHS
    set k₀ : ℝ := ((ℓ / 10 : ℕ) : ℝ) with hk₀
    have hk1 : (ℓ : ℝ) / 10 - 1 < k₀ := by
      have := Nat.lt_div_mul_add (a := ℓ) (b := 10) (by norm_num)
      rw [hk₀]
      have h' : (ℓ : ℝ) < ((ℓ / 10 : ℕ) : ℝ) * 10 + 10 := by exact_mod_cast this
      linarith
    have hk2 : k₀ ≤ (ℓ : ℝ) / 10 := by
      rw [hk₀]
      have : (ℓ / 10) * 10 ≤ ℓ := Nat.div_mul_le_self ℓ 10
      have h' : ((ℓ / 10 : ℕ) : ℝ) * 10 ≤ ℓ := by exact_mod_cast this
      linarith
    set s : ℝ := (k₀ + 1) / ℓ with hs
    have hs1 : 1/10 ≤ s := by rw [hs, le_div_iff₀ hℓpos]; linarith
    have hs2 : s ≤ 1/10 + 1/1000 := by
      rw [hs, div_le_iff₀ hℓpos]
      have : (1 : ℝ) ≤ ℓ / 1000 := by rw [le_div_iff₀ (by norm_num)]; linarith
      nlinarith
    have hΛ3 : (6/5) * s + (1 - s) * y ≤ Λ := by
      refine le_trans ?_ hΛ2
      have e1 : (k₀ + 1) * dk / n = s * (ℓ * dk / n) := by rw [hs]; field_simp
      have e2 : ((ℓ : ℝ) - k₀ - 1) * D / n = (1 - s) * y := by rw [hs, hy]; field_simp; ring
      rw [e1, e2]
      have : (6/5 : ℝ) ≤ ℓ * dk / n := by
        rw [le_div_iff₀ hn]
        have := mul_le_mul_of_nonneg_left hB hℓpos.le
        rw [show (ℓ : ℝ) * ((6/5) * n / ℓ) = (6/5) * n by field_simp] at this
        linarith
      nlinarith
    have h1s : 0 < 1 - s := by linarith
    calc Real.exp (-Λ) * D ≤ Real.exp (-((6/5) * s + (1 - s) * y)) * D :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hD0
      _ = n / ℓ * Real.exp (-((6/5) * s)) * (((1 - s) * y * Real.exp (-((1 - s) * y))) / (1 - s)) := by
          rw [hDy]; field_simp; rw [← Real.exp_add]; ring_nf
      _ ≤ n / ℓ * Real.exp (-(3/25)) * (Real.exp (-1) / (1 - s)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith))
            (by positivity)) _ (by positivity) (by positivity)
          apply div_le_div_of_nonneg_right (mul_exp_neg_le _) h1s.le
      _ ≤ n / (Real.exp 1 * ℓ) * (1 - 1/250) := by
          have h3 := exp_3_25_ge
          have h4 : Real.exp (-(3/25)) ≤ 25/28 := by
            rw [Real.exp_neg]; rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
          have h5 : 1 / (1 - s) ≤ 1000 / 899 := by
            rw [div_le_div_iff₀ h1s (by norm_num)]; linarith
          rw [Real.exp_neg 1]
          have hpos : 0 < n / ℓ := by positivity
          have hepos := Real.exp_pos 1
          calc n / ℓ * Real.exp (-(3/25)) * ((Real.exp 1)⁻¹ / (1 - s))
              = n / ℓ * (Real.exp 1)⁻¹ * (Real.exp (-(3/25)) * (1 / (1 - s))) := by ring
            _ ≤ n / ℓ * (Real.exp 1)⁻¹ * ((25/28) * (1000/899)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul h4 h5 (by positivity) (by norm_num)
            _ ≤ n / ℓ * (Real.exp 1)⁻¹ * (1 - 1/250) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity); norm_num
            _ = n / (Real.exp 1 * ℓ) * (1 - 1/250) := by field_simp
  push Not at hB
  by_cases hC : f ≤ (17/20) * n / ℓ
  · -- few candidates
    refine le_trans ?_ hRHS
    have hD9 : (9/10) * n / ℓ ≤ D := by
      rw [div_le_iff₀ hℓpos]; rw [hy, le_div_iff₀ hn] at hA; linarith
    have hfD' : f ≤ (17/18) * D := by
      have : (17/20) * n / ℓ = (17/18) * ((9/10) * n / ℓ) := by ring
      rw [this] at hC; nlinarith
    have : (5/6) * D + f / 6 ≤ (107/108) * D := by linarith
    calc Real.exp (-Λ) * ((5/6) * D + f / 6) ≤ Real.exp (-Λ) * ((107/108) * D) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = (107/108) * (Real.exp (-Λ) * D) := by ring
      _ ≤ (107/108) * base := by
          apply mul_le_mul_of_nonneg_left (he1.trans hcommon) (by norm_num)
      _ ≤ base * (1 - 1/250) := by nlinarith
  · -- many candidates: the indicator term is large
    push Not at hC
    refine hfin.trans ((he1.trans hcommon).trans ?_)
    rw [if_pos hB]
    have : 1 ≤ (ℓ / ((17/20) * n)) * f := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      rw [div_lt_iff₀ hℓpos] at hC; linarith
    nlinarith

end pointwise

section potential
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {P₁ P₂ S : Finset ℕ} {p₁ p₂ p₃ : ℕ}

/-- accumulated survival exponent after `j` stages -/
noncomputable def LamJ (P₁ S : Finset ℕ) (a : V) (j : ℕ) (ω : Perm V) : ℝ :=
  ∑ i ∈ Finset.range j, ((AJ G P₁ S a i ω).card : ℝ) / (Fintype.card V : ℝ)

/-- the candidate potential -/
noncomputable def HxJ (P₁ S : Finset ℕ) (a : V) (j : ℕ) (ω : Perm V) : ℝ :=
  if j < P₁.card / 10 then
    (24/17) * (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - P₁.card / 10)
  else
    ((P₁.card : ℝ) / ((17/20) * Fintype.card V)) *
      (if ((AJ G P₁ S a (P₁.card / 10) ω).card : ℝ) < (6/5) * Fintype.card V / P₁.card then
        ((candJ G P₁ S a ((Fintype.card V : ℝ) / (2 * P₁.card)) j ω).card : ℝ) else 0) *
      (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - j)

/-- the full potential -/
noncomputable def HJ (P₁ S : Finset ℕ) (a : V) (K : ℝ) (j : ℕ) (ω : Perm V) : ℝ :=
  Real.exp (LamJ G P₁ S a j ω) * K * ((1 - 1/250) + (1/250) * HxJ G P₁ S a j ω)

lemma HxJ_nonneg (hℓ : 1 ≤ P₁.card) (a : V) (j : ℕ) (ω : Perm V) : 0 ≤ HxJ G P₁ S a j ω := by
  have hℓR : (1 : ℝ) ≤ P₁.card := by exact_mod_cast hℓ
  have hρ : 0 ≤ 1 - (1/2) / (P₁.card : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  unfold HxJ
  split_ifs <;> positivity

lemma HxJ_step (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (hℓ : 1 ≤ P₁.card) (a : V) {j : ℕ}
    (hj : j < P₁.sort.length) (ω : Perm V) :
    ∑ x ∈ unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω, HxJ G P₁ S a (j + 1) (stPut hs hj ω x) ≤
      ((unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω).card : ℝ) * HxJ G P₁ S a j ω := by
  classical
  have hj' : j < P₁.card := by rw [← lenJ]; exact hj
  have hℓR : (1 : ℝ) ≤ P₁.card := by exact_mod_cast hℓ
  have hnR : (0 : ℝ) < Fintype.card V := by
    have := hs.hp₃n; have := hs.hp₂₃; have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  have hρ0 : 0 ≤ 1 - (1/2) / (P₁.card : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  rcases Nat.lt_or_ge (j + 1) (P₁.card / 10) with h1 | h1
  · -- both constant
    have : ∀ x ∈ unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω,
        HxJ G P₁ S a (j + 1) (stPut hs hj ω x) = HxJ G P₁ S a j ω := by
      intro x _; unfold HxJ; rw [if_pos h1, if_pos (by omega)]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_or_lt_of_le h1 with h2 | h2
  · -- j + 1 = k₀
    have hjk : j < P₁.card / 10 := by omega
    have : ∀ x ∈ unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω,
        HxJ G P₁ S a (j + 1) (stPut hs hj ω x) ≤ HxJ G P₁ S a j ω := by
      intro x _
      unfold HxJ
      rw [if_neg (by omega), if_pos hjk, h2]
      split_ifs with hc
      · have hcard : ((candJ G P₁ S a ((Fintype.card V : ℝ) / (2 * P₁.card)) (j + 1)
            (stPut hs hj ω x)).card : ℝ) ≤ (6/5) * Fintype.card V / P₁.card := by
          refine le_trans ?_ hc.le
          exact Nat.cast_le.2 (Finset.card_le_card (candJ_sub_AJ G a _ _ _))
        calc (P₁.card : ℝ) / ((17/20) * Fintype.card V) * ((candJ G P₁ S a
              ((Fintype.card V : ℝ) / (2 * P₁.card)) (j + 1) (stPut hs hj ω x)).card : ℝ) *
              (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - (j + 1))
            ≤ (P₁.card : ℝ) / ((17/20) * Fintype.card V) * ((6/5) * Fintype.card V / P₁.card) *
              (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - (j + 1)) := by gcongr
          _ = (24/17) * (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - (j + 1)) := by field_simp; ring
      · simp only [mul_zero, zero_mul]; positivity
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  · -- j ≥ k₀: decay of candidates
    have hjk : P₁.card / 10 ≤ j := by omega
    have hind : ∀ x ∈ unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω,
        AJ G P₁ S a (P₁.card / 10) (stPut hs hj ω x) = AJ G P₁ S a (P₁.card / 10) ω := by
      intro x hx
      exact AJ_congr G hs a hjk hj'.le (stage_put_mem hs hj ω x (Finset.mem_sdiff.1 hx).1)
    have hsplit : ∀ x ∈ unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω,
        HxJ G P₁ S a (j + 1) (stPut hs hj ω x) =
        ((P₁.card : ℝ) / ((17/20) * Fintype.card V)) *
          (if ((AJ G P₁ S a (P₁.card / 10) ω).card : ℝ) < (6/5) * Fintype.card V / P₁.card
            then 1 else 0) *
          (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - (j + 1)) *
          ((candJ G P₁ S a ((Fintype.card V : ℝ) / (2 * P₁.card)) (j + 1)
            (stPut hs hj ω x)).card : ℝ) := by
      intro x hx
      unfold HxJ
      rw [if_neg (show ¬ (j + 1 < P₁.card / 10) by omega), hind x hx]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
    have hdec := candJ_decay G hs a ((Fintype.card V : ℝ) / (2 * P₁.card)) hj ω
    have hGdn : ((unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω).card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast Finset.card_le_univ _
    have hdec2 : ((candJ G P₁ S a ((Fintype.card V : ℝ) / (2 * P₁.card)) j ω).card : ℝ) *
        (((unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω).card : ℝ) -
          (Fintype.card V : ℝ) / (2 * P₁.card)) ≤
        ((candJ G P₁ S a ((Fintype.card V : ℝ) / (2 * P₁.card)) j ω).card : ℝ) *
        (((unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω).card : ℝ) *
          (1 - (1/2) / (P₁.card : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : ((unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω).card : ℝ) * ((1/2) / P₁.card) ≤
          (Fintype.card V : ℝ) / (2 * P₁.card) := by
        rw [show (Fintype.card V : ℝ) / (2 * P₁.card) = (Fintype.card V : ℝ) * ((1/2) / P₁.card)
          by field_simp]
        exact mul_le_mul_of_nonneg_right hGdn (by positivity)
      nlinarith
    have hpow : (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - (j + 1)) * (1 - (1/2) / (P₁.card : ℝ)) =
        (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - j) := by
      have e : P₁.card - j = (P₁.card - (j + 1)) + 1 := by omega
      rw [e, pow_succ]
    unfold HxJ
    rw [if_neg (show ¬ (j < P₁.card / 10) by omega)]
    have hc0 : 0 ≤ ((P₁.card : ℝ) / ((17/20) * Fintype.card V)) *
        (if ((AJ G P₁ S a (P₁.card / 10) ω).card : ℝ) < (6/5) * Fintype.card V / P₁.card
          then 1 else 0) *
        (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - (j + 1)) := by
      apply mul_nonneg (mul_nonneg (by positivity) (by split_ifs <;> norm_num)) (pow_nonneg hρ0 _)
    refine (mul_le_mul_of_nonneg_left (hdec.trans hdec2) hc0).trans (le_of_eq ?_)
    rw [← hpow]; split_ifs <;> ring

end potential

section potential2
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {P₁ P₂ S : Finset ℕ} {p₁ p₂ p₃ : ℕ}

lemma LamJ_succ (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (a : V) {j : ℕ}
    (hj : j < P₁.sort.length) {ω ω' : Perm V} (h : ω' ∈ cls (stX S P₁.sort j) ω) :
    LamJ G P₁ S a (j + 1) ω' = LamJ G P₁ S a j ω +
      ((AJ G P₁ S a j ω).card : ℝ) / (Fintype.card V : ℝ) := by
  have hj' : j < P₁.card := by rw [← lenJ]; exact hj
  unfold LamJ
  rw [Finset.sum_range_succ, AJ_congr G hs a le_rfl hj'.le h]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [AJ_congr G hs a hi.le hj'.le h]

lemma HJ_step (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (hℓ : 1 ≤ P₁.card) (a : V) (K : ℝ)
    (hK : 0 ≤ K) {j : ℕ} (hj : j < P₁.sort.length) (ω : Perm V) :
    (∑ x ∈ unexp (stX S P₁.sort j) ω ∩ (Finset.univ \ AJ G P₁ S a j ω),
        HJ G P₁ S a K (j + 1) (stPut hs hj ω x)) /
      ((unexp (stX S P₁.sort j) ω).card : ℝ) ≤ HJ G P₁ S a K j ω := by
  classical
  have hj' : j < P₁.card := by rw [← lenJ]; exact hj
  have hnR : (0 : ℝ) < Fintype.card V := by
    have := hs.hp₃n; have := hs.hp₂₃; have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  have hint : unexp (stX S P₁.sort j) ω ∩ (Finset.univ \ AJ G P₁ S a j ω) =
      unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω := by
    ext x; simp
  rw [hint]
  have hAU : AJ G P₁ S a j ω ⊆ unexp (stX S P₁.sort j) ω := by
    intro w hw; simp only [AJ, actSet, Finset.mem_filter] at hw
    simp only [unexp, Finset.mem_filter, Finset.mem_univ, true_and]; exact hw.2.2.1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((unexp (stX S (P₁.sort (· ≤ ·)) j) ω).card : ℝ) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ((AJ G P₁ S a j ω).card : ℝ) := ⟨_, rfl⟩
  rw [← hm]
  have hGd : ((unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω).card : ℝ) = m - d := by
    rw [Finset.card_sdiff_of_subset hAU, Nat.cast_sub (Finset.card_le_card hAU), hm, hd]
  have hmpos : 0 < m := by
    rw [hm]; exact_mod_cast Finset.card_pos.2 (unexp_nonempty_of ω _
      (sortJ_valid hs _ (List.getElem_mem hj)) (sortJ_not_mem hs hj))
  have hmn : m ≤ Fintype.card V := by rw [hm]; exact_mod_cast Finset.card_le_univ _
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hdm : d ≤ m := by rw [hd, hm]; exact_mod_cast Finset.card_le_card hAU
  have heach : ∀ x ∈ unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω,
      HJ G P₁ S a K (j + 1) (stPut hs hj ω x) = Real.exp (LamJ G P₁ S a j ω) *
        Real.exp (d / Fintype.card V) * K *
        ((1 - 1/250) + (1/250) * HxJ G P₁ S a (j + 1) (stPut hs hj ω x)) := by
    intro x hx
    unfold HJ
    rw [LamJ_succ G hs a hj (stage_put_mem hs hj ω x (Finset.mem_sdiff.1 hx).1), Real.exp_add, hd]
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ x ∈ unexp (stX S (P₁.sort (· ≤ ·)) j) ω \ AJ G P₁ S a j ω,
      HxJ G P₁ S a (j + 1) (stPut hs hj ω x) := ⟨_, rfl⟩
  have hsum : ∑ x ∈ unexp (stX S P₁.sort j) ω \ AJ G P₁ S a j ω,
      HJ G P₁ S a K (j + 1) (stPut hs hj ω x) = Real.exp (LamJ G P₁ S a j ω) *
        Real.exp (d / Fintype.card V) * K * ((m - d) * (1 - 1/250) + 1/250 * T) := by
    rw [Finset.sum_congr rfl heach, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum, hGd, hT]
  rw [hsum]
  have hx : T ≤ (m - d) * HxJ G P₁ S a j ω := by
    have := HxJ_step G hs hℓ a hj ω
    rw [hGd] at this; rw [hT]; exact this
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = HxJ G P₁ S a j ω := ⟨_, rfl⟩
  obtain ⟨Lm, hLm⟩ : ∃ Lm : ℝ, Lm = LamJ G P₁ S a j ω := ⟨_, rfl⟩
  have hHx0 : 0 ≤ X := by rw [hX]; exact HxJ_nonneg G hℓ (S := S) a j ω
  rw [← hX] at hx
  unfold HJ
  rw [← hX, ← hLm]
  have hkey : Real.exp (d / Fintype.card V) * (m - d) ≤ m := by
    have h1 : Real.exp (d / Fintype.card V) * (1 - d / Fintype.card V) ≤ 1 := by
      have := Real.add_one_le_exp (-(d / Fintype.card V))
      have h2 : Real.exp (d / Fintype.card V) * Real.exp (-(d / Fintype.card V)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (d / Fintype.card V)]
    have h3 : (m - d) ≤ m * (1 - d / Fintype.card V) := by
      have : m * (d / Fintype.card V) ≤ d := by
        rw [mul_div_assoc', div_le_iff₀ hnR]; nlinarith
      nlinarith
    calc Real.exp (d / Fintype.card V) * (m - d)
        ≤ Real.exp (d / Fintype.card V) * (m * (1 - d / Fintype.card V)) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = m * (Real.exp (d / Fintype.card V) * (1 - d / Fintype.card V)) := by ring
      _ ≤ m * 1 := mul_le_mul_of_nonneg_left h1 hmpos.le
      _ = m := mul_one m
  rw [div_le_iff₀ hmpos]
  have hE0 := Real.exp_pos Lm
  have hE1 := Real.exp_pos (d / Fintype.card V)
  have hinner : (m - d) * (1 - 1/250) + 1/250 * T ≤ (m - d) * ((1 - 1/250) + (1/250) * X) := by
    nlinarith
  have hpos2 : 0 ≤ (1 - 1/250 : ℝ) + (1/250) * X := by nlinarith
  calc Real.exp Lm * Real.exp (d / Fintype.card V) * K * ((m - d) * (1 - 1/250) + 1/250 * T)
      ≤ Real.exp Lm * Real.exp (d / Fintype.card V) * K * ((m - d) * ((1 - 1/250) + (1/250) * X)) := by
        apply mul_le_mul_of_nonneg_left hinner; positivity
    _ = Real.exp Lm * K * ((1 - 1/250) + (1/250) * X) *
        (Real.exp (d / Fintype.card V) * (m - d)) := by ring
    _ ≤ Real.exp Lm * K * ((1 - 1/250) + (1/250) * X) * m := by
        apply mul_le_mul_of_nonneg_left hkey; positivity

end potential2

section final2hop
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {P₁ P₂ S : Finset ℕ} {p₁ p₂ p₃ : ℕ}

lemma nExp_mono (V : Type*) [Fintype V] {X Y : Finset ℕ} (h : X ⊆ Y) : nExp V X ≤ nExp V Y :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma gmax_le_small {n n' : ℝ} (hn : 0 < n) (hn' : 0 < n') {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {c : ℕ}
    (hc : (c : ℝ) < n / (2 * ℓ)) :
    gmax n n' ℓ c ≤ (5/6) * (n / (Real.exp 1 * ℓ * n')) := by
  unfold gmax
  apply Finset.sup'_le
  intro D hD
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hDc : (D : ℝ) ≤ c := by
    have : D ≤ c := by simp at hD; omega
    exact_mod_cast this
  have hy0 : 0 ≤ (ℓ : ℝ) * D / n := by positivity
  have hy : (ℓ : ℝ) * D / n ≤ 1/2 := by
    rw [div_le_iff₀ hn]
    have h1 : (ℓ : ℝ) * D ≤ ℓ * c := mul_le_mul_of_nonneg_left hDc (by linarith)
    have h2 : (ℓ : ℝ) * c < ℓ * (n / (2 * ℓ)) := mul_lt_mul_of_pos_left hc (by linarith)
    have h3 : (ℓ : ℝ) * (n / (2 * ℓ)) = n / 2 := by field_simp
    linarith
  have h1 := mul_exp_neg_le_of_le hy0 hy (by norm_num : (1/2 : ℝ) ≤ 1)
  have h2 : (1/2 : ℝ) * Real.exp (-(1/2)) ≤ (5/6) * Real.exp (-1) := by
    have e : Real.exp (-(1/2)) = Real.exp (1/2) * Real.exp (-1) := by
      rw [← Real.exp_add]; norm_num
    rw [e]
    have := exp_half_le
    have := Real.exp_pos (-1)
    nlinarith
  rw [Real.exp_neg 1] at h2
  have e2 : Real.exp (-(ℓ : ℝ) * D / n) * D / n' =
      (n / (ℓ * n')) * ((ℓ : ℝ) * D / n * Real.exp (-((ℓ : ℝ) * D / n))) := by
    rw [neg_mul, neg_div]
    field_simp
  rw [e2]
  calc (n / (ℓ * n')) * ((ℓ : ℝ) * D / n * Real.exp (-((ℓ : ℝ) * D / n)))
      ≤ (n / (ℓ * n')) * ((5/6) * (Real.exp 1)⁻¹) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = (5/6) * (n / (Real.exp 1 * ℓ * n')) := by field_simp

theorem twohop_terminal (hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃) (hℓ : 1000 ≤ P₁.card)
    (hℓ2 : P₂.card = P₁.card) (a : V) (ω : Perm V) (ha : rank ω a = p₁) (n' : ℝ) (hn' : 0 < n')
    (hn'le : n' ≤ (Fintype.card V - nExp V (insert p₂ (S ∪ P₁) ∪ P₂) : ℕ)) :
    condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃) (stX S P₁.sort P₁.sort.length) ω ≤
      HJ G P₁ S a ((Fintype.card V / (Real.exp 1 * P₁.card * n')) ^ 2) P₁.sort.length ω := by
  classical
  have hnR : (0 : ℝ) < Fintype.card V := by
    have := hs.hp₃n; have := hs.hp₂₃; have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  have hℓR : (1000 : ℝ) ≤ P₁.card := by exact_mod_cast hℓ
  rw [lenJ, stX_card]
  have h1 := phase1_end G hs a ω ha n' hn' hn'le
  -- identify the stage-ℓ quantities
  have hA : AJ G P₁ S a P₁.card ω = actSet G ω a (S ∪ P₁) (P₁.sup id + 1) := by
    unfold AJ; rw [stX_card, curJ_card]
  have hN : ∀ b, N2J G P₁ S a P₁.card b ω =
      actSetΦ G (fun w => ¬ G.Adj a w) ω b (S ∪ P₁) (P₁.sup id + 1) := by
    intro b; unfold N2J; rw [stX_card, curJ_card]
  rw [← hA] at h1
  simp_rw [← hN] at h1
  set φ := Fintype.card V / (Real.exp 1 * P₁.card * n') with hφ
  have hφ0 : 0 < φ := by positivity
  set θℓ := (Fintype.card V : ℝ) / (2 * P₁.card) with hθℓ
  set D := ((AJ G P₁ S a P₁.card ω).card : ℝ) with hD
  set f := ((candJ G P₁ S a θℓ P₁.card ω).card : ℝ) with hf
  -- sum over the final active set
  have hsum : ∑ b ∈ AJ G P₁ S a P₁.card ω,
      gmax (Fintype.card V) n' P₂.card (N2J G P₁ S a P₁.card b ω).card ≤
      φ * ((5/6) * D + f / 6) := by
    rw [← Finset.sum_filter_add_sum_filter_not (AJ G P₁ S a P₁.card ω)
      (fun u => θℓ ≤ ((N2J G P₁ S a P₁.card u ω).card : ℝ))]
    have hc1 : ∑ b ∈ (AJ G P₁ S a P₁.card ω).filter
        (fun u => θℓ ≤ ((N2J G P₁ S a P₁.card u ω).card : ℝ)),
        gmax (Fintype.card V) n' P₂.card (N2J G P₁ S a P₁.card b ω).card ≤ f * φ := by
      rw [hf]
      unfold candJ
      refine (Finset.sum_le_sum (fun b _ => ?_)).trans (le_of_eq (by
        rw [Finset.sum_const, nsmul_eq_mul]))
      rw [hℓ2, hφ]
      exact gmax_le hnR hn' (by omega) _
    have hcard : ((AJ G P₁ S a P₁.card ω).filter
        (fun u => ¬ θℓ ≤ ((N2J G P₁ S a P₁.card u ω).card : ℝ))).card = D - f := by
      rw [hD, hf, candJ]
      have := Finset.card_filter_add_card_filter_not (s := AJ G P₁ S a P₁.card ω)
        (fun u => θℓ ≤ ((N2J G P₁ S a P₁.card u ω).card : ℝ))
      have h' : (((AJ G P₁ S a P₁.card ω).filter
          (fun u => θℓ ≤ ((N2J G P₁ S a P₁.card u ω).card : ℝ))).card : ℝ) +
          (((AJ G P₁ S a P₁.card ω).filter
          (fun u => ¬ θℓ ≤ ((N2J G P₁ S a P₁.card u ω).card : ℝ))).card : ℝ) =
          ((AJ G P₁ S a P₁.card ω).card : ℝ) := by exact_mod_cast this
      linarith
    have hc2 : ∑ b ∈ (AJ G P₁ S a P₁.card ω).filter
        (fun u => ¬ θℓ ≤ ((N2J G P₁ S a P₁.card u ω).card : ℝ)),
        gmax (Fintype.card V) n' P₂.card (N2J G P₁ S a P₁.card b ω).card ≤
        (D - f) * ((5/6) * φ) := by
      rw [← hcard]
      refine (Finset.sum_le_sum (fun b hb => ?_)).trans (le_of_eq (by
        rw [Finset.sum_const, nsmul_eq_mul]))
      simp only [Finset.mem_filter, not_le] at hb
      rw [hℓ2, hφ]
      exact gmax_le_small hnR hn' (by omega) hb.2
    nlinarith
  -- m ≥ n'
  have hm : n' ≤ ((unexp (S ∪ P₁) ω).card : ℝ) := by
    rw [card_unexp]
    refine hn'le.trans ?_
    have := nExp_mono V ((Finset.subset_insert p₂ (S ∪ P₁)).trans Finset.subset_union_left :
      S ∪ P₁ ⊆ insert p₂ (S ∪ P₁) ∪ P₂)
    have h2 := nExp_le_card V (insert p₂ (S ∪ P₁) ∪ P₂)
    exact_mod_cast Nat.sub_le_sub_left this _
  have hmpos : 0 < ((unexp (S ∪ P₁) ω).card : ℝ) := hn'.trans_le hm
  have hstep1 : condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃) (S ∪ P₁) ω ≤
      φ * ((5/6) * D + f / 6) / n' := by
    refine h1.trans ?_
    have hnum0 : 0 ≤ φ * ((5/6) * D + f / 6) := le_trans (Finset.sum_nonneg (fun b _ => by
      exact le_trans (by simp) (le_gmax _ _ _ (D := 0) (Nat.zero_le _)))) hsum
    calc (∑ b ∈ AJ G P₁ S a P₁.card ω,
          gmax (Fintype.card V) n' P₂.card (N2J G P₁ S a P₁.card b ω).card) /
          ((unexp (S ∪ P₁) ω).card : ℝ)
        ≤ φ * ((5/6) * D + f / 6) / ((unexp (S ∪ P₁) ω).card : ℝ) :=
          div_le_div_of_nonneg_right hsum hmpos.le
      _ ≤ φ * ((5/6) * D + f / 6) / n' := div_le_div_of_nonneg_left hnum0 hn' hm
  refine hstep1.trans ?_
  -- the pointwise inequality
  set k₀ := P₁.card / 10 with hk₀
  set dk := ((AJ G P₁ S a k₀ ω).card : ℝ) with hdk
  set Λ := LamJ G P₁ S a P₁.card ω with hΛ
  have hk₀ℓ : k₀ < P₁.card := by omega
  have hDi : ∀ i ∈ Finset.range P₁.card, D ≤ ((AJ G P₁ S a i ω).card : ℝ) := by
    intro i hi; rw [Finset.mem_range] at hi
    rw [hD]; exact_mod_cast Finset.card_le_card (AJ_anti_stage G hs a hi.le le_rfl ω)
  have hdki : ∀ i ∈ Finset.range (k₀ + 1), dk ≤ ((AJ G P₁ S a i ω).card : ℝ) := by
    intro i hi; rw [Finset.mem_range] at hi
    rw [hdk]
    exact_mod_cast Finset.card_le_card (AJ_anti_stage G hs a (i := i) (j := k₀) (by omega)
      hk₀ℓ.le ω)
  have hΛ1 : (P₁.card : ℝ) * D / Fintype.card V ≤ Λ := by
    rw [hΛ, LamJ, ← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ hnR.le
    have := Finset.card_nsmul_le_sum (Finset.range P₁.card) _ D hDi
    simpa using this
  have hΛ2 : (((P₁.card / 10 : ℕ) : ℝ) + 1) * dk / Fintype.card V +
      ((P₁.card : ℝ) - ((P₁.card / 10 : ℕ) : ℝ) - 1) * D / Fintype.card V ≤ Λ := by
    rw [hΛ, LamJ, ← Finset.sum_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hnR.le
    rw [← Finset.sum_range_add_sum_Ico _ (show k₀ + 1 ≤ P₁.card by omega)]
    have h1 := Finset.card_nsmul_le_sum (Finset.range (k₀ + 1))
      (fun i => ((AJ G P₁ S a i ω).card : ℝ)) dk hdki
    have h2 := Finset.card_nsmul_le_sum (Finset.Ico (k₀ + 1) P₁.card)
      (fun i => ((AJ G P₁ S a i ω).card : ℝ)) D (by
      intro i hi; rw [Finset.mem_Ico] at hi; exact hDi i (Finset.mem_range.2 hi.2))
    simp only [Finset.card_range, Nat.card_Ico, nsmul_eq_mul] at h1 h2
    have hc : ((P₁.card - (k₀ + 1) : ℕ) : ℝ) = (P₁.card : ℝ) - k₀ - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc] at h2
    push_cast at h1
    rw [← hk₀]
    linarith
  have hfD : f ≤ D := by
    rw [hf, hD]; exact_mod_cast Finset.card_le_card (candJ_sub_AJ G a _ _ _)
  have hDk : D ≤ dk := by
    rw [hD, hdk]; exact_mod_cast Finset.card_le_card (AJ_anti_stage G hs a hk₀ℓ.le le_rfl ω)
  have hpw := twohop_pointwise (Fintype.card V) hnR P₁.card hℓ D f dk Λ (by positivity) hfD hDk
    hΛ1 hΛ2
  -- HxJ at the end
  have hHx : HxJ G P₁ S a P₁.card ω = ((P₁.card : ℝ) / ((17/20) * Fintype.card V)) *
      (if dk < (6/5) * Fintype.card V / P₁.card then f else 0) := by
    unfold HxJ
    rw [if_neg (show ¬ (P₁.card < P₁.card / 10) by omega), Nat.sub_self, pow_zero, mul_one]
  unfold HJ
  rw [hHx, ← hΛ]
  have hφn : φ * n' = Fintype.card V / (Real.exp 1 * P₁.card) := by
    rw [hφ]; field_simp
  have hE := Real.exp_pos Λ
  have key : Real.exp (-Λ) * ((5/6) * D + f / 6) * Real.exp Λ = (5/6) * D + f / 6 := by
    rw [mul_comm, ← mul_assoc, ← Real.exp_add]; simp
  rw [div_le_iff₀ hn']
  calc φ * ((5/6) * D + f / 6)
      = φ * (Real.exp (-Λ) * ((5/6) * D + f / 6) * Real.exp Λ) := by rw [key]
    _ ≤ φ * ((Fintype.card V / (Real.exp 1 * P₁.card)) * ((1 - 1/250) + (1/250) *
        ((P₁.card / ((17/20) * Fintype.card V)) *
          (if dk < (6/5) * Fintype.card V / P₁.card then f else 0))) * Real.exp Λ) := by
        apply mul_le_mul_of_nonneg_left _ hφ0.le
        exact mul_le_mul_of_nonneg_right hpw hE.le
    _ = Real.exp Λ * φ ^ 2 * ((1 - 1/250) + (1/250) *
        ((P₁.card / ((17/20) * Fintype.card V)) *
          (if dk < (6/5) * Fintype.card V / P₁.card then f else 0))) * n' := by
        rw [← hφn]; ring

end final2hop

section twohopfinal
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem twoHop_main (β : ℝ) (hβ0 : 0 < β) (hβ : β ≤ 1/100000)
    (hn2 : 2 ≤ Fintype.card V) (ℓ : ℕ) (hℓ : 10 ^ 3 < ℓ)
    (P₁ P₂ : Finset ℕ) (hP₁ : P₁.card = ℓ) (hP₂ : P₂.card = ℓ) (p₁ p₂ p₃ : ℕ)
    (h12 : ∀ x ∈ P₁, ∀ y ∈ P₂, x < y) (h2p : ∀ y ∈ P₂, y < p₁) (hp12 : p₁ < p₂) (hp23 : p₂ < p₃)
    (hp3 : (p₃ : ℝ) < β * (Fintype.card V : ℝ))
    (S : Finset ℕ) (hSβ : ∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) ≤ β * (Fintype.card V : ℝ))
    (hp₁S : p₁ ∈ S) (hfill : ∀ q, 1 ≤ q → q ≤ P₂.sup id → q ∉ P₁ → q ∉ P₂ → q ∈ S)
    (hSP : ∀ q ∈ S, q ∉ P₁ ∧ q ∉ P₂ ∧ q ≠ p₂ ∧ q ≠ p₃)
    (τ : ℕ) (hτ : 1 ≤ τ) (hτP : ∀ x ∈ P₁, τ < x) (ω₀ : Perm V) :
    condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃) S ω₀ ≤ (1 - 1/5000) / (Real.exp 1 * ℓ) ^ 2 := by
  have hnR : (0 : ℝ) < Fintype.card V := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  have hβ1 : β < 1 := by linarith
  have hP₂ne : P₂.Nonempty := Finset.card_pos.1 (by omega)
  have hP₁ne : P₁.Nonempty := Finset.card_pos.1 (by omega)
  have hp₃n : p₃ ≤ Fintype.card V := by
    have : (p₃ : ℝ) ≤ Fintype.card V := by nlinarith
    exact_mod_cast this
  have hs : THS (V := V) P₁ P₂ S p₁ p₂ p₃ :=
    { hp₁S := hp₁S
      hP₁S := Finset.disjoint_left.2 (fun x hx hxS => (hSP x hxS).1 hx)
      hP₂S := Finset.disjoint_left.2 (fun x hx hxS => (hSP x hxS).2.1 hx)
      hP₁₂ := h12
      hP₁p₁ := fun x hx => by
        obtain ⟨y, hy⟩ := hP₂ne; exact (h12 x hx y hy).trans (h2p y hy)
      hP₂p₁ := h2p
      hp₁₂ := hp12
      hp₂₃ := hp23
      hp₂S := fun h => (hSP p₂ h).2.2.1 rfl
      hp₃S := fun h => (hSP p₃ h).2.2.2 rfl
      hp₃n := hp₃n
      hPpos := by
        intro q hq
        rcases Finset.mem_union.1 hq with hq | hq
        · have := hτP q hq; omega
        · obtain ⟨x, hx⟩ := hP₁ne
          have := hτP x hx; have := h12 x hx q hq; omega
      hfill := hfill
      hP₁ne := hP₁ne
      hP₂ne := hP₂ne }
  obtain ⟨a, ha⟩ := exists_rank_eq ω₀ p₁ (hSβ p₁ hp₁S).1 (by have := hs.hp₁₂; omega)
  obtain ⟨n', hn'⟩ : ∃ n' : ℝ, n' = (1 - β) * Fintype.card V := ⟨_, rfl⟩
  have hn'pos : 0 < n' := by rw [hn']; exact mul_pos (by linarith) hnR
  have hn'le : n' ≤ ((Fintype.card V - nExp V (insert p₂ (S ∪ P₁) ∪ P₂) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (nExp_le_card V _)]
    have := nExp_le_floor (V := V) (insert p₂ (S ∪ P₁) ∪ P₂) β hβ0.le (by
      intro q hq
      simp only [Finset.mem_union, Finset.mem_insert] at hq
      have hp₁β := (hSβ p₁ hp₁S).2
      have hp12R : (p₁ : ℝ) < p₂ := by exact_mod_cast hp12
      have hp23R : (p₂ : ℝ) < p₃ := by exact_mod_cast hp23
      rcases hq with (rfl | hq | hq) | hq
      · linarith
      · exact (hSβ q hq).2
      · have := hs.hP₁p₁ q hq
        have : (q : ℝ) < p₁ := by exact_mod_cast this
        linarith
      · have := h2p q hq
        have : (q : ℝ) < p₁ := by exact_mod_cast this
        linarith)
    rw [hn']; linarith
  have hℓ1000 : 1000 ≤ P₁.card := by omega
  have hΩ : ∀ j (hj : j < P₁.sort.length), ∀ ω ∈ cls S ω₀,
      ∀ x ∈ unexp (stX S P₁.sort j) ω,
      put ω x (P₁.sort)[j] (sortJ_valid hs _ (List.getElem_mem hj)) ∈ cls S ω₀ := by
    intro j hj ω hω x hx
    have h1 := stage_put_mem hs hj ω x hx
    have h2 : cls (stX S P₁.sort j) ω ⊆ cls S ω₀ := by
      intro ω'' h''
      have hsub : S ⊆ stX S P₁.sort j := Finset.subset_union_left
      rw [mem_cls] at h'' ⊢
      exact (mem_cls.1 hω).trans (h''.mono hsub)
    exact h2 h1
  have hterm : ∀ ω ∈ cls S ω₀, condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃)
      (stX S P₁.sort P₁.sort.length) ω ≤
      HJ G P₁ S a ((Fintype.card V / (Real.exp 1 * P₁.card * n')) ^ 2) P₁.sort.length ω := by
    intro ω hω
    have haω : rank ω a = p₁ := by rw [(mem_cls.1 hω) a (by rw [ha]; exact hp₁S), ha]
    exact twohop_terminal G hs hℓ1000 (by rw [hP₁, hP₂]) a ω haω n' hn'pos hn'le
  have hbad : ∀ j (hj : j < P₁.sort.length), ∀ ω ∈ cls S ω₀,
      ∀ x ∈ unexp (stX S P₁.sort j) ω, x ∉ Finset.univ \ AJ G P₁ S a j ω →
      condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃) (stX S P₁.sort (j + 1))
        (put ω x (P₁.sort)[j] (sortJ_valid hs _ (List.getElem_mem hj))) = 0 := by
    intro j hj ω hω x hx hxg
    have haω : rank ω a = p₁ := by rw [(mem_cls.1 hω) a (by rw [ha]; exact hp₁S), ha]
    have hxA : x ∈ AJ G P₁ S a j ω := by simpa using hxg
    exact kill_a_stage G hs a hj ω haω x hx hxA
  have hsuper : ∀ j (hj : j < P₁.sort.length), ∀ ω ∈ cls S ω₀,
      (∑ x ∈ unexp (stX S P₁.sort j) ω ∩ (Finset.univ \ AJ G P₁ S a j ω),
        HJ G P₁ S a ((Fintype.card V / (Real.exp 1 * P₁.card * n')) ^ 2) (j + 1)
          (put ω x (P₁.sort)[j] (sortJ_valid hs _ (List.getElem_mem hj)))) /
        ((unexp (stX S P₁.sort j) ω).card : ℝ) ≤
      HJ G P₁ S a ((Fintype.card V / (Real.exp 1 * P₁.card * n')) ^ 2) j ω := by
    intro j hj ω _
    exact HJ_step G hs (by omega) a _ (by positivity) hj ω
  have hnew : ∀ j (hj : j < P₁.sort.length), (P₁.sort)[j] ∉ stX S P₁.sort j :=
    fun j hj => sortJ_not_mem hs hj
  have hpot : condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃) S ω₀ ≤
      HJ G P₁ S a ((Fintype.card V / (Real.exp 1 * P₁.card * n')) ^ 2) 0 ω₀ := by
    refine condProb_le_potential (twoHopEvent G P₁ P₂ p₁ p₂ p₃) S P₁.sort
      (sortJ_valid hs) hnew (cls S ω₀) hΩ (fun j ω => Finset.univ \ AJ G P₁ S a j ω)
      (HJ G P₁ S a ((Fintype.card V / (Real.exp 1 * P₁.card * n')) ^ 2))
      ?_ hbad hsuper ω₀ (self_mem_cls _ _)
    intro ω hω
    have := hterm ω hω
    convert this using 2
  refine hpot.trans ?_
  -- the initial value of the potential
  have hk0 : 0 < P₁.card / 10 := by omega
  unfold HJ
  have hL0 : LamJ G P₁ S a 0 ω₀ = 0 := by simp [LamJ]
  have hHx0 : HxJ G P₁ S a 0 ω₀ =
      (24/17) * (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - P₁.card / 10) := by
    unfold HxJ; rw [if_pos hk0]
  rw [hL0, hHx0, Real.exp_zero, one_mul]
  have hℓR : (1000 : ℝ) ≤ P₁.card := by exact_mod_cast hℓ1000
  -- (1 - 1/(2ℓ))^(ℓ - ℓ/10) ≤ e^{-9/20} ≤ 2/3
  have hpow : (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - P₁.card / 10) ≤ 2/3 := by
    have hb0 : 0 ≤ 1 - (1/2) / (P₁.card : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have h1 : (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - P₁.card / 10) ≤
        Real.exp (-((1/2) / (P₁.card : ℝ))) ^ (P₁.card - P₁.card / 10) := by
      apply pow_le_pow_left₀ hb0
      have := Real.add_one_le_exp (-((1/2) / (P₁.card : ℝ))); linarith
    rw [← Real.exp_nat_mul] at h1
    have h2 : ((P₁.card - P₁.card / 10 : ℕ) : ℝ) * (-((1/2) / (P₁.card : ℝ))) ≤ -(9/20) := by
      have hk : ((P₁.card / 10 : ℕ) : ℝ) ≤ (P₁.card : ℝ) / 10 := by
        have : (P₁.card / 10) * 10 ≤ P₁.card := Nat.div_mul_le_self _ 10
        have h' : ((P₁.card / 10 : ℕ) : ℝ) * 10 ≤ P₁.card := by exact_mod_cast this
        linarith
      rw [Nat.cast_sub (Nat.div_le_self _ _)]
      have : ((P₁.card : ℝ) - ((P₁.card / 10 : ℕ) : ℝ)) * ((1/2) / (P₁.card : ℝ)) ≥ 9/20 := by
        rw [ge_iff_le, mul_div_assoc', le_div_iff₀ (by linarith)]; nlinarith
      nlinarith
    have h3 := Real.exp_le_exp.2 h2
    have h4 : Real.exp (-(9/20)) ≤ 2/3 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := exp_9_20_ge; linarith
    linarith
  have hK : (Fintype.card V / (Real.exp 1 * P₁.card * n')) ^ 2 =
      1 / ((Real.exp 1 * ℓ) ^ 2 * (1 - β) ^ 2) := by
    rw [hn', hP₁]; field_simp
  rw [hK]
  have hinner : (1 - 1/250 : ℝ) + 1/250 * ((24/17) *
      (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - P₁.card / 10)) ≤ 1 - 1/4250 := by
    nlinarith
  have hβ2 : (1 - 1/4250 : ℝ) ≤ (1 - 1/5000) * (1 - β) ^ 2 := by nlinarith
  have hE : 0 < (Real.exp 1 * ℓ) ^ 2 := by positivity
  have hB : 0 < (1 - β) ^ 2 := by positivity
  calc 1 / ((Real.exp 1 * ℓ) ^ 2 * (1 - β) ^ 2) * ((1 - 1/250) + 1/250 * ((24/17) *
        (1 - (1/2) / (P₁.card : ℝ)) ^ (P₁.card - P₁.card / 10)))
      ≤ 1 / ((Real.exp 1 * ℓ) ^ 2 * (1 - β) ^ 2) * (1 - 1/4250) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ 1 / ((Real.exp 1 * ℓ) ^ 2 * (1 - β) ^ 2) * ((1 - 1/5000) * (1 - β) ^ 2) :=
        mul_le_mul_of_nonneg_left hβ2 (by positivity)
    _ = (1 - 1/5000) / (Real.exp 1 * ℓ) ^ 2 := by
        have : (1 - β) ≠ 0 := by linarith
        field_simp

theorem twoHopBound_of (β : ℝ) (hβ0 : 0 < β) (hβ : β ≤ 1/100000) :
    TwoHopBound β (1/5000) := by
  intro V _ _ G _ hn2 ℓ hℓ P₁ P₂ hP₁ hP₂ p₁ p₂ p₃ h12 h2p hp12 hp23 hp3 S hSβ hp₁S hfill hSP
    τ hτ hτP _ ω₀ _
  exact twoHop_main G β hβ0 hβ hn2 ℓ hℓ P₁ P₂ hP₁ hP₂ p₁ p₂ p₃ h12 h2p hp12 hp23 hp3 S hSβ hp₁S
    hfill hSP τ hτ hτP ω₀

end twohopfinal

end QDM

open QueryDepthMIS

theorem solution :
    ∃ β ε : ℝ, 0 < β ∧ β < 0.1 ∧ 0 < ε ∧ ε < 0.1 ∧ TwoHopBound β ε :=
  ⟨1/100000, 1/5000, by norm_num, by norm_num, by norm_num, by norm_num,
    QDM.twoHopBound_of (1/100000) (by norm_num) le_rfl⟩

