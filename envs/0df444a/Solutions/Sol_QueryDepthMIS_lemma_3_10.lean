-- Prove2me | solution 1 for QueryDepthMIS.lemma_3_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T14:29:23.040257+00:00
-- url     : https://prove2.me/submissions/a267b396-99db-4a33-9cd0-d00e761b5cd5

import Mathlib
import Definitions.Def_NoSignalPA_uniformExp
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_QueryDepthMIS_TwoHopBound
import Definitions.Def_QueryDepthMIS_Z
import Definitions.Def_QueryDepthMIS_aliveSet
import Definitions.Def_QueryDepthMIS_condProb
import Definitions.Def_QueryDepthMIS_maxDegOn
import Definitions.Def_QueryDepthMIS_oneHopEvent
import Definitions.Def_QueryDepthMIS_queryDepth
import Definitions.Def_QueryDepthMIS_rank
import Definitions.Def_QueryDepthMIS_shortcutIdx
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


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM
open QueryDepthMIS RGMISFast

section yyi
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- all duplicate-free lists of vertices -/
def NL (V : Type*) [Fintype V] [DecidableEq V] : Finset (List V) :=
  (Finset.univ : Finset {l : List V // l.Nodup}).map (Function.Embedding.subtype _)

lemma mem_NL {R : List V} : R ∈ NL V ↔ R.Nodup := by
  simp [NL]

/-- the query step relation, written "later, earlier" (paths are stored reversed, newest first) -/
def QRel (r : V → ℕ) (x y : V) : Prop := G.Adj y x ∧ r y < r x ∧ r y ≤ tau G r x

/-- a (reversed) query path at time `t`: all vertices but the newest have rank `≤ t` -/
def QPt (r : V → ℕ) (t : ℕ) (R : List V) : Prop :=
  2 ≤ R.length ∧ R.IsChain (QRel G r) ∧ ∀ v ∈ R.tail, r v ≤ t

/-- a (reversed) dangerous path at time `t` -/
def Dang (r : V → ℕ) (t : ℕ) (R : List V) : Prop :=
  ∃ z u rest, R = z :: u :: rest ∧ (rest = [] ∨ QPt G r t (u :: rest)) ∧ G.Adj u z ∧
    t < r u ∧ t < r z ∧ t + 1 ≤ tau G r z

def EndsAB (a b : V) (R : List V) : Prop := ∃ M, R = M ++ [b, a]

open Classical in
noncomputable def Qset (a b : V) (ω : Perm V) (t : ℕ) : Finset (List V) :=
  (NL V).filter (fun R => QPt G (rank ω) t R ∧ EndsAB a b R)

open Classical in
noncomputable def Dset (a b : V) (ω : Perm V) (t : ℕ) : Finset (List V) :=
  (NL V).filter (fun R => Dang G (rank ω) t R ∧ EndsAB a b R)

noncomputable def PhiY (a b : V) (ω : Perm V) (t : ℕ) : ℝ :=
  ((Qset G a b ω t).card : ℝ) + ((Dset G a b ω t).card : ℝ) / 2

open Classical in
/-- the extension set of a dangerous path -/
noncomputable def Aext (r : V → ℕ) (t : ℕ) (R : List V) : Finset V :=
  Finset.univ.filter (fun w => ∃ z u rest, R = z :: u :: rest ∧ G.Adj z w ∧ w ≠ u ∧ t < r w ∧
    t + 1 ≤ tau G r w)

/-- ranks decrease along a reversed query chain -/
lemma QRel_chain_lt {r : V → ℕ} {x : V} {R : List V} (h : (x :: R).IsChain (QRel G r)) :
    ∀ v ∈ R, r v < r x := by
  have h2 : (x :: R).IsChain (fun a b => r b < r a) := h.imp (fun a b h => h.2.1)
  have h3 : (x :: R).Pairwise (fun a b => r b < r a) := by
    apply List.IsChain.pairwise
    exact h2
  exact (List.pairwise_cons.1 h3).1

section transfer
variable {t : ℕ} {ω ω' : Perm V}

/-- the setting of one exposure step in natural order -/
structure StepSet (ω ω' : Perm V) (t : ℕ) (x : V) : Prop where
  hag : Agree (Finset.Icc 1 t) ω ω'
  hx : rank ω' x = t + 1
  hxω : t < rank ω x

lemma StepSet.le_iff {x : V} (hs : StepSet ω ω' t x) (v : V) : rank ω v ≤ t ↔ rank ω' v ≤ t := by
  constructor
  · intro h; rw [hs.hag v (by simp [h, rank_pos])]; exact h
  · intro h; rw [hs.hag.symm v (by simp [h, rank_pos])]; exact h

lemma StepSet.rank_eq {x : V} (hs : StepSet ω ω' t x) {v : V} (h : rank ω v ≤ t) :
    rank ω' v = rank ω v := hs.hag v (by simp [h, rank_pos])

lemma StepSet.alive {x : V} (hs : StepSet ω ω' t x) (v : V) {s : ℕ} (hst : s ≤ t + 1) :
    s ≤ tau G (rank ω) v ↔ s ≤ tau G (rank ω') v :=
  le_tau_congr G (agreeLE_of_agree hs.hag) v hst

lemma StepSet.gt_of_ne {x : V} (hs : StepSet ω ω' t x) {v : V} (hv : v ≠ x)
    (hvt : t < rank ω v) : t + 1 < rank ω' v := by
  have h1 : ¬ rank ω' v ≤ t := fun h => by rw [← hs.le_iff] at h; omega
  have h2 : rank ω' v ≠ t + 1 := fun h => hv (rank_injective ω' (h.trans hs.hx.symm))
  omega

/-- pairwise transfer of the query relation when the earlier vertex is exposed -/
lemma QRel_transfer {x : V} (hs : StepSet ω ω' t x) {u v : V} (hv : rank ω v ≤ t) :
    QRel G (rank ω) u v ↔ QRel G (rank ω') u v := by
  unfold QRel
  rw [hs.rank_eq hv, hs.alive G u (by omega)]
  have : rank ω v < rank ω u ↔ rank ω v < rank ω' u := by
    by_cases hu : rank ω u ≤ t
    · rw [hs.rank_eq hu]
    · push Not at hu
      have : ¬ rank ω' u ≤ t := fun h => by rw [← hs.le_iff] at h; omega
      constructor <;> intro _ <;> omega
  rw [this]

lemma chain_transfer {x : V} (hs : StepSet ω ω' t x) :
    ∀ R : List V, (∀ v ∈ R.tail, rank ω v ≤ t) →
      (R.IsChain (QRel G (rank ω)) ↔ R.IsChain (QRel G (rank ω'))) := by
  intro R
  induction R with
  | nil => intro _; simp
  | cons y R ih =>
    intro h
    cases R with
    | nil => simp
    | cons z R =>
      rw [List.isChain_cons_cons, List.isChain_cons_cons]
      have hz : rank ω z ≤ t := h z (by simp)
      rw [QRel_transfer G hs hz, ih (fun v hv => h v (by simp at hv ⊢; exact Or.inr hv))]

end transfer

section claims
variable {t : ℕ} {ω ω' : Perm V} {x : V}

lemma claimQ (hs : StepSet ω ω' t x) (R : List V) (h : QPt G (rank ω') (t + 1) R) :
    QPt G (rank ω) t R ∨ (Dang G (rank ω) t R ∧ R[1]? = some x) := by
  obtain ⟨hlen, hch, htail⟩ := h
  match R, hlen, hch, htail with
  | z :: u :: rest', _, hch, htail =>
    by_cases hall : ∀ v ∈ u :: rest', rank ω' v ≤ t
    · left
      have hallω : ∀ v ∈ (z :: u :: rest').tail, rank ω v ≤ t := by
        intro v hv; rw [hs.le_iff]; exact hall v hv
      refine ⟨by simp, (chain_transfer G hs _ hallω).2 hch, hallω⟩
    · right
      push Not at hall
      obtain ⟨v, hv, hvt⟩ := hall
      have hv1 : rank ω' v ≤ t + 1 := htail v hv
      have hvx : v = x := rank_injective ω' (by rw [hs.hx]; omega)
      subst hvx
      have hch' : (u :: rest').IsChain (QRel G (rank ω')) := (List.isChain_cons_cons.1 hch).2
      have hlt := QRel_chain_lt G hch'
      have hux : u = v := by
        rcases List.mem_cons.1 hv with h | h
        · exact h.symm
        · have := hlt v h
          have := htail u (by simp)
          omega
      subst hux
      have hzrel : QRel G (rank ω') z u := (List.isChain_cons_cons.1 hch).1
      refine ⟨⟨z, u, rest', rfl, ?_, hzrel.1, hs.hxω, ?_, ?_⟩, by simp⟩
      · rcases rest' with _ | ⟨w, rest''⟩
        · exact Or.inl rfl
        · right
          have hrestω : ∀ v ∈ (u :: w :: rest'').tail, rank ω v ≤ t := by
            intro v hv'
            rw [hs.le_iff]
            have := hlt v hv'
            rw [hs.hx] at this; omega
          exact ⟨by simp, (chain_transfer G hs _ hrestω).2 hch', hrestω⟩
      · have h1 := hzrel.2.1
        rw [hs.hx] at h1
        by_contra hc; push Not at hc
        rw [hs.le_iff] at hc; omega
      · have h1 := hzrel.2.2
        rw [hs.hx] at h1
        exact (hs.alive G z le_rfl).2 h1

lemma claimD (hs : StepSet ω ω' t x) (R : List V) (h : Dang G (rank ω') (t + 1) R) :
    (Dang G (rank ω) t R ∧ ∀ z u rest, R = z :: u :: rest →
        x ≠ z ∧ x ≠ u ∧ x ∉ Aext G (rank ω) t R) ∨
      (∃ z R₀, R = z :: R₀ ∧ Dang G (rank ω) t R₀ ∧ R₀[1]? = some x ∧
        z ∈ Aext G (rank ω) t R₀) := by
  classical
  obtain ⟨z, u, rest, rfl, hrest, hadj, hu, hz, hzτ⟩ := h
  have huω : t < rank ω u := by
    by_contra hc; push Not at hc; rw [hs.le_iff] at hc; omega
  have hzω : t < rank ω z := by
    by_contra hc; push Not at hc; rw [hs.le_iff] at hc; omega
  have hzτω : t + 1 ≤ tau G (rank ω) z := (hs.alive G z le_rfl).2 (by omega)
  by_cases hall : ∀ v ∈ rest, rank ω' v ≤ t
  · left
    refine ⟨⟨z, u, rest, rfl, ?_, hadj, huω, hzω, hzτω⟩, ?_⟩
    · rcases hrest with h | h
      · exact Or.inl h
      · right
        have hallω : ∀ v ∈ (u :: rest).tail, rank ω v ≤ t := by
          intro v hv; rw [hs.le_iff]; exact hall v hv
        exact ⟨h.1, (chain_transfer G hs _ hallω).2 h.2.1, hallω⟩
    · intro z' u' rest' he
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨fun h => by rw [← h, hs.hx] at hz; omega,
        fun h => by rw [← h, hs.hx] at hu; omega, ?_⟩
      intro hxA
      simp only [Aext, Finset.mem_filter, Finset.mem_univ, true_and] at hxA
      obtain ⟨z'', u'', rest'', he, hzx, hxu, hxt, hxτ⟩ := hxA
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      -- x is alive at t+1, placed at t+1: it joins the MIS and kills z
      have hxτ' : rank ω' x ≤ tau G (rank ω') x := by
        rw [hs.hx]; exact (hs.alive G x le_rfl).1 hxτ
      have := tau_le_of_adj_alive G (rank ω') z x hzx hxτ'
      rw [hs.hx] at this; omega
  · right
    push Not at hall
    obtain ⟨v, hv, hvt⟩ := hall
    rcases hrest with h | h
    · subst h; simp at hv
    obtain ⟨_, hch, htail⟩ := h
    have hv1 : rank ω' v ≤ t + 1 := htail v (by simpa using hv)
    have hvx : v = x := rank_injective ω' (by rw [hs.hx]; omega)
    subst hvx
    -- v must be the newest element of `rest`
    rcases rest with _ | ⟨w, rest''⟩
    · simp at hv
    have hch' : (w :: rest'').IsChain (QRel G (rank ω')) := (List.isChain_cons_cons.1 hch).2
    have hlt := QRel_chain_lt G hch'
    have hwv : w = v := by
      rcases List.mem_cons.1 hv with h | h
      · exact h.symm
      · have := hlt v h
        have := htail w (by simp)
        omega
    subst hwv
    have hurel : QRel G (rank ω') u w := (List.isChain_cons_cons.1 hch).1
    refine ⟨z, u :: w :: rest'', rfl, ⟨u, w, rest'', rfl, ?_, hurel.1, hs.hxω, huω, ?_⟩,
      by simp, ?_⟩
    · rcases rest'' with _ | ⟨y, rest3⟩
      · exact Or.inl rfl
      · right
        have hrestω : ∀ v ∈ (w :: y :: rest3).tail, rank ω v ≤ t := by
          intro v hv'
          rw [hs.le_iff]
          have := hlt v hv'
          rw [hs.hx] at this; omega
        exact ⟨by simp, (chain_transfer G hs _ hrestω).2 hch', hrestω⟩
    · have h1 := hurel.2.2
      rw [hs.hx] at h1
      exact (hs.alive G u le_rfl).2 h1
    · simp only [Aext, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨u, w, rest'', rfl, hadj, fun h => by rw [h, hs.hx] at hz; omega, hzω, hzτω⟩

end claims

section counting
variable {t : ℕ} {ω : Perm V}

lemma endsAB_tail {a b z : V} {R₀ : List V} (h : EndsAB a b (z :: R₀)) (hl : 2 ≤ R₀.length) :
    EndsAB a b R₀ := by
  obtain ⟨M, hM⟩ := h
  rcases M with _ | ⟨m, M'⟩
  · simp at hM; rw [hM.2] at hl; simp at hl
  · simp only [List.cons_append, List.cons.injEq] at hM
    exact ⟨M', hM.2⟩

lemma sum_card_filter_some_le (U : Finset V) (D : Finset (List V)) (f : List V → Option V) :
    ∑ x ∈ U, ((D.filter (fun R => f R = some x)).card : ℝ) ≤ (D.card : ℝ) := by
  classical
  have : ∑ x ∈ U, ((D.filter (fun R => f R = some x)).card : ℝ) =
      ∑ R ∈ D, ((U.filter (fun x => f R = some x)).card : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum]
    rw [Finset.sum_comm]
  rw [this, Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro R _
  have : (U.filter (fun x => f R = some x)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter] at hx hy
    rw [hx.2] at hy; exact Option.some_injective _ hy.2
  simp only [Nat.cast_one]; exact_mod_cast this

lemma dang_props {R : List V} (h : Dang G (rank ω) t R) :
    ∃ z u rest, R = z :: u :: rest ∧ z ∈ unexp (Finset.Icc 1 t) ω ∧
      u ∈ unexp (Finset.Icc 1 t) ω ∧ z ≠ u ∧ Aext G (rank ω) t R ⊆ unexp (Finset.Icc 1 t) ω ∧
      z ∉ Aext G (rank ω) t R ∧ u ∉ Aext G (rank ω) t R := by
  classical
  obtain ⟨z, u, rest, rfl, _, hadj, hu, hz, _⟩ := h
  refine ⟨z, u, rest, rfl, by simp [unexp]; omega, by simp [unexp]; omega, hadj.ne', ?_, ?_, ?_⟩
  · intro w hw
    simp only [Aext, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨_, _, _, _, _, _, hwt, _⟩ := hw
    simp [unexp]; omega
  · intro hz'
    simp only [Aext, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
    obtain ⟨z', u', r', he, hzz, _⟩ := hz'
    simp only [List.cons.injEq] at he
    rw [← he.1] at hzz; exact (G.ne_of_adj hzz) rfl
  · intro hu'
    simp only [Aext, Finset.mem_filter, Finset.mem_univ, true_and] at hu'
    obtain ⟨z', u', r', he, _, hne, _⟩ := hu'
    simp only [List.cons.injEq] at he
    exact hne he.2.1

theorem step_sum (a b : V) (ht : t < Fintype.card V) (ω : Perm V) :
    ∑ x ∈ unexp (Finset.Icc 1 t) ω,
        PhiY G a b (put ω x (t + 1) ⟨by omega, by omega⟩) (t + 1) ≤
      ((unexp (Finset.Icc 1 t) ω).card : ℝ) * PhiY G a b ω t := by
  classical
  have hp : 1 ≤ t + 1 ∧ t + 1 ≤ Fintype.card V := ⟨by omega, by omega⟩
  set U := unexp (Finset.Icc 1 t) ω with hU
  set Q := Qset G a b ω t with hQ
  set D := Dset G a b ω t with hD
  have hstep : ∀ x ∈ U, StepSet ω (put ω x (t + 1) hp) t x := by
    intro x hx
    have hxt : t < rank ω x := by
      have := rank_pos ω x; simp [hU, unexp] at hx; omega
    exact ⟨mem_cls.1 (put_mem_cls ω x (t + 1) hp (by simp) (by simp only [Finset.mem_Icc, not_and, not_le]; intro _; exact hxt)),
      rank_put_self ω x (t + 1) hp, hxt⟩
  -- the bound on the new query paths
  have hQ' : ∀ x ∈ U, ((Qset G a b (put ω x (t + 1) hp) (t + 1)).card : ℝ) ≤
      (Q.card : ℝ) + ((D.filter (fun R => R[1]? = some x)).card : ℝ) := by
    intro x hx
    have hsub : Qset G a b (put ω x (t + 1) hp) (t + 1) ⊆
        Q ∪ D.filter (fun R => R[1]? = some x) := by
      intro R hR
      simp only [Qset, Finset.mem_filter] at hR
      rcases claimQ G (hstep x hx) R hR.2.1 with h | h
      · exact Finset.mem_union_left _ (by simp only [hQ, Qset, Finset.mem_filter]; exact ⟨hR.1, h, hR.2.2⟩)
      · exact Finset.mem_union_right _ (by
          simp only [hD, Dset, Finset.mem_filter]; exact ⟨⟨hR.1, h.1, hR.2.2⟩, h.2⟩)
    calc ((Qset G a b (put ω x (t + 1) hp) (t + 1)).card : ℝ)
        ≤ ((Q ∪ D.filter (fun R => R[1]? = some x)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ _ := by exact_mod_cast Finset.card_union_le _ _
  -- the bound on the new dangerous paths
  have hD' : ∀ x ∈ U, ((Dset G a b (put ω x (t + 1) hp) (t + 1)).card : ℝ) ≤
      ((D.filter (fun R => ∀ z u rest, R = z :: u :: rest →
          x ≠ z ∧ x ≠ u ∧ x ∉ Aext G (rank ω) t R)).card : ℝ) +
        ∑ R₀ ∈ D.filter (fun R => R[1]? = some x), ((Aext G (rank ω) t R₀).card : ℝ) := by
    intro x hx
    have hsub : Dset G a b (put ω x (t + 1) hp) (t + 1) ⊆
        D.filter (fun R => ∀ z u rest, R = z :: u :: rest →
          x ≠ z ∧ x ≠ u ∧ x ∉ Aext G (rank ω) t R) ∪
        (D.filter (fun R => R[1]? = some x)).biUnion
          (fun R₀ => (Aext G (rank ω) t R₀).image (fun w => w :: R₀)) := by
      intro R hR
      simp only [Dset, Finset.mem_filter] at hR
      rcases claimD G (hstep x hx) R hR.2.1 with h | h
      · exact Finset.mem_union_left _ (by
          simp only [hD, Dset, Finset.mem_filter]; exact ⟨⟨hR.1, h.1, hR.2.2⟩, h.2⟩)
      · obtain ⟨z, R₀, rfl, hdang, hpen, hzA⟩ := h
        apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        refine ⟨R₀, ?_, Finset.mem_image.2 ⟨z, hzA, rfl⟩⟩
        have hl : 2 ≤ R₀.length := by
          obtain ⟨_, _, _, he, _⟩ := hdang; rw [he]; simp
        simp only [hD, Dset, Finset.mem_filter]
        refine ⟨⟨?_, hdang, endsAB_tail hR.2.2 hl⟩, hpen⟩
        rw [mem_NL] at hR ⊢
        exact hR.1.of_cons
    calc ((Dset G a b (put ω x (t + 1) hp) (t + 1)).card : ℝ)
        ≤ ((D.filter (fun R => ∀ z u rest, R = z :: u :: rest →
            x ≠ z ∧ x ≠ u ∧ x ∉ Aext G (rank ω) t R) ∪
          (D.filter (fun R => R[1]? = some x)).biUnion
            (fun R₀ => (Aext G (rank ω) t R₀).image (fun w => w :: R₀))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((D.filter (fun R => ∀ z u rest, R = z :: u :: rest →
            x ≠ z ∧ x ≠ u ∧ x ∉ Aext G (rank ω) t R)).card : ℝ) +
          (((D.filter (fun R => R[1]? = some x)).biUnion
            (fun R₀ => (Aext G (rank ω) t R₀).image (fun w => w :: R₀))).card : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ _ := by
          gcongr
          refine (Nat.cast_le.2 Finset.card_biUnion_le).trans ?_
          push_cast
          apply Finset.sum_le_sum
          intro R₀ _
          exact_mod_cast Finset.card_image_le
  -- sum over x
  have hsumQ : ∑ x ∈ U, ((Qset G a b (put ω x (t + 1) hp) (t + 1)).card : ℝ) ≤
      (U.card : ℝ) * Q.card + D.card := by
    calc ∑ x ∈ U, ((Qset G a b (put ω x (t + 1) hp) (t + 1)).card : ℝ)
        ≤ ∑ x ∈ U, ((Q.card : ℝ) + ((D.filter (fun R => R[1]? = some x)).card : ℝ)) :=
          Finset.sum_le_sum hQ'
      _ = (U.card : ℝ) * Q.card + ∑ x ∈ U, ((D.filter (fun R => R[1]? = some x)).card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by linarith [sum_card_filter_some_le U D (fun R => R[1]?)]
  have hsumD : ∑ x ∈ U, ((Dset G a b (put ω x (t + 1) hp) (t + 1)).card : ℝ) ≤
      ((U.card : ℝ) - 2) * D.card := by
    refine (Finset.sum_le_sum hD').trans ?_
    rw [Finset.sum_add_distrib]
    -- first part
    have h1 : ∑ x ∈ U, ((D.filter (fun R => ∀ z u rest, R = z :: u :: rest →
          x ≠ z ∧ x ≠ u ∧ x ∉ Aext G (rank ω) t R)).card : ℝ) =
        ∑ R ∈ D, ((U.filter (fun x => ∀ z u rest, R = z :: u :: rest →
          x ≠ z ∧ x ≠ u ∧ x ∉ Aext G (rank ω) t R)).card : ℝ) := by
      simp only [Finset.card_filter, Nat.cast_sum]
      rw [Finset.sum_comm]
    have h2 : ∑ x ∈ U, ∑ R₀ ∈ D.filter (fun R => R[1]? = some x),
          ((Aext G (rank ω) t R₀).card : ℝ) =
        ∑ R ∈ D, ∑ x ∈ U, (if R[1]? = some x then ((Aext G (rank ω) t R).card : ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.sum_filter]
    rw [h1, h2, ← Finset.sum_add_distrib, show ((U.card : ℝ) - 2) * D.card =
      ∑ R ∈ D, ((U.card : ℝ) - 2) by rw [Finset.sum_const, nsmul_eq_mul]; ring]
    apply Finset.sum_le_sum
    intro R hR
    have hR' : Dang G (rank ω) t R := by
      simp only [hD, Dset, Finset.mem_filter] at hR; exact hR.2.1
    obtain ⟨z, u, rest, he, hzU, huU, hzu, hAU, hzA, huA⟩ := dang_props G hR'
    -- the good placements avoid `z`, `u` and the extension set
    have hsub : U.filter (fun x => ∀ z u rest, R = z :: u :: rest →
        x ≠ z ∧ x ≠ u ∧ x ∉ Aext G (rank ω) t R) ⊆
        U \ (insert z (insert u (Aext G (rank ω) t R))) := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      obtain ⟨h1, h2, h3⟩ := hx.2 z u rest he
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
      exact ⟨hx.1, h1, h2, h3⟩
    have hins : insert z (insert u (Aext G (rank ω) t R)) ⊆ U := by
      intro y hy
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | rfl | hy
      · exact hzU
      · exact huU
      · exact hAU hy
    have hcard_ins : (insert z (insert u (Aext G (rank ω) t R))).card =
        (Aext G (rank ω) t R).card + 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem huA]
      simp only [Finset.mem_insert, not_or]; exact ⟨hzu, hzA⟩
    have hA1 : ((U.filter (fun x => ∀ z u rest, R = z :: u :: rest →
        x ≠ z ∧ x ≠ u ∧ x ∉ Aext G (rank ω) t R)).card : ℝ) ≤
        (U.card : ℝ) - 2 - (Aext G (rank ω) t R).card := by
      have := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset hins, hcard_ins] at this
      have hle := Finset.card_le_card hins
      rw [hcard_ins] at hle
      have : (((U.filter (fun x => ∀ z u rest, R = z :: u :: rest →
        x ≠ z ∧ x ≠ u ∧ x ∉ Aext G (rank ω) t R)).card : ℕ) : ℝ) ≤
          ((U.card - ((Aext G (rank ω) t R).card + 2) : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub hle] at this; push_cast at this; linarith
    have hA2 : ∑ x ∈ U, (if R[1]? = some x then ((Aext G (rank ω) t R).card : ℝ) else 0) ≤
        ((Aext G (rank ω) t R).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have : (U.filter (fun x => R[1]? = some x)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        simp only [Finset.mem_filter] at hx hy
        rw [hx.2] at hy; exact Option.some_injective _ hy.2
      have h' : ((U.filter (fun x => R[1]? = some x)).card : ℝ) ≤ 1 := by exact_mod_cast this
      nlinarith [(by positivity : (0 : ℝ) ≤ (Aext G (rank ω) t R).card)]
    linarith
  unfold PhiY
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  have : ((U.card : ℝ)) * ((Q.card : ℝ) + (D.card : ℝ) / 2) =
      (U.card : ℝ) * Q.card + D.card + ((U.card : ℝ) - 2) * D.card / 2 := by ring
  rw [← hQ, ← hD, this]
  linarith

end counting

section final
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma cls_full_eq {ω ω' : Perm V} (h : ω' ∈ cls (Finset.Icc 1 (Fintype.card V)) ω) : ω' = ω := by
  have hag := mem_cls.1 h
  ext v
  have := hag v (by simp [rank_pos, rank_le])
  simp only [rank, add_left_inj] at this
  exact this

theorem phi_supermart (a b : V) :
    ∀ k t, t + k = Fintype.card V → ∀ ω : Perm V,
      cexp (fun ω => PhiY G a b ω (Fintype.card V)) (Finset.Icc 1 t) ω ≤ PhiY G a b ω t := by
  intro k
  induction k with
  | zero =>
    intro t ht ω
    rw [show t = Fintype.card V by omega]
    rw [cexp_of_determined _ _ _ (fun ω' hω' => by rw [cls_full_eq hω'])]
  | succ k ih =>
    intro t ht ω
    have hp : 1 ≤ t + 1 ∧ t + 1 ≤ Fintype.card V := ⟨by omega, by omega⟩
    rw [cexp_step _ ω (t + 1) hp (by simp), Icc_insert]
    have hm : 0 < ((unexp (Finset.Icc 1 t) ω).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 (unexp_nonempty_of ω (t + 1) hp (by simp))
    rw [div_le_iff₀ hm]
    calc ∑ x ∈ unexp (Finset.Icc 1 t) ω,
          cexp (fun ω => PhiY G a b ω (Fintype.card V)) (Finset.Icc 1 (t + 1)) (put ω x (t + 1) hp)
        ≤ ∑ x ∈ unexp (Finset.Icc 1 t) ω, PhiY G a b (put ω x (t + 1) hp) (t + 1) :=
          Finset.sum_le_sum (fun x _ => ih (t + 1) (by omega) _)
      _ ≤ ((unexp (Finset.Icc 1 t) ω).card : ℝ) * PhiY G a b ω t := step_sum G a b (by omega) ω
      _ = _ := by ring

lemma phi_zero_le (a b : V) (ω : Perm V) : PhiY G a b ω 0 ≤ 1 / 2 := by
  classical
  have hQ : Qset G a b ω 0 = ∅ := by
    ext R
    simp only [Qset, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro _ hq
    obtain ⟨hl, _, ht⟩ := hq
    rcases R with _ | ⟨z, _ | ⟨u, rest⟩⟩
    · simp at hl
    · simp at hl
    · have := ht u (by simp); have := rank_pos ω u; omega
  have hD : Dset G a b ω 0 ⊆ {[b, a]} := by
    intro R hR
    simp only [Dset, Finset.mem_filter] at hR
    obtain ⟨_, ⟨z, u, rest, rfl, hrest, _⟩, M, hM⟩ := hR
    rcases hrest with rfl | hq
    · rcases M with _ | ⟨m, M'⟩
      · simp at hM; simp [hM.1, hM.2]
      · have := congrArg List.length hM; simp at this
    · obtain ⟨hl, _, ht⟩ := hq
      rcases rest with _ | ⟨w, rest'⟩
      · simp at hl
      · have := ht w (by simp); have := rank_pos ω w; omega
  unfold PhiY
  rw [hQ]
  have := Finset.card_le_card hD
  simp only [Finset.card_singleton] at this
  have h' : ((Dset G a b ω 0).card : ℝ) ≤ 1 := by exact_mod_cast this
  simp; linarith

theorem expect_Qn_le (a b : V) :
    NoSignalPA.uniformExp (fun ω : Perm V => ((Qset G a b ω (Fintype.card V)).card : ℝ)) ≤ 1 / 2 := by
  obtain ⟨ω₀⟩ : Nonempty (Perm V) := ⟨Fintype.equivFin V⟩
  rw [uniformExp_eq_cexp _ ω₀]
  have h1 := phi_supermart G a b (Fintype.card V) 0 (by simp) ω₀
  have e : Finset.Icc 1 0 = (∅ : Finset ℕ) := by simp
  rw [e] at h1
  refine le_trans (cexp_mono (fun ω => ?_) _ _) (h1.trans (phi_zero_le G a b ω₀))
  unfold PhiY
  have : (0 : ℝ) ≤ ((Dset G a b ω (Fintype.card V)).card : ℝ) / 2 := by positivity
  linarith

lemma chain_and {α : Type*} {R S : α → α → Prop} {l : List α} (h1 : l.IsChain R) (h2 : l.IsChain S) :
    l.IsChain (fun a b => R a b ∧ S a b) := by
  rw [List.isChain_iff_getElem] at *
  intro i hi; exact ⟨h1 i hi, h2 i hi⟩

lemma sum_card_filter_eq_some_le {α β : Type*} [DecidableEq β] (U : Finset β) (D : Finset α)
    (f : α → Option β) :
    ∑ x ∈ U, ((D.filter (fun R => f R = some x)).card : ℝ) ≤ (D.card : ℝ) := by
  classical
  have : ∑ x ∈ U, ((D.filter (fun R => f R = some x)).card : ℝ) =
      ∑ R ∈ D, ((U.filter (fun x => f R = some x)).card : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum]
    rw [Finset.sum_comm]
  rw [this, Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro R _
  have : (U.filter (fun x => f R = some x)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter] at hx hy
    rw [hx.2] at hy; exact Option.some_injective _ hy.2
  simp only [Nat.cast_one]; exact_mod_cast this

lemma Z_le (ω : Perm V) :
    (Z G (rank ω) : ℝ) ≤ Fintype.card V +
      ∑ a, ∑ b ∈ G.neighborFinset a, ((Qset G a b ω (Fintype.card V)).card : ℝ) := by
  classical
  have hr := rank_injective ω
  set QP := (Finset.univ : Finset (Finset V)).filter
    (fun U => IsQueryPath G (rank ω) (RGMISFast.scanOrder (rank ω) U)) with hQP
  -- Z ≤ #QP
  have h1 : (Z G (rank ω) : ℝ) ≤ QP.card := by
    unfold Z T
    push_cast
    have := sum_card_filter_eq_some_le (Finset.univ : Finset V) QP
      (fun U => (RGMISFast.scanOrder (rank ω) U).getLast?)
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl
    intro v _
    rw [hQP, Finset.filter_filter]
  -- split by size
  have h2 : (QP.card : ℝ) ≤ (QP.filter (fun U => U.card ≤ 1)).card +
      (QP.filter (fun U => ¬ U.card ≤ 1)).card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not _).ge
  have h3 : (QP.filter (fun U => U.card ≤ 1)).card ≤ Fintype.card V := by
    have hsub : QP.filter (fun U => U.card ≤ 1) ⊆
        (Finset.univ : Finset V).image (fun v => ({v} : Finset V)) := by
      intro U hU
      simp only [hQP, Finset.mem_filter, Finset.mem_univ, true_and] at hU
      have hne : U.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        subst h
        have := hU.1.1.1
        apply this
        have := (scanOrder_spec (rank ω) hr ∅).2.2
        simpa using this
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 (le_antisymm hU.2 (Finset.card_pos.2 hne))
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨v, rfl⟩
    calc (QP.filter (fun U => U.card ≤ 1)).card
        ≤ ((Finset.univ : Finset V).image (fun v => ({v} : Finset V))).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset V).card := Finset.card_image_le
      _ = Fintype.card V := Finset.card_univ
  have h4 : ((QP.filter (fun U => ¬ U.card ≤ 1)).card : ℝ) ≤
      ∑ a, ∑ b ∈ G.neighborFinset a, ((Qset G a b ω (Fintype.card V)).card : ℝ) := by
    set T := (Finset.univ : Finset V).biUnion
      (fun a => (G.neighborFinset a).biUnion (fun b => Qset G a b ω (Fintype.card V))) with hT
    have hinj : ((QP.filter (fun U => ¬ U.card ≤ 1)).card : ℝ) ≤ T.card := by
      apply Nat.cast_le.2
      apply Finset.card_le_card_of_injOn (fun U => (RGMISFast.scanOrder (rank ω) U).reverse)
      · intro U hU
        simp only [Finset.coe_filter, hQP, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq, not_le] at hU
        obtain ⟨hqp, hcard⟩ := hU
        obtain ⟨hpw, hnd, hlen⟩ := scanOrder_spec (rank ω) hr U
        generalize hl : RGMISFast.scanOrder (rank ω) U = l at hqp hpw hnd hlen ⊢
        rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · simp at hlen; omega
        · simp at hlen; omega
        show (RGMISFast.scanOrder (rank ω) U).reverse ∈ T
        rw [hl]
        have hab : G.Adj a b := (List.isChain_cons_cons.1 hqp.1.2).1.1
        rw [hT, Finset.mem_biUnion]
        refine ⟨a, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_biUnion]
        refine ⟨b, (SimpleGraph.mem_neighborFinset _ _ _).2 hab, ?_⟩
        simp only [Qset, Finset.mem_filter]
        refine ⟨mem_NL.2 (List.nodup_reverse.2 hnd), ⟨?_, ?_, ?_⟩, ⟨rest.reverse, by simp⟩⟩
        · simp
        · rw [List.isChain_reverse]
          have := chain_and hqp.1.2 hqp.2
          exact List.IsChain.imp (fun x y (h : (G.Adj x y ∧ rank ω x < rank ω y) ∧
            rank ω x ≤ tau G (rank ω) y) => (⟨h.1.1, h.1.2, h.2⟩ : QRel G (rank ω) y x)) this
        · intro v _; exact rank_le ω v
      · intro U _ U' _ h
        have h' : RGMISFast.scanOrder (rank ω) U = RGMISFast.scanOrder (rank ω) U' :=
          List.reverse_injective h
        ext v
        rw [← mem_scanOrder (rank ω) U v, ← mem_scanOrder (rank ω) U' v, h']
    refine hinj.trans ?_
    calc (T.card : ℝ) ≤ ∑ a, (((G.neighborFinset a).biUnion
          (fun b => Qset G a b ω (Fintype.card V))).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro a _
          exact_mod_cast Finset.card_biUnion_le
  have h3' : ((QP.filter (fun U => U.card ≤ 1)).card : ℝ) ≤ Fintype.card V := by exact_mod_cast h3
  linarith

theorem lemma_2_11_proof :
    NoSignalPA.uniformExp (fun ω : Perm V => (Z G (rank ω) : ℝ)) ≤
      (Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ) := by
  classical
  have hmono : NoSignalPA.uniformExp (fun ω : Perm V => (Z G (rank ω) : ℝ)) ≤
      NoSignalPA.uniformExp (fun ω : Perm V => (Fintype.card V : ℝ) +
        ∑ a, ∑ b ∈ G.neighborFinset a, ((Qset G a b ω (Fintype.card V)).card : ℝ)) := by
    unfold NoSignalPA.uniformExp
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum (fun ω _ => Z_le G ω)
  refine hmono.trans ?_
  have hlin : NoSignalPA.uniformExp (fun ω : Perm V => (Fintype.card V : ℝ) +
        ∑ a, ∑ b ∈ G.neighborFinset a, ((Qset G a b ω (Fintype.card V)).card : ℝ)) =
      (Fintype.card V : ℝ) + ∑ a, ∑ b ∈ G.neighborFinset a,
        NoSignalPA.uniformExp (fun ω : Perm V => ((Qset G a b ω (Fintype.card V)).card : ℝ)) := by
    unfold NoSignalPA.uniformExp
    have hpos : (0 : ℝ) < Fintype.card (Perm V) := by
      exact_mod_cast Fintype.card_pos_iff.2 ⟨Fintype.equivFin V⟩
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div,
      mul_div_cancel_left₀ _ hpos.ne']
    congr 1
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm, Finset.sum_div]
  rw [hlin]
  have hb : ∑ a, ∑ b ∈ G.neighborFinset a,
      NoSignalPA.uniformExp (fun ω : Perm V => ((Qset G a b ω (Fintype.card V)).card : ℝ)) ≤
      ∑ a, ∑ b ∈ G.neighborFinset a, (1 / 2 : ℝ) := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    exact expect_Qn_le G a b
  have hdeg : ∑ a : V, ∑ b ∈ G.neighborFinset a, (1 / 2 : ℝ) = G.edgeFinset.card := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_mul]
    have := G.sum_degrees_eq_twice_card_edges
    have h' : (∑ a : V, ((G.neighborFinset a).card : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
      simp only [SimpleGraph.card_neighborFinset_eq_degree]; exact_mod_cast this
    rw [h']; ring
  linarith

end final

end yyi

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM
open QueryDepthMIS RGMISFast

section markov
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma coinProb_markov (f : Perm V → ℝ) (hf : ∀ ω, 0 ≤ f ω) (c : ℝ) (hc : 0 < c) :
    PunctSketch.coinProb (fun ω => c < f ω) ≤ NoSignalPA.uniformExp f / c := by
  classical
  unfold PunctSketch.coinProb NoSignalPA.uniformExp
  rw [div_div, mul_comm, ← div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [le_div_iff₀ hc, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with h
  · simp; linarith
  · simp; exact hf ω

lemma edges_le (n : ℕ) (hn : Fintype.card V = n) :
    (Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  have h := G.card_edgeFinset_le_card_choose_two
  rw [Nat.choose_two_right] at h
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | h0
  · have : G.edgeFinset.card = 0 := by
      have := h; rw [h0] at this; simpa using this
    simp [h0, this]
  have h2 : (G.edgeFinset.card : ℝ) ≤ ((Fintype.card V * (Fintype.card V - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast h
  have h3 : ((Fintype.card V * (Fintype.card V - 1) / 2 : ℕ) : ℝ) ≤
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2 := by
    calc ((Fintype.card V * (Fintype.card V - 1) / 2 : ℕ) : ℝ)
        ≤ ((Fintype.card V * (Fintype.card V - 1) : ℕ) : ℝ) / 2 := Nat.cast_div_le
      _ = _ := by rw [Nat.cast_mul, Nat.cast_sub h0]; simp
  have h1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast h0
  nlinarith

theorem corollary_2_12_proof (hn : 2 ≤ Fintype.card V) :
    PunctSketch.coinProb (fun ω : Perm V => Fintype.card V ^ 9 < Z G (rank ω)) ≤
      1 / (Fintype.card V : ℝ) ^ 7 := by
  have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (Fintype.card V : ℝ) ^ 9 := by positivity
  have h1 : PunctSketch.coinProb (fun ω : Perm V => Fintype.card V ^ 9 < Z G (rank ω)) =
      PunctSketch.coinProb (fun ω : Perm V => (Fintype.card V : ℝ) ^ 9 < (Z G (rank ω) : ℝ)) := by
    unfold PunctSketch.coinProb
    congr 3
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact_mod_cast Iff.rfl
  rw [h1]
  refine (coinProb_markov (fun ω => (Z G (rank ω) : ℝ)) (fun ω => by positivity) _ hpos).trans ?_
  have h2 := lemma_2_11_proof G
  have h3 := edges_le G _ rfl
  rw [div_le_div_iff₀ hpos (by positivity)]
  have : NoSignalPA.uniformExp (fun ω : Perm V => (Z G (rank ω) : ℝ)) ≤ (Fintype.card V : ℝ) ^ 2 :=
    h2.trans h3
  calc NoSignalPA.uniformExp (fun ω : Perm V => (Z G (rank ω) : ℝ)) * (Fintype.card V : ℝ) ^ 7
      ≤ (Fintype.card V : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 7 :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = 1 * (Fintype.card V : ℝ) ^ 9 := by ring

end markov

section shortcut
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- index order agrees with rank order in a rank-sorted list -/
lemma sorted_idx_lt {r : V → ℕ} {l : List V} (hl : l.Pairwise (fun a b => r a < r b))
    {a b : ℕ} (ha : a < l.length) (hb : b < l.length) (h : r l[a] < r l[b]) : a < b := by
  rw [List.pairwise_iff_getElem] at hl
  by_contra hc
  push Not at hc
  rcases Nat.eq_or_lt_of_le hc with e | e
  · subst e; omega
  · have := hl b a hb ha e; omega

/-- consecutive-pair criterion for query paths -/
lemma qp_of_consec (r : V → ℕ) (hr : Function.Injective r) (U : Finset V) (hU : U.Nonempty)
    (h : ∀ x ∈ U, ∀ y ∈ U, r x < r y → (∀ z ∈ U, ¬ (r x < r z ∧ r z < r y)) →
      G.Adj x y ∧ r x ≤ tau G r y) :
    IsQueryPath G r (scanOrder r U) := by
  obtain ⟨hpw, hnd, hlen⟩ := scanOrder_spec r hr U
  have hpw' := List.pairwise_iff_getElem.1 hpw
  have hmem : ∀ i (hi : i < (scanOrder r U).length), (scanOrder r U)[i] ∈ U := by
    intro i hi; rw [← mem_scanOrder r U]; exact List.getElem_mem _
  have key : ∀ i (hi : i + 1 < (scanOrder r U).length),
      G.Adj (scanOrder r U)[i] (scanOrder r U)[i + 1] ∧
        r (scanOrder r U)[i] ≤ tau G r (scanOrder r U)[i + 1] := by
    intro i hi
    apply h _ (hmem i (by omega)) _ (hmem (i + 1) hi) (hpw' i (i + 1) (by omega) hi (by omega))
    intro z hz ⟨h1, h2⟩
    rw [← mem_scanOrder r U] at hz
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hz
    have := sorted_idx_lt hpw (by omega) hk h1
    have := sorted_idx_lt hpw hk hi h2
    omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro he
    rw [he] at hlen
    simp at hlen
    exact (Finset.card_pos.2 hU).ne' hlen.symm
  · rw [List.isChain_iff_getElem]
    intro i hi
    exact ⟨(key i hi).1, hpw' i (i + 1) (by omega) hi (by omega)⟩
  · rw [List.isChain_iff_getElem]
    intro i hi
    exact (key i hi).2

lemma qp_sorted {r : V → ℕ} {l : List V} (hl : IsQueryPath G r l) :
    l.Pairwise (fun a b => r a < r b) := by
  apply List.IsChain.pairwise
  exact hl.1.2.imp (fun a b h => h.2)

/-- the doubling lemma: a query path with a set `D` of pairwise non-consecutive shortcut indices
yields `2^|D|` distinct query paths -/
theorem many_qp (r : V → ℕ) (hr : Function.Injective r) (l : List V) (hl : IsQueryPath G r l)
    (D : Finset ℕ) (hD : D ⊆ shortcutIdx G l) (hcons : ∀ i ∈ D, i + 1 ∉ D) :
    2 ^ D.card ≤ ((Finset.univ : Finset (Finset V)).filter
      (fun U => IsQueryPath G r (scanOrder r U))).card := by
  classical
  have hpw := qp_sorted G hl
  have hnd : l.Nodup := hpw.imp (fun h e => by rw [e] at h; exact lt_irrefl _ h)
  have hD' : ∀ i ∈ D, i + 2 < l.length := by
    intro i hi
    have := hD hi
    simp only [shortcutIdx, Finset.mem_filter] at this
    obtain ⟨h2, _⟩ := this.2; exact h2
  -- the middle vertices
  let mid : Finset ℕ → Finset V := fun D' => D'.biUnion (fun i => (l[i + 1]?).toFinset)
  have hmid : ∀ D' ⊆ D, ∀ v, v ∈ mid D' ↔ ∃ i ∈ D', ∃ hi : i + 1 < l.length, l[i + 1] = v := by
    intro D' hD'sub v
    simp only [mid, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]
    constructor
    · rintro ⟨i, hi, he⟩
      have hlt : i + 1 < l.length := by have := hD' i (hD'sub hi); omega
      rw [List.getElem?_eq_getElem hlt] at he
      exact ⟨i, hi, hlt, Option.some_injective _ he⟩
    · rintro ⟨i, hi, hlt, he⟩
      exact ⟨i, hi, by rw [List.getElem?_eq_getElem hlt, he]⟩
  let Uf : Finset ℕ → Finset V := fun D' => l.toFinset \ mid D'
  have hinj : Set.InjOn Uf (D.powerset : Set (Finset ℕ)) := by
    intro D₁ h₁ D₂ h₂ he
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at h₁ h₂
    have hm : ∀ D' ⊆ D, mid D' ⊆ l.toFinset := by
      intro D' hsub v hv
      obtain ⟨i, _, hlt, rfl⟩ := (hmid D' hsub v).1 hv
      simp
    have hmeq : mid D₁ = mid D₂ := by
      have e1 : mid D₁ = l.toFinset \ Uf D₁ := by
        simp only [Uf]; rw [Finset.sdiff_sdiff_eq_self (hm D₁ h₁)]
      have e2 : mid D₂ = l.toFinset \ Uf D₂ := by
        simp only [Uf]; rw [Finset.sdiff_sdiff_eq_self (hm D₂ h₂)]
      rw [e1, e2, he]
    ext i
    constructor
    · intro hi
      have hlt : i + 1 < l.length := by have := hD' i (h₁ hi); omega
      have : l[i + 1] ∈ mid D₂ := by rw [← hmeq]; exact (hmid D₁ h₁ _).2 ⟨i, hi, hlt, rfl⟩
      obtain ⟨j, hj, hlt', he'⟩ := (hmid D₂ h₂ _).1 this
      have := (List.Nodup.getElem_inj_iff hnd).1 he'
      have hij : j = i := by omega
      rw [← hij]; exact hj
    · intro hi
      have hlt : i + 1 < l.length := by have := hD' i (h₂ hi); omega
      have : l[i + 1] ∈ mid D₁ := by rw [hmeq]; exact (hmid D₂ h₂ _).2 ⟨i, hi, hlt, rfl⟩
      obtain ⟨j, hj, hlt', he'⟩ := (hmid D₁ h₁ _).1 this
      have := (List.Nodup.getElem_inj_iff hnd).1 he'
      have hij : j = i := by omega
      rw [← hij]; exact hj
  have hmaps : ∀ D' ∈ D.powerset, Uf D' ∈ (Finset.univ : Finset (Finset V)).filter
      (fun U => IsQueryPath G r (scanOrder r U)) := by
    intro D' hD'
    rw [Finset.mem_powerset] at hD'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hl0 : 0 < l.length := by
      rcases l with _ | ⟨a, l⟩
      · exact absurd rfl hl.1.1
      · simp
    have hpw' := List.pairwise_iff_getElem.1 hpw
    -- membership in `Uf D'`
    have hmemU : ∀ k (hk : k < l.length), l[k] ∈ Uf D' ↔ ¬ (∃ i ∈ D', i + 1 = k) := by
      intro k hk
      simp only [Uf, Finset.mem_sdiff, List.mem_toFinset, List.getElem_mem, true_and,
        hmid D' hD']
      constructor
      · rintro h ⟨i, hi, rfl⟩; exact h ⟨i, hi, hk, rfl⟩
      · rintro h ⟨i, hi, hlt, he⟩
        have := (List.Nodup.getElem_inj_iff hnd).1 he
        exact h ⟨i, hi, this⟩
    apply qp_of_consec G r hr
    · refine ⟨l[0], (hmemU 0 hl0).2 ?_⟩
      rintro ⟨i, _, h⟩; omega
    · intro x hx y hy hxy hbetw
      have hxl : x ∈ l := by simp only [Uf, Finset.mem_sdiff, List.mem_toFinset] at hx; exact hx.1
      have hyl : y ∈ l := by simp only [Uf, Finset.mem_sdiff, List.mem_toFinset] at hy; exact hy.1
      obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 hxl
      obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.1 hyl
      have hab := sorted_idx_lt hpw ha hb hxy
      -- a vertex strictly between in the list is removed
      have hrem : ∀ k (hk : k < l.length), a < k → k < b → ∃ i ∈ D', i + 1 = k := by
        intro k hk h1 h2
        by_contra hc
        exact hbetw _ ((hmemU k hk).2 hc) ⟨hpw' a k ha hk h1, hpw' k b hk hb h2⟩
      have hchain := List.isChain_iff_getElem.1 hl.1.2
      have hchain2 := List.isChain_iff_getElem.1 hl.2
      rcases Nat.lt_or_ge (a + 1) b with h1 | h1
      · -- b ≥ a + 2: the vertex a+1 is removed, so a ∈ D'
        obtain ⟨i, hi, hia⟩ := hrem (a + 1) (by omega) (by omega) h1
        have hiaa : i = a := by omega
        subst hiaa
        have hb2 : b = i + 2 := by
          by_contra hne
          obtain ⟨j, hj, hja⟩ := hrem (i + 2) (by omega) (by omega) (by omega)
          have : j = i + 1 := by omega
          subst this
          exact hcons i (hD'.trans (le_refl _) hi) (hD' hj)
        subst hb2
        have hsc := hD (hD' hi)
        simp only [shortcutIdx, Finset.mem_filter] at hsc
        obtain ⟨_, hadj⟩ := hsc.2
        refine ⟨hadj, ?_⟩
        have h1 := (hchain2 (i + 1) (by omega))
        have h2 := hpw' i (i + 1) (by omega) (by omega) (by omega)
        exact le_trans h2.le h1
      · have hb1 : b = a + 1 := by omega
        subst hb1
        exact ⟨(hchain a hb).1, hchain2 a hb⟩
  have := Finset.card_le_card_of_injOn Uf hmaps hinj
  rw [Finset.card_powerset] at this
  exact this

lemma Z_ge_qp (r : V → ℕ) (hr : Function.Injective r) :
    ((Finset.univ : Finset (Finset V)).filter
      (fun U => IsQueryPath G r (scanOrder r U))).card ≤ Z G r := by
  classical
  unfold Z T
  set QP := (Finset.univ : Finset (Finset V)).filter (fun U => IsQueryPath G r (scanOrder r U))
  have hsub : QP ⊆ (Finset.univ : Finset V).biUnion
      (fun v => QP.filter (fun U => (scanOrder r U).getLast? = some v)) := by
    intro U hU
    rw [Finset.mem_biUnion]
    have hne : scanOrder r U ≠ [] := by
      simp only [QP, Finset.mem_filter] at hU; exact hU.2.1.1
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (by
      intro h; exact hne (List.getLast?_eq_none_iff.1 h))
    exact ⟨v, Finset.mem_univ _, Finset.mem_filter.2 ⟨hU, hv⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (le_of_eq ?_))
  apply Finset.sum_congr rfl
  intro v _
  simp only [QP, Finset.filter_filter]

/-- a query path with more than `h` shortcuts forces many query paths -/
lemma Z_ge_of_shortcuts (r : V → ℕ) (hr : Function.Injective r) (l : List V)
    (hl : IsQueryPath G r l) : (2 : ℝ) ^ (((shortcutIdx G l).card : ℝ) / 2) ≤ Z G r := by
  classical
  set C := shortcutIdx G l
  have hsplit := Finset.card_filter_add_card_filter_not (s := C) (fun i => Even i)
  have hcons_e : ∀ i ∈ C.filter (fun i => Even i), i + 1 ∉ C.filter (fun i => Even i) := by
    intro i hi hi1
    simp only [Finset.mem_filter] at hi hi1
    exact (Nat.even_add_one.1 hi1.2) hi.2
  have hcons_o : ∀ i ∈ C.filter (fun i => ¬ Even i), i + 1 ∉ C.filter (fun i => ¬ Even i) := by
    intro i hi hi1
    simp only [Finset.mem_filter] at hi hi1
    exact hi1.2 (Nat.even_add_one.2 hi.2)
  have he := many_qp G r hr l hl _ (Finset.filter_subset _ _) hcons_e
  have ho := many_qp G r hr l hl _ (Finset.filter_subset _ _) hcons_o
  have hZ := Z_ge_qp G r hr
  set e := (C.filter (fun i => Even i)).card
  set o := (C.filter (fun i => ¬ Even i)).card
  have hmax : ((C.card : ℝ)) / 2 ≤ max (e : ℝ) (o : ℝ) := by
    have : (C.card : ℝ) = e + o := by exact_mod_cast hsplit.symm
    rw [this]
    rcases le_total (e : ℝ) o with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (2 : ℝ) ^ ((C.card : ℝ) / 2) ≤ (2 : ℝ) ^ (max (e : ℝ) (o : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hmax
    _ ≤ Z G r := by
        rcases le_total (e : ℝ) o with h | h
        · rw [max_eq_right h, Real.rpow_natCast]
          exact_mod_cast ho.trans hZ
        · rw [max_eq_left h, Real.rpow_natCast]
          exact_mod_cast he.trans hZ

theorem lemma_3_4_part1 (h : ℕ) :
    PunctSketch.coinProb (fun ω : Perm V => ∃ l : List V, IsQueryPath G (rank ω) l ∧
        h < (shortcutIdx G l).card) ≤
      ((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ)) * (2 : ℝ) ^ (-(h : ℝ) / 2) := by
  classical
  have hc : (0 : ℝ) < (2 : ℝ) ^ ((h : ℝ) / 2) := by positivity
  have hsub : PunctSketch.coinProb (fun ω : Perm V => ∃ l : List V, IsQueryPath G (rank ω) l ∧
        h < (shortcutIdx G l).card) ≤
      PunctSketch.coinProb (fun ω : Perm V => (2 : ℝ) ^ ((h : ℝ) / 2) < (Z G (rank ω) : ℝ)) := by
    obtain ⟨ω₀⟩ : Nonempty (Perm V) := ⟨Fintype.equivFin V⟩
    rw [coinProb_eq_condProb _ ω₀, coinProb_eq_condProb _ ω₀]
    apply condProb_mono
    rintro ω ⟨l, hl, hh⟩
    refine lt_of_lt_of_le ?_ (Z_ge_of_shortcuts G (rank ω) (rank_injective ω) l hl)
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    have : (h : ℝ) < (shortcutIdx G l).card := by exact_mod_cast hh
    linarith
  refine hsub.trans ((coinProb_markov (fun ω => (Z G (rank ω) : ℝ)) (fun ω => by positivity) _
    hc).trans ?_)
  rw [div_le_iff₀ hc, mul_assoc, ← Real.rpow_add (by norm_num)]
  have : -(h : ℝ) / 2 + (h : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero, mul_one]
  exact lemma_2_11_proof G

theorem lemma_3_4_part2 (hn : 2 ≤ Fintype.card V) :
    1 - 1 / (Fintype.card V : ℝ) ^ 7 ≤
      PunctSketch.coinProb (fun ω : Perm V => ∀ l : List V, IsQueryPath G (rank ω) l →
        (shortcutIdx G l).card ≤ ⌈18 * Real.logb 2 (Fintype.card V : ℝ)⌉₊) := by
  classical
  obtain ⟨ω₀⟩ : Nonempty (Perm V) := ⟨Fintype.equivFin V⟩
  have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  set h := ⌈18 * Real.logb 2 (Fintype.card V : ℝ)⌉₊ with hh
  have h1 := lemma_3_4_part1 G h
  have h2 := edges_le G _ rfl
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  have hpow : (2 : ℝ) ^ (-(h : ℝ) / 2) ≤ 1 / (Fintype.card V : ℝ) ^ 9 := by
    have hlog : 18 * Real.logb 2 (Fintype.card V : ℝ) ≤ h := Nat.le_ceil _
    calc (2 : ℝ) ^ (-(h : ℝ) / 2) ≤ (2 : ℝ) ^ (Real.logb 2 (Fintype.card V : ℝ) * (-9 : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num); linarith
      _ = 1 / (Fintype.card V : ℝ) ^ 9 := by
          rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hnpos,
            Real.rpow_neg hnpos.le, show ((9 : ℝ)) = ((9 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast, one_div]
  have h3 : ((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ)) * (2 : ℝ) ^ (-(h : ℝ) / 2) ≤
      1 / (Fintype.card V : ℝ) ^ 7 := by
    calc ((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ)) * (2 : ℝ) ^ (-(h : ℝ) / 2)
        ≤ (Fintype.card V : ℝ) ^ 2 * (1 / (Fintype.card V : ℝ) ^ 9) :=
          mul_le_mul h2 hpow (by positivity) (by positivity)
      _ = 1 / (Fintype.card V : ℝ) ^ 7 := by field_simp
  rw [coinProb_eq_condProb _ ω₀] at h1 ⊢
  have h4 := condProb_compl (S := ∅) (ω₀ := ω₀) (fun ω : Perm V => ∃ l : List V,
    IsQueryPath G (rank ω) l ∧ h < (shortcutIdx G l).card)
  have h5 : condProb (fun ω : Perm V => ¬ ∃ l : List V, IsQueryPath G (rank ω) l ∧
      h < (shortcutIdx G l).card) ∅ ω₀ ≤ condProb (fun ω : Perm V => ∀ l : List V,
      IsQueryPath G (rank ω) l → (shortcutIdx G l).card ≤ h) ∅ ω₀ := by
    apply condProb_mono
    intro ω hω l hl
    push Not at hω
    exact hω l hl
  linarith

end shortcut

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM

section intervals

/-- the interval index: the least `i` with `p < (1+α)^i` -/
noncomputable def ivI (α : ℝ) (p : ℕ) : ℕ := by
  classical
  exact if h : ∃ i : ℕ, (p : ℝ) < (1 + α) ^ i then Nat.find h else 0

lemma ivI_exists {α : ℝ} (hα : 0 < α) (p : ℕ) : ∃ i : ℕ, (p : ℝ) < (1 + α) ^ i :=
  pow_unbounded_of_one_lt (p : ℝ) (by linarith)

lemma ivI_spec {α : ℝ} (hα : 0 < α) (p : ℕ) : (p : ℝ) < (1 + α) ^ (ivI α p) := by
  classical
  unfold ivI
  rw [dif_pos (ivI_exists hα p)]
  exact Nat.find_spec (ivI_exists hα p)

lemma ivI_min {α : ℝ} (hα : 0 < α) (p : ℕ) {j : ℕ} (hj : j < ivI α p) : (1 + α) ^ j ≤ (p : ℝ) := by
  classical
  unfold ivI at hj
  rw [dif_pos (ivI_exists hα p)] at hj
  have := Nat.find_min (ivI_exists hα p) hj
  push Not at this; exact this

lemma ivI_le_of {α : ℝ} (hα : 0 < α) {p i : ℕ} (h : (p : ℝ) < (1 + α) ^ i) : ivI α p ≤ i := by
  by_contra hc; push Not at hc
  have := ivI_min hα p hc; linarith

lemma ivI_pos {α : ℝ} (hα : 0 < α) {p : ℕ} (hp : 1 ≤ p) : 1 ≤ ivI α p := by
  by_contra hc; push Not at hc
  have h0 : ivI α p = 0 := by omega
  have := ivI_spec hα p
  rw [h0, pow_zero] at this
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

lemma ivI_lower {α : ℝ} (hα : 0 < α) {p : ℕ} (hp : 1 ≤ p) : (1 + α) ^ (ivI α p - 1) ≤ (p : ℝ) :=
  ivI_min hα p (by have := ivI_pos hα hp; omega)

lemma ivI_mono {α : ℝ} (hα : 0 < α) {p q : ℕ} (h : p ≤ q) : ivI α p ≤ ivI α q := by
  apply ivI_le_of hα
  have : (p : ℝ) ≤ q := by exact_mod_cast h
  linarith [ivI_spec hα q]

/-- the `i`-th interval `[(1+α)^{i-1}, (1+α)^i) ∩ ℕ` -/
noncomputable def Ivl (α : ℝ) (i : ℕ) : Finset ℕ :=
  Finset.Ico ⌈(1 + α) ^ (i - 1)⌉₊ ⌈(1 + α) ^ i⌉₊

lemma mem_Ivl {α : ℝ} (hα : 0 < α) {i p : ℕ} :
    p ∈ Ivl α i ↔ (1 + α) ^ (i - 1) ≤ (p : ℝ) ∧ (p : ℝ) < (1 + α) ^ i := by
  unfold Ivl
  rw [Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil]

lemma mem_Ivl_iff_ivI {α : ℝ} (hα : 0 < α) {i p : ℕ} (hi : 1 ≤ i) (hp : 1 ≤ p) :
    p ∈ Ivl α i ↔ ivI α p = i := by
  rw [mem_Ivl hα]
  constructor
  · rintro ⟨h1, h2⟩
    apply le_antisymm (ivI_le_of hα h2)
    by_contra hc; push Not at hc
    have := ivI_spec hα p
    have : (1 + α) ^ (ivI α p) ≤ (1 + α) ^ (i - 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  · rintro rfl
    exact ⟨ivI_lower hα hp, ivI_spec hα p⟩

lemma Ivl_lt {α : ℝ} (hα : 0 < α) {i j p q : ℕ} (hij : i < j) (hp : p ∈ Ivl α i)
    (hq : q ∈ Ivl α j) : p < q := by
  rw [mem_Ivl hα] at hp hq
  have h1 : (1 + α) ^ i ≤ (1 + α) ^ (j - 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have : (p : ℝ) < q := by linarith [hp.2, hq.1]
  exact_mod_cast this

lemma card_Ivl_ge {α : ℝ} (hα : 0 < α) {i : ℕ} (hi : 1 ≤ i) :
    α * (1 + α) ^ (i - 1) - 1 ≤ ((Ivl α i).card : ℝ) := by
  unfold Ivl
  rw [Nat.card_Ico]
  have h1 : (1 + α) ^ (i - 1) ≤ (1 + α) ^ i := pow_le_pow_right₀ (by linarith) (by omega)
  have h2 : ⌈(1 + α) ^ (i - 1)⌉₊ ≤ ⌈(1 + α) ^ i⌉₊ := Nat.ceil_mono h1
  rw [Nat.cast_sub h2]
  have h3 := Nat.le_ceil ((1 + α) ^ i)
  have h4 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (1 + α) ^ (i - 1) by positivity)
  have h5 : (1 + α) ^ i = (1 + α) * (1 + α) ^ (i - 1) := by
    rw [← pow_succ']; congr 1; omega
  linarith

lemma card_Ivl_le {α : ℝ} (hα : 0 < α) {i : ℕ} (hi : 1 ≤ i) :
    ((Ivl α i).card : ℝ) ≤ α * (1 + α) ^ (i - 1) + 1 := by
  unfold Ivl
  rw [Nat.card_Ico]
  have h1 : (1 + α) ^ (i - 1) ≤ (1 + α) ^ i := pow_le_pow_right₀ (by linarith) (by omega)
  have h2 : ⌈(1 + α) ^ (i - 1)⌉₊ ≤ ⌈(1 + α) ^ i⌉₊ := Nat.ceil_mono h1
  rw [Nat.cast_sub h2]
  have h3 := Nat.le_ceil ((1 + α) ^ (i - 1))
  have h4 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (1 + α) ^ i by positivity)
  have h5 : (1 + α) ^ i = (1 + α) * (1 + α) ^ (i - 1) := by
    rw [← pow_succ']; congr 1; omega
  linarith

end intervals

section chunks

/-- the `j`-th chunk of length `ℓ` of a finite set of naturals (in increasing order) -/
noncomputable def chunk (A : Finset ℕ) (j ℓ : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin A.card => j * ℓ ≤ (i : ℕ) ∧ (i : ℕ) < (j + 1) * ℓ)).map
    (A.orderEmbOfFin rfl).toEmbedding

lemma chunk_sub (A : Finset ℕ) (j ℓ : ℕ) : chunk A j ℓ ⊆ A := by
  intro x hx
  simp only [chunk, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact Finset.orderEmbOfFin_mem A rfl i

lemma card_chunk (A : Finset ℕ) (j ℓ : ℕ) (h : (j + 1) * ℓ ≤ A.card) :
    (chunk A j ℓ).card = ℓ := by
  unfold chunk
  rw [Finset.card_map]
  have : (Finset.univ.filter (fun i : Fin A.card => j * ℓ ≤ (i : ℕ) ∧ (i : ℕ) < (j + 1) * ℓ)).card =
      (Finset.Ico (j * ℓ) ((j + 1) * ℓ)).card := by
    apply Finset.card_bij (fun (i : Fin A.card) _ => (i : ℕ))
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_Ico.2 hi
    · intro a _ b _ h; exact Fin.ext h
    · intro b hb
      rw [Finset.mem_Ico] at hb
      exact ⟨⟨b, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hb,
        rfl⟩
  rw [this, Nat.card_Ico, add_mul, one_mul, Nat.add_sub_cancel_left]

lemma chunk_lt (A : Finset ℕ) {j j' ℓ : ℕ} (hjj : j < j') {x y : ℕ} (hx : x ∈ chunk A j ℓ)
    (hy : y ∈ chunk A j' ℓ) : x < y := by
  simp only [chunk, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨i', hi', rfl⟩ := hy
  simp only [RelEmbedding.coe_toEmbedding]
  apply (A.orderEmbOfFin rfl).strictMono
  show (i : ℕ) < (i' : ℕ)
  have : (j + 1) * ℓ ≤ j' * ℓ := Nat.mul_le_mul_right ℓ hjj
  omega

end chunks

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM

section blocks
variable (α : ℝ) (P : Finset ℕ)

/-- occupancy of the interval `i` -/
noncomputable def sOccP (i : ℕ) : ℕ := (P.filter (fun q => ivI α q = i)).card

/-- available positions in the interval before `i` -/
noncomputable def availP (i : ℕ) : Finset ℕ := Ivl α (i - 1) \ P

/-- block length of the interval `i` -/
noncomputable def ellP (i : ℕ) : ℕ := ⌊(1 - α) * ((Ivl α (i - 1)).card : ℝ) / (sOccP α P i : ℝ)⌋₊

/-- rank of `p` among the positions of its interval -/
noncomputable def rnkP (p : ℕ) : ℕ := (P.filter (fun q => ivI α q = ivI α p ∧ q < p)).card

/-- the protected block of the path position `p` -/
noncomputable def blkP (p : ℕ) : Finset ℕ :=
  chunk (availP α P (ivI α p)) (rnkP α P p) (ellP α P (ivI α p))

/-- room in every occupied interval -/
def Roomy : Prop :=
  ∀ p ∈ P, 2 ≤ ivI α p ∧ sOccP α P (ivI α p) * ellP α P (ivI α p) ≤ (availP α P (ivI α p)).card

variable {α P}

lemma blkP_sub_Ivl (p : ℕ) : blkP α P p ⊆ Ivl α (ivI α p - 1) := by
  intro x hx
  have := chunk_sub _ _ _ hx
  simp only [availP, Finset.mem_sdiff] at this
  exact this.1

lemma blkP_disj (p : ℕ) : ∀ x ∈ blkP α P p, x ∉ P := by
  intro x hx
  have := chunk_sub _ _ _ hx
  simp only [availP, Finset.mem_sdiff] at this
  exact this.2

lemma rnkP_lt {p : ℕ} (hp : p ∈ P) : rnkP α P p < sOccP α P (ivI α p) := by
  unfold rnkP sOccP
  apply Finset.card_lt_card
  refine ⟨fun q hq => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩
  · have := h (Finset.mem_filter.2 ⟨hp, rfl⟩)
    simp at this

lemma card_blkP (hR : Roomy α P) {p : ℕ} (hp : p ∈ P) :
    (blkP α P p).card = ellP α P (ivI α p) := by
  apply card_chunk
  have h1 := rnkP_lt (α := α) hp
  have h2 := (hR p hp).2
  calc (rnkP α P p + 1) * ellP α P (ivI α p) ≤ sOccP α P (ivI α p) * ellP α P (ivI α p) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ _ := h2

lemma blkP_lt_self (hα : 0 < α) (hR : Roomy α P) {p : ℕ} (hp : p ∈ P) (hp1 : 1 ≤ p) :
    ∀ x ∈ blkP α P p, x < p := by
  intro x hx
  have h2 := (hR p hp).1
  apply Ivl_lt hα (i := ivI α p - 1) (j := ivI α p) (by omega) (blkP_sub_Ivl p hx)
  exact (mem_Ivl_iff_ivI hα (by omega) hp1).2 rfl

lemma blkP_lt (hα : 0 < α) (hR : Roomy α P) {p q : ℕ} (hp : p ∈ P) (hq : q ∈ P) (hpq : p < q) :
    ∀ x ∈ blkP α P p, ∀ y ∈ blkP α P q, x < y := by
  intro x hx y hy
  have hmono := ivI_mono hα hpq.le (α := α)
  rcases Nat.eq_or_lt_of_le hmono with he | hlt
  · -- same interval: ranks are ordered
    have hrk : rnkP α P p < rnkP α P q := by
      unfold rnkP
      apply Finset.card_lt_card
      refine ⟨fun r hr => ?_, fun h => ?_⟩
      · simp only [Finset.mem_filter] at hr ⊢
        exact ⟨hr.1, by rw [hr.2.1, he], lt_trans hr.2.2 hpq⟩
      · have := h (Finset.mem_filter.2 ⟨hp, he, hpq⟩)
        simp at this
    unfold blkP at hx hy
    rw [he] at hx
    exact chunk_lt _ hrk hx hy
  · have h2 := (hR p hp).1
    exact Ivl_lt hα (i := ivI α p - 1) (j := ivI α q - 1) (by omega) (blkP_sub_Ivl p hx)
      (blkP_sub_Ivl q hy)

/-- lower bound on the block length -/
lemma ellP_ge {α : ℝ} (P : Finset ℕ) (i : ℕ) (hs : 0 < sOccP α P i) :
    (1 - α) * ((Ivl α (i - 1)).card : ℝ) / (sOccP α P i : ℝ) - 1 ≤ (ellP α P i : ℝ) := by
  unfold ellP
  have := Nat.lt_floor_add_one ((1 - α) * ((Ivl α (i - 1)).card : ℝ) / (sOccP α P i : ℝ))
  linarith

end blocks

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM
open QueryDepthMIS RGMISFast

section chaingen
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- bound through a coarser exposure set -/
lemma condProb_le_of_finer (X : Perm V → Prop) {S T : Finset ℕ} (hST : S ⊆ T) (b : ℝ)
    (h : ∀ ω, condProb X T ω ≤ b) (ω : Perm V) : condProb X S ω ≤ b := by
  classical
  rw [condProb_tower X hST ω]
  have hpos : (0 : ℝ) < (cls S ω).card := by exact_mod_cast cls_card_pos S ω
  rw [div_le_iff₀ hpos]
  calc ∑ ω' ∈ cls S ω, condProb X T ω' ≤ ∑ ω' ∈ cls S ω, b := Finset.sum_le_sum (fun ω' _ => h ω')
    _ = b * (cls S ω).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- one step of the chain -/
lemma chain_step (E X : Perm V → Prop) {S S' : Finset ℕ} (hSS : S ⊆ S')
    (hdet : ∀ ω ω', Agree S' ω ω' → (X ω ↔ X ω')) (hEX : ∀ ω, E ω → X ω)
    (B b : ℝ) (hB0 : 0 ≤ B) (hB : ∀ ω, condProb E S' ω ≤ B) (hb : ∀ ω, condProb X S ω ≤ b)
    (ω : Perm V) : condProb E S ω ≤ b * B := by
  classical
  have h1 : condProb E S ω = cexp (fun ω' => if X ω' then condProb E S' ω' else 0) S ω := by
    rw [condProb_tower E hSS ω, cexp]
    congr 1
    apply Finset.sum_congr rfl
    intro ω' _
    split_ifs with hX
    · rfl
    · apply condProb_eq_zero
      intro ω'' h'' hE
      exact hX ((hdet ω' ω'' (mem_cls.1 h'')).2 (hEX _ hE))
  rw [h1]
  have h2 : cexp (fun ω' => if X ω' then condProb E S' ω' else 0) S ω ≤
      cexp (fun ω' => (if X ω' then 1 else 0) * B) S ω := by
    apply cexp_mono
    intro ω'
    split_ifs
    · rw [one_mul]; exact hB ω'
    · simp
  refine h2.trans ?_
  have h3 : cexp (fun ω' => (if X ω' then 1 else 0) * B) S ω = condProb X S ω * B := by
    rw [condProb_eq_cexp, cexp, cexp, ← Finset.sum_mul, mul_div_right_comm]
  rw [h3]
  exact mul_le_mul_of_nonneg_right (hb ω) hB0

end chaingen

section procedure
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (α : ℝ) (P Q : Finset ℕ)

/-- the `k`-th path position (0-based) -/
noncomputable def posK (k : ℕ) : ℕ := (P.sort).getD k 0

/-- the protected set of the `k`-th path position (`k ≥ 1`) -/
noncomputable def ProtK (k : ℕ) : Finset ℕ := if k = 0 then ∅ else blkP α P (posK P (k - 1))

noncomputable def mxK (k : ℕ) : ℕ := (ProtK α P k).sup id

/-- exposed positions before the test of edge `k` -/
noncomputable def BefK (k : ℕ) : Finset ℕ :=
  Finset.Icc 1 (mxK α P (k - 1)) ∪ ((P.sort).take (k + 1)).toFinset

/-- the event `E(P, Q)` -/
def pathEv (ω : Perm V) : Prop :=
  ∃ l : List V, l.map (rank ω) = P.sort ∧ IsQueryPath G (rank ω) l ∧ shortcutIdx G l = Q

/-- the two-hop condition at edge `k` -/
def THc (k : ℕ) : Prop :=
  Odd k ∧ k + 2 ≤ P.card - 1 ∧ ivI α (posK P (k - 1)) = ivI α (posK P k) ∧ k ∉ Q

open Classical in
/-- the product of the test bounds from edge `k` on -/
noncomputable def BndK (β ε : ℝ) (k : ℕ) : ℝ :=
  if h : P.card ≤ k + 1 then 1
  else if THc α P Q k then
    (1 - ε) / (Real.exp 1 * (ProtK α P k).card) ^ 2 * BndK β ε (k + 2)
  else 1 / (Real.exp 1 * (ProtK α P k).card * (1 - β)) * BndK β ε (k + 1)
termination_by P.card - k

variable {α P Q}

lemma posK_eq {k : ℕ} (hk : k < P.card) :
    posK P k = (P.sort)[k]'(by rw [Finset.length_sort]; exact hk) := by
  unfold posK; rw [List.getD_eq_getElem]

lemma posK_mem {k : ℕ} (hk : k < P.card) : posK P k ∈ P := by
  rw [posK_eq hk, ← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem _

lemma posK_lt {j k : ℕ} (hjk : j < k) (hk : k < P.card) : posK P j < posK P k := by
  rw [posK_eq (by omega), posK_eq hk]
  exact (Finset.sortedLT_sort P).getElem_lt_getElem_of_lt hjk

lemma mem_take_posK {j k : ℕ} (hjk : j ≤ k) (hk : k < P.card) :
    posK P j ∈ ((P.sort).take (k + 1)).toFinset := by
  rw [List.mem_toFinset, posK_eq (by omega), List.mem_iff_getElem]
  refine ⟨j, by simp; omega, by simp⟩

lemma mem_take_iff {q k : ℕ} (hq : q ∈ ((P.sort).take (k + 1)).toFinset) :
    ∃ j, j ≤ k ∧ j < P.card ∧ q = posK P j := by
  rw [List.mem_toFinset, List.mem_iff_getElem] at hq
  obtain ⟨j, hj, rfl⟩ := hq
  simp only [List.length_take, Finset.length_sort] at hj
  refine ⟨j, by omega, by omega, ?_⟩
  rw [posK_eq (by omega)]; simp

lemma ProtK_eq {k : ℕ} (hk : 1 ≤ k) : ProtK α P k = blkP α P (posK P (k - 1)) := by
  unfold ProtK; rw [if_neg (by omega)]

end procedure

section chainfacts
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- standing assumptions on the position set -/
structure ChainSet (α β : ℝ) (P : Finset ℕ) (n : ℕ) : Prop where
  hα : 0 < α
  hR : Roomy α P
  hbig : ∀ p ∈ P, 1000 < ellP α P (ivI α p)
  hb2 : ∀ p ∈ P, ∀ x ∈ blkP α P p, 2 ≤ x
  hP1 : ∀ p ∈ P, 1 ≤ p
  hPβ : ∀ p ∈ P, (p : ℝ) < β * n

variable {α β : ℝ} {P Q : Finset ℕ} {n : ℕ}

lemma ChainSet.prot_lt_pos (hc : ChainSet α β P n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ P.card) :
    ∀ x ∈ ProtK α P k, x < posK P (k - 1) := by
  intro x hx
  rw [ProtK_eq hk1] at hx
  have hm := posK_mem (P := P) (k := k - 1) (by omega)
  exact blkP_lt_self hc.hα hc.hR hm (hc.hP1 _ hm) x hx

lemma ChainSet.prot_not_mem (hc : ChainSet α β P n) {k : ℕ} (hk1 : 1 ≤ k) :
    ∀ x ∈ ProtK α P k, x ∉ P := by
  intro x hx
  rw [ProtK_eq hk1] at hx
  exact blkP_disj _ x hx

lemma ChainSet.prot_ge2 (hc : ChainSet α β P n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ P.card) :
    ∀ x ∈ ProtK α P k, 2 ≤ x := by
  intro x hx
  rw [ProtK_eq hk1] at hx
  exact hc.hb2 _ (posK_mem (by omega)) x hx

lemma ChainSet.prot_card (hc : ChainSet α β P n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ P.card) :
    (ProtK α P k).card = ellP α P (ivI α (posK P (k - 1))) := by
  rw [ProtK_eq hk1]
  exact card_blkP hc.hR (posK_mem (by omega))

lemma ChainSet.prot_big (hc : ChainSet α β P n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ P.card) :
    1000 < (ProtK α P k).card := by
  rw [hc.prot_card hk1 hk]; exact hc.hbig _ (posK_mem (by omega))

lemma ChainSet.prot_ne (hc : ChainSet α β P n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ P.card) :
    (ProtK α P k).Nonempty :=
  Finset.card_pos.1 (by have := hc.prot_big hk1 hk; omega)

lemma ChainSet.prot_lt_prot (hc : ChainSet α β P n) {j k : ℕ} (hj1 : 1 ≤ j) (hjk : j < k)
    (hk : k ≤ P.card) : ∀ x ∈ ProtK α P j, ∀ y ∈ ProtK α P k, x < y := by
  intro x hx y hy
  rw [ProtK_eq hj1] at hx
  rw [ProtK_eq (by omega)] at hy
  exact blkP_lt hc.hα hc.hR (posK_mem (by omega)) (posK_mem (by omega))
    (posK_lt (by omega) (by omega)) x hx y hy

lemma ChainSet.le_mx {k : ℕ} : ∀ x ∈ ProtK α P k, x ≤ mxK α P k := fun x hx => le_sup_id hx

lemma ChainSet.mx_lt_pos (hc : ChainSet α β P n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ P.card) :
    mxK α P k < posK P (k - 1) := by
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup _ (hc.prot_ne hk1 hk) id
  unfold mxK; rw [hxe]; exact hc.prot_lt_pos hk1 hk x hx

lemma ChainSet.mx_prev_lt (hc : ChainSet α β P n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ P.card) :
    ∀ y ∈ ProtK α P k, mxK α P (k - 1) < y := by
  intro y hy
  rcases Nat.eq_or_lt_of_le hk1 with h | h
  · subst h
    have : mxK α P 0 = 0 := by simp [mxK, ProtK]
    rw [show 1 - 1 = 0 from rfl, this]
    have := hc.prot_ge2 le_rfl hk y hy; omega
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup _ (hc.prot_ne (k := k - 1) (by omega)
      (by omega)) id
    unfold mxK; rw [hxe]
    exact hc.prot_lt_prot (by omega) (by omega) hk x hx y hy

lemma ChainSet.mx_mono (hc : ChainSet α β P n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ P.card) :
    mxK α P (k - 1) < mxK α P k := by
  obtain ⟨y, hy⟩ := hc.prot_ne hk1 hk
  exact lt_of_lt_of_le (hc.mx_prev_lt hk1 hk y hy) (ChainSet.le_mx y hy)

lemma ChainSet.pos_valid (hc : ChainSet α β P n) {k : ℕ} (hk : k < P.card) (hβ1 : β < 1) :
    1 ≤ posK P k ∧ posK P k ≤ n := by
  have hm := posK_mem hk
  refine ⟨hc.hP1 _ hm, ?_⟩
  have h1 := hc.hPβ _ hm
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have : (posK P k : ℝ) ≤ n := by nlinarith
  exact_mod_cast this

lemma BefK_mono (hc : ChainSet α β P n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ P.card) :
    BefK α P k ⊆ BefK α P (k + 1) := by
  intro q hq
  simp only [BefK, Finset.mem_union, Finset.mem_Icc, List.mem_toFinset] at hq ⊢
  rcases hq with hq | hq
  · left
    have := hc.mx_mono hk1 (by omega)
    refine ⟨hq.1, ?_⟩
    simp only [Nat.add_sub_cancel]
    omega
  · right; exact (List.take_subset_take_left _ (by omega)) hq

end chainfacts

section tests
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {α β : ℝ} {P Q : Finset ℕ}

theorem oneHop_test (hc : ChainSet α β P (Fintype.card V)) (hβ0 : 0 < β) (hβ1 : β < 0.1)
    (hn : 2 ≤ Fintype.card V) {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 2 ≤ P.card) (ω : Perm V) :
    condProb (oneHopEvent G (ProtK α P k) (posK P k) (posK P (k + 1))) (BefK α P k) ω ≤
      1 / (Real.exp 1 * ((ProtK α P k).card : ℝ) * (1 - β)) := by
  classical
  set T := (Finset.Icc 1 (mxK α P k) \ ProtK α P k) ∪ ((P.sort).take (k + 1)).toFinset with hT
  have hpk1 : (posK P (k - 1) : ℝ) < β * Fintype.card V := hc.hPβ _ (posK_mem (by omega))
  have hBT : BefK α P k ⊆ T := by
    intro q hq
    simp only [BefK, Finset.mem_union] at hq
    rcases hq with hq | hq
    · apply Finset.mem_union_left
      rw [Finset.mem_sdiff, Finset.mem_Icc]
      rw [Finset.mem_Icc] at hq
      have := hc.mx_mono hk1 (by omega)
      refine ⟨⟨hq.1, by omega⟩, fun h => ?_⟩
      have := hc.mx_prev_lt hk1 (by omega) q h; omega
    · exact Finset.mem_union_right _ hq
  apply condProb_le_of_finer _ hBT
  intro ω'
  apply lemma_3_2_proof G β hβ0 hβ1 hn (ProtK α P k) (hc.prot_ne hk1 (by omega))
  · intro x hx
    exact lt_trans (hc.prot_lt_pos hk1 (by omega) x hx) (posK_lt (by omega) (by omega))
  · exact posK_lt (by omega) (by omega)
  · exact hc.hPβ _ (posK_mem (by omega))
  · intro q hq
    rw [hT, Finset.mem_union] at hq
    rcases hq with hq | hq
    · rw [Finset.mem_sdiff, Finset.mem_Icc] at hq
      refine ⟨hq.1.1, ?_⟩
      have h1 := hc.mx_lt_pos hk1 (by omega)
      have : (q : ℝ) < posK P (k - 1) := by exact_mod_cast (show q < posK P (k - 1) by omega)
      linarith
    · obtain ⟨j, hj, hjL, rfl⟩ := mem_take_iff hq
      exact ⟨hc.hP1 _ (posK_mem hjL), (hc.hPβ _ (posK_mem hjL)).le⟩
  · exact Finset.mem_union_right _ (mem_take_posK le_rfl (by omega))
  · intro q hq1 hq2 hq3
    exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨hq1, hq2⟩, hq3⟩)
  · intro q hq
    rw [hT, Finset.mem_union] at hq
    rcases hq with hq | hq
    · rw [Finset.mem_sdiff, Finset.mem_Icc] at hq
      refine ⟨hq.2, fun h => ?_⟩
      have h1 := hc.mx_lt_pos hk1 (by omega)
      have h2 := posK_lt (P := P) (j := k - 1) (k := k + 1) (by omega) (by omega)
      omega
    · obtain ⟨j, hj, hjL, rfl⟩ := mem_take_iff hq
      refine ⟨hc.prot_not_mem hk1 _ |> fun h h' => h h' (posK_mem hjL), fun h => ?_⟩
      have := posK_lt (P := P) (j := j) (k := k + 1) (by omega) (by omega)
      omega
  · intro x hx; have := hc.prot_ge2 hk1 (by omega) x hx; omega

theorem twoHop_test (hc : ChainSet α β P (Fintype.card V)) (hβ0 : 0 < β) (hβ : β ≤ 1/100000)
    (hn : 2 ≤ Fintype.card V) {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 3 ≤ P.card)
    (hsame : ivI α (posK P (k - 1)) = ivI α (posK P k)) (ω : Perm V) :
    condProb (twoHopEvent G (ProtK α P k) (ProtK α P (k + 1)) (posK P k) (posK P (k + 1))
      (posK P (k + 2))) (BefK α P k) ω ≤
      (1 - 1/5000) / (Real.exp 1 * ((ProtK α P k).card : ℝ)) ^ 2 := by
  classical
  set T := (Finset.Icc 1 (mxK α P (k + 1)) \ (ProtK α P k ∪ ProtK α P (k + 1))) ∪
    ((P.sort).take (k + 1)).toFinset with hT
  have hm1 := hc.mx_mono hk1 (by omega)
  have hm2 := hc.mx_mono (k := k + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hm2
  have hBT : BefK α P k ⊆ T := by
    intro q hq
    simp only [BefK, Finset.mem_union] at hq
    rcases hq with hq | hq
    · apply Finset.mem_union_left
      rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_union, not_or]
      rw [Finset.mem_Icc] at hq
      refine ⟨⟨hq.1, by omega⟩, fun h => ?_, fun h => ?_⟩
      · have := hc.mx_prev_lt hk1 (by omega) q h; omega
      · have := hc.mx_prev_lt (k := k + 1) (by omega) (by omega) q h
        simp only [Nat.add_sub_cancel] at this; omega
    · exact Finset.mem_union_right _ hq
  apply condProb_le_of_finer _ hBT
  intro ω'
  have hcard2 : (ProtK α P (k + 1)).card = (ProtK α P k).card := by
    rw [hc.prot_card (k := k + 1) (by omega) (by omega), hc.prot_card hk1 (by omega)]
    simp only [Nat.add_sub_cancel]; rw [hsame]
  have hlt := hc.mx_lt_pos (k := k + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hlt
  have hpk : (posK P k : ℝ) < β * Fintype.card V := hc.hPβ _ (posK_mem (by omega))
  apply twoHop_main G β hβ0 hβ hn _ (hc.prot_big hk1 (by omega)) _ _ rfl hcard2
  · intro x hx y hy; exact hc.prot_lt_prot hk1 (by omega) (by omega) x hx y hy
  · intro y hy
    have := hc.prot_lt_pos (k := k + 1) (by omega) (by omega) y hy
    simpa using this
  · exact posK_lt (by omega) (by omega)
  · exact posK_lt (by omega) (by omega)
  · exact hc.hPβ _ (posK_mem (by omega))
  · intro q hq
    rw [hT, Finset.mem_union] at hq
    rcases hq with hq | hq
    · rw [Finset.mem_sdiff, Finset.mem_Icc] at hq
      refine ⟨hq.1.1, ?_⟩
      have : (q : ℝ) < posK P k := by exact_mod_cast (show q < posK P k by omega)
      linarith
    · obtain ⟨j, hj, hjL, rfl⟩ := mem_take_iff hq
      exact ⟨hc.hP1 _ (posK_mem hjL), (hc.hPβ _ (posK_mem hjL)).le⟩
  · exact Finset.mem_union_right _ (mem_take_posK le_rfl (by omega))
  · intro q hq1 hq2 hq3 hq4
    exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨hq1, hq2⟩, by
      rw [Finset.mem_union, not_or]; exact ⟨hq3, hq4⟩⟩)
  · intro q hq
    rw [hT, Finset.mem_union] at hq
    have h1 := posK_lt (P := P) (j := k) (k := k + 1) (by omega) (by omega)
    have h2 := posK_lt (P := P) (j := k) (k := k + 2) (by omega) (by omega)
    rcases hq with hq | hq
    · rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_union, not_or] at hq
      exact ⟨hq.2.1, hq.2.2, by omega, by omega⟩
    · obtain ⟨j, hj, hjL, rfl⟩ := mem_take_iff hq
      have h3 := posK_lt (P := P) (j := j) (k := k + 1) (by omega) (by omega)
      have h4 := posK_lt (P := P) (j := j) (k := k + 2) (by omega) (by omega)
      exact ⟨fun h => hc.prot_not_mem hk1 _ h (posK_mem hjL),
        fun h => hc.prot_not_mem (k := k + 1) (by omega) _ h (posK_mem hjL), by omega, by omega⟩
  · exact le_rfl
  · intro x hx; have := hc.prot_ge2 hk1 (by omega) x hx; omega

end tests

section chainmain
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {α β : ℝ} {P Q : Finset ℕ}

lemma pathEv_spec {ω : Perm V} (h : pathEv G P Q ω) :
    ∃ l : List V, l.length = P.card ∧ IsQueryPath G (rank ω) l ∧ shortcutIdx G l = Q ∧
      ∀ j (hj : j < l.length), rank ω l[j] = posK P j := by
  obtain ⟨l, hmap, hqp, hsc⟩ := h
  have hlen : l.length = P.card := by
    have := congrArg List.length hmap; simp at this; exact this
  refine ⟨l, hlen, hqp, hsc, fun j hj => ?_⟩
  have := congrArg (fun m => m.getD j 0) hmap
  rw [List.getD_eq_getElem _ _ (by simp; exact hj), List.getElem_map] at this
  rw [this]; rfl

lemma pathEv_oneHop (hc : ChainSet α β P (Fintype.card V)) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k + 2 ≤ P.card) (ω : Perm V) (h : pathEv G P Q ω) :
    oneHopEvent G (ProtK α P k) (posK P k) (posK P (k + 1)) ω := by
  obtain ⟨l, hlen, hqp, hsc, hr⟩ := pathEv_spec G h
  have hc1 := List.isChain_iff_getElem.1 hqp.1.2
  have hc2 := List.isChain_iff_getElem.1 hqp.2
  have hmx := hc.mx_lt_pos hk1 (by omega)
  refine ⟨l[k], l[k + 1], hr k (by omega), hr (k + 1) (by omega), (hc1 k (by omega)).1, ?_, ?_⟩
  · have := hc2 (k - 1) (by omega)
    simp only [show k - 1 + 1 = k by omega] at this
    rw [hr (k - 1) (by omega)] at this
    show mxK α P k + 1 ≤ _
    omega
  · have := hc2 k (by omega)
    rw [hr k (by omega)] at this
    have := posK_lt (P := P) (j := k - 1) (k := k) (by omega) (by omega)
    show mxK α P k + 1 ≤ _
    omega

lemma pathEv_twoHop (hc : ChainSet α β P (Fintype.card V)) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k + 3 ≤ P.card) (hQ : k ∉ Q) (ω : Perm V) (h : pathEv G P Q ω) :
    twoHopEvent G (ProtK α P k) (ProtK α P (k + 1)) (posK P k) (posK P (k + 1))
      (posK P (k + 2)) ω := by
  obtain ⟨l, hlen, hqp, hsc, hr⟩ := pathEv_spec G h
  have hc1 := List.isChain_iff_getElem.1 hqp.1.2
  have hc2 := List.isChain_iff_getElem.1 hqp.2
  have hmx := hc.mx_lt_pos hk1 (by omega)
  have hmx2 := hc.mx_lt_pos (k := k + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hmx2
  refine ⟨l[k], l[k + 1], l[k + 2], hr k (by omega), hr (k + 1) (by omega), hr (k + 2) (by omega),
    ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨(hc1 k (by omega)).1, (hc1 (k + 1) (by omega)).1⟩
  · intro i j hi hj hij hj1
    simp only [List.length_cons, List.length_nil] at hi hj
    have hnotsc : ¬ G.Adj l[k] l[k + 2] := by
      intro hadj
      apply hQ
      rw [← hsc]
      simp only [shortcutIdx, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, hadj⟩
    interval_cases i <;> interval_cases j <;> simp_all [G.loopless.irrefl]
  · have := hc2 (k - 1) (by omega)
    simp only [show k - 1 + 1 = k by omega] at this
    rw [hr (k - 1) (by omega)] at this
    show mxK α P k + 1 ≤ _
    omega
  · have := hc2 k (by omega)
    rw [hr k (by omega)] at this
    show mxK α P (k + 1) + 1 ≤ _
    omega
  · have := hc2 (k + 1) (by omega)
    simp only [show k + 1 + 1 = k + 2 by omega] at this
    rw [hr (k + 1) (by omega)] at this
    have := posK_lt (P := P) (j := k) (k := k + 1) (by omega) (by omega)
    show mxK α P (k + 1) + 1 ≤ _
    omega

end chainmain

section chainmain2
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {α β : ℝ} {P Q : Finset ℕ}

/-- vertices at exposed positions agree -/
lemma vertex_agree {S : Finset ℕ} {ω ω' : Perm V} (h : Agree S ω ω') {u : V} {p : ℕ}
    (hp : p ∈ S) (hu : rank ω u = p) : rank ω' u = p := by
  rw [h u (hu ▸ hp), hu]

lemma oneHop_det (hc : ChainSet α β P (Fintype.card V)) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k + 2 ≤ P.card) (ω ω' : Perm V) (hag : Agree (BefK α P (k + 1)) ω ω') :
    oneHopEvent G (ProtK α P k) (posK P k) (posK P (k + 1)) ω →
      oneHopEvent G (ProtK α P k) (posK P k) (posK P (k + 1)) ω' := by
  rintro ⟨u, v, hu, hv, hadj, h1, h2⟩
  have hS : ∀ q, 1 ≤ q → q ≤ mxK α P k → q ∈ BefK α P (k + 1) := by
    intro q h1 h2; simp only [BefK, Finset.mem_union, Finset.mem_Icc, Nat.add_sub_cancel]
    exact Or.inl ⟨h1, h2⟩
  have hle := agreeLE_of_agree_sub hS hag
  have hm1 : posK P k ∈ BefK α P (k + 1) := by
    simp only [BefK]; exact Finset.mem_union_right _ (mem_take_posK (by omega) (by omega))
  have hm2 : posK P (k + 1) ∈ BefK α P (k + 1) := by
    simp only [BefK]; exact Finset.mem_union_right _ (mem_take_posK (by omega) (by omega))
  refine ⟨u, v, vertex_agree hag hm1 hu, vertex_agree hag hm2 hv, hadj, ?_, ?_⟩
  · exact (le_tau_congr G hle u le_rfl).1 h1
  · exact (le_tau_congr G hle v le_rfl).1 h2

lemma twoHop_det (hc : ChainSet α β P (Fintype.card V)) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k + 3 ≤ P.card) (ω ω' : Perm V) (hag : Agree (BefK α P (k + 2)) ω ω') :
    twoHopEvent G (ProtK α P k) (ProtK α P (k + 1)) (posK P k) (posK P (k + 1))
      (posK P (k + 2)) ω →
    twoHopEvent G (ProtK α P k) (ProtK α P (k + 1)) (posK P k) (posK P (k + 1))
      (posK P (k + 2)) ω' := by
  rintro ⟨u, v, w, hu, hv, hw, hind, h1, h2, h3⟩
  have hS : ∀ q, 1 ≤ q → q ≤ mxK α P (k + 1) → q ∈ BefK α P (k + 2) := by
    intro q h1 h2; simp only [BefK, Finset.mem_union, Finset.mem_Icc]
    exact Or.inl ⟨h1, by simpa using h2⟩
  have hle := agreeLE_of_agree_sub hS hag
  have hm := hc.mx_mono (k := k + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hm
  have hmem : ∀ j, j ≤ k + 2 → posK P j ∈ BefK α P (k + 2) := by
    intro j hj; simp only [BefK]
    exact Finset.mem_union_right _ (mem_take_posK hj (by omega))
  refine ⟨u, v, w, vertex_agree hag (hmem k (by omega)) hu,
    vertex_agree hag (hmem (k + 1) (by omega)) hv, vertex_agree hag (hmem (k + 2) le_rfl) hw,
    hind, ?_, ?_, ?_⟩
  · exact (le_tau_congr G hle u (by show mxK α P k + 1 ≤ _ ; omega)).1 h1
  · exact (le_tau_congr G hle v le_rfl).1 h2
  · exact (le_tau_congr G hle w le_rfl).1 h3

lemma BndK_nonneg (hβ1 : β < 1) (ε : ℝ) (hε : ε < 1) :
    ∀ m k, P.card = k + 1 + m → 0 ≤ BndK α P Q β ε k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk
    rw [BndK]
    split_ifs with h1 h2
    · norm_num
    · apply mul_nonneg (div_nonneg (by linarith) (by positivity))
      rcases Nat.lt_or_ge (k + 2) P.card with h3 | h3
      · exact ih (m - 2) (by omega) (k + 2) (by omega)
      · rw [BndK, dif_pos (by omega)]; norm_num
    · apply mul_nonneg (by
        apply div_nonneg zero_le_one
        apply mul_nonneg (by positivity); linarith)
      exact ih (m - 1) (by omega) (k + 1) (by omega)

theorem chain_main (hc : ChainSet α β P (Fintype.card V)) (hβ0 : 0 < β) (hβ : β ≤ 1/100000)
    (hn : 2 ≤ Fintype.card V) :
    ∀ m k, P.card = k + 1 + m → 1 ≤ k → ∀ ω : Perm V,
      condProb (pathEv G P Q) (BefK α P k) ω ≤ BndK α P Q β (1/5000) k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk hk1 ω
    rw [BndK]
    split_ifs with h1 h2
    · exact condProb_le_one _ _ _
    · -- two-hop test
      obtain ⟨_, hk2, hsame, hQ⟩ := h2
      have hS1 := BefK_mono hc hk1 (by omega)
      have hS2 := BefK_mono hc (k := k + 1) (by omega) (by omega)
      have hrec : ∀ ω', condProb (pathEv G P Q) (BefK α P (k + 2)) ω' ≤
          BndK α P Q β (1/5000) (k + 2) := by
        intro ω'
        rcases Nat.lt_or_ge (k + 3) P.card with h3 | h3
        · exact ih (m - 2) (by omega) (k + 2) (by omega) (by omega) ω'
        · rw [BndK, dif_pos (by omega)]; exact condProb_le_one _ _ _
      have := chain_step (pathEv G P Q) _ (hS1.trans hS2)
        (fun ω₁ ω₂ hag => ⟨twoHop_det G hc hk1 (by omega) ω₁ ω₂ hag,
          twoHop_det G hc hk1 (by omega) ω₂ ω₁ hag.symm⟩)
        (pathEv_twoHop G hc hk1 (by omega) hQ)
        _ _ (BndK_nonneg (by linarith) _ (by norm_num) (m - 2) (k + 2) (by omega)) hrec
        (fun ω' => twoHop_test G hc hβ0 hβ hn hk1 (by omega) hsame ω') ω
      exact this
    · -- one-hop test
      have hS1 := BefK_mono hc hk1 (by omega)
      have hrec : ∀ ω', condProb (pathEv G P Q) (BefK α P (k + 1)) ω' ≤
          BndK α P Q β (1/5000) (k + 1) := fun ω' =>
        ih (m - 1) (by omega) (k + 1) (by omega) (by omega) ω'
      exact chain_step (pathEv G P Q) _ hS1
        (fun ω₁ ω₂ hag => ⟨oneHop_det G hc hk1 (by omega) ω₁ ω₂ hag,
          oneHop_det G hc hk1 (by omega) ω₂ ω₁ hag.symm⟩)
        (pathEv_oneHop G hc hk1 (by omega))
        _ _ (BndK_nonneg (by linarith) _ (by norm_num) (m - 1) (k + 1) (by omega)) hrec
        (fun ω' => oneHop_test G hc hβ0 (by linarith) hn hk1 (by omega) ω') ω

end chainmain2

section closedform
variable {α β : ℝ} {P Q : Finset ℕ} {n : ℕ}

open Classical in
lemma BndK_le (hc : ChainSet α β P n) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < 1) :
    ∀ m k, P.card = k + 1 + m → 1 ≤ k →
      BndK α P Q β ε k ≤ (1 - ε) ^ ((Finset.Ico k (P.card - 1)).filter (THc α P Q)).card *
        ((1 - β) ^ (P.card - 1 - k))⁻¹ *
        ∏ j ∈ Finset.Ico k (P.card - 1), 1 / (Real.exp 1 * ((ProtK α P j).card : ℝ)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk hk1
    have hb1 : 0 < 1 - β := by linarith
    rw [BndK]
    split_ifs with h1 h2
    · rw [show P.card - 1 = k by omega]; simp
    · obtain ⟨hodd, hk2, hsame, hQ⟩ := h2
      have hcard2 : (ProtK α P (k + 1)).card = (ProtK α P k).card := by
        rw [hc.prot_card (k := k + 1) (by omega) (by omega), hc.prot_card hk1 (by omega)]
        simp only [Nat.add_sub_cancel]; rw [hsame]
      have hrest : BndK α P Q β ε (k + 2) ≤
          (1 - ε) ^ ((Finset.Ico (k + 2) (P.card - 1)).filter (THc α P Q)).card *
          ((1 - β) ^ (P.card - 1 - (k + 2)))⁻¹ *
          ∏ j ∈ Finset.Ico (k + 2) (P.card - 1), 1 / (Real.exp 1 * ((ProtK α P j).card : ℝ)) := by
        rcases Nat.lt_or_ge (k + 3) P.card with h3 | h3
        · exact ih (m - 2) (by omega) (k + 2) (by omega) (by omega)
        · rw [BndK, dif_pos (by omega)]
          rw [show P.card - 1 = k + 2 by omega]; simp
      -- split the index sets
      have hI : Finset.Ico k (P.card - 1) = insert k (insert (k + 1) (Finset.Ico (k + 2) (P.card - 1))) := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hk_notin : k ∉ insert (k + 1) (Finset.Ico (k + 2) (P.card - 1)) := by
        simp only [Finset.mem_insert, Finset.mem_Ico]; omega
      have hk1_notin : k + 1 ∉ Finset.Ico (k + 2) (P.card - 1) := by simp
      have hTH : (Finset.Ico k (P.card - 1)).filter (THc α P Q) =
          insert k ((Finset.Ico (k + 2) (P.card - 1)).filter (THc α P Q)) := by
        rw [hI, Finset.filter_insert, Finset.filter_insert, if_pos ⟨hodd, hk2, hsame, hQ⟩,
          if_neg (fun h : THc α P Q (k + 1) => (Nat.not_odd_iff_even.2 hodd.add_one) h.1)]
      rw [hTH, Finset.card_insert_of_notMem (by simp only [Finset.mem_filter, Finset.mem_Ico]; omega),
        hI, Finset.prod_insert hk_notin,
        Finset.prod_insert hk1_notin, pow_succ, hcard2]
      have hpos : 0 ≤ BndK α P Q β ε (k + 2) := BndK_nonneg hβ1 ε hε (m - 2) (k + 2) (by omega)
      have hβpow : ((1 - β) ^ (P.card - 1 - (k + 2)))⁻¹ ≤ ((1 - β) ^ (P.card - 1 - k))⁻¹ := by
        apply inv_anti₀ (by positivity)
        apply pow_le_pow_of_le_one hb1.le (by linarith) (by omega)
      have hprod0 : 0 ≤ ∏ j ∈ Finset.Ico (k + 2) (P.card - 1),
          1 / (Real.exp 1 * ((ProtK α P j).card : ℝ)) :=
        Finset.prod_nonneg (fun j _ => by positivity)
      calc (1 - ε) / (Real.exp 1 * ((ProtK α P k).card : ℝ)) ^ 2 * BndK α P Q β ε (k + 2)
          ≤ (1 - ε) / (Real.exp 1 * ((ProtK α P k).card : ℝ)) ^ 2 *
            ((1 - ε) ^ ((Finset.Ico (k + 2) (P.card - 1)).filter (THc α P Q)).card *
            ((1 - β) ^ (P.card - 1 - (k + 2)))⁻¹ *
            ∏ j ∈ Finset.Ico (k + 2) (P.card - 1), 1 / (Real.exp 1 * ((ProtK α P j).card : ℝ))) :=
            mul_le_mul_of_nonneg_left hrest (div_nonneg (by linarith) (by positivity))
        _ ≤ (1 - ε) / (Real.exp 1 * ((ProtK α P k).card : ℝ)) ^ 2 *
            ((1 - ε) ^ ((Finset.Ico (k + 2) (P.card - 1)).filter (THc α P Q)).card *
            ((1 - β) ^ (P.card - 1 - k))⁻¹ *
            ∏ j ∈ Finset.Ico (k + 2) (P.card - 1), 1 / (Real.exp 1 * ((ProtK α P j).card : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg (by linarith) (by positivity))
            apply mul_le_mul_of_nonneg_right _ hprod0
            apply mul_le_mul_of_nonneg_left hβpow (pow_nonneg (by linarith) _)
        _ = _ := by ring
    · have hrest := ih (m - 1) (by omega) (k + 1) (by omega) (by omega)
      have hI : Finset.Ico k (P.card - 1) = insert k (Finset.Ico (k + 1) (P.card - 1)) := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hTH : (Finset.Ico k (P.card - 1)).filter (THc α P Q) =
          (Finset.Ico (k + 1) (P.card - 1)).filter (THc α P Q) := by
        rw [hI, Finset.filter_insert, if_neg h2]
      rw [hTH, hI, Finset.prod_insert (by simp only [Finset.mem_Ico]; omega)]
      have hpow : ((1 - β) ^ (P.card - 1 - k))⁻¹ =
          ((1 - β) ^ (P.card - 1 - (k + 1)))⁻¹ * (1 - β)⁻¹ := by
        rw [← mul_inv, ← pow_succ]; congr 2; omega
      rw [hpow]
      have hprod0 : 0 ≤ ∏ j ∈ Finset.Ico (k + 1) (P.card - 1),
          1 / (Real.exp 1 * ((ProtK α P j).card : ℝ)) :=
        Finset.prod_nonneg (fun j _ => by positivity)
      calc 1 / (Real.exp 1 * ((ProtK α P k).card : ℝ) * (1 - β)) * BndK α P Q β ε (k + 1)
          ≤ 1 / (Real.exp 1 * ((ProtK α P k).card : ℝ) * (1 - β)) *
            ((1 - ε) ^ ((Finset.Ico (k + 1) (P.card - 1)).filter (THc α P Q)).card *
            ((1 - β) ^ (P.card - 1 - (k + 1)))⁻¹ *
            ∏ j ∈ Finset.Ico (k + 1) (P.card - 1), 1 / (Real.exp 1 * ((ProtK α P j).card : ℝ))) :=
            mul_le_mul_of_nonneg_left hrest (by positivity)
        _ = _ := by
            rw [one_div (Real.exp 1 * ((ProtK α P k).card : ℝ) * (1 - β)), mul_inv]
            ring

end closedform

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM

section count
variable {β : Type*} [DecidableEq β]

/-- sums over subsets of a disjoint union factor -/
lemma sum_powerset_union_mul {A B : Finset β} (hAB : Disjoint A B) (f g : Finset β → ℝ) :
    ∑ P ∈ (A ∪ B).powerset, f (P ∩ A) * g (P ∩ B) =
      (∑ S ∈ A.powerset, f S) * (∑ T ∈ B.powerset, g T) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun P => (P ∩ A, P ∩ B))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset] at hp ⊢
    exact Finset.union_subset_union hp.1 hp.2
  · intro P hP
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset] at hP ⊢
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset] at hp
    have h1 : (p.1 ∪ p.2) ∩ A = p.1 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 hp.1]
      have : p.2 ∩ A = ∅ := by
        rw [← Finset.disjoint_iff_inter_eq_empty]
        exact Finset.disjoint_of_subset_left hp.2 hAB.symm
      rw [this, Finset.union_empty]
    have h2 : (p.1 ∪ p.2) ∩ B = p.2 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 hp.2]
      have : p.1 ∩ B = ∅ := by
        rw [← Finset.disjoint_iff_inter_eq_empty]
        exact Finset.disjoint_of_subset_left hp.1 hAB
      rw [this, Finset.empty_union]
    simp [h1, h2]
  · intro P hP
    simp only [Finset.mem_coe, Finset.mem_powerset] at hP
    simp only
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.2 hP]
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset] at hp
    have h1 : (p.1 ∪ p.2) ∩ A = p.1 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 hp.1]
      have : p.2 ∩ A = ∅ := by
        rw [← Finset.disjoint_iff_inter_eq_empty]
        exact Finset.disjoint_of_subset_left hp.2 hAB.symm
      rw [this, Finset.union_empty]
    have h2 : (p.1 ∪ p.2) ∩ B = p.2 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 hp.2]
      have : p.1 ∩ B = ∅ := by
        rw [← Finset.disjoint_iff_inter_eq_empty]
        exact Finset.disjoint_of_subset_left hp.1 hAB
      rw [this, Finset.empty_union]
    simp [h1, h2]

/-- sums over subsets of a disjoint family factor -/
lemma sum_powerset_biUnion_prod {ι : Type*} [DecidableEq ι] (I : Finset ι) (U : ι → Finset β)
    (hU : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (U i) (U j)) (F : ι → Finset β → ℝ) :
    ∑ P ∈ (I.biUnion U).powerset, ∏ i ∈ I, F i (P ∩ U i) =
      ∏ i ∈ I, ∑ T ∈ (U i).powerset, F i T := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert ha]
    have hdisj : Disjoint (U a) (I.biUnion U) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hU a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    have key : ∀ P ∈ (U a ∪ I.biUnion U).powerset,
        F a (P ∩ U a) * ∏ i ∈ I, F i (P ∩ U i) =
          F a (P ∩ U a) * ∏ i ∈ I, F i ((P ∩ I.biUnion U) ∩ U i) := by
      intro P _
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      rw [Finset.inter_assoc, Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem U hi)]
    rw [Finset.sum_congr rfl (fun P hP => by rw [Finset.prod_insert ha]),
      Finset.sum_congr rfl key,
      sum_powerset_union_mul hdisj (F a) (fun T => ∏ i ∈ I, F i (T ∩ U i))]
    rw [ih (fun i hi j hj hij => hU i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)]

/-- the generating-function bound -/
lemma sum_card_eq_le_gf (U : Finset β) (L : ℕ) (W : Finset β → ℝ) (hW : ∀ P, 0 ≤ W P)
    (x : ℝ) (hx : 0 < x) :
    ∑ P ∈ U.powerset.filter (fun P => P.card = L), W P ≤
      (x ^ L)⁻¹ * ∑ P ∈ U.powerset, W P * x ^ P.card := by
  rw [Finset.mul_sum]
  calc ∑ P ∈ U.powerset.filter (fun P => P.card = L), W P
      = ∑ P ∈ U.powerset.filter (fun P => P.card = L), (x ^ L)⁻¹ * (W P * x ^ P.card) := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [Finset.mem_filter] at hP
        rw [hP.2]; field_simp
    _ ≤ ∑ P ∈ U.powerset, (x ^ L)⁻¹ * (W P * x ^ P.card) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro P _ _; have := hW P; positivity

/-- one interval: `∑_{T ⊆ U} (|T|/(e c N'))^{|T|} x^{|T|} ≤ 1/(1-ρx)` -/
lemma interval_gf (N : ℕ) (U : Finset β) (hU : U.card ≤ N) (c N' x ρ : ℝ) (hc : 0 < c)
    (hN' : 0 < N') (hx : 0 ≤ x) (hρ : (N : ℝ) / (c * N') ≤ ρ) (hρx : ρ * x < 1) :
    ∑ T ∈ U.powerset, ((T.card : ℝ) / (Real.exp 1 * c * N')) ^ T.card * x ^ T.card ≤
      1 / (1 - ρ * x) := by
  rw [Finset.sum_powerset_apply_card (fun s => ((s : ℝ) / (Real.exp 1 * c * N')) ^ s * x ^ s)]
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hterm : ∀ s, ((U.card.choose s : ℕ) : ℝ) * (((s : ℝ) / (Real.exp 1 * c * N')) ^ s * x ^ s) ≤
      (ρ * x) ^ s := by
    intro s
    have h1 : ((U.card.choose s : ℕ) : ℝ) ≤ (U.card : ℝ) ^ s / (s.factorial : ℝ) :=
      Nat.choose_le_pow_div s U.card
    have h2 : (s : ℝ) ^ s / (s.factorial : ℝ) ≤ Real.exp s :=
      Real.pow_div_factorial_le_exp (x := (s : ℝ)) (by positivity) s
    have hf : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
    have hes : Real.exp s = Real.exp 1 ^ s := by rw [← Real.exp_nat_mul]; ring_nf
    rw [hes] at h2
    have hUN : (U.card : ℝ) ≤ N := by exact_mod_cast hU
    calc ((U.card.choose s : ℕ) : ℝ) * (((s : ℝ) / (Real.exp 1 * c * N')) ^ s * x ^ s)
        ≤ (U.card : ℝ) ^ s / (s.factorial : ℝ) * (((s : ℝ) / (Real.exp 1 * c * N')) ^ s * x ^ s) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((s : ℝ) ^ s / (s.factorial : ℝ)) * ((U.card : ℝ) / (Real.exp 1 * c * N')) ^ s * x ^ s := by
          rw [div_pow, div_pow]; ring
      _ ≤ Real.exp 1 ^ s * ((U.card : ℝ) / (Real.exp 1 * c * N')) ^ s * x ^ s := by
          gcongr
      _ = ((U.card : ℝ) / (c * N')) ^ s * x ^ s := by
          rw [← mul_pow]; congr 2; field_simp
      _ ≤ ((N : ℝ) / (c * N')) ^ s * x ^ s := by gcongr
      _ ≤ ρ ^ s * x ^ s := by gcongr
      _ = (ρ * x) ^ s := by rw [mul_pow]
  calc ∑ s ∈ Finset.range (U.card + 1), (U.card.choose s) • (((s : ℝ) / (Real.exp 1 * c * N')) ^ s * x ^ s)
      ≤ ∑ s ∈ Finset.range (U.card + 1), (ρ * x) ^ s := by
        apply Finset.sum_le_sum; intro s _; rw [nsmul_eq_mul]; exact hterm s
    _ ≤ 1 / (1 - ρ * x) := by
        rw [geom_sum_eq (ne_of_lt hρx) _]
        have h0 : 0 < 1 - ρ * x := by linarith
        have e : ((ρ * x) ^ (U.card + 1) - 1) / (ρ * x - 1) =
            (1 - (ρ * x) ^ (U.card + 1)) / (1 - ρ * x) := by
          rw [← neg_div_neg_eq]; ring_nf
        rw [e]
        apply div_le_div_of_nonneg_right _ h0.le
        have : 0 ≤ (ρ * x) ^ (U.card + 1) := by positivity
        linarith

/-- the number of index sets of size at most `h` in `[0, L)` -/
lemma card_small_subsets (L h : ℕ) (hh : 1 ≤ h) (hLh : h ≤ L) :
    (((Finset.range L).powerset.filter (fun Q => Q.card ≤ h)).card : ℝ) ≤
      (Real.exp 1 * L / h) ^ h := by
  have hcount : ((Finset.range L).powerset.filter (fun Q => Q.card ≤ h)).card =
      ∑ r ∈ Finset.range (h + 1), L.choose r := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_powerset_apply_card (fun s => if s ≤ h then 1 else 0)]
    simp only [Finset.card_range, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext r; simp only [Finset.mem_filter, Finset.mem_range]; omega
    · intro _ _; rfl
  rw [hcount, Nat.cast_sum]
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hLR : (h : ℝ) ≤ L := by exact_mod_cast hLh
  have hratio : (1 : ℝ) ≤ L / h := by rw [le_div_iff₀ (by linarith)]; linarith
  calc ∑ r ∈ Finset.range (h + 1), ((L.choose r : ℕ) : ℝ)
      ≤ ∑ r ∈ Finset.range (h + 1), ((L : ℝ) / h) ^ h * ((h : ℝ) ^ r / r.factorial) := by
        apply Finset.sum_le_sum
        intro r hr
        rw [Finset.mem_range] at hr
        have h1 : ((L.choose r : ℕ) : ℝ) ≤ (L : ℝ) ^ r / (r.factorial : ℝ) := Nat.choose_le_pow_div r L
        have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
        refine h1.trans ?_
        have : (L : ℝ) ^ r = ((L : ℝ) / h) ^ r * (h : ℝ) ^ r := by
          rw [← mul_pow]; congr 1; field_simp
        rw [this, mul_div_assoc]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ hratio (by omega)
    _ = ((L : ℝ) / h) ^ h * ∑ r ∈ Finset.range (h + 1), (h : ℝ) ^ r / r.factorial := by
        rw [Finset.mul_sum]
    _ ≤ ((L : ℝ) / h) ^ h * Real.exp h := by
        apply mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) _)
          (by positivity)
    _ = (Real.exp 1 * L / h) ^ h := by
        rw [show Real.exp h = Real.exp 1 ^ h by rw [← Real.exp_nat_mul]; ring_nf, ← mul_pow]
        congr 1; ring

end count

end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM
open QueryDepthMIS RGMISFast

section jumps

lemma jumps_le (f : ℕ → ℕ) (hf : Monotone f) :
    ∀ L, ((Finset.Ico 1 (L + 1)).filter (fun k => f (k - 1) ≠ f k)).card ≤ f L - f 0 := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    have hI : Finset.Ico 1 (L + 1 + 1) = insert (L + 1) (Finset.Ico 1 (L + 1)) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hI, Finset.filter_insert]
    have h1 : f L ≤ f (L + 1) := hf (Nat.le_succ L)
    have h0 : f 0 ≤ f L := hf (Nat.zero_le L)
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
      simp only [Nat.add_sub_cancel] at h
      have : f L < f (L + 1) := lt_of_le_of_ne h1 h
      omega
    · have e : f (L + 1) - f 0 ≥ f L - f 0 := Nat.sub_le_sub_right h1 _
      exact ih.trans e

lemma card_odds (L : ℕ) : ((Finset.Ico 1 (L - 2)).filter Odd).card = (L - 2) / 2 := by
  have : (Finset.Ico 1 (L - 2)).filter Odd = (Finset.range ((L - 2) / 2)).image (fun t => 2 * t + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨t, rfl⟩⟩
      exact ⟨t, by omega, by ring⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨t, by ring⟩⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simp at h; omega), Finset.card_range]

end jumps

section perPQ
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {α β : ℝ} {P Q : Finset ℕ}

open Classical in
lemma count_TH (hc : ChainSet α β P (Fintype.card V)) (hL : 3 ≤ P.card) :
    (P.card - 2) / 2 ≤ ((Finset.Ico 1 (P.card - 1)).filter (THc α P Q)).card + Q.card +
      (ivI α (posK P (P.card - 1)) - ivI α (posK P 0)) := by
  have hsub : (Finset.Ico 1 (P.card - 2)).filter Odd ⊆
      ((Finset.Ico 1 (P.card - 1)).filter (THc α P Q)) ∪ Q ∪
        ((Finset.Ico 1 (P.card - 1 + 1)).filter
          (fun k => ivI α (posK P (k - 1)) ≠ ivI α (posK P k))) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    by_cases hs : ivI α (posK P (k - 1)) = ivI α (posK P k)
    · by_cases hq : k ∈ Q
      · exact Or.inl (Or.inr hq)
      · exact Or.inl (Or.inl ⟨⟨hk.1.1, by omega⟩, hk.2, by omega, hs, hq⟩)
    · exact Or.inr ⟨⟨hk.1.1, by omega⟩, hs⟩
  have hmono : Monotone (fun k => ivI α (posK P (min k (P.card - 1)))) := by
    intro a b hab
    apply ivI_mono hc.hα
    rcases Nat.eq_or_lt_of_le (min_le_min_right (P.card - 1) hab) with h | h
    · rw [h]
    · exact (posK_lt h (by omega)).le
  have hj := jumps_le _ hmono (P.card - 1)
  have hj' : ((Finset.Ico 1 (P.card - 1 + 1)).filter
      (fun k => ivI α (posK P (k - 1)) ≠ ivI α (posK P k))).card ≤
      ivI α (posK P (P.card - 1)) - ivI α (posK P 0) := by
    refine le_trans (le_of_eq ?_) (hj.trans (le_of_eq ?_))
    · congr 1
      apply Finset.filter_congr
      intro k hk
      simp only [Finset.mem_Ico] at hk
      simp only [min_eq_left (show k - 1 ≤ P.card - 1 by omega),
        min_eq_left (show k ≤ P.card - 1 by omega)]
    · simp
  have := Finset.card_le_card hsub
  rw [card_odds] at this
  refine this.trans ((Finset.card_union_le _ _).trans ?_)
  have := Finset.card_union_le ((Finset.Ico 1 (P.card - 1)).filter (THc α P Q)) Q
  omega

lemma prot_prod_le (hc : ChainSet α β P (Fintype.card V)) (hL : 3 ≤ P.card)
    (hellN : ∀ p ∈ P, (ellP α P (ivI α p) : ℝ) ≤ Fintype.card V) :
    ∏ j ∈ Finset.Ico 1 (P.card - 1), 1 / (Real.exp 1 * ((ProtK α P j).card : ℝ)) ≤
      (Real.exp 1 * Fintype.card V) ^ 2 *
        ∏ p ∈ P, 1 / (Real.exp 1 * (ellP α P (ivI α p) : ℝ)) := by
  set f : ℕ → ℝ := fun p => 1 / (Real.exp 1 * (ellP α P (ivI α p) : ℝ)) with hf
  have hfpos : ∀ p ∈ P, 0 < f p := by
    intro p hp; have := hc.hbig p hp
    simp only [hf]; apply div_pos one_pos; apply mul_pos (Real.exp_pos 1)
    exact_mod_cast (by omega : 0 < ellP α P (ivI α p))
  have h1 : ∏ j ∈ Finset.Ico 1 (P.card - 1), 1 / (Real.exp 1 * ((ProtK α P j).card : ℝ)) =
      ∏ k ∈ Finset.range (P.card - 2), f (posK P k) := by
    rw [Finset.prod_Ico_eq_prod_range, show P.card - 1 - 1 = P.card - 2 by omega]
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [hc.prot_card (by omega) (by omega)]
    simp [hf, Nat.add_sub_cancel_left]
  have h2 : ∏ p ∈ P, f p = ∏ k ∈ Finset.range P.card, f (posK P k) := by
    rw [← Finset.prod_image (s := Finset.range P.card) (g := posK P)]
    · congr 1
      ext p
      simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · intro hp
        rw [← Finset.mem_sort (· ≤ ·)] at hp
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hp
        rw [Finset.length_sort] at hk
        exact ⟨k, hk, by rw [posK_eq hk]⟩
      · rintro ⟨k, hk, rfl⟩; exact posK_mem hk
    · intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      rcases lt_trichotomy a b with h | h | h
      · exact absurd hab (posK_lt h hb).ne
      · exact h
      · exact absurd hab (posK_lt h ha).ne'
  rw [h1, h2]
  have hsplit : Finset.range P.card = insert (P.card - 1) (insert (P.card - 2)
      (Finset.range (P.card - 2))) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert]; omega
  rw [hsplit, Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp)]
  have hb : ∀ k, k < P.card → 1 / f (posK P k) ≤ Real.exp 1 * Fintype.card V := by
    intro k hk
    have hm := posK_mem hk
    simp only [hf, one_div, inv_inv]
    exact mul_le_mul_of_nonneg_left (hellN _ hm) (Real.exp_pos 1).le
  have hp1 := hfpos _ (posK_mem (k := P.card - 1) (by omega))
  have hp2 := hfpos _ (posK_mem (k := P.card - 2) (by omega))
  have hb1 := hb (P.card - 1) (by omega)
  have hb2 := hb (P.card - 2) (by omega)
  have hrest : 0 ≤ ∏ k ∈ Finset.range (P.card - 2), f (posK P k) :=
    Finset.prod_nonneg (fun k hk => (hfpos _ (posK_mem (by simp at hk; omega))).le)
  rw [div_le_iff₀ hp1] at hb1
  rw [div_le_iff₀ hp2] at hb2
  calc ∏ k ∈ Finset.range (P.card - 2), f (posK P k)
      = 1 * 1 * ∏ k ∈ Finset.range (P.card - 2), f (posK P k) := by ring
    _ ≤ (Real.exp 1 * Fintype.card V * f (posK P (P.card - 1))) *
        (Real.exp 1 * Fintype.card V * f (posK P (P.card - 2))) *
        ∏ k ∈ Finset.range (P.card - 2), f (posK P k) := by
        apply mul_le_mul_of_nonneg_right _ hrest
        exact mul_le_mul hb1 hb2 zero_le_one (by positivity)
    _ = _ := by ring

end perPQ

section perPQ2
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {α β : ℝ} {P Q : Finset ℕ}

theorem pathEv_prob_le (hc : ChainSet α β P (Fintype.card V)) (hβ0 : 0 < β)
    (hβ : β ≤ 1/100000) (hn : 2 ≤ Fintype.card V) (hL : 3 ≤ P.card)
    (hellN : ∀ p ∈ P, (ellP α P (ivI α p) : ℝ) ≤ Fintype.card V) (b₀ h : ℕ) (hQ : Q.card ≤ h)
    (hB : ivI α (posK P (P.card - 1)) ≤ b₀) :
    PunctSketch.coinProb (pathEv G P Q) ≤
      (1 - 1/5000 : ℝ) ^ ((P.card - 2) / 2 - h - b₀) * ((1 - β) ^ (P.card - 2))⁻¹ *
        (Real.exp 1 * Fintype.card V) ^ 2 *
        ∏ p ∈ P, 1 / (Real.exp 1 * (ellP α P (ivI α p) : ℝ)) := by
  classical
  obtain ⟨ω₀⟩ : Nonempty (Perm V) := ⟨Fintype.equivFin V⟩
  rw [coinProb_eq_condProb _ ω₀]
  have h1 : condProb (pathEv G P Q) ∅ ω₀ ≤ BndK α P Q β (1/5000) 1 :=
    condProb_le_of_finer _ (Finset.empty_subset _) _
      (fun ω => chain_main G hc hβ0 hβ hn (P.card - 2) 1 (by omega) le_rfl ω) ω₀
  have h2 := BndK_le (Q := Q) hc hβ0.le (by linarith) (1/5000) (by norm_num) (by norm_num)
    (P.card - 2) 1 (by omega) le_rfl
  refine h1.trans (h2.trans ?_)
  have hcount := count_TH (Q := Q) hc hL
  have hT : (P.card - 2) / 2 - h - b₀ ≤
      ((Finset.Ico 1 (P.card - 1)).filter (THc α P Q)).card := by omega
  have hpow : (1 - 1/5000 : ℝ) ^ ((Finset.Ico 1 (P.card - 1)).filter (THc α P Q)).card ≤
      (1 - 1/5000 : ℝ) ^ ((P.card - 2) / 2 - h - b₀) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hT
  have hprod := prot_prod_le hc hL hellN
  rw [show P.card - 1 - 1 = P.card - 2 by omega]
  have hb1 : 0 < 1 - β := by linarith
  have hprod0 : 0 ≤ ∏ j ∈ Finset.Ico 1 (P.card - 1), 1 / (Real.exp 1 * ((ProtK α P j).card : ℝ)) :=
    Finset.prod_nonneg (fun j _ => by positivity)
  calc (1 - 1/5000 : ℝ) ^ ((Finset.Ico 1 (P.card - 1)).filter (THc α P Q)).card *
        ((1 - β) ^ (P.card - 2))⁻¹ *
        ∏ j ∈ Finset.Ico 1 (P.card - 1), 1 / (Real.exp 1 * ((ProtK α P j).card : ℝ))
      ≤ (1 - 1/5000 : ℝ) ^ ((P.card - 2) / 2 - h - b₀) * ((1 - β) ^ (P.card - 2))⁻¹ *
        ((Real.exp 1 * Fintype.card V) ^ 2 *
          ∏ p ∈ P, 1 / (Real.exp 1 * (ellP α P (ivI α p) : ℝ))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hpow (by positivity)) hprod hprod0
          (by positivity)
    _ = _ := by ring

end perPQ2

section prefixsec
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma isQueryPath_take {r : V → ℕ} {l : List V} (hl : IsQueryPath G r l) {L : ℕ} (hL : 1 ≤ L) :
    IsQueryPath G r (l.take L) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with h | h
    · omega
    · exact hl.1.1 h
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_take] at hi
    simp only [List.getElem_take]
    exact List.isChain_iff_getElem.1 hl.1.2 i (by omega)
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_take] at hi
    simp only [List.getElem_take]
    exact List.isChain_iff_getElem.1 hl.2 i (by omega)

lemma shortcutIdx_take (l : List V) (L : ℕ) : shortcutIdx G (l.take L) ⊆ shortcutIdx G l := by
  intro i hi
  simp only [shortcutIdx, Finset.mem_filter, Finset.mem_range, List.length_take] at hi ⊢
  obtain ⟨h1, h2, hadj⟩ := hi
  refine ⟨by omega, by omega, ?_⟩
  simp only [List.getElem_take] at hadj
  exact hadj

lemma shortcutIdx_sub_range (l : List V) : shortcutIdx G l ⊆ Finset.range l.length :=
  Finset.filter_subset _ _

/-- a long query path in a set of positions yields a path event for some `(P, Q)` -/
lemma exists_pathEv (ω : Perm V) (l : List V) (hl : IsQueryPath G (rank ω) l) (L : ℕ)
    (hL : 1 ≤ L) (hlen : L ≤ l.length) :
    pathEv G ((l.take L).map (rank ω)).toFinset (shortcutIdx G (l.take L)) ω ∧
      (((l.take L).map (rank ω)).toFinset).card = L ∧
      (∀ p ∈ ((l.take L).map (rank ω)).toFinset, ∃ v ∈ l, rank ω v = p) := by
  have hq := isQueryPath_take G hl hL
  have hpw : ((l.take L).map (rank ω)).Pairwise (· < ·) := by
    rw [List.pairwise_map]; exact qp_sorted G hq
  have hnd : ((l.take L).map (rank ω)).Nodup := hpw.imp (fun h e => by rw [e] at h; exact lt_irrefl _ h)
  refine ⟨⟨l.take L, ?_, hq, rfl⟩, ?_, ?_⟩
  · -- the sorted listing of a sorted duplicate-free list is itself
    apply List.Perm.eq_of_pairwise (le := fun a b : ℕ => a < b)
    · intro a b _ _ h1 h2; omega
    · exact hpw
    · exact (Finset.sortedLT_sort _).pairwise
    · rw [List.perm_ext_iff_of_nodup hnd (Finset.sort_nodup _ _)]
      intro x; simp
  · rw [List.toFinset_card_of_nodup hnd]; simp; omega
  · intro p hp
    simp only [List.mem_toFinset, List.mem_map] at hp
    obtain ⟨v, hv, rfl⟩ := hp
    exact ⟨v, List.mem_of_mem_take hv, rfl⟩

end prefixsec

section midfacts

/-- the interval parameter `a = 2^{-20}` -/
noncomputable def aC : ℝ := 1 / 2 ^ 20

lemma aC_pos : 0 < aC := by unfold aC; positivity
lemma aC_le : aC ≤ 1 / 1000000 := by unfold aC; norm_num
lemma one_add_aC_sq : (1 + aC) ^ 2 ≤ 2 := by unfold aC; norm_num

/-- the middle range of positions -/
noncomputable def MidR (n : ℕ) (M : ℝ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun p => M < (p : ℝ) ∧ (p : ℝ) < aC * n)

variable {n : ℕ} {M : ℝ}

lemma mem_MidR {p : ℕ} : p ∈ MidR n M ↔ (1 ≤ p ∧ p ≤ n) ∧ M < (p : ℝ) ∧ (p : ℝ) < aC * n := by
  simp [MidR]

/-- size facts for the interval before that of a middle position -/
lemma mid_interval (hM : 4 ≤ M) {p : ℕ} (hp : p ∈ MidR n M) :
    2 ≤ ivI aC p ∧ aC * M / 2 - 1 ≤ ((Ivl aC (ivI aC p - 1)).card : ℝ) ∧
      (∀ x ∈ Ivl aC (ivI aC p - 1), M / 2 ≤ (x : ℝ) ∧ x < p) ∧
      ((Ivl aC (ivI aC p - 1)).card : ℝ) ≤ n := by
  rw [mem_MidR] at hp
  obtain ⟨⟨hp1, hpn⟩, hMp, _⟩ := hp
  have ha := aC_pos
  have hsp := ivI_spec ha p
  have hi1 := ivI_pos ha hp1
  set i := ivI aC p with hi
  have hlow : M / 2 < (1 + aC) ^ (i - 2) := by
    have h2 : (1 + aC) ^ i = (1 + aC) ^ 2 * (1 + aC) ^ (i - 2) := by
      rw [← pow_add]; congr 1
      by_contra hc
      have hi' : i = 1 := by omega
      rw [hi', pow_one] at hsp
      have : (p : ℝ) ≥ 4 := by linarith
      have : aC < 1 := by unfold aC; norm_num
      linarith
    have := one_add_aC_sq
    have hpos : 0 < (1 + aC) ^ (i - 2) := by positivity
    rw [h2] at hsp
    nlinarith
  have hi2 : 2 ≤ i := by
    by_contra hc
    have : i - 2 = 0 := by omega
    rw [this, pow_zero] at hlow
    linarith
  refine ⟨hi2, ?_, ?_, ?_⟩
  · have := card_Ivl_ge ha (i := i - 1) (by omega)
    rw [show i - 1 - 1 = i - 2 by omega] at this
    nlinarith
  · intro x hx
    rw [mem_Ivl ha] at hx
    rw [show i - 1 - 1 = i - 2 by omega] at hx
    refine ⟨by linarith [hx.1], ?_⟩
    have h1 := ivI_lower ha hp1
    rw [← hi] at h1
    have : (x : ℝ) < p := lt_of_lt_of_le hx.2 h1
    exact_mod_cast this
  · have hsub : Ivl aC (i - 1) ⊆ Finset.Icc 1 n := by
      intro x hx
      rw [mem_Ivl ha] at hx
      rw [show i - 1 - 1 = i - 2 by omega] at hx
      have h1 := ivI_lower ha hp1
      rw [← hi] at h1
      have hxp : (x : ℝ) < p := lt_of_lt_of_le hx.2 h1
      have hx1 : (1 : ℝ) ≤ x := by
        have : (1 : ℝ) ≤ (1 + aC) ^ (i - 2) := one_le_pow₀ (by linarith)
        linarith [hx.1]
      rw [Finset.mem_Icc]
      constructor
      · exact_mod_cast hx1
      · have : x < p := by exact_mod_cast hxp
        omega
    have := Finset.card_le_card hsub
    simp at this
    exact_mod_cast this

end midfacts

section midchain
variable {n : ℕ} {M : ℝ} {P : Finset ℕ}

lemma sOcc_bounds {p : ℕ} (hp : p ∈ P) :
    1 ≤ sOccP aC P (ivI aC p) ∧ sOccP aC P (ivI aC p) ≤ P.card := by
  constructor
  · exact Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨hp, rfl⟩⟩
  · exact Finset.card_filter_le _ _

theorem mid_chainset (hM : 4 ≤ M) (hNL : (P.card : ℝ) * 2 ^ 25 ≤ aC * M / 2 - 1)
    (hPsub : P ⊆ MidR n M) (hL1 : 1 ≤ P.card) :
    ChainSet aC aC P n ∧ (∀ p ∈ P, (ellP aC P (ivI aC p) : ℝ) ≤ n) ∧
      (∀ p ∈ P, 1 / (Real.exp 1 * (ellP aC P (ivI aC p) : ℝ)) ≤
        (sOccP aC P (ivI aC p) : ℝ) /
          (Real.exp 1 * (1 - 2 * aC) * ((Ivl aC (ivI aC p - 1)).card : ℝ))) := by
  have ha := aC_pos
  have ha' := aC_le
  have hLR : (1 : ℝ) ≤ P.card := by exact_mod_cast hL1
  -- the basic per-position estimates
  have key : ∀ p ∈ P, 2 ≤ ivI aC p ∧
      (P.card : ℝ) * 2 ^ 25 ≤ ((Ivl aC (ivI aC p - 1)).card : ℝ) ∧
      (∀ x ∈ Ivl aC (ivI aC p - 1), M / 2 ≤ (x : ℝ)) ∧
      ((Ivl aC (ivI aC p - 1)).card : ℝ) ≤ n := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := mid_interval hM (hPsub hp)
    exact ⟨h1, by linarith, fun x hx => (h3 x hx).1, h4⟩
  -- the floor estimates
  have hell : ∀ p ∈ P,
      (1 - aC) * ((Ivl aC (ivI aC p - 1)).card : ℝ) / (sOccP aC P (ivI aC p) : ℝ) - 1 ≤
        (ellP aC P (ivI aC p) : ℝ) ∧
      (ellP aC P (ivI aC p) : ℝ) * (sOccP aC P (ivI aC p) : ℝ) ≤
        (1 - aC) * ((Ivl aC (ivI aC p - 1)).card : ℝ) := by
    intro p hp
    have hs := sOcc_bounds (P := P) hp
    have hsR : (0 : ℝ) < sOccP aC P (ivI aC p) := by exact_mod_cast hs.1
    refine ⟨ellP_ge P _ hs.1, ?_⟩
    unfold ellP
    have := Nat.floor_le (show (0 : ℝ) ≤ (1 - aC) * ((Ivl aC (ivI aC p - 1)).card : ℝ) /
      (sOccP aC P (ivI aC p) : ℝ) by
        apply div_nonneg _ hsR.le; apply mul_nonneg (by linarith) (by positivity))
    rw [le_div_iff₀ hsR] at this
    exact this
  refine ⟨⟨ha, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- room
    intro p hp
    obtain ⟨h1, h2, _, _⟩ := key p hp
    refine ⟨h1, ?_⟩
    have havail : ((Ivl aC (ivI aC p - 1)).card : ℝ) - P.card ≤
        ((availP aC P (ivI aC p)).card : ℝ) := by
      unfold availP
      have := Finset.card_sdiff_add_card_inter (Ivl aC (ivI aC p - 1)) P
      have h3 : ((Ivl aC (ivI aC p - 1) ∩ P).card : ℝ) ≤ P.card := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      have h4 : ((Ivl aC (ivI aC p - 1) \ P).card : ℝ) + ((Ivl aC (ivI aC p - 1) ∩ P).card : ℝ) =
          ((Ivl aC (ivI aC p - 1)).card : ℝ) := by exact_mod_cast this
      linarith
    have h5 := (hell p hp).2
    have : (sOccP aC P (ivI aC p) * ellP aC P (ivI aC p) : ℝ) ≤
        ((availP aC P (ivI aC p)).card : ℝ) := by
      rw [mul_comm]
      refine h5.trans ?_
      have : aC * ((Ivl aC (ivI aC p - 1)).card : ℝ) ≥ P.card := by
        have : (P.card : ℝ) ≤ (P.card : ℝ) * 2 ^ 25 := by nlinarith
        have h6 : aC * ((P.card : ℝ) * 2 ^ 25) ≥ P.card := by unfold aC; nlinarith
        nlinarith
      linarith
    exact_mod_cast this
  · -- big blocks
    intro p hp
    obtain ⟨_, h2, _, _⟩ := key p hp
    have hs := sOcc_bounds (P := P) hp
    have hsL : (sOccP aC P (ivI aC p) : ℝ) ≤ P.card := by exact_mod_cast hs.2
    have hsR : (0 : ℝ) < sOccP aC P (ivI aC p) := by exact_mod_cast hs.1
    have h1 := (hell p hp).1
    have : (1001 : ℝ) < (ellP aC P (ivI aC p) : ℝ) := by
      have h7 : (1 - aC) * ((P.card : ℝ) * 2 ^ 25) / (sOccP aC P (ivI aC p) : ℝ) ≥
          (1 - aC) * 2 ^ 25 := by
        rw [ge_iff_le, le_div_iff₀ hsR]; nlinarith
      have h8 : (1 - aC) * ((Ivl aC (ivI aC p - 1)).card : ℝ) / (sOccP aC P (ivI aC p) : ℝ) ≥
          (1 - aC) * ((P.card : ℝ) * 2 ^ 25) / (sOccP aC P (ivI aC p) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hsR.le
        exact mul_le_mul_of_nonneg_left h2 (by linarith)
      have h9 : (1 - aC) * 2 ^ 25 ≥ (1002 : ℝ) := by unfold aC; norm_num
      linarith
    have : 1001 < ellP aC P (ivI aC p) := by exact_mod_cast this
    omega
  · -- blocks lie high
    intro p hp x hx
    obtain ⟨_, _, h3, _⟩ := key p hp
    have := h3 x (blkP_sub_Ivl p hx)
    have : (2 : ℝ) ≤ x := by linarith
    exact_mod_cast this
  · intro p hp; exact ((mem_MidR.1 (hPsub hp)).1).1
  · intro p hp; exact (mem_MidR.1 (hPsub hp)).2.2
  · -- block length at most n
    intro p hp
    obtain ⟨_, _, _, h4⟩ := key p hp
    have hs := sOcc_bounds (P := P) hp
    have hsR : (1 : ℝ) ≤ sOccP aC P (ivI aC p) := by exact_mod_cast hs.1
    have h5 := (hell p hp).2
    have : (ellP aC P (ivI aC p) : ℝ) ≤ ((Ivl aC (ivI aC p - 1)).card : ℝ) := by
      have h0 : (0 : ℝ) ≤ ellP aC P (ivI aC p) := by positivity
      nlinarith
    linarith
  · -- the weight bound
    intro p hp
    obtain ⟨_, h2, _, _⟩ := key p hp
    have hs := sOcc_bounds (P := P) hp
    have hsL : (sOccP aC P (ivI aC p) : ℝ) ≤ P.card := by exact_mod_cast hs.2
    have hsR : (0 : ℝ) < sOccP aC P (ivI aC p) := by exact_mod_cast hs.1
    have h1 := (hell p hp).1
    set N := ((Ivl aC (ivI aC p - 1)).card : ℝ)
    set sR := (sOccP aC P (ivI aC p) : ℝ)
    have hN : 0 < N := by nlinarith
    have hgood : (1 - 2 * aC) * N / sR ≤ (ellP aC P (ivI aC p) : ℝ) := by
      have : aC * N / sR ≥ 1 := by
        rw [ge_iff_le, le_div_iff₀ hsR]
        have : aC * (sR * 2 ^ 25) ≥ sR := by unfold aC; nlinarith
        nlinarith
      have e : (1 - 2 * aC) * N / sR = (1 - aC) * N / sR - aC * N / sR := by ring
      linarith
    have hpos : 0 < (1 - 2 * aC) * N / sR := by
      apply div_pos _ hsR; apply mul_pos _ hN; unfold aC; norm_num
    have hellpos : (0 : ℝ) < ellP aC P (ivI aC p) := lt_of_lt_of_le hpos hgood
    have h2a : (0 : ℝ) < 1 - 2 * aC := by unfold aC; norm_num
    rw [div_le_div_iff₀ (mul_pos (Real.exp_pos 1) hellpos)
      (mul_pos (mul_pos (Real.exp_pos 1) h2a) hN)]
    have : (1 - 2 * aC) * N ≤ (ellP aC P (ivI aC p) : ℝ) * sR := by
      rw [div_le_iff₀ hsR] at hgood; linarith
    nlinarith [Real.exp_pos 1]

end midchain

section midsum
variable {n : ℕ} {M : ℝ}

noncomputable def xC : ℝ := (1 - aC) * (1 - 2 * aC) / (1 + 2 * aC)

lemma xC_pos : 0 < xC := by unfold xC aC; norm_num

/-- the per-interval weight -/
noncomputable def wC (i s : ℕ) : ℝ :=
  ((s : ℝ) / (Real.exp 1 * (1 - 2 * aC) * ((Ivl aC (i - 1)).card : ℝ))) ^ s

lemma wC_nonneg (i s : ℕ) : 0 ≤ wC i s := by
  unfold wC
  have : (0 : ℝ) ≤ 1 - 2 * aC := by unfold aC; norm_num
  positivity

lemma Ivl_zero : Ivl aC 0 = ∅ := by
  unfold Ivl; simp

lemma filter_ivI_eq {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p) (i : ℕ) :
    P.filter (fun p => ivI aC p = i) = P ∩ Ivl aC i := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hp, rfl⟩
    exact ⟨hp, (mem_Ivl_iff_ivI aC_pos (ivI_pos aC_pos (hP p hp)) (hP p hp)).2 rfl⟩
  · rintro ⟨hp, hi⟩
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; rw [Ivl_zero] at hi; simp at hi
    · exact ⟨hp, (mem_Ivl_iff_ivI aC_pos h0 (hP p hp)).1 hi⟩

theorem sum_W_le (hM : 4 ≤ M) (L : ℕ) (hL1 : 1 ≤ L) (hNL : (L : ℝ) * 2 ^ 25 ≤ aC * M / 2 - 1)
    (b₀ : ℕ) (hb₀ : ∀ p ∈ MidR n M, ivI aC p ≤ b₀) :
    ∑ P ∈ (MidR n M).powerset.filter (fun P => P.card = L),
        ∏ p ∈ P, 1 / (Real.exp 1 * (ellP aC P (ivI aC p) : ℝ)) ≤
      (xC ^ L)⁻¹ * (1 / aC) ^ (b₀ + 1) := by
  classical
  have ha := aC_pos
  set ι := Finset.range (b₀ + 1) with hι
  set U : ℕ → Finset ℕ := fun i => MidR n M ∩ Ivl aC i with hU
  set c : ℝ := 1 - 2 * aC with hc
  have hc0 : 0 < c := by rw [hc]; unfold aC; norm_num
  have hMid1 : ∀ p ∈ MidR n M, 1 ≤ p := fun p hp => (mem_MidR.1 hp).1.1
  -- the cover
  have hcover : MidR n M = ι.biUnion U := by
    ext p
    simp only [Finset.mem_biUnion, hU, Finset.mem_inter, hι, Finset.mem_range]
    constructor
    · intro hp
      refine ⟨ivI aC p, by have := hb₀ p hp; omega, hp, ?_⟩
      exact (mem_Ivl_iff_ivI ha (ivI_pos ha (hMid1 p hp)) (hMid1 p hp)).2 rfl
    · rintro ⟨i, _, hp, _⟩; exact hp
  have hdisj : ∀ i ∈ ι, ∀ j ∈ ι, i ≠ j → Disjoint (U i) (U j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro p hpi hpj
    simp only [hU, Finset.mem_inter] at hpi hpj
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; rw [Ivl_zero] at hpi; simp at hpi
    rcases Nat.eq_zero_or_pos j with h0' | h0'
    · subst h0'; rw [Ivl_zero] at hpj; simp at hpj
    have := (mem_Ivl_iff_ivI ha h0 (hMid1 p hpi.1)).1 hpi.2
    have := (mem_Ivl_iff_ivI ha h0' (hMid1 p hpj.1)).1 hpj.2
    omega
  -- per-set weight bound
  have hWle : ∀ P ∈ (MidR n M).powerset.filter (fun P => P.card = L),
      ∏ p ∈ P, 1 / (Real.exp 1 * (ellP aC P (ivI aC p) : ℝ)) ≤
        ∏ i ∈ ι, wC i (P ∩ U i).card := by
    intro P hP
    simp only [Finset.mem_filter, Finset.mem_powerset] at hP
    obtain ⟨hPsub, hPL⟩ := hP
    have hch := mid_chainset (n := n) hM (by rw [hPL]; exact hNL) hPsub (by omega)
    have hP1 : ∀ p ∈ P, 1 ≤ p := fun p hp => hMid1 p (hPsub hp)
    calc ∏ p ∈ P, 1 / (Real.exp 1 * (ellP aC P (ivI aC p) : ℝ))
        ≤ ∏ p ∈ P, (sOccP aC P (ivI aC p) : ℝ) /
          (Real.exp 1 * c * ((Ivl aC (ivI aC p - 1)).card : ℝ)) := by
          apply Finset.prod_le_prod (fun p _ => by positivity)
          intro p hp; rw [hc]; exact hch.2.2 p hp
      _ = ∏ i ∈ ι, ∏ p ∈ P.filter (fun p => ivI aC p = i), (sOccP aC P (ivI aC p) : ℝ) /
          (Real.exp 1 * c * ((Ivl aC (ivI aC p - 1)).card : ℝ)) := by
          rw [Finset.prod_fiberwise_of_maps_to]
          intro p hp
          simp only [hι, Finset.mem_range]
          have := hb₀ p (hPsub hp); omega
      _ = ∏ i ∈ ι, wC i (P ∩ U i).card := by
          unfold wC
          apply Finset.prod_congr rfl
          intro i _
          rw [Finset.prod_congr rfl (fun p hp => by
            rw [(Finset.mem_filter.1 hp).2])]
          rw [Finset.prod_const]
          have hcardeq : (P.filter (fun p => ivI aC p = i)).card = (P ∩ U i).card := by
            rw [filter_ivI_eq hP1]
            congr 1
            simp only [hU]
            rw [← Finset.inter_assoc, Finset.inter_eq_left.2 hPsub]
          have hs : sOccP aC P i = (P ∩ U i).card := hcardeq
          rw [hs, hcardeq]
  refine (Finset.sum_le_sum hWle).trans ?_
  -- the generating-function bound
  have hgf := sum_card_eq_le_gf (MidR n M) L (fun P => ∏ i ∈ ι, wC i (P ∩ U i).card)
    (fun P => Finset.prod_nonneg (fun i _ => wC_nonneg _ _)) xC xC_pos
  refine hgf.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by have := xC_pos; positivity)
  have hfac : ∀ P ∈ (MidR n M).powerset,
      (∏ i ∈ ι, wC i (P ∩ U i).card) * xC ^ P.card =
        ∏ i ∈ ι, (wC i (P ∩ U i).card * xC ^ (P ∩ U i).card) := by
    intro P hP
    rw [Finset.mem_powerset] at hP
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    congr 2
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_inter]
      constructor
      · intro hp
        have := hP hp
        rw [hcover, Finset.mem_biUnion] at this
        obtain ⟨i, hi, hpi⟩ := this
        exact ⟨i, hi, hp, hpi⟩
      · rintro ⟨i, _, hp, _⟩; exact hp
    · intro i hi j hj hij
      exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right (hdisj i hi j hj hij))
  rw [Finset.sum_congr rfl hfac]
  have hps := sum_powerset_biUnion_prod ι U hdisj (fun i T => wC i T.card * xC ^ T.card)
  rw [← hcover] at hps
  rw [hps]
  have hfin : ∀ i ∈ ι, ∑ T ∈ (U i).powerset, wC i T.card * xC ^ T.card ≤ 1 / aC := by
    intro i _
    by_cases hne : (U i).Nonempty
    · obtain ⟨p, hp⟩ := hne
      simp only [hU, Finset.mem_inter] at hp
      have hpi : ivI aC p = i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · subst h0; rw [Ivl_zero] at hp; simp at hp
        · exact (mem_Ivl_iff_ivI ha h0 (hMid1 p hp.1)).1 hp.2
      obtain ⟨hi2, hN, _, _⟩ := mid_interval hM hp.1
      rw [hpi] at hi2 hN
      -- the ratio of consecutive interval lengths
      have hLR1 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
      have hNbig : (2 : ℝ) ^ 25 ≤ ((Ivl aC (i - 1)).card : ℝ) := by nlinarith
      have hZ : (2 : ℝ) ^ 24 ≤ aC * (1 + aC) ^ (i - 2) := by
        have h1 := card_Ivl_le ha (i := i - 1) (by omega)
        rw [show i - 1 - 1 = i - 2 by omega] at h1
        linarith
      have hratio : ((Ivl aC i).card : ℝ) / (c * ((Ivl aC (i - 1)).card : ℝ)) ≤
          (1 + 2 * aC) / c := by
        have h1 := card_Ivl_le ha (i := i) (by omega)
        have h2 := card_Ivl_ge ha (i := i - 1) (by omega)
        rw [show i - 1 - 1 = i - 2 by omega] at h2
        have he : (1 + aC) ^ (i - 1) = (1 + aC) * (1 + aC) ^ (i - 2) := by
          rw [← pow_succ']; congr 1; omega
        rw [he] at h1
        have hNpos : (0 : ℝ) < ((Ivl aC (i - 1)).card : ℝ) := by linarith
        rw [div_le_div_iff₀ (mul_pos hc0 hNpos) hc0]
        have : ((Ivl aC i).card : ℝ) ≤ (1 + 2 * aC) * ((Ivl aC (i - 1)).card : ℝ) := by
          have h3 : aC * (aC * (1 + aC) ^ (i - 2)) ≥ aC * 2 ^ 24 := by nlinarith
          have h4 : aC * 2 ^ 24 ≥ (2 : ℝ) + 2 * aC := by unfold aC; norm_num
          nlinarith
        nlinarith
      have hρx : (1 + 2 * aC) / c * xC = 1 - aC := by
        have h1 : (1 : ℝ) - 2 * aC ≠ 0 := by unfold aC; norm_num
        have h2 : (1 : ℝ) + 2 * aC ≠ 0 := by unfold aC; norm_num
        rw [hc]; unfold xC; field_simp
      have := interval_gf (Ivl aC i).card (U i) (Finset.card_le_card Finset.inter_subset_right)
        c ((Ivl aC (i - 1)).card : ℝ) xC ((1 + 2 * aC) / c) hc0
        (by linarith) xC_pos.le hratio (by rw [hρx]; linarith)
      rw [hρx, show (1 : ℝ) - (1 - aC) = aC by ring] at this
      unfold wC; rw [← hc]; exact this
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, wC,
        Nat.cast_zero, pow_zero, mul_one]
      rw [le_div_iff₀ ha, one_mul]; unfold aC; norm_num
  calc ∏ i ∈ ι, ∑ T ∈ (U i).powerset, wC i T.card * xC ^ T.card
      ≤ ∏ i ∈ ι, (1 / aC) := Finset.prod_le_prod
        (fun i _ => Finset.sum_nonneg (fun T _ => by
          have := xC_pos; have := wC_nonneg i T.card; positivity))
        hfin
    _ = (1 / aC) ^ (b₀ + 1) := by rw [Finset.prod_const, hι, Finset.card_range]

end midsum

section numeric

lemma inv_one_sub_le_exp {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1/2) : 1 / (1 - t) ≤ Real.exp (2 * t) := by
  rw [div_le_iff₀ (by linarith)]
  have := Real.add_one_le_exp (2 * t)
  nlinarith

lemma two_le_exp_07 : (2 : ℝ) ≤ Real.exp 0.7 := by
  have h := Real.log_two_lt_d9
  have : Real.log 2 ≤ 0.7 := by linarith
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp 0.7 := Real.exp_le_exp.2 this

lemma pow_le_exp_of_le {x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ Real.exp c) (k : ℕ) :
    x ^ k ≤ Real.exp (c * k) := by
  calc x ^ k ≤ Real.exp c ^ k := pow_le_pow_left₀ hx hxc k
    _ = Real.exp (c * k) := by rw [← Real.exp_nat_mul]; ring_nf

set_option maxHeartbeats 1000000 in
theorem mid_numeric (nR : ℝ) (hn : 2 ≤ nR) (L h b₀ : ℕ)
    (hL1 : 2 ^ 60 * Real.logb 2 nR ≤ L) (hL2 : (L : ℝ) ≤ 2 ^ 60 * Real.logb 2 nR + 1)
    (hh1 : 18 * Real.logb 2 nR ≤ h) (hh2 : (h : ℝ) ≤ 18 * Real.logb 2 nR + 1)
    (hb : (b₀ : ℝ) ≤ 2 ^ 20 * (Real.logb 2 nR + 1)) :
    (Real.exp 1 * L / h) ^ h * (1 - 1/5000 : ℝ) ^ ((L - 2) / 2 - h - b₀) *
      ((1 - aC) ^ (L - 2))⁻¹ * (Real.exp 1 * nR) ^ 2 * (xC ^ L)⁻¹ * (1 / aC) ^ (b₀ + 1) ≤
      1 / nR ^ 7 := by
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = Real.logb 2 nR := ⟨_, rfl⟩
  rw [← hlam] at hL1 hL2 hh1 hh2 hb
  have hlam1 : 1 ≤ lam := by
    rw [hlam, Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hn
  have hlogn : Real.log nR = lam * Real.log 2 := by
    rw [hlam, Real.logb, div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne']
  have hln2 : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  have hln2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha := aC_pos
  have ha' : aC ≤ 1 / 1000000 := aC_le
  have hLpos : (0 : ℝ) < L := by nlinarith
  have hhpos : (0 : ℝ) < h := by nlinarith
  -- F1
  have hF1 : (Real.exp 1 * L / h) ^ h ≤ Real.exp (800 * lam) := by
    have hq : Real.exp 1 * L / h ≤ Real.exp 42 := by
      rw [div_le_iff₀ hhpos]
      have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
      have h60 : (2 : ℝ) ^ 60 ≤ Real.exp 42 := by
        calc (2 : ℝ) ^ 60 ≤ Real.exp 0.7 ^ 60 := pow_le_pow_left₀ (by norm_num) two_le_exp_07 60
          _ = Real.exp 42 := by rw [← Real.exp_nat_mul]; norm_num
      have : Real.exp 1 * L ≤ 3 * (2 ^ 60 * lam + 1) := by nlinarith [Real.exp_pos 1]
      nlinarith
    calc (Real.exp 1 * L / h) ^ h ≤ Real.exp (42 * h) :=
          pow_le_exp_of_le (by positivity) hq h
      _ ≤ Real.exp (800 * lam) := Real.exp_le_exp.2 (by nlinarith)
  -- F2
  have hT : (L : ℝ) / 2 - 2 - h - b₀ ≤ (((L - 2) / 2 - h - b₀ : ℕ) : ℝ) := by
    have h1 : ((L - 2) / 2 : ℕ) * 2 + 1 ≥ L - 2 := by omega
    have h2 : (((L - 2) / 2 : ℕ) : ℝ) ≥ (L : ℝ) / 2 - 2 := by
      have h3 : ((((L - 2) / 2 : ℕ) * 2 + 1 : ℕ) : ℝ) ≥ ((L - 2 : ℕ) : ℝ) := by exact_mod_cast h1
      have h4 : ((L - 2 : ℕ) : ℝ) ≥ (L : ℝ) - 2 := by
        rcases Nat.lt_or_ge L 2 with hl | hl
        · have : (L : ℝ) < 2 := by exact_mod_cast hl
          have : (0 : ℝ) ≤ ((L - 2 : ℕ) : ℝ) := by positivity
          linarith
        · rw [Nat.cast_sub hl]; simp
      push_cast at h3
      linarith
    have h5 : ((((L - 2) / 2 - h - b₀) : ℕ) : ℝ) ≥ (((L - 2) / 2 : ℕ) : ℝ) - h - b₀ := by
      have : ((L - 2) / 2 - h - b₀) + h + b₀ ≥ (L - 2) / 2 := by omega
      have : ((((L - 2) / 2 - h - b₀) + h + b₀ : ℕ) : ℝ) ≥ (((L - 2) / 2 : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at this; linarith
    linarith
  have hF2 : (1 - 1/5000 : ℝ) ^ ((L - 2) / 2 - h - b₀) ≤
      Real.exp (-(1/5000) * ((L : ℝ) / 2 - 2 - h - b₀)) := by
    have h1 : (1 - 1/5000 : ℝ) ≤ Real.exp (-(1/5000)) := by
      have := Real.add_one_le_exp (-(1/5000 : ℝ)); linarith
    calc (1 - 1/5000 : ℝ) ^ ((L - 2) / 2 - h - b₀)
        ≤ Real.exp (-(1/5000) * (((L - 2) / 2 - h - b₀ : ℕ) : ℝ)) :=
          pow_le_exp_of_le (by norm_num) h1 _
      _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)
  -- F3
  have hF3 : ((1 - aC) ^ (L - 2))⁻¹ ≤ Real.exp (2 * aC * L) := by
    have h1 : 1 / (1 - aC) ≤ Real.exp (2 * aC) := inv_one_sub_le_exp ha.le (by linarith)
    have h2 : ((1 - aC) ^ (L - 2))⁻¹ = (1 / (1 - aC)) ^ (L - 2) := by rw [one_div, inv_pow]
    rw [h2]
    have hpos1 : (0 : ℝ) ≤ 1 / (1 - aC) := by
      have : 0 < 1 - aC := by linarith
      positivity
    calc (1 / (1 - aC)) ^ (L - 2) ≤ Real.exp (2 * aC * ((L - 2 : ℕ) : ℝ)) :=
          pow_le_exp_of_le hpos1 h1 _
      _ ≤ Real.exp (2 * aC * L) := by
          apply Real.exp_le_exp.2
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast Nat.sub_le L 2
  -- F4
  have hF4 : (Real.exp 1 * nR) ^ 2 ≤ Real.exp (4 * lam) := by
    have h1 : nR = Real.exp (lam * Real.log 2) := by
      rw [← hlogn, Real.exp_log (by linarith)]
    rw [h1, ← Real.exp_add, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    push_cast; nlinarith
  -- F5
  have hF5 : (xC ^ L)⁻¹ ≤ Real.exp (8 * aC * L) := by
    have h1 : 1 / xC ≤ Real.exp (8 * aC) := by
      unfold xC
      have e : 1 / ((1 - aC) * (1 - 2 * aC) / (1 + 2 * aC)) =
          (1 / (1 - aC)) * (1 / (1 - 2 * aC)) * (1 + 2 * aC) := by
        have : (1 : ℝ) - aC ≠ 0 := by linarith
        have : (1 : ℝ) - 2 * aC ≠ 0 := by linarith
        field_simp
      rw [e]
      have g1 := inv_one_sub_le_exp ha.le (by linarith : aC ≤ 1/2)
      have g2 := inv_one_sub_le_exp (by linarith : 0 ≤ 2 * aC) (by linarith : 2 * aC ≤ 1/2)
      have g3 : 1 + 2 * aC ≤ Real.exp (2 * aC) := by
        have := Real.add_one_le_exp (2 * aC); linarith
      have hp2 : (0 : ℝ) ≤ 1 / (1 - 2 * aC) := by
        have : 0 < 1 - 2 * aC := by linarith
        positivity
      calc 1 / (1 - aC) * (1 / (1 - 2 * aC)) * (1 + 2 * aC)
          ≤ Real.exp (2 * aC) * Real.exp (2 * (2 * aC)) * Real.exp (2 * aC) := by
            apply mul_le_mul (mul_le_mul g1 g2 hp2 (Real.exp_pos _).le) g3
              (by linarith) (by positivity)
        _ = Real.exp (8 * aC) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hx0 : (0 : ℝ) ≤ 1 / xC := by have := xC_pos; positivity
    have h2 := pow_le_exp_of_le hx0 h1 L
    rw [one_div, inv_pow] at h2
    exact h2
  -- F6
  have hF6 : (1 / aC) ^ (b₀ + 1) ≤ Real.exp (15 * 2 ^ 21 * lam) := by
    have h1 : 1 / aC ≤ Real.exp 14 := by
      unfold aC
      rw [one_div_one_div]
      calc (2 : ℝ) ^ 20 ≤ Real.exp 0.7 ^ 20 := pow_le_pow_left₀ (by norm_num) two_le_exp_07 20
        _ = Real.exp 14 := by rw [← Real.exp_nat_mul]; norm_num
    calc (1 / aC) ^ (b₀ + 1) ≤ Real.exp (14 * ((b₀ + 1 : ℕ) : ℝ)) :=
          pow_le_exp_of_le (by positivity) h1 _
      _ ≤ _ := Real.exp_le_exp.2 (by push_cast; nlinarith)
  -- combine
  have hprod : (Real.exp 1 * L / h) ^ h * (1 - 1/5000 : ℝ) ^ ((L - 2) / 2 - h - b₀) *
      ((1 - aC) ^ (L - 2))⁻¹ * (Real.exp 1 * nR) ^ 2 * (xC ^ L)⁻¹ * (1 / aC) ^ (b₀ + 1) ≤
      Real.exp (800 * lam) * Real.exp (-(1/5000) * ((L : ℝ) / 2 - 2 - h - b₀)) *
        Real.exp (2 * aC * L) * Real.exp (4 * lam) * Real.exp (8 * aC * L) *
        Real.exp (15 * 2 ^ 21 * lam) := by
    have i1 : 0 ≤ (xC ^ L)⁻¹ := inv_nonneg.2 (pow_nonneg xC_pos.le _)
    have i2 : 0 ≤ ((1 - aC) ^ (L - 2))⁻¹ := inv_nonneg.2 (pow_nonneg (by linarith) _)
    gcongr
  refine hprod.trans ?_
  simp only [← Real.exp_add]
  have hfinal : 800 * lam + -(1/5000) * ((L : ℝ) / 2 - 2 - h - b₀) + 2 * aC * L + 4 * lam +
      8 * aC * L + 15 * 2 ^ 21 * lam ≤ -6 * lam := by
    have : 10 * aC * L ≤ (1/100000) * L := by
      have : 10 * aC ≤ 1/100000 := by linarith
      nlinarith
    nlinarith
  calc Real.exp (800 * lam + -(1/5000) * ((L : ℝ) / 2 - 2 - h - b₀) + 2 * aC * L + 4 * lam +
        8 * aC * L + 15 * 2 ^ 21 * lam) ≤ Real.exp (-6 * lam) := Real.exp_le_exp.2 hfinal
    _ ≤ 1 / nR ^ 7 := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : nR ^ 7 = Real.exp (7 * (lam * Real.log 2)) := by
          rw [show nR ^ 7 = Real.exp (Real.log nR) ^ 7 by rw [Real.exp_log (by linarith)],
            ← Real.exp_nat_mul, hlogn]; push_cast; ring_nf
        rw [h1, ← Real.exp_add]
        apply Real.exp_le_one_iff.2
        nlinarith

end numeric


end QDM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QDM
open QueryDepthMIS RGMISFast

section lemma310
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma condProb_or_le (A B : Perm V → Prop) (S : Finset ℕ) (ω₀ : Perm V) :
    condProb (fun ω => A ω ∨ B ω) S ω₀ ≤ condProb A S ω₀ + condProb B S ω₀ := by
  have := condProb_union_le (Finset.univ : Finset (Fin 2))
    (fun i => if i = 0 then A else B) S ω₀
  simp only [Fin.sum_univ_two, Fin.isValue, if_pos, one_ne_zero, if_false] at this
  refine le_trans (condProb_mono (fun ω h => ?_) _ _) this
  rcases h with h | h
  · exact ⟨0, Finset.mem_univ _, by simpa using h⟩
  · exact ⟨1, Finset.mem_univ _, by simpa using h⟩

lemma n_le_pow_b0 {nR : ℝ} (hn : 2 ≤ nR) :
    nR ≤ (1 + aC) ^ (2 ^ 20 * ⌈Real.logb 2 nR⌉₊) := by
  have h1 : (2 : ℝ) ≤ (1 + aC) ^ (2 ^ 20) := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ aC by have := aC_pos; linarith) (2 ^ 20)
    have e : ((2 ^ 20 : ℕ) : ℝ) * aC = 1 := by unfold aC; norm_num
    rw [e] at this
    generalize (1 + aC) ^ (2 ^ 20) = X at this ⊢
    linarith
  have h2 : nR = (2 : ℝ) ^ (Real.logb 2 nR) := (Real.rpow_logb (by norm_num) (by norm_num)
    (by linarith)).symm
  rw [pow_mul]
  calc nR = (2 : ℝ) ^ (Real.logb 2 nR) := h2
    _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 nR⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = (2 : ℝ) ^ ⌈Real.logb 2 nR⌉₊ := Real.rpow_natCast _ _
    _ ≤ ((1 + aC) ^ 2 ^ 20) ^ ⌈Real.logb 2 nR⌉₊ := pow_le_pow_left₀ (by norm_num) h1 _

theorem lemma_3_10_core (hn : 2 ≤ Fintype.card V) :
    1 - 1 / (Fintype.card V : ℝ) ^ 6 ≤
      PunctSketch.coinProb (fun ω : Perm V => ∀ l : List V, IsQueryPath G (rank ω) l →
        (∀ v ∈ l, 2 ^ 120 * Real.logb 2 (Fintype.card V) < (rank ω v : ℝ) ∧
          (rank ω v : ℝ) < aC * (Fintype.card V : ℝ)) →
        l.length < ⌈2 ^ 60 * Real.logb 2 (Fintype.card V)⌉₊) := by
  classical
  obtain ⟨ω₀⟩ : Nonempty (Perm V) := ⟨Fintype.equivFin V⟩
  set n := Fintype.card V with hndef
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = Real.logb 2 (n : ℝ) := ⟨_, rfl⟩
  have hlam1 : 1 ≤ lam := by
    rw [hlam, Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hnR
  rw [← hlam]
  set M : ℝ := 2 ^ 120 * lam with hM
  set L : ℕ := ⌈2 ^ 60 * lam⌉₊ with hL
  set h : ℕ := ⌈18 * Real.logb 2 (n : ℝ)⌉₊ with hh
  set b₀ : ℕ := 2 ^ 20 * ⌈lam⌉₊ with hb₀
  have hL1 : 2 ^ 60 * lam ≤ L := Nat.le_ceil _
  have hL2 : (L : ℝ) ≤ 2 ^ 60 * lam + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (by linarith))).le
  have hh1 : 18 * lam ≤ h := by rw [hlam]; exact Nat.le_ceil _
  have hh2 : (h : ℝ) ≤ 18 * lam + 1 := by
    have := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 18 * Real.logb 2 (n : ℝ) by
      rw [← hlam]; linarith)).le
    rw [hlam]; exact this
  have hb₀R : (b₀ : ℝ) ≤ 2 ^ 20 * (lam + 1) := by
    rw [hb₀]; push_cast
    have := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ lam by linarith)).le
    linarith
  have hL3 : 3 ≤ L := by
    have : (3 : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hhL : h ≤ L := by
    have : (h : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hh1' : 1 ≤ h := by
    have : (1 : ℝ) ≤ h := by linarith
    exact_mod_cast this
  have hM4 : (4 : ℝ) ≤ M := by rw [hM]; linarith
  have hNL : (L : ℝ) * 2 ^ 25 ≤ aC * M / 2 - 1 := by
    rw [hM]; unfold aC; linarith
  have hb0mid : ∀ p ∈ MidR n M, ivI aC p ≤ b₀ := by
    intro p hp
    apply ivI_le_of aC_pos
    obtain ⟨⟨_, _⟩, _, hpβ⟩ := mem_MidR.1 hp
    have := n_le_pow_b0 hnR
    rw [← hlam] at this
    have hβ1 : aC * (n : ℝ) ≤ n :=
      mul_le_of_le_one_left (by positivity) (by unfold aC; norm_num)
    linarith
  -- the bad event
  set PP := (MidR n M).powerset.filter (fun P => P.card = L) with hPP
  set QQ := (Finset.range L).powerset.filter (fun Q => Q.card ≤ h) with hQQ
  have hincl : ∀ ω : Perm V, ¬ (∀ l : List V, IsQueryPath G (rank ω) l →
      (∀ v ∈ l, M < (rank ω v : ℝ) ∧ (rank ω v : ℝ) < aC * (n : ℝ)) → l.length < L) →
      (∃ l : List V, IsQueryPath G (rank ω) l ∧ h < (shortcutIdx G l).card) ∨
      (∃ P ∈ PP, ∃ Q ∈ QQ, pathEv G P Q ω) := by
    intro ω hbad
    push Not at hbad
    obtain ⟨l, hl, hrng, hlen⟩ := hbad
    by_cases hsc : h < (shortcutIdx G l).card
    · exact Or.inl ⟨l, hl, hsc⟩
    · right
      push Not at hsc
      obtain ⟨hev, hcard, hmem⟩ := exists_pathEv G ω l hl L (by omega) hlen
      refine ⟨_, ?_, _, ?_, hev⟩
      · simp only [hPP, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, hcard⟩
        intro p hp
        obtain ⟨v, hv, rfl⟩ := hmem p hp
        rw [mem_MidR]
        exact ⟨⟨rank_pos _ _, rank_le _ _⟩, (hrng v hv).1, (hrng v hv).2⟩
      · simp only [hQQ, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, (Finset.card_le_card (shortcutIdx_take G l L)).trans hsc⟩
        intro i hi
        have := shortcutIdx_sub_range G (l.take L) hi
        simp only [Finset.mem_range, List.length_take] at this ⊢
        omega
  -- bound on the first part
  have hbad1 : condProb (fun ω : Perm V => ∃ l : List V, IsQueryPath G (rank ω) l ∧
      h < (shortcutIdx G l).card) ∅ ω₀ ≤ 1 / (n : ℝ) ^ 7 := by
    have h1 := lemma_3_4_part2 G hn
    rw [coinProb_eq_condProb _ ω₀] at h1
    have h2 := condProb_compl (S := ∅) (ω₀ := ω₀) (fun ω : Perm V => ∃ l : List V,
      IsQueryPath G (rank ω) l ∧ h < (shortcutIdx G l).card)
    have h3 : condProb (fun ω : Perm V => ∀ l : List V, IsQueryPath G (rank ω) l →
        (shortcutIdx G l).card ≤ ⌈18 * Real.logb 2 (n : ℝ)⌉₊) ∅ ω₀ ≤
        condProb (fun ω : Perm V => ¬ ∃ l : List V, IsQueryPath G (rank ω) l ∧
          h < (shortcutIdx G l).card) ∅ ω₀ := by
      apply condProb_mono
      intro ω hω ⟨l, hl, hl2⟩
      have := hω l hl
      omega
    linarith
  -- bound on the second part
  have hbad2 : condProb (fun ω : Perm V => ∃ P ∈ PP, ∃ Q ∈ QQ, pathEv G P Q ω) ∅ ω₀ ≤
      1 / (n : ℝ) ^ 7 := by
    have hu1 := condProb_union_le PP (fun P ω => ∃ Q ∈ QQ, pathEv G P Q ω) ∅ ω₀
    refine hu1.trans ?_
    set K : ℝ := (1 - 1/5000 : ℝ) ^ ((L - 2) / 2 - h - b₀) * ((1 - aC) ^ (L - 2))⁻¹ *
      (Real.exp 1 * n) ^ 2 with hK
    have hK0 : 0 ≤ K := by
      rw [hK]
      have : 0 ≤ 1 - aC := by unfold aC; norm_num
      positivity
    have hP : ∀ P ∈ PP, condProb (fun ω => ∃ Q ∈ QQ, pathEv G P Q ω) ∅ ω₀ ≤
        (QQ.card : ℝ) * (K * ∏ p ∈ P, 1 / (Real.exp 1 * (ellP aC P (ivI aC p) : ℝ))) := by
      intro P hP
      simp only [hPP, Finset.mem_filter, Finset.mem_powerset] at hP
      obtain ⟨hPsub, hPL⟩ := hP
      have hch := mid_chainset (n := n) hM4 (by rw [hPL]; exact hNL) hPsub (by omega)
      refine (condProb_union_le QQ (fun Q ω => pathEv G P Q ω) ∅ ω₀).trans ?_
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro Q hQ
      simp only [hQQ, Finset.mem_filter] at hQ
      have := pathEv_prob_le G (Q := Q) hch.1 aC_pos (by unfold aC; norm_num) hn
        (by rw [hPL]; exact hL3) hch.2.1 b₀ h hQ.2
        (hb0mid _ (hPsub (posK_mem (by omega))))
      rw [coinProb_eq_condProb _ ω₀, hPL] at this
      rw [hK]; linarith
    refine (Finset.sum_le_sum hP).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hW := sum_W_le (n := n) hM4 L (by omega) hNL b₀ hb0mid
    have hQc := card_small_subsets L h hh1' hhL
    have hW0 : 0 ≤ ∑ P ∈ PP, ∏ p ∈ P, 1 / (Real.exp 1 * (ellP aC P (ivI aC p) : ℝ)) :=
      Finset.sum_nonneg (fun P _ => Finset.prod_nonneg (fun p _ => by positivity))
    have hnum := mid_numeric (n : ℝ) hnR L h b₀ (by rw [← hlam]; exact hL1)
      (by rw [← hlam]; exact hL2) (by rw [← hlam]; exact hh1) (by rw [← hlam]; exact hh2)
      (by rw [← hlam]; exact hb₀R)
    calc (QQ.card : ℝ) * (K * ∑ P ∈ PP, ∏ p ∈ P, 1 / (Real.exp 1 * (ellP aC P (ivI aC p) : ℝ)))
        ≤ (Real.exp 1 * L / h) ^ h * (K * ((xC ^ L)⁻¹ * (1 / aC) ^ (b₀ + 1))) := by
          apply mul_le_mul hQc (mul_le_mul_of_nonneg_left hW hK0) (by positivity) (by positivity)
      _ = _ := by rw [hK]; ring
      _ ≤ 1 / (n : ℝ) ^ 7 := hnum
  -- combine
  rw [coinProb_eq_condProb _ ω₀]
  have hcompl := condProb_compl (S := ∅) (ω₀ := ω₀) (fun ω : Perm V => ∀ l : List V,
    IsQueryPath G (rank ω) l → (∀ v ∈ l, M < (rank ω v : ℝ) ∧ (rank ω v : ℝ) < aC * (n : ℝ)) →
      l.length < L)
  have hbadle := condProb_mono (S := ∅) (ω := ω₀) hincl
  have hor := condProb_or_le (fun ω : Perm V => ∃ l : List V, IsQueryPath G (rank ω) l ∧
      h < (shortcutIdx G l).card) (fun ω => ∃ P ∈ PP, ∃ Q ∈ QQ, pathEv G P Q ω) ∅ ω₀
  have h7 : 2 / (n : ℝ) ^ 7 ≤ 1 / (n : ℝ) ^ 6 := by
    have hn6 : (0 : ℝ) < (n : ℝ) ^ 6 := by positivity
    have e : 2 / (n : ℝ) ^ 7 = (2 / n) / (n : ℝ) ^ 6 := by
      rw [div_div, pow_succ, mul_comm]
    rw [e]
    apply div_le_div_of_nonneg_right _ hn6.le
    rw [div_le_one (by linarith)]; exact hnR
  show 1 - 1 / (n : ℝ) ^ 6 ≤ condProb (fun ω : Perm V => ∀ l : List V, IsQueryPath G (rank ω) l →
    (∀ v ∈ l, M < (rank ω v : ℝ) ∧ (rank ω v : ℝ) < aC * (n : ℝ)) → l.length < L) ∅ ω₀
  have hsum : condProb (fun ω : Perm V => ∃ l : List V, IsQueryPath G (rank ω) l ∧
      h < (shortcutIdx G l).card) ∅ ω₀ + condProb (fun ω => ∃ P ∈ PP, ∃ Q ∈ QQ, pathEv G P Q ω) ∅ ω₀
      ≤ 2 / (n : ℝ) ^ 7 := by
    have := add_le_add hbad1 hbad2
    rw [← add_div] at this; norm_num at this ⊢; exact this
  have hb := hbadle.trans (hor.trans hsum)
  rw [hcompl] at hb
  linarith

end lemma310

end QDM

open QueryDepthMIS

theorem solution :
    ∃ A β : ℝ, 0 < A ∧ 0 < β ∧ ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
      1 - 1 / (Fintype.card V : ℝ) ^ 6 ≤
        PunctSketch.coinProb (fun ω : Perm V => ∀ l : List V, IsQueryPath G (rank ω) l →
          (∀ v ∈ l, A * Real.logb 2 (Fintype.card V) < (rank ω v : ℝ) ∧
            (rank ω v : ℝ) < β * (Fintype.card V : ℝ)) →
          l.length < ⌈Real.sqrt A * Real.logb 2 (Fintype.card V)⌉₊) := by
  refine ⟨2 ^ 120, QDM.aC, by positivity, QDM.aC_pos, 2, ?_⟩
  intro V _ _ G _ hn
  have hs : Real.sqrt (2 ^ 120) = (2 : ℝ) ^ 60 := by
    rw [show (2 : ℝ) ^ 120 = (2 ^ 60) ^ 2 by norm_num]
    exact Real.sqrt_sq (by positivity)
  rw [hs]
  exact QDM.lemma_3_10_core G hn

