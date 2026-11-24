-- Prove2me | solution 1 for QueryDepthMIS.lemma_2_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T11:39:12.508638+00:00
-- url     : https://prove2.me/submissions/60b6f67b-93f4-4fcb-97dc-0693a800ff34

import Mathlib
import Definitions.Def_NoSignalPA_uniformExp
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_QueryDepthMIS_aliveSet
import Definitions.Def_QueryDepthMIS_condProb
import Definitions.Def_QueryDepthMIS_maxDegOn
import Definitions.Def_QueryDepthMIS_queryDepth
import Definitions.Def_QueryDepthMIS_rank

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

open QueryDepthMIS

theorem solution :
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ),
      1 ≤ t → t < Fintype.card V →
      (∀ d : ℝ, 0 < d →
        PunctSketch.coinProb (fun ω : Perm V =>
          d ≤ (maxDegOn G (aliveSet G (rank ω) (t + 1) (Fintype.card V)) : ℝ)) ≤
          (Fintype.card V : ℝ) * Real.exp (-((t : ℝ) * d) / (Fintype.card V : ℝ))) ∧
      1 - 1 / (Fintype.card V : ℝ) ^ 7 ≤
        PunctSketch.coinProb (fun ω : Perm V =>
          (maxDegOn G (aliveSet G (rank ω) (t + 1) (Fintype.card V)) : ℝ) ≤
            8 * (Fintype.card V : ℝ) * Real.log (Fintype.card V : ℝ) / (t : ℝ)) := by
  intro V _ _ G _ t ht1 ht
  exact ⟨fun d hd => QDM.lemma_2_9_part1 G t ht1 ht d hd, QDM.lemma_2_9_part2 G t ht1 ht⟩

