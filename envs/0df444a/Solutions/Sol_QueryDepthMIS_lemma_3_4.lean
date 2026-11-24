-- Prove2me | solution 1 for QueryDepthMIS.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T12:55:31.547517+00:00
-- url     : https://prove2.me/submissions/26b07c5c-0d45-45e3-8efd-be3f105c2b17

import Mathlib
import Definitions.Def_NoSignalPA_uniformExp
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_QueryDepthMIS_Z
import Definitions.Def_QueryDepthMIS_aliveSet
import Definitions.Def_QueryDepthMIS_condProb
import Definitions.Def_QueryDepthMIS_maxDegOn
import Definitions.Def_QueryDepthMIS_queryDepth
import Definitions.Def_QueryDepthMIS_rank
import Definitions.Def_QueryDepthMIS_shortcutIdx

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

open QueryDepthMIS

theorem solution :
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      2 ≤ Fintype.card V →
      (∀ h : ℕ,
        PunctSketch.coinProb (fun ω : Perm V => ∃ l : List V, IsQueryPath G (rank ω) l ∧
            h < (shortcutIdx G l).card) ≤
          ((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ)) * (2 : ℝ) ^ (-(h : ℝ) / 2)) ∧
      1 - 1 / (Fintype.card V : ℝ) ^ 7 ≤
        PunctSketch.coinProb (fun ω : Perm V => ∀ l : List V, IsQueryPath G (rank ω) l →
          (shortcutIdx G l).card ≤ ⌈18 * Real.logb 2 (Fintype.card V : ℝ)⌉₊) := by
  intro V _ _ G _ hn
  exact ⟨fun h => QDM.lemma_3_4_part1 G h, QDM.lemma_3_4_part2 G hn⟩

