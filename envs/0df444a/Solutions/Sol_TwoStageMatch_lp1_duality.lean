-- Prove2me | solution 1 for TwoStageMatch.lp1_duality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T05:05:39.881388+00:00
-- url     : https://prove2.me/submissions/dbc6b1fd-dcba-4ea2-adac-3344175a3edb

import Mathlib
import Definitions.Def_TwoStageMatch_Bipartite

namespace Aux_DepRound

variable {E A B : Type*} [Fintype E] [DecidableEq E] [DecidableEq A] [DecidableEq B]

/-! ### Part 1: alternating directions in a bipartite edge set -/

def starF (a : E → A) (b : E → B) (F : Finset E) (v : A ⊕ B) : Finset E :=
  F.filter (fun e => (Sum.inl (a e) : A ⊕ B) = v ∨ (Sum.inr (b e) : A ⊕ B) = v)

def nz (S : Finset E) (d : E → ℤ) : Finset E := S.filter (fun e => d e ≠ 0)

def IsSingle (S : Finset E) (d : E → ℤ) : Prop :=
  ∃ e1, nz S d = {e1} ∧ S = {e1} ∧ (d e1 = 1 ∨ d e1 = -1)

def ValidAt (S : Finset E) (d : E → ℤ) : Prop :=
  nz S d = ∅ ∨ (∃ e1 e2, e1 ≠ e2 ∧ nz S d = {e1, e2} ∧ d e1 = 1 ∧ d e2 = -1) ∨ IsSingle S d

def GoodDir (a : E → A) (b : E → B) (F : Finset E) (d : E → ℤ) : Prop :=
  (∀ e, d e ≠ 0 → e ∈ F) ∧ (∃ e, d e ≠ 0) ∧ ∀ v, ValidAt (starF a b F v) d

lemma mem_nz {S : Finset E} {d : E → ℤ} {e : E} : e ∈ nz S d ↔ e ∈ S ∧ d e ≠ 0 :=
  Finset.mem_filter

lemma mem_starF {a : E → A} {b : E → B} {F : Finset E} {v : A ⊕ B} {e : E} :
    e ∈ starF a b F v ↔ e ∈ F ∧ ((Sum.inl (a e) : A ⊕ B) = v ∨ (Sum.inr (b e) : A ⊕ B) = v) :=
  Finset.mem_filter

lemma validAt_congr {S : Finset E} {d d' : E → ℤ} (h : ∀ e ∈ S, d e = d' e)
    (h' : ValidAt S d') : ValidAt S d := by
  have hnz : nz S d = nz S d' := Finset.filter_congr (fun e he => by rw [h e he])
  unfold ValidAt IsSingle
  rw [hnz]
  rcases h' with h0 | ⟨e1, e2, hne, h12, h1, h2⟩ | ⟨e1, h1, h2, h3⟩
  · exact Or.inl h0
  · have m1 : e1 ∈ S := (mem_nz.1 (by rw [h12]; simp)).1
    have m2 : e2 ∈ S := (mem_nz.1 (by rw [h12]; simp)).1
    exact Or.inr (Or.inl ⟨e1, e2, hne, h12, by rw [h e1 m1]; exact h1, by rw [h e2 m2]; exact h2⟩)
  · have m1 : e1 ∈ S := by rw [h2]; simp
    refine Or.inr (Or.inr ⟨e1, h1, h2, ?_⟩)
    rw [h e1 m1]; exact h3

lemma sum_eq_nz (S : Finset E) (d : E → ℤ) : ∑ e ∈ S, d e = ∑ e ∈ nz S d, d e := by
  unfold nz
  exact (Finset.sum_filter_of_ne (fun x _ hx => hx)).symm

lemma net_nonsingle {S : Finset E} {d : E → ℤ} (hv : ValidAt S d) (hs : ¬ IsSingle S d) :
    ∑ e ∈ S, d e = 0 := by
  rw [sum_eq_nz]
  rcases hv with h0 | ⟨e1, e2, hne, h12, h1, h2⟩ | h
  · rw [h0]; simp
  · rw [h12, Finset.sum_pair hne, h1, h2] <;> norm_num
  · exact absurd h hs

lemma net_single {S : Finset E} {d : E → ℤ} (hs : IsSingle S d) :
    ∃ e1, S = {e1} ∧ ∑ e ∈ S, d e = d e1 ∧ (d e1 = 1 ∨ d e1 = -1) := by
  obtain ⟨e1, _, h2, h3⟩ := hs
  exact ⟨e1, h2, by rw [h2, Finset.sum_singleton], h3⟩

lemma net_single_ne {S : Finset E} {d : E → ℤ} (hs : IsSingle S d) : ∑ e ∈ S, d e ≠ 0 := by
  obtain ⟨e1, _, h2, h3⟩ := net_single hs
  rw [h2]; rcases h3 with h | h <;> rw [h] <;> norm_num

lemma starF_erase (a : E → A) (b : E → B) (F : Finset E) (e : E) (v : A ⊕ B) :
    starF a b (F.erase e) v = (starF a b F v).erase e := by
  unfold starF; exact Finset.filter_erase _ _ _

lemma starF_notinc (a : E → A) (b : E → B) (F : Finset E) (e : E) (v : A ⊕ B)
    (hv : ¬ ((Sum.inl (a e) : A ⊕ B) = v ∨ (Sum.inr (b e) : A ⊕ B) = v)) :
    starF a b F v = starF a b (F.erase e) v := by
  rw [starF_erase]
  refine (Finset.erase_eq_of_notMem ?_).symm
  intro h; exact hv (mem_starF.1 h).2

lemma starF_inc (a : E → A) (b : E → B) (F : Finset E) (e : E) (heF : e ∈ F) (v : A ⊕ B)
    (hv : (Sum.inl (a e) : A ⊕ B) = v ∨ (Sum.inr (b e) : A ⊕ B) = v) :
    starF a b F v = insert e (starF a b (F.erase e) v) := by
  rw [starF_erase]
  exact (Finset.insert_erase (mem_starF.2 ⟨heF, hv⟩)).symm

lemma sideA (a : E → A) (b : E → B) (F : Finset E) (d : E → ℤ) :
    ∑ e ∈ F, d e = ∑ x ∈ F.image a, ∑ e ∈ starF a b F (Sum.inl x), d e := by
  have : ∀ x, starF a b F (Sum.inl x) = F.filter (fun e => a e = x) := by
    intro x; unfold starF; apply Finset.filter_congr; intro e _; simp
  simp only [this]
  exact (Finset.sum_fiberwise_of_maps_to (fun e he => Finset.mem_image_of_mem a he) _).symm

lemma sideB (a : E → A) (b : E → B) (F : Finset E) (d : E → ℤ) :
    ∑ e ∈ F, d e = ∑ x ∈ F.image b, ∑ e ∈ starF a b F (Sum.inr x), d e := by
  have : ∀ x, starF a b F (Sum.inr x) = F.filter (fun e => b e = x) := by
    intro x; unfold starF; apply Finset.filter_congr; intro e _; simp
  simp only [this]
  exact (Finset.sum_fiberwise_of_maps_to (fun e he => Finset.mem_image_of_mem b he) _).symm

lemma ext_zero {S' : Finset E} {e : E} {d' : E → ℤ} (hd'e : d' e = 0)
    (hv : ValidAt S' d') (hs : ¬ IsSingle S' d') :
    ValidAt (insert e S') (Function.update d' e 0) := by
  have hu : Function.update d' e 0 = d' := by rw [← hd'e]; exact Function.update_eq_self e d'
  rw [hu]
  have hnz : nz (insert e S') d' = nz S' d' := by
    unfold nz; rw [Finset.filter_insert]; simp [hd'e]
  unfold ValidAt
  rw [hnz]
  rcases hv with h0 | h2 | h1
  · exact Or.inl h0
  · exact Or.inr (Or.inl h2)
  · exact absurd h1 hs

lemma ext_single {S' : Finset E} {e : E} {d' : E → ℤ} (he : e ∉ S') {e1 : E}
    (hnz1 : nz S' d' = {e1}) (hS : S' = {e1}) (hv1 : d' e1 = 1 ∨ d' e1 = -1) :
    ValidAt (insert e S') (Function.update d' e (-(d' e1))) := by
  have hne : e1 ≠ e := by rintro rfl; exact he (by rw [hS]; simp)
  have hd1 : d' e1 ≠ 0 := by rcases hv1 with h | h <;> rw [h] <;> norm_num
  have hnz' : nz (insert e S') (Function.update d' e (-(d' e1))) = {e1, e} := by
    rw [hS]; ext x
    by_cases hx : x = e
    · rw [hx]
      constructor
      · intro _; simp
      · intro _
        exact mem_nz.2 ⟨Finset.mem_insert_self _ _, by
          rw [Function.update_self]; exact neg_ne_zero.mpr hd1⟩
    · simp only [mem_nz, Finset.mem_insert, Finset.mem_singleton, Function.update_of_ne hx]
      constructor
      · rintro ⟨h | h, _⟩
        · exact absurd h hx
        · exact Or.inl h
      · rintro (h | h)
        · exact ⟨Or.inr h, h ▸ hd1⟩
        · exact absurd h hx
  unfold ValidAt
  rcases hv1 with h | h
  · refine Or.inr (Or.inl ⟨e1, e, hne, hnz', ?_, ?_⟩)
    · rw [Function.update_of_ne hne]; exact h
    · rw [Function.update_self, h]
  · refine Or.inr (Or.inl ⟨e, e1, hne.symm, ?_, ?_, ?_⟩)
    · rw [hnz', Finset.pair_comm]
    · rw [Function.update_self]; simp [h]
    · rw [Function.update_of_ne hne]; exact h

lemma valid_leaf {e : E} {d : E → ℤ} (hd : d e = 1 ∨ d e = -1 ∨ d e = 0) : ValidAt {e} d := by
  by_cases h0 : d e = 0
  · left; unfold nz; ext x; simp only [Finset.mem_filter, Finset.mem_singleton,
      Finset.notMem_empty, iff_false, not_and]
    rintro rfl; exact fun h => h h0
  · right; right
    refine ⟨e, ?_, rfl, ?_⟩
    · unfold nz; ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · rintro rfl; exact ⟨rfl, h0⟩
    · rcases hd with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h0

lemma valid_empty (d : E → ℤ) : ValidAt (∅ : Finset E) d := by
  left; unfold nz; simp

lemma inc_cases (a : E → A) (b : E → B) (e : E) (v : A ⊕ B)
    (h : (Sum.inl (a e) : A ⊕ B) = v ∨ (Sum.inr (b e) : A ⊕ B) = v) :
    v = Sum.inl (a e) ∨ v = Sum.inr (b e) := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- The supports and the nonzero edge of an extension. -/
lemma ext_supp {F : Finset E} {e : E} (heF : e ∈ F) {d' : E → ℤ}
    (hsupp : ∀ x, d' x ≠ 0 → x ∈ F.erase e) (r : ℤ) :
    ∀ x, Function.update d' e r x ≠ 0 → x ∈ F := by
  intro x hx
  by_cases hxe : x = e
  · rw [hxe]; exact heF
  · rw [Function.update_of_ne hxe] at hx
    exact Finset.mem_of_mem_erase (hsupp x hx)

lemma ext_nonzero {F : Finset E} {e : E} {d' : E → ℤ}
    (hsupp : ∀ x, d' x ≠ 0 → x ∈ F.erase e) (hne : ∃ x, d' x ≠ 0) (r : ℤ) :
    ∃ x, Function.update d' e r x ≠ 0 := by
  obtain ⟨x, hx⟩ := hne
  have hxe : x ≠ e := Finset.ne_of_mem_erase (hsupp x hx)
  exact ⟨x, by rw [Function.update_of_ne hxe]; exact hx⟩

lemma ext_notinc (a : E → A) (b : E → B) {F : Finset E} {e : E} {d' : E → ℤ}
    (hval : ∀ v, ValidAt (starF a b (F.erase e) v) d') (r : ℤ) (v : A ⊕ B)
    (hv : ¬ ((Sum.inl (a e) : A ⊕ B) = v ∨ (Sum.inr (b e) : A ⊕ B) = v)) :
    ValidAt (starF a b F v) (Function.update d' e r) := by
  rw [starF_notinc a b F e v hv]
  refine validAt_congr (fun x hx => ?_) (hval v)
  have : x ≠ e := Finset.ne_of_mem_erase (mem_starF.1 hx).1
  rw [Function.update_of_ne this]

lemma base_dir (a : E → A) (b : E → B) (e : E) :
    GoodDir a b {e} (Function.update (fun _ => (0 : ℤ)) e 1) := by
  refine ⟨?_, ⟨e, by simp⟩, ?_⟩
  · intro x hx
    by_cases hxe : x = e
    · rw [hxe]; simp
    · rw [Function.update_of_ne hxe] at hx; exact (hx rfl).elim
  · intro v
    by_cases hv : (Sum.inl (a e) : A ⊕ B) = v ∨ (Sum.inr (b e) : A ⊕ B) = v
    · have : starF a b {e} v = {e} := by
        ext x; simp only [mem_starF, Finset.mem_singleton]
        constructor
        · exact fun h => h.1
        · rintro rfl; exact ⟨rfl, hv⟩
      rw [this]; exact valid_leaf (Or.inl (by simp))
    · have : starF a b {e} v = ∅ := by
        ext x; simp only [mem_starF, Finset.mem_singleton, Finset.notMem_empty, iff_false,
          not_and]
        rintro rfl; exact hv
      rw [this]; exact valid_empty _

theorem exists_dir_aux (a : E → A) (b : E → B) (n : ℕ) :
    ∀ F : Finset E, F.card = n → F.Nonempty → ∃ d, GoodDir a b F d := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hcard hne
  by_cases hleaf : ∃ v, (starF a b F v).card = 1
  · obtain ⟨v, hv⟩ := hleaf
    obtain ⟨e, he⟩ := Finset.card_eq_one.1 hv
    have heS : e ∈ starF a b F v := by rw [he]; simp
    have heF : e ∈ F := (mem_starF.1 heS).1
    have hinc : (Sum.inl (a e) : A ⊕ B) = v ∨ (Sum.inr (b e) : A ⊕ B) = v := (mem_starF.1 heS).2
    by_cases hF' : (F.erase e).Nonempty
    · have hlt : (F.erase e).card < n := by
        rw [← hcard]; exact Finset.card_erase_lt_of_mem heF
      obtain ⟨d', hsupp, hnz', hval⟩ := ih _ hlt (F.erase e) rfl hF'
      -- the other endpoint
      obtain ⟨o, hoinc, hov, hboth⟩ : ∃ o : A ⊕ B,
          ((Sum.inl (a e) : A ⊕ B) = o ∨ (Sum.inr (b e) : A ⊕ B) = o) ∧ o ≠ v ∧
          ∀ x : A ⊕ B, ((Sum.inl (a e) : A ⊕ B) = x ∨ (Sum.inr (b e) : A ⊕ B) = x) →
            x = v ∨ x = o := by
        rcases hinc with h | h
        · refine ⟨Sum.inr (b e), Or.inr rfl, ?_, ?_⟩
          · rw [← h]; exact Sum.inr_ne_inl
          · intro x hx
            rcases hx with hx | hx
            · left; rw [← hx, h]
            · right; rw [hx]
        · refine ⟨Sum.inl (a e), Or.inl rfl, ?_, ?_⟩
          · rw [← h]; exact Sum.inl_ne_inr
          · intro x hx
            rcases hx with hx | hx
            · right; rw [hx]
            · left; rw [← hx, h]
      have hd'e : d' e = 0 := by
        by_contra h; exact Finset.notMem_erase e F (hsupp e h)
      have heo : e ∉ starF a b (F.erase e) o := by
        intro h; exact Finset.notMem_erase e F (mem_starF.1 h).1
      have hFo := starF_inc a b F e heF o hoinc
      by_cases hs : IsSingle (starF a b (F.erase e) o) d'
      · obtain ⟨e1, h1, h2, h3⟩ := hs
        refine ⟨Function.update d' e (-(d' e1)), ext_supp heF hsupp _,
          ext_nonzero hsupp hnz' _, ?_⟩
        intro x
        by_cases hx : (Sum.inl (a e) : A ⊕ B) = x ∨ (Sum.inr (b e) : A ⊕ B) = x
        · rcases hboth x hx with rfl | rfl
          · rw [he]; refine valid_leaf ?_
            rw [Function.update_self]
            rcases h3 with h | h <;> rw [h] <;> simp
          · rw [hFo]; exact ext_single heo h1 h2 h3
        · exact ext_notinc a b hval _ x hx
      · refine ⟨Function.update d' e 0, ext_supp heF hsupp _, ext_nonzero hsupp hnz' _, ?_⟩
        intro x
        by_cases hx : (Sum.inl (a e) : A ⊕ B) = x ∨ (Sum.inr (b e) : A ⊕ B) = x
        · rcases hboth x hx with rfl | rfl
          · rw [he]; refine valid_leaf ?_
            rw [Function.update_self]; simp
          · rw [hFo]; exact ext_zero hd'e (hval _) hs
        · exact ext_notinc a b hval _ x hx
    · have hF1 : F = {e} := by
        rw [Finset.not_nonempty_iff_eq_empty] at hF'
        have := Finset.insert_erase heF
        rw [hF'] at this; rw [← this]; simp
      rw [hF1]; exact ⟨_, base_dir a b e⟩
  · push_neg at hleaf
    obtain ⟨e, heF⟩ := hne
    have hF' : (F.erase e).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      apply hleaf (Sum.inl (a e))
      rw [starF_inc a b F e heF _ (Or.inl rfl), h]
      simp [starF]
    have hlt : (F.erase e).card < n := by
      rw [← hcard]; exact Finset.card_erase_lt_of_mem heF
    obtain ⟨d', hsupp, hnz', hval⟩ := ih _ hlt (F.erase e) rfl hF'
    have hd'e : d' e = 0 := by
      by_contra h; exact Finset.notMem_erase e F (hsupp e h)
    -- vertices other than the endpoints are not single
    have hns : ∀ x : A ⊕ B, ¬ ((Sum.inl (a e) : A ⊕ B) = x ∨ (Sum.inr (b e) : A ⊕ B) = x) →
        ¬ IsSingle (starF a b (F.erase e) x) d' := by
      intro x hx hs
      obtain ⟨e1, _, h2, _⟩ := hs
      apply hleaf x
      rw [starF_notinc a b F e x hx, h2]; simp
    have hnetA : ∑ e' ∈ (F.erase e), d' e' = ∑ e' ∈ starF a b (F.erase e) (Sum.inl (a e)), d' e' := by
      rw [sideA a b (F.erase e) d']
      apply Finset.sum_eq_single (a e)
      · intro x _ hx
        apply net_nonsingle (hval _)
        apply hns
        rintro (h | h)
        · exact hx (Sum.inl_injective h).symm
        · exact Sum.inr_ne_inl h
      · intro hx
        apply Finset.sum_eq_zero
        intro e' he'
        exfalso; apply hx
        have := mem_starF.1 he'
        rcases this.2 with h | h
        · exact Finset.mem_image.2 ⟨e', this.1, Sum.inl_injective h⟩
        · exact absurd h Sum.inr_ne_inl
    have hnetB : ∑ e' ∈ (F.erase e), d' e' = ∑ e' ∈ starF a b (F.erase e) (Sum.inr (b e)), d' e' := by
      rw [sideB a b (F.erase e) d']
      apply Finset.sum_eq_single (b e)
      · intro x _ hx
        apply net_nonsingle (hval _)
        apply hns
        rintro (h | h)
        · exact Sum.inl_ne_inr h
        · exact hx (Sum.inr_injective h).symm
      · intro hx
        apply Finset.sum_eq_zero
        intro e' he'
        exfalso; apply hx
        have := mem_starF.1 he'
        rcases this.2 with h | h
        · exact absurd h Sum.inl_ne_inr
        · exact Finset.mem_image.2 ⟨e', this.1, Sum.inr_injective h⟩
    have hFu := starF_inc a b F e heF (Sum.inl (a e)) (Or.inl rfl)
    have hFw := starF_inc a b F e heF (Sum.inr (b e)) (Or.inr rfl)
    have heu : e ∉ starF a b (F.erase e) (Sum.inl (a e)) := by
      intro h; exact Finset.notMem_erase e F (mem_starF.1 h).1
    have hew : e ∉ starF a b (F.erase e) (Sum.inr (b e)) := by
      intro h; exact Finset.notMem_erase e F (mem_starF.1 h).1
    by_cases hsu : IsSingle (starF a b (F.erase e) (Sum.inl (a e))) d'
    · have hsw : IsSingle (starF a b (F.erase e) (Sum.inr (b e))) d' := by
        by_contra hsw
        have h1 := net_nonsingle (hval _) hsw
        exact net_single_ne hsu (by rw [← hnetA, hnetB, h1])
      obtain ⟨e1, h1, h2, h3⟩ := hsu
      obtain ⟨e2, k1, k2, k3⟩ := hsw
      have hval12 : d' e1 = d' e2 := by
        have := hnetA.symm.trans hnetB
        rw [h2, k2, Finset.sum_singleton, Finset.sum_singleton] at this
        exact this
      refine ⟨Function.update d' e (-(d' e1)), ext_supp heF hsupp _,
        ext_nonzero hsupp hnz' _, ?_⟩
      intro x
      by_cases hx : (Sum.inl (a e) : A ⊕ B) = x ∨ (Sum.inr (b e) : A ⊕ B) = x
      · rcases inc_cases a b e x hx with rfl | rfl
        · rw [hFu]; exact ext_single heu h1 h2 h3
        · rw [hFw, hval12]; exact ext_single hew k1 k2 k3
      · exact ext_notinc a b hval _ x hx
    · have hsw : ¬ IsSingle (starF a b (F.erase e) (Sum.inr (b e))) d' := by
        intro hsw
        have h1 := net_nonsingle (hval _) hsu
        exact net_single_ne hsw (by rw [← hnetB, hnetA, h1])
      refine ⟨Function.update d' e 0, ext_supp heF hsupp _, ext_nonzero hsupp hnz' _, ?_⟩
      intro x
      by_cases hx : (Sum.inl (a e) : A ⊕ B) = x ∨ (Sum.inr (b e) : A ⊕ B) = x
      · rcases inc_cases a b e x hx with rfl | rfl
        · rw [hFu]; exact ext_zero hd'e (hval _) hsu
        · rw [hFw]; exact ext_zero hd'e (hval _) hsw
      · exact ext_notinc a b hval _ x hx

theorem exists_dir (a : E → A) (b : E → B) (F : Finset E) (hF : F.Nonempty) :
    ∃ d, GoodDir a b F d :=
  exists_dir_aux a b _ F rfl hF


/-! ### Part 2: dependent rounding with negative correlation at vertices -/

def bitR (b : Bool) : ℝ := if b then 1 else 0

lemma bitR_nonneg (b : Bool) : 0 ≤ bitR b := by unfold bitR; split_ifs <;> norm_num
lemma bitR_le_one (b : Bool) : bitR b ≤ 1 := by unfold bitR; split_ifs <;> norm_num

def star (a : E → A) (b : E → B) (v : A ⊕ B) : Finset E := starF a b Finset.univ v

def Feas (a : E → A) (b : E → B) (lo hi : A ⊕ B → ℕ) (y : E → ℝ) : Prop :=
  (∀ e, 0 ≤ y e ∧ y e ≤ 1) ∧
  ∀ v, (lo v : ℝ) ≤ ∑ e ∈ star a b v, y e ∧ ∑ e ∈ star a b v, y e ≤ (hi v : ℝ)

noncomputable def frac (y : E → ℝ) : Finset E :=
  Finset.univ.filter (fun e => 0 < y e ∧ y e < 1)

lemma mem_frac {y : E → ℝ} {e : E} : e ∈ frac y ↔ 0 < y e ∧ y e < 1 := by
  unfold frac; simp

structure Good (a : E → A) (b : E → B) (lo hi : A ⊕ B → ℕ) (y : E → ℝ)
    (w : (E → Bool) → ℝ) : Prop where
  nonneg : ∀ X, 0 ≤ w X
  sum_one : ∑ X, w X = 1
  marg : ∀ e, ∑ X, w X * bitR (X e) = y e
  supp : ∀ X, w X ≠ 0 → Feas a b lo hi (fun e => bitR (X e))
  nc : ∀ (c : E → ℝ) (v : A ⊕ B), (∀ e ∈ star a b v, 0 ≤ c e ∧ c e ≤ 1) →
    ∑ X, w X * ∏ e ∈ star a b v, (1 - c e * bitR (X e)) ≤ ∏ e ∈ star a b v, (1 - c e * y e)

lemma base_good (a : E → A) (b : E → B) (lo hi : A ⊕ B → ℕ) (y : E → ℝ)
    (hy : Feas a b lo hi y) (h0 : frac y = ∅) : ∃ w, Good a b lo hi y w := by
  have h01 : ∀ e, y e = 0 ∨ y e = 1 := by
    intro e
    have : e ∉ frac y := by rw [h0]; exact Finset.notMem_empty e
    rw [mem_frac, not_and_or, not_lt, not_lt] at this
    rcases this with h | h
    · left; linarith [(hy.1 e).1]
    · right; linarith [(hy.1 e).2]
  obtain ⟨X0, hX0⟩ : ∃ X0 : E → Bool, X0 = fun e => decide (y e = 1) := ⟨_, rfl⟩
  have hbit : ∀ e, bitR (X0 e) = y e := by
    intro e; rw [hX0]; simp only [bitR]
    rcases h01 e with h | h <;> simp [h]
  refine ⟨fun X => if X = X0 then 1 else 0, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro X; beta_reduce; split_ifs <;> norm_num
  · simp
  · intro e; simp [ite_mul, hbit]
  · intro X hX
    have hXe : X = X0 := by
      by_contra h; exact hX (if_neg h)
    have hfun : (fun e => bitR (X e)) = y := by rw [hXe]; exact funext hbit
    rw [hfun]; exact hy
  · intro c v _
    simp [ite_mul, hbit]

lemma nz_star_eq (a : E → A) (b : E → B) (y : E → ℝ) (d : E → ℤ)
    (hsupp : ∀ e, d e ≠ 0 → e ∈ frac y) (v : A ⊕ B) :
    nz (star a b v) d = nz (starF a b (frac y) v) d := by
  ext e; simp only [mem_nz, star, mem_starF, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨hsupp e h2, h1⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩

lemma sum_D (S : Finset E) (d : E → ℤ) :
    ∑ e ∈ S, (d e : ℝ) = ∑ e ∈ nz S d, (d e : ℝ) := by
  unfold nz
  refine (Finset.sum_filter_of_ne (fun x _ hx => ?_)).symm
  exact_mod_cast hx

lemma pattern (a : E → A) (b : E → B) (y : E → ℝ) (d : E → ℤ) (hd : GoodDir a b (frac y) d)
    (v : A ⊕ B) :
    nz (star a b v) d = ∅ ∨
    (∃ e1 e2, e1 ≠ e2 ∧ nz (star a b v) d = {e1, e2} ∧ d e1 = 1 ∧ d e2 = -1) ∨
    (∃ e1, nz (star a b v) d = {e1} ∧ starF a b (frac y) v = {e1} ∧
      (d e1 = 1 ∨ d e1 = -1)) := by
  rw [nz_star_eq a b y d hd.1 v]
  exact hd.2.2 v

lemma dir_val (a : E → A) (b : E → B) (F : Finset E) (d : E → ℤ) (hd : GoodDir a b F d)
    (e : E) (h : d e ≠ 0) : d e = 1 ∨ d e = -1 := by
  have hmem : e ∈ nz (starF a b F (Sum.inl (a e))) d :=
    mem_nz.2 ⟨mem_starF.2 ⟨hd.1 e h, Or.inl rfl⟩, h⟩
  rcases hd.2.2 (Sum.inl (a e)) with h0 | ⟨e1, e2, _, h12, h1, h2⟩ | ⟨e1, h1, _, h3⟩
  · rw [h0] at hmem; simp at hmem
  · rw [h12] at hmem
    rcases Finset.mem_insert.1 hmem with h' | h'
    · rw [h']; exact Or.inl h1
    · rw [Finset.mem_singleton.1 h']; exact Or.inr h2
  · rw [h1] at hmem
    rw [Finset.mem_singleton.1 hmem]; exact h3

lemma feas_move (a : E → A) (b : E → B) (lo hi : A ⊕ B → ℕ) (y : E → ℝ)
    (hy : Feas a b lo hi y) (d : E → ℤ) (hd : GoodDir a b (frac y) d)
    (t : ℝ) (ht : ∀ e, d e ≠ 0 → 0 ≤ y e + t * d e ∧ y e + t * d e ≤ 1) :
    Feas a b lo hi (fun e => y e + t * d e) := by
  refine ⟨fun e => ?_, fun v => ?_⟩
  · beta_reduce
    by_cases h : d e = 0
    · rw [h]; simp only [Int.cast_zero, mul_zero, add_zero]; exact hy.1 e
    · exact ht e h
  · beta_reduce
    have hsum : ∑ e ∈ star a b v, (y e + t * (d e : ℝ)) =
        ∑ e ∈ star a b v, y e + t * ∑ e ∈ nz (star a b v) d, (d e : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_D]
    rw [hsum]
    rcases pattern a b y d hd v with h0 | ⟨e1, e2, hne, h12, h1, h2⟩ | ⟨e1, h1, h2, h3⟩
    · rw [h0, Finset.sum_empty, mul_zero, add_zero]; exact hy.2 v
    · rw [h12, Finset.sum_pair hne, h1, h2]
      simp only [Int.cast_one, Int.cast_neg, add_neg_cancel, mul_zero, add_zero]
      exact hy.2 v
    · rw [h1, Finset.sum_singleton]
      have he1n : e1 ∈ nz (star a b v) d := by rw [h1]; simp
      have he1 : e1 ∈ star a b v := (mem_nz.1 he1n).1
      have hd1 : d e1 ≠ 0 := (mem_nz.1 he1n).2
      have he1f : e1 ∈ frac y := by
        have : e1 ∈ starF a b (frac y) v := by rw [h2]; simp
        exact (mem_starF.1 this).1
      have hother : ∀ e ∈ (star a b v).erase e1, y e = 0 ∨ y e = 1 := by
        intro e he
        have hne : e ≠ e1 := Finset.ne_of_mem_erase he
        have hes : e ∈ star a b v := Finset.mem_of_mem_erase he
        have hnf : e ∉ frac y := by
          intro hf
          have : e ∈ starF a b (frac y) v := mem_starF.2 ⟨hf, (mem_starF.1 hes).2⟩
          rw [h2] at this; exact hne (Finset.mem_singleton.1 this)
        rw [mem_frac, not_and_or, not_lt, not_lt] at hnf
        rcases hnf with h | h
        · left; linarith [(hy.1 e).1]
        · right; linarith [(hy.1 e).2]
      have hK : ∑ e ∈ (star a b v).erase e1, y e =
          ((((star a b v).erase e1).filter (fun e => y e = 1)).card : ℝ) := by
        have : ∀ e ∈ (star a b v).erase e1, y e = if y e = 1 then 1 else 0 := by
          intro e he; rcases hother e he with h | h <;> simp [h]
        rw [Finset.sum_congr rfl this, Finset.sum_boole]
      obtain ⟨k, hk⟩ : ∃ k : ℕ, ∑ e ∈ (star a b v).erase e1, y e = k := ⟨_, hK⟩
      have hsplit : ∑ e ∈ star a b v, y e = y e1 + ∑ e ∈ (star a b v).erase e1, y e :=
        (Finset.add_sum_erase _ _ he1).symm
      rw [hsplit, hk]
      have hb := hy.2 v
      rw [hsplit, hk] at hb
      have hf := mem_frac.1 he1f
      have hlo : (lo v : ℝ) ≤ k := by
        have h' : (lo v : ℝ) < k + 1 := by linarith
        have h'' : lo v < k + 1 := by exact_mod_cast h'
        exact_mod_cast Nat.lt_succ_iff.1 h''
      have hhi : (k : ℝ) + 1 ≤ hi v := by
        have h' : (k : ℝ) < hi v := by linarith
        have h'' : k < hi v := by exact_mod_cast h'
        exact_mod_cast h''
      have hz := ht e1 hd1
      constructor <;> linarith

lemma prod_mix (a : E → A) (b : E → B) (y : E → ℝ) (hy01 : ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (d : E → ℤ) (hd : GoodDir a b (frac y) d)
    (c : E → ℝ) (v : A ⊕ B) (hc : ∀ e ∈ star a b v, 0 ≤ c e ∧ c e ≤ 1)
    (q t1 t2 : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hqt : q * t1 + (1 - q) * t2 = 0) :
    q * ∏ e ∈ star a b v, (1 - c e * (y e + t1 * d e)) +
      (1 - q) * ∏ e ∈ star a b v, (1 - c e * (y e + t2 * d e)) ≤
      ∏ e ∈ star a b v, (1 - c e * y e) := by
  have hsplit : ∀ t : ℝ, ∏ e ∈ star a b v, (1 - c e * (y e + t * d e)) =
      (∏ e ∈ nz (star a b v) d, (1 - c e * (y e + t * d e))) *
        ∏ e ∈ (star a b v).filter (fun e => ¬ d e ≠ 0), (1 - c e * y e) := by
    intro t
    rw [← Finset.prod_filter_mul_prod_filter_not (star a b v) (fun e => d e ≠ 0)]
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    have : d e = 0 := by
      have := (Finset.mem_filter.1 he).2
      push_neg at this; exact this
    rw [this]; simp
  have h0 : ∏ e ∈ star a b v, (1 - c e * y e) =
      (∏ e ∈ nz (star a b v) d, (1 - c e * (y e + 0 * d e))) *
        ∏ e ∈ (star a b v).filter (fun e => ¬ d e ≠ 0), (1 - c e * y e) := by
    rw [← hsplit 0]; simp
  obtain ⟨R, hR⟩ : ∃ R, R = ∏ e ∈ (star a b v).filter (fun e => ¬ d e ≠ 0), (1 - c e * y e) :=
    ⟨_, rfl⟩
  have hRnn : 0 ≤ R := by
    rw [hR]
    apply Finset.prod_nonneg
    intro e he
    have hce := hc e (Finset.mem_filter.1 he).1
    have hye := hy01 e
    have : c e * y e ≤ 1 := mul_le_one₀ hce.2 hye.1 hye.2
    linarith
  rw [hsplit t1, hsplit t2, h0, ← hR]
  rcases pattern a b y d hd v with h0' | ⟨e1, e2, hne, h12, h1, h2⟩ | ⟨e1, h1, _, _⟩
  · rw [h0']; simp only [Finset.prod_empty]; nlinarith
  · have m1 : e1 ∈ nz (star a b v) d := by rw [h12]; simp
    have m2 : e2 ∈ nz (star a b v) d := by rw [h12]; simp
    have hc1 := hc e1 (mem_nz.1 m1).1
    have hc2 := hc e2 (mem_nz.1 m2).1
    rw [h12, Finset.prod_pair hne, Finset.prod_pair hne, Finset.prod_pair hne, h1, h2]
    push_cast
    have hnn : 0 ≤ R * c e1 * c e2 * (q * t1 ^ 2 + (1 - q) * t2 ^ 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hRnn hc1.1) hc2.1)
        (add_nonneg (mul_nonneg hq0 (sq_nonneg t1)) (mul_nonneg (by linarith) (sq_nonneg t2)))
    have hlin := congrArg
      (fun z => R * ((1 - c e1 * y e1) * c e2 - (1 - c e2 * y e2) * c e1) * z) hqt
    simp only [mul_zero] at hlin
    nlinarith [hnn, hlin]
  · rw [h1, Finset.prod_singleton, Finset.prod_singleton, Finset.prod_singleton]
    have hlin := congrArg (fun z => R * c e1 * (d e1 : ℝ) * z) hqt
    simp only [mul_zero] at hlin
    nlinarith [hlin]

lemma mix_good (a : E → A) (b : E → B) (lo hi : A ⊕ B → ℕ) (y y1 y2 : E → ℝ)
    (w1 w2 : (E → Bool) → ℝ) (q : ℝ)
    (h1 : Good a b lo hi y1 w1) (h2 : Good a b lo hi y2 w2) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hm : ∀ e, q * y1 e + (1 - q) * y2 e = y e)
    (hnc : ∀ (c : E → ℝ) (v : A ⊕ B), (∀ e ∈ star a b v, 0 ≤ c e ∧ c e ≤ 1) →
      q * ∏ e ∈ star a b v, (1 - c e * y1 e) + (1 - q) * ∏ e ∈ star a b v, (1 - c e * y2 e) ≤
        ∏ e ∈ star a b v, (1 - c e * y e)) :
    Good a b lo hi y (fun X => q * w1 X + (1 - q) * w2 X) := by
  have hq1' : 0 ≤ 1 - q := by linarith
  refine ⟨fun X => ?_, ?_, fun e => ?_, fun X hX => ?_, fun c v hc => ?_⟩
  · exact add_nonneg (mul_nonneg hq0 (h1.nonneg X)) (mul_nonneg hq1' (h2.nonneg X))
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1.sum_one, h2.sum_one]
    ring
  · have : ∑ X, (q * w1 X + (1 - q) * w2 X) * bitR (X e) =
        q * ∑ X, w1 X * bitR (X e) + (1 - q) * ∑ X, w2 X * bitR (X e) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro X _; ring
    rw [this, h1.marg, h2.marg]; exact hm e
  · by_cases hw : w1 X = 0
    · have : w2 X ≠ 0 := by
        intro h; apply hX; rw [hw, h]; ring
      exact h2.supp X this
    · exact h1.supp X hw
  · calc ∑ X, (q * w1 X + (1 - q) * w2 X) * ∏ e ∈ star a b v, (1 - c e * bitR (X e))
        = q * ∑ X, w1 X * ∏ e ∈ star a b v, (1 - c e * bitR (X e)) +
            (1 - q) * ∑ X, w2 X * ∏ e ∈ star a b v, (1 - c e * bitR (X e)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro X _; ring
      _ ≤ q * ∏ e ∈ star a b v, (1 - c e * y1 e) + (1 - q) * ∏ e ∈ star a b v, (1 - c e * y2 e) :=
          add_le_add (mul_le_mul_of_nonneg_left (h1.nc c v hc) hq0)
            (mul_le_mul_of_nonneg_left (h2.nc c v hc) hq1')
      _ ≤ _ := hnc c v hc

theorem round_aux (a : E → A) (b : E → B) (lo hi : A ⊕ B → ℕ) (n : ℕ) :
    ∀ y : E → ℝ, Feas a b lo hi y → (frac y).card ≤ n → ∃ w, Good a b lo hi y w := by
  induction n with
  | zero =>
    intro y hy hc
    exact base_good a b lo hi y hy (Finset.card_eq_zero.1 (Nat.le_zero.1 hc))
  | succ n ih =>
    intro y hy hc
    by_cases h0 : frac y = ∅
    · exact base_good a b lo hi y hy h0
    obtain ⟨d, hd⟩ := exists_dir a b (frac y) (Finset.nonempty_iff_ne_empty.2 h0)
    have hdv := dir_val a b _ d hd
    have hfr : ∀ e, d e ≠ 0 → 0 < y e ∧ y e < 1 := fun e he => mem_frac.1 (hd.1 e he)
    obtain ⟨e0, he0⟩ := hd.2.1
    have hmemS : ∀ e, d e ≠ 0 → e ∈ Finset.univ.filter (fun e => d e ≠ 0) := by
      intro e he; simp [he]
    have hne : (Finset.univ.filter (fun e => d e ≠ 0)).Nonempty := ⟨e0, hmemS e0 he0⟩
    obtain ⟨α, hα⟩ : ∃ α, α = (Finset.univ.filter (fun e => d e ≠ 0)).inf' hne
        (fun e => if d e = 1 then 1 - y e else y e) := ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ : ∃ β, β = (Finset.univ.filter (fun e => d e ≠ 0)).inf' hne
        (fun e => if d e = 1 then y e else 1 - y e) := ⟨_, rfl⟩
    have hαle : ∀ e, d e ≠ 0 → α ≤ (if d e = 1 then 1 - y e else y e) := by
      intro e he; rw [hα]; exact Finset.inf'_le _ (hmemS e he)
    have hβle : ∀ e, d e ≠ 0 → β ≤ (if d e = 1 then y e else 1 - y e) := by
      intro e he; rw [hβ]; exact Finset.inf'_le _ (hmemS e he)
    have hαpos : 0 < α := by
      rw [hα, Finset.lt_inf'_iff]
      intro e he
      have := hfr e (Finset.mem_filter.1 he).2
      split_ifs <;> linarith
    have hβpos : 0 < β := by
      rw [hβ, Finset.lt_inf'_iff]
      intro e he
      have := hfr e (Finset.mem_filter.1 he).2
      split_ifs <;> linarith
    obtain ⟨e1, he1, hαe1⟩ := Finset.exists_mem_eq_inf' hne
      (fun e => if d e = 1 then 1 - y e else y e)
    obtain ⟨e2, he2, hβe2⟩ := Finset.exists_mem_eq_inf' hne
      (fun e => if d e = 1 then y e else 1 - y e)
    rw [← hα] at hαe1
    rw [← hβ] at hβe2
    have hd1 : d e1 ≠ 0 := (Finset.mem_filter.1 he1).2
    have hd2 : d e2 ≠ 0 := (Finset.mem_filter.1 he2).2
    have hy1 : Feas a b lo hi (fun e => y e + α * d e) := by
      apply feas_move a b lo hi y hy d hd α
      intro e he
      have h1 := hαle e he
      have h2 := hfr e he
      rcases hdv e he with h | h
      · rw [if_pos h] at h1; rw [h]; push_cast; constructor <;> linarith
      · rw [if_neg (by rw [h]; norm_num)] at h1; rw [h]; push_cast; constructor <;> linarith
    have hy2 : Feas a b lo hi (fun e => y e + (-β) * d e) := by
      apply feas_move a b lo hi y hy d hd (-β)
      intro e he
      have h1 := hβle e he
      have h2 := hfr e he
      rcases hdv e he with h | h
      · rw [if_pos h] at h1; rw [h]; push_cast; constructor <;> linarith
      · rw [if_neg (by rw [h]; norm_num)] at h1; rw [h]; push_cast; constructor <;> linarith
    have hsub : ∀ t : ℝ, frac (fun e => y e + t * d e) ⊆ frac y := by
      intro t e he
      by_cases h : d e = 0
      · rw [mem_frac] at he ⊢; rw [h] at he; simpa using he
      · exact hd.1 e h
    have hlt1 : (frac (fun e => y e + α * d e)).card < (frac y).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (hsub α)]
      refine ⟨e1, hd.1 e1 hd1, ?_⟩
      rw [mem_frac]
      rcases hdv e1 hd1 with h | h
      · rw [if_pos h] at hαe1; rw [h, hαe1]; push_cast; intro h'; linarith [h'.2]
      · rw [if_neg (by rw [h]; norm_num)] at hαe1; rw [h, hαe1]; push_cast; intro h'
        linarith [h'.1]
    have hlt2 : (frac (fun e => y e + (-β) * d e)).card < (frac y).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (hsub (-β))]
      refine ⟨e2, hd.1 e2 hd2, ?_⟩
      rw [mem_frac]
      rcases hdv e2 hd2 with h | h
      · rw [if_pos h] at hβe2; rw [h, hβe2]; push_cast; intro h'; linarith [h'.1]
      · rw [if_neg (by rw [h]; norm_num)] at hβe2; rw [h, hβe2]; push_cast; intro h'
        linarith [h'.2]
    obtain ⟨w1, hw1⟩ := ih _ hy1 (by omega)
    obtain ⟨w2, hw2⟩ := ih _ hy2 (by omega)
    have hab : 0 < α + β := by linarith
    obtain ⟨q, hq⟩ : ∃ q, q = β / (α + β) := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := by rw [hq]; positivity
    have hq1 : q ≤ 1 := by rw [hq, div_le_one hab]; linarith
    have hqt : q * α + (1 - q) * (-β) = 0 := by
      rw [hq]; field_simp; ring
    refine ⟨_, mix_good a b lo hi y _ _ w1 w2 q hw1 hw2 hq0 hq1 ?_ ?_⟩
    · intro e
      linear_combination (d e : ℝ) * hqt
    · intro c v hc
      exact prod_mix a b y hy.1 d hd c v hc q α (-β) hq0 hq1 hqt

theorem round_exists (a : E → A) (b : E → B) (lo hi : A ⊕ B → ℕ) (y : E → ℝ)
    (hy : Feas a b lo hi y) : ∃ w, Good a b lo hi y w :=
  round_aux a b lo hi _ y hy le_rfl

end Aux_DepRound

namespace Aux_Farkas


section Cone

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [Fintype W]

def LI (g : ι → (W → ℝ)) (T : Finset ι) : Prop :=
  ∀ f : ι → ℝ, ∑ i ∈ T, f i • g i = 0 → ∀ i ∈ T, f i = 0

theorem carath (g : ι → (W → ℝ)) : ∀ (K : ℕ) (lam : ι → ℝ), (∀ i, 0 ≤ lam i) →
    (Finset.univ.filter (fun i => lam i ≠ 0)).card ≤ K →
    ∃ T : Finset ι, LI g T ∧ ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧
      ∑ i, μ i • g i = ∑ i, lam i • g i := by
  intro K
  induction K with
  | zero =>
    intro lam hlam hcard
    refine ⟨∅, fun f _ i hi => absurd hi (Finset.notMem_empty i), lam, hlam, ?_, rfl⟩
    intro i _
    by_contra h
    have hi : i ∈ Finset.univ.filter (fun i => lam i ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  | succ K ih =>
    intro lam hlam hcard
    obtain ⟨S, hS⟩ : ∃ S : Finset ι, S = Finset.univ.filter (fun i => lam i ≠ 0) := ⟨_, rfl⟩
    have memS : ∀ i, i ∈ S ↔ lam i ≠ 0 := by intro i; rw [hS]; simp
    rw [← hS] at hcard
    by_cases hLI : LI g S
    · refine ⟨S, hLI, lam, hlam, fun i hi => ?_, rfl⟩
      by_contra h
      exact hi ((memS i).mpr h)
    · unfold LI at hLI
      push_neg at hLI
      obtain ⟨f, hf, i₀, hi₀S, hfi₀⟩ := hLI
      have hc : ∑ i, (if i ∈ S then f i else 0) • g i = 0 := by
        calc ∑ i, (if i ∈ S then f i else 0) • g i
            = ∑ i ∈ S, (if i ∈ S then f i else 0) • g i :=
              Eq.symm (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi]))
          _ = ∑ i ∈ S, f i • g i := Finset.sum_congr rfl (fun i hi => by simp [hi])
          _ = 0 := hf
      obtain ⟨d, hd0, hdS, hdi₀⟩ : ∃ d : ι → ℝ, ∑ i, d i • g i = 0 ∧
          (∀ i, i ∉ S → d i = 0) ∧ 0 < d i₀ := by
        rcases lt_or_gt_of_ne hfi₀ with hneg | hpos
        · refine ⟨fun i => -(if i ∈ S then f i else 0), ?_, ?_, ?_⟩
          · simp only [neg_smul, Finset.sum_neg_distrib, hc, neg_zero]
          · intro i hi; simp [hi]
          · simp only [if_pos hi₀S]; linarith
        · refine ⟨fun i => if i ∈ S then f i else 0, hc, ?_, ?_⟩
          · intro i hi; simp [hi]
          · simp only [if_pos hi₀S]; exact hpos
      have hdpos : ∀ i, 0 < d i → i ∈ S := by
        intro i hi
        by_contra h
        rw [hdS i h] at hi
        exact lt_irrefl _ hi
      obtain ⟨P, hP⟩ : ∃ P : Finset ι, P = Finset.univ.filter (fun i => 0 < d i) := ⟨_, rfl⟩
      have memP : ∀ i, i ∈ P ↔ 0 < d i := by intro i; rw [hP]; simp
      have hPne : P.Nonempty := ⟨i₀, (memP i₀).mpr hdi₀⟩
      obtain ⟨i₁, hi₁P, hmin⟩ := Finset.exists_min_image P (fun i => lam i / d i) hPne
      have hd1 : 0 < d i₁ := (memP i₁).mp hi₁P
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = lam i₁ / d i₁ := ⟨_, rfl⟩
      have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (hlam i₁) hd1.le
      have hlam' : ∀ i, 0 ≤ lam i - t * d i := by
        intro i
        by_cases hdi : 0 < d i
        · have h1 : t ≤ lam i / d i := by rw [ht]; exact hmin i ((memP i).mpr hdi)
          rw [le_div_iff₀ hdi] at h1
          linarith
        · push_neg at hdi
          nlinarith [hlam i, ht0, hdi]
      have hzero : lam i₁ - t * d i₁ = 0 := by
        rw [ht, div_mul_cancel₀ _ hd1.ne', sub_self]
      have hsupp : Finset.univ.filter (fun i => lam i - t * d i ≠ 0) ⊆ S.erase i₁ := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [Finset.mem_erase]
        refine ⟨fun h => hi.2 (by rw [h]; exact hzero), ?_⟩
        by_contra hiS
        apply hi.2
        rw [hdS i hiS]
        have : lam i = 0 := by
          by_contra h'
          exact hiS ((memS i).mpr h')
        rw [this]
        ring
      have hcard' : (Finset.univ.filter (fun i => lam i - t * d i ≠ 0)).card ≤ K := by
        have h1 := Finset.card_le_card hsupp
        have h2 := Finset.card_erase_of_mem (hdpos i₁ hd1)
        omega
      obtain ⟨T, hT, μ, hμ0, hμT, hμsum⟩ := ih (fun i => lam i - t * d i) hlam' hcard'
      refine ⟨T, hT, μ, hμ0, hμT, ?_⟩
      have hsplit : ∑ i, (lam i - t * d i) • g i = ∑ i, lam i • g i - t • ∑ i, d i • g i := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [sub_smul, mul_smul]
      rw [hμsum, hsplit, hd0, smul_zero, sub_zero]

def coneOf (g : ι → (W → ℝ)) : Set (W → ℝ) :=
  {x | ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i • g i = x}

theorem mem_coneOf (g : ι → (W → ℝ)) (x : W → ℝ) :
    x ∈ coneOf g ↔ ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i • g i = x := Iff.rfl

def coneT (g : ι → (W → ℝ)) (T : Finset ι) : Set (W → ℝ) :=
  {x | ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • g i = x}

theorem mem_coneT (g : ι → (W → ℝ)) (T : Finset ι) (x : W → ℝ) :
    x ∈ coneT g T ↔
      ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • g i = x := Iff.rfl

theorem sum_ext_T (g : ι → (W → ℝ)) (T : Finset ι) (μ : T → ℝ) :
    ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i = ∑ i : T, μ i • g i := by
  have h1 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i =
      ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i :=
    Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [dif_neg hi, zero_smul])
  rw [← h1, ← Finset.sum_coe_sort T]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.2]

theorem sum_restrict_T (g : ι → (W → ℝ)) (T : Finset ι) (μ : ι → ℝ)
    (hμT : ∀ i, i ∉ T → μ i = 0) :
    ∑ i : T, μ i • g i = ∑ i, μ i • g i := by
  have h1 : ∑ i : T, μ i • g i = ∑ i ∈ T, μ i • g i := Finset.sum_coe_sort T (fun i => μ i • g i)
  rw [h1]
  exact Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [hμT i hi, zero_smul])

theorem coneT_closed (g : ι → (W → ℝ)) (T : Finset ι) (hT : LI g T) :
    IsClosed (coneT g T) := by
  let L : (T → ℝ) →ₗ[ℝ] (W → ℝ) := Fintype.linearCombination ℝ (fun i : T => g i)
  have hL : ∀ μ : T → ℝ, L μ = ∑ i : T, μ i • g i := fun μ => rfl
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro μ hμ
    rw [hL] at hμ
    have h1 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i = 0 := by
      have h3 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i =
          ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i :=
        Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [dif_neg hi, zero_smul])
      rw [h3, sum_ext_T]
      exact hμ
    have h2 := hT _ h1
    funext i
    have := h2 i i.2
    rw [dif_pos i.2] at this
    exact this
  have hA : IsClosed {μ : T → ℝ | ∀ i, 0 ≤ μ i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have heq : coneT g T = L '' {μ : T → ℝ | ∀ i, 0 ≤ μ i} := by
    ext x
    rw [mem_coneT]
    constructor
    · rintro ⟨μ, hμ0, hμT, rfl⟩
      refine ⟨fun i => μ i, fun i => hμ0 i, ?_⟩
      rw [hL]
      exact sum_restrict_T g T μ hμT
    · rintro ⟨μ, hμ0, rfl⟩
      refine ⟨fun i => if h : i ∈ T then μ ⟨i, h⟩ else 0, ?_, ?_, ?_⟩
      · intro i
        show 0 ≤ (if h : i ∈ T then μ ⟨i, h⟩ else 0)
        by_cases h : i ∈ T
        · rw [dif_pos h]; exact hμ0 _
        · rw [dif_neg h]
      · intro i hi
        show (if h : i ∈ T then μ ⟨i, h⟩ else 0) = 0
        rw [dif_neg hi]
      · rw [hL]
        exact sum_ext_T g T μ
  rw [heq]
  exact (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap _ hA

theorem cone_closed (g : ι → (W → ℝ)) : IsClosed (coneOf g) := by
  have heq : coneOf g = ⋃ (T : Finset ι), ⋃ (_ : LI g T), coneT g T := by
    ext x
    rw [mem_coneOf, Set.mem_iUnion₂]
    constructor
    · rintro ⟨lam, hlam, rfl⟩
      obtain ⟨T, hT, μ, hμ0, hμT, hμ⟩ :=
        carath g (Finset.univ.filter (fun i => lam i ≠ 0)).card lam hlam le_rfl
      exact ⟨T, hT, (mem_coneT g T _).mpr ⟨μ, hμ0, hμT, hμ⟩⟩
    · rintro ⟨T, _, hx⟩
      obtain ⟨μ, hμ0, _, hμ⟩ := (mem_coneT g T x).mp hx
      exact ⟨μ, hμ0, hμ⟩
  rw [heq]
  exact isClosed_iUnion_of_finite (fun T => isClosed_iUnion_of_finite (fun hT => coneT_closed g T hT))

end Cone


/-! ### Affine Farkas lemma -/

section Farkas

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma coneOf_convex {ι W : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] (g : ι → (W → ℝ)) :
    Convex ℝ (coneOf g) := by
  intro x hx y hy a b ha hb _
  obtain ⟨l1, hl1, rfl⟩ := (mem_coneOf g x).mp hx
  obtain ⟨l2, hl2, rfl⟩ := (mem_coneOf g y).mp hy
  refine (mem_coneOf g _).mpr ⟨fun i => a * l1 i + b * l2 i,
    fun i => add_nonneg (mul_nonneg ha (hl1 i)) (mul_nonneg hb (hl2 i)), ?_⟩
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_smul, mul_smul, mul_smul]

/-- generators of the homogenised cone. -/
def g1 {p : ℕ} (G : Fin p → V → ℝ) (h : Fin p → ℝ) (j : Fin p) : Option V → ℝ :=
  fun o => Option.elim o (h j) (G j)

def g3 {r : ℕ} (K : Fin r → V → ℝ) (e : Fin r → ℝ) (l : Fin r) : Option V → ℝ :=
  fun o => Option.elim o (e l) (K l)

def g4 : Option V → ℝ := fun o => Option.elim o 1 (fun _ => 0)

def gens {p r : ℕ} (G : Fin p → V → ℝ) (h : Fin p → ℝ) (K : Fin r → V → ℝ) (e : Fin r → ℝ) :
    ((Fin p ⊕ Fin p) ⊕ (Fin r ⊕ Unit)) → (Option V → ℝ) :=
  Sum.elim (Sum.elim (g1 G h) (fun j => -(g1 G h j))) (Sum.elim (g3 K e) (fun _ => g4))

lemma farkas {p r : ℕ} (G : Fin p → V → ℝ) (h : Fin p → ℝ) (K : Fin r → V → ℝ)
    (e : Fin r → ℝ) (a : V → ℝ) (β : ℝ)
    (hne : ∃ z : V → ℝ, (∀ j, ∑ v, G j v * z v = h j) ∧ (∀ l, ∑ v, K l v * z v ≤ e l))
    (hval : ∀ z : V → ℝ, (∀ j, ∑ v, G j v * z v = h j) → (∀ l, ∑ v, K l v * z v ≤ e l) →
      ∑ v, a v * z v ≤ β) :
    ∃ (μ : Fin p → ℝ) (lam : Fin r → ℝ), (∀ l, 0 ≤ lam l) ∧
      (∀ v, a v = ∑ j, μ j * G j v + ∑ l, lam l * K l v) ∧
      ∑ j, μ j * h j + ∑ l, lam l * e l ≤ β := by
  classical
  have hmem : (fun o => Option.elim o β a) ∈ coneOf (gens G h K e) := by
    by_contra hnot
    obtain ⟨f, u, hfu, hut⟩ :=
      geometric_hahn_banach_closed_point (coneOf_convex _) (cone_closed _) hnot
    have h0mem : (0 : Option V → ℝ) ∈ coneOf (gens G h K e) :=
      (mem_coneOf _ 0).mpr ⟨0, fun _ => le_rfl, by simp⟩
    have hu : 0 < u := by
      have := hfu 0 h0mem
      simpa using this
    have hg : ∀ i, f (gens G h K e i) ≤ 0 := by
      intro i
      by_contra hneg
      push_neg at hneg
      have hm : (u / f (gens G h K e i)) • gens G h K e i ∈ coneOf (gens G h K e) := by
        refine (mem_coneOf _ _).mpr ⟨fun j => if j = i then u / f (gens G h K e i) else 0,
          fun j => ?_, ?_⟩
        · show 0 ≤ (if j = i then u / f (gens G h K e i) else 0)
          by_cases hj : j = i
          · rw [if_pos hj]; exact le_of_lt (div_pos hu hneg)
          · rw [if_neg hj]
        · simp [ite_smul]
      have := hfu _ hm
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne'] at this
      exact lt_irrefl _ this
    have hfx : ∀ w : Option V → ℝ, f w = ∑ o, w o * f (fun j => if o = j then (1 : ℝ) else 0) := by
      intro w
      conv_lhs => rw [pi_eq_sum_univ w]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [map_smul, smul_eq_mul]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = f (fun j => if (none : Option V) = j then (1 : ℝ) else 0) :=
      ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : V → ℝ, y = fun v => f (fun j => if (some v : Option V) = j then (1 : ℝ) else 0) :=
      ⟨_, rfl⟩
    have hf' : ∀ w : Option V → ℝ, f w = w none * t + ∑ v, w (some v) * y v := by
      intro w
      rw [hfx, Fintype.sum_option, ht, hy]
    have hunit := hg (Sum.inr (Sum.inr ()))
    simp only [gens, Sum.elim_inr, hf', g4, Option.elim_none, Option.elim_some, one_mul,
      zero_mul, Finset.sum_const_zero, add_zero] at hunit
    have heq : ∀ j, h j * t + ∑ v, G j v * y v = 0 := by
      intro j
      have h1 := hg (Sum.inl (Sum.inl j))
      have h2 := hg (Sum.inl (Sum.inr j))
      simp only [gens, Sum.elim_inl, Sum.elim_inr, map_neg, hf', g1, Option.elim_none,
        Option.elim_some,
        Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at h1 h2
      linarith
    have hineq : ∀ l, e l * t + ∑ v, K l v * y v ≤ 0 := by
      intro l
      have h1 := hg (Sum.inr (Sum.inl l))
      simp only [gens, Sum.elim_inr, Sum.elim_inl, hf', g3, Option.elim_none,
        Option.elim_some] at h1
      exact h1
    have htop : u < β * t + ∑ v, a v * y v := by
      have := hut
      simp only [hf', Option.elim_none, Option.elim_some] at this
      exact this
    rcases lt_or_eq_of_le hunit with htn | htz
    · have htp : 0 < -t := by linarith
      have hz : ∑ v, a v * (y v / -t) ≤ β := hval (fun v => y v / (-t)) (fun j => by
          show ∑ v, G j v * (y v / -t) = h j
          have := heq j
          rw [show ∑ v, G j v * (y v / -t) = (∑ v, G j v * y v) / (-t) by
            rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun v _ => by ring)]
          rw [div_eq_iff htp.ne']
          linarith)
        (fun l => by
          show ∑ v, K l v * (y v / -t) ≤ e l
          have := hineq l
          rw [show ∑ v, K l v * (y v / -t) = (∑ v, K l v * y v) / (-t) by
            rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun v _ => by ring)]
          rw [div_le_iff₀ htp]
          linarith)
      rw [show ∑ v, a v * (y v / -t) = (∑ v, a v * y v) / (-t) by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun v _ => by ring),
        div_le_iff₀ htp] at hz
      nlinarith
    · rw [htz] at heq hineq htop
      simp only [mul_zero, zero_add] at heq hineq htop
      obtain ⟨z0, hz0e, hz0l⟩ := hne
      have hv0 := hval z0 hz0e hz0l
      have hay : 0 < ∑ v, a v * y v := by linarith
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (β - ∑ v, a v * z0 v + 1) / ∑ v, a v * y v := ⟨_, rfl⟩
      have hs0 : 0 ≤ s := by
        rw [hs]
        apply div_nonneg _ hay.le
        linarith
      have hsplit : ∀ c : V → ℝ, ∑ v, c v * (z0 v + s * y v)
          = ∑ v, c v * z0 v + s * ∑ v, c v * y v := by
        intro c
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun v _ => by ring)
      have hz : ∑ v, a v * (z0 v + s * y v) ≤ β := hval (fun v => z0 v + s * y v)
        (fun j => by
          show ∑ v, G j v * (z0 v + s * y v) = h j
          rw [hsplit, hz0e j, heq j, mul_zero, add_zero])
        (fun l => by
          show ∑ v, K l v * (z0 v + s * y v) ≤ e l
          rw [hsplit]
          have := hineq l
          have := hz0l l
          nlinarith)
      rw [hsplit] at hz
      have hsa : s * ∑ v, a v * y v = β - ∑ v, a v * z0 v + 1 := by
        rw [hs, div_mul_cancel₀ _ hay.ne']
      linarith
  obtain ⟨lam, hlam, hsum⟩ := (mem_coneOf _ _).mp hmem
  refine ⟨fun j => lam (Sum.inl (Sum.inl j)) - lam (Sum.inl (Sum.inr j)),
    fun l => lam (Sum.inr (Sum.inl l)), fun l => hlam _, ?_, ?_⟩
  · intro v
    have := congrFun hsum (some v)
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, gens, Sum.elim_inl,
      Sum.elim_inr, g1, g3, g4, Pi.neg_apply, Option.elim_some, Fintype.sum_unique,
      mul_zero, add_zero] at this
    rw [← this]
    simp only [sub_mul, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
    ring
  · have := congrFun hsum none
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, gens, Sum.elim_inl,
      Sum.elim_inr, g1, g3, g4, Pi.neg_apply, Option.elim_none, Fintype.sum_unique,
      mul_one] at this
    have hl4 := hlam (Sum.inr (Sum.inr default))
    have e1 : ∑ j, (lam (Sum.inl (Sum.inl j)) - lam (Sum.inl (Sum.inr j))) * h j
        = ∑ j, lam (Sum.inl (Sum.inl j)) * h j + ∑ j, lam (Sum.inl (Sum.inr j)) * -h j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [e1]
    linarith

/-- the slack identity coming from a Farkas certificate. -/
lemma farkas_slack {p r : ℕ} (G : Fin p → V → ℝ) (h : Fin p → ℝ) (K : Fin r → V → ℝ)
    (e : Fin r → ℝ) (a : V → ℝ) (μ : Fin p → ℝ) (lam : Fin r → ℝ)
    (ha : ∀ v, a v = ∑ j, μ j * G j v + ∑ l, lam l * K l v)
    (z : V → ℝ) (hz : ∀ j, ∑ v, G j v * z v = h j) :
    ∑ v, a v * z v = ∑ j, μ j * h j + ∑ l, lam l * ∑ v, K l v * z v := by
  simp only [ha, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hz j, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => by ring)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => by ring)

end Farkas


end Aux_Farkas

namespace Aux_LP1

open TwoStageMatch

/-! ### Farkas over a finite index type -/

lemma farkasT {V T : Type*} [Fintype V] [DecidableEq V] [Fintype T]
    (K : T → V → ℝ) (e : T → ℝ) (a : V → ℝ) (β : ℝ)
    (hne : ∃ z : V → ℝ, ∀ t, ∑ v, K t v * z v ≤ e t)
    (hval : ∀ z : V → ℝ, (∀ t, ∑ v, K t v * z v ≤ e t) → ∑ v, a v * z v ≤ β) :
    ∃ lam : T → ℝ, (∀ t, 0 ≤ lam t) ∧ (∀ v, a v = ∑ t, lam t * K t v) ∧
      ∑ t, lam t * e t ≤ β := by
  classical
  obtain ⟨σ, -⟩ : ∃ σ : T ≃ Fin (Fintype.card T), σ = Fintype.equivFin T := ⟨_, rfl⟩
  obtain ⟨G, -⟩ : ∃ G : Fin 0 → V → ℝ, True := ⟨fun j => Fin.elim0 j, trivial⟩
  obtain ⟨h, -⟩ : ∃ h : Fin 0 → ℝ, True := ⟨fun j => Fin.elim0 j, trivial⟩
  obtain ⟨z0, hz0⟩ := hne
  have hval' : ∀ z : V → ℝ, (∀ j, ∑ v, G j v * z v = h j) →
      (∀ l, ∑ v, K (σ.symm l) v * z v ≤ e (σ.symm l)) → ∑ v, a v * z v ≤ β := by
    intro z _ hz
    apply hval z
    intro t
    have h1 := hz (σ t)
    rw [Equiv.symm_apply_apply] at h1
    exact h1
  obtain ⟨μ, lam, hlam, ha, hb⟩ := Aux_Farkas.farkas G h (fun l => K (σ.symm l))
    (fun l => e (σ.symm l)) a β ⟨z0, fun j => Fin.elim0 j, fun l => hz0 (σ.symm l)⟩ hval'
  refine ⟨fun t => lam (σ t), fun t => hlam _, ?_, ?_⟩
  · intro v
    have h2 : ∑ t, lam (σ t) * K t v = ∑ l, lam l * K (σ.symm l) v := by
      rw [← Equiv.sum_comp σ (fun l => lam l * K (σ.symm l) v)]
      simp only [Equiv.symm_apply_apply]
    rw [ha v, Fin.sum_univ_zero, zero_add, h2]
  · have h3 : ∑ t, lam (σ t) * e t = ∑ l, lam l * e (σ.symm l) := by
      rw [← Equiv.sum_comp σ (fun l => lam l * e (σ.symm l))]
      simp only [Equiv.symm_apply_apply]
    rw [h3]
    have hb' := hb
    rw [Fin.sum_univ_zero, zero_add] at hb'
    exact hb'

variable {U S : Type*} [Fintype U] [Fintype S] [DecidableEq U] [DecidableEq S]

/-! ### Matchings -/

lemma mem_matchings (E : U → S → Prop) (X : Finset U) (Y : Finset S) (M : Finset (U × S)) :
    M ∈ matchings E X Y ↔ IsMatching E X Y M := by
  simp [matchings]

lemma weight_matching (E : U → S → Prop) (w : S → ℝ) (X : Finset U) (Y : Finset S)
    (M : Finset (U × S)) (hM : IsMatching E X Y M) : weight w M = ∑ e ∈ M, w e.2 := by
  have hinj : Set.InjOn (Prod.snd : U × S → S) (M : Set (U × S)) := by
    intro e he e' he' h
    exact hM.2.2 e he e' he' h
  unfold weight matchedSupply
  rw [Finset.sum_image hinj]

lemma weak (E : U → S → Prop) (w : S → ℝ) (X : Finset U) (Y : Finset S)
    (α : U → ℝ) (β : S → ℝ) (hd : IsDualFeasible E w X Y α β) :
    maxWeightMatch E w X Y ≤ dualObj X Y α β := by
  obtain ⟨hα, hβ, hE⟩ := hd
  unfold maxWeightMatch
  apply Finset.sup'_le
  intro M hM
  have hM' : IsMatching E X Y M := (mem_matchings E X Y M).1 hM
  rw [weight_matching E w X Y M hM']
  have hinj1 : Set.InjOn (Prod.fst : U × S → U) (M : Set (U × S)) := by
    intro e he e' he' h
    exact hM'.2.1 e he e' he' h
  have hinj2 : Set.InjOn (Prod.snd : U × S → S) (M : Set (U × S)) := by
    intro e he e' he' h
    exact hM'.2.2 e he e' he' h
  have hsub1 : M.image Prod.fst ⊆ X := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hu
    exact (hM'.1 e he).2.1
  have hsub2 : M.image Prod.snd ⊆ Y := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hu
    exact (hM'.1 e he).2.2
  unfold dualObj
  calc ∑ e ∈ M, w e.2 ≤ ∑ e ∈ M, (α e.1 + β e.2) := by
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨h1, h2, h3⟩ := hM'.1 e he
        exact hE _ h2 _ h3 h1
    _ = ∑ e ∈ M, α e.1 + ∑ e ∈ M, β e.2 := Finset.sum_add_distrib
    _ = ∑ u ∈ M.image Prod.fst, α u + ∑ j ∈ M.image Prod.snd, β j := by
        rw [Finset.sum_image hinj1, Finset.sum_image hinj2]
    _ ≤ ∑ i ∈ X, α i + ∑ j ∈ Y, β j := by
        apply add_le_add
        · exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun i hi _ => hα i hi)
        · exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun j hj _ => hβ j hj)

/-! ### Integrality: fractional matchings are dominated by matchings -/

lemma star_fst_sum (f : U × S → ℝ) (i : U) :
    ∑ e ∈ Aux_DepRound.star (Prod.fst : U × S → U) Prod.snd (Sum.inl i), f e = ∑ j, f (i, j) := by
  apply Finset.sum_nbij' (fun e => e.2) (fun j => (i, j))
  · intro e _; simp
  · intro j _; simp [Aux_DepRound.star, Aux_DepRound.mem_starF]
  · intro e he
    simp [Aux_DepRound.star, Aux_DepRound.mem_starF] at he
    exact Prod.ext he.symm rfl
  · intro j _; rfl
  · intro e he
    simp [Aux_DepRound.star, Aux_DepRound.mem_starF] at he
    rw [show (i, e.2) = e from Prod.ext he.symm rfl]

lemma star_snd_sum (f : U × S → ℝ) (j : S) :
    ∑ e ∈ Aux_DepRound.star (Prod.fst : U × S → U) Prod.snd (Sum.inr j), f e = ∑ i, f (i, j) := by
  apply Finset.sum_nbij' (fun e => e.1) (fun i => (i, j))
  · intro e _; simp
  · intro i _; simp [Aux_DepRound.star, Aux_DepRound.mem_starF]
  · intro e he
    simp [Aux_DepRound.star, Aux_DepRound.mem_starF] at he
    exact Prod.ext rfl he.symm
  · intro i _; rfl
  · intro e he
    simp [Aux_DepRound.star, Aux_DepRound.mem_starF] at he
    rw [show (e.1, j) = e from Prod.ext rfl he.symm]

lemma two_le_of_two_true {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Bool) (a b : ι)
    (hab : a ≠ b) (ha : g a = true) (hb : g b = true) :
    (2 : ℝ) ≤ ∑ j, Aux_DepRound.bitR (g j) := by
  have h1 : ∑ j ∈ ({a, b} : Finset ι), Aux_DepRound.bitR (g j) ≤ ∑ j, Aux_DepRound.bitR (g j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => Aux_DepRound.bitR_nonneg _)
  rw [Finset.sum_pair hab] at h1
  have e1 : Aux_DepRound.bitR (g a) = 1 := by simp [Aux_DepRound.bitR, ha]
  have e2 : Aux_DepRound.bitR (g b) = 1 := by simp [Aux_DepRound.bitR, hb]
  rw [e1, e2] at h1
  linarith

lemma frac_le (E : U → S → Prop) (w : S → ℝ) (X : Finset U) (Y : Finset S)
    (x : U → S → ℝ) (hx : IsFracMatching E X Y x) :
    fracWeight w x ≤ maxWeightMatch E w X Y := by
  obtain ⟨hx0, hxE, hrow, hcol⟩ := hx
  have hfeas : Aux_DepRound.Feas (Prod.fst : U × S → U) Prod.snd (fun _ => 0) (fun _ => 1)
      (fun e : U × S => x e.1 e.2) := by
    refine ⟨fun e => ⟨hx0 _ _, ?_⟩, ?_⟩
    · calc x e.1 e.2 ≤ ∑ j, x e.1 j :=
            Finset.single_le_sum (f := fun j => x e.1 j) (fun j _ => hx0 e.1 j) (Finset.mem_univ _)
        _ ≤ 1 := hrow e.1
    · rintro (i | j)
      · rw [star_fst_sum]
        simp only [Nat.cast_zero, Nat.cast_one]
        exact ⟨Finset.sum_nonneg (fun j _ => hx0 i j), hrow i⟩
      · rw [star_snd_sum]
        simp only [Nat.cast_zero, Nat.cast_one]
        exact ⟨Finset.sum_nonneg (fun i _ => hx0 i j), hcol j⟩
  obtain ⟨ρ, hρ⟩ := Aux_DepRound.round_exists _ _ _ _ _ hfeas
  have hoff : ∀ Z, ρ Z ≠ 0 → ∀ e : U × S, Z e = true → x e.1 e.2 ≠ 0 := by
    intro Z hZ e he hy0
    have hm := hρ.marg e
    rw [hy0] at hm
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun Z _ => mul_nonneg (hρ.nonneg Z) (Aux_DepRound.bitR_nonneg _))).1 hm Z (Finset.mem_univ _)
    rw [show Aux_DepRound.bitR (Z e) = 1 by simp [Aux_DepRound.bitR, he], mul_one] at h0
    exact hZ h0
  -- each support point is a matching
  have hbound : ∀ Z, ρ Z ≠ 0 →
      ∑ e, Aux_DepRound.bitR (Z e) * w e.2 ≤ maxWeightMatch E w X Y := by
    intro Z hZ
    have hF := hρ.supp Z hZ
    have hrow1 : ∀ a : U, ∑ j, Aux_DepRound.bitR (Z (a, j)) ≤ 1 := by
      intro a
      have h1 := (hF.2 (Sum.inl a)).2
      rw [star_fst_sum] at h1
      simpa using h1
    have hcol1 : ∀ b : S, ∑ i, Aux_DepRound.bitR (Z (i, b)) ≤ 1 := by
      intro b
      have h1 := (hF.2 (Sum.inr b)).2
      rw [star_snd_sum] at h1
      simpa using h1
    obtain ⟨M, hMdef⟩ : ∃ M : Finset (U × S), M = Finset.univ.filter (fun e => Z e = true) :=
      ⟨_, rfl⟩
    have hmemM : ∀ e, e ∈ M ↔ Z e = true := by
      intro e
      rw [hMdef, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
    have hM : IsMatching E X Y M := by
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        exact hxE _ _ (hoff Z hZ e ((hmemM e).1 he))
      · intro e he e' he' h1
        by_contra hne
        have hbb : e.2 ≠ e'.2 := by
          intro h2
          exact hne (Prod.ext h1 h2)
        have h3 := two_le_of_two_true (fun j => Z (e.1, j)) e.2 e'.2 hbb
          (by simpa using (hmemM e).1 he)
          (by rw [h1]; simpa using (hmemM e').1 he')
        linarith [hrow1 e.1]
      · intro e he e' he' h1
        by_contra hne
        have haa : e.1 ≠ e'.1 := by
          intro h2
          exact hne (Prod.ext h2 h1)
        have h3 := two_le_of_two_true (fun i => Z (i, e.2)) e.1 e'.1 haa
          (by simpa using (hmemM e).1 he)
          (by rw [h1]; simpa using (hmemM e').1 he')
        linarith [hcol1 e.2]
    have hmem : M ∈ matchings E X Y := (mem_matchings E X Y M).2 hM
    have hw : ∑ e, Aux_DepRound.bitR (Z e) * w e.2 = weight w M := by
      rw [weight_matching E w X Y M hM, hMdef, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : Z e = true
      · rw [if_pos h]
        simp [Aux_DepRound.bitR, h]
      · rw [if_neg h]
        simp [Aux_DepRound.bitR, h]
    rw [hw]
    unfold maxWeightMatch
    exact Finset.le_sup' (weight w) hmem
  have hfw : fracWeight w x = ∑ e : U × S, x e.1 e.2 * w e.2 :=
    (Fintype.sum_prod_type' (fun a b => x a b * w b)).symm
  rw [hfw]
  calc ∑ e : U × S, x e.1 e.2 * w e.2
      = ∑ e : U × S, (∑ Z, ρ Z * Aux_DepRound.bitR (Z e)) * w e.2 := by
        apply Finset.sum_congr rfl
        intro e _
        rw [hρ.marg e]
    _ = ∑ Z, ρ Z * ∑ e : U × S, Aux_DepRound.bitR (Z e) * w e.2 := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro Z _
        apply Finset.sum_congr rfl
        intro e _
        ring
    _ ≤ ∑ Z, ρ Z * maxWeightMatch E w X Y := by
        apply Finset.sum_le_sum
        intro Z _
        by_cases hZ : ρ Z = 0
        · rw [hZ, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hbound Z hZ) (hρ.nonneg Z)
    _ = maxWeightMatch E w X Y := by
        rw [← Finset.sum_mul, hρ.sum_one, one_mul]

/-! ### An optimal matching as a fractional matching -/

lemma attain (E : U → S → Prop) (w : S → ℝ) (X : Finset U) (Y : Finset S) :
    ∃ x : U → S → ℝ, IsFracMatching E X Y x ∧ fracWeight w x = maxWeightMatch E w X Y := by
  obtain ⟨M, hM, hMeq⟩ :=
    Finset.exists_mem_eq_sup' (matchings_nonempty E X Y) (weight w)
  have hM' : IsMatching E X Y M := (mem_matchings E X Y M).1 hM
  refine ⟨fun i j => if (i, j) ∈ M then 1 else 0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i j
    show (0 : ℝ) ≤ if (i, j) ∈ M then 1 else 0
    by_cases h : (i, j) ∈ M
    · rw [if_pos h]; norm_num
    · rw [if_neg h]
  · intro i j hne
    have h : (i, j) ∈ M := by
      by_contra h
      apply hne
      show (if (i, j) ∈ M then (1 : ℝ) else 0) = 0
      rw [if_neg h]
    exact hM'.1 _ h
  · intro i
    show ∑ j, (if (i, j) ∈ M then (1 : ℝ) else 0) ≤ 1
    by_cases h : ∃ j, (i, j) ∈ M
    · obtain ⟨j0, hj0⟩ := h
      rw [Finset.sum_eq_single j0]
      · rw [if_pos hj0]
      · intro j _ hj
        have hn : (i, j) ∉ M := by
          intro hmem
          have h1 := hM'.2.1 _ hmem _ hj0 rfl
          exact hj (congrArg Prod.snd h1)
        rw [if_neg hn]
      · intro hn
        exact absurd (Finset.mem_univ j0) hn
    · push_neg at h
      have hz : ∑ j, (if (i, j) ∈ M then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero (fun j _ => if_neg (h j))
      rw [hz]
      norm_num
  · intro j
    show ∑ i, (if (i, j) ∈ M then (1 : ℝ) else 0) ≤ 1
    by_cases h : ∃ i, (i, j) ∈ M
    · obtain ⟨i0, hi0⟩ := h
      rw [Finset.sum_eq_single i0]
      · rw [if_pos hi0]
      · intro i _ hi
        have hn : (i, j) ∉ M := by
          intro hmem
          have h1 := hM'.2.2 _ hmem _ hi0 rfl
          exact hi (congrArg Prod.fst h1)
        rw [if_neg hn]
      · intro hn
        exact absurd (Finset.mem_univ i0) hn
    · push_neg at h
      have hz : ∑ i, (if (i, j) ∈ M then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero (fun i _ => if_neg (h i))
      rw [hz]
      norm_num
  · unfold maxWeightMatch
    rw [hMeq, weight_matching E w X Y M hM']
    have hfw : fracWeight w (fun i j => if (i, j) ∈ M then (1 : ℝ) else 0) =
        ∑ e : U × S, (if e ∈ M then (1 : ℝ) else 0) * w e.2 :=
      (Fintype.sum_prod_type' (fun a b => (if (a, b) ∈ M then (1 : ℝ) else 0) * w b)).symm
    rw [hfw]
    have h1 : ∀ e : U × S, (if e ∈ M then (1 : ℝ) else 0) * w e.2 =
        if e ∈ M then w e.2 else 0 := by
      intro e
      by_cases h : e ∈ M
      · rw [if_pos h, if_pos h, one_mul]
      · rw [if_neg h, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl (fun e _ => h1 e), Finset.sum_ite_mem, Finset.univ_inter]

/-! ### Strong duality via Farkas -/

open Classical in
noncomputable def cB (E : U → S → Prop) (X : Finset U) (Y : Finset S) (e : U × S) : ℝ :=
  if E e.1 e.2 ∧ e.1 ∈ X ∧ e.2 ∈ Y then 0 else 1

noncomputable def Kc (E : U → S → Prop) (X : Finset U) (Y : Finset S) :
    ((U × S) ⊕ (U × S)) ⊕ (U ⊕ S) → U × S → ℝ :=
  Sum.elim (Sum.elim (fun e v => if v = e then -1 else 0)
      (fun e v => if v = e then cB E X Y e else 0))
    (Sum.elim (fun i v => if v.1 = i then 1 else 0) (fun j v => if v.2 = j then 1 else 0))

noncomputable def ec : ((U × S) ⊕ (U × S)) ⊕ (U ⊕ S) → ℝ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

lemma sumA (E : U → S → Prop) (X : Finset U) (Y : Finset S) (z : U × S → ℝ) (e : U × S) :
    ∑ v, Kc E X Y (Sum.inl (Sum.inl e)) v * z v = -z e := by
  show ∑ v : U × S, (if v = e then (-1 : ℝ) else 0) * z v = -z e
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl, neg_one_mul]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ e) h

lemma sumB (E : U → S → Prop) (X : Finset U) (Y : Finset S) (z : U × S → ℝ) (e : U × S) :
    ∑ v, Kc E X Y (Sum.inl (Sum.inr e)) v * z v = cB E X Y e * z e := by
  show ∑ v : U × S, (if v = e then cB E X Y e else 0) * z v = cB E X Y e * z e
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ e) h

lemma sumC (E : U → S → Prop) (X : Finset U) (Y : Finset S) (z : U × S → ℝ) (i : U) :
    ∑ v, Kc E X Y (Sum.inr (Sum.inl i)) v * z v = ∑ j, z (i, j) := by
  show ∑ v : U × S, (if v.1 = i then (1 : ℝ) else 0) * z v = ∑ j, z (i, j)
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro b _
    rw [if_pos rfl, one_mul]
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg ha, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma sumD (E : U → S → Prop) (X : Finset U) (Y : Finset S) (z : U × S → ℝ) (j : S) :
    ∑ v, Kc E X Y (Sum.inr (Sum.inr j)) v * z v = ∑ i, z (i, j) := by
  show ∑ v : U × S, (if v.2 = j then (1 : ℝ) else 0) * z v = ∑ i, z (i, j)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma sumK (E : U → S → Prop) (X : Finset U) (Y : Finset S)
    (lam : ((U × S) ⊕ (U × S)) ⊕ (U ⊕ S) → ℝ) (v : U × S) :
    ∑ t, lam t * Kc E X Y t v =
      (-lam (Sum.inl (Sum.inl v)) + lam (Sum.inl (Sum.inr v)) * cB E X Y v) +
        (lam (Sum.inr (Sum.inl v.1)) + lam (Sum.inr (Sum.inr v.2))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ e, lam (Sum.inl (Sum.inl e)) * Kc E X Y (Sum.inl (Sum.inl e)) v =
      -lam (Sum.inl (Sum.inl v)) := by
    rw [Finset.sum_eq_single v]
    · show lam (Sum.inl (Sum.inl v)) * (if v = v then (-1 : ℝ) else 0) = _
      rw [if_pos rfl, mul_neg_one]
    · intro b _ hb
      show lam (Sum.inl (Sum.inl b)) * (if v = b then (-1 : ℝ) else 0) = 0
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ v) h
  have h2 : ∑ e, lam (Sum.inl (Sum.inr e)) * Kc E X Y (Sum.inl (Sum.inr e)) v =
      lam (Sum.inl (Sum.inr v)) * cB E X Y v := by
    rw [Finset.sum_eq_single v]
    · show lam (Sum.inl (Sum.inr v)) * (if v = v then cB E X Y v else 0) = _
      rw [if_pos rfl]
    · intro b _ hb
      show lam (Sum.inl (Sum.inr b)) * (if v = b then cB E X Y b else 0) = 0
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ v) h
  have h3 : ∑ i, lam (Sum.inr (Sum.inl i)) * Kc E X Y (Sum.inr (Sum.inl i)) v =
      lam (Sum.inr (Sum.inl v.1)) := by
    rw [Finset.sum_eq_single v.1]
    · show lam (Sum.inr (Sum.inl v.1)) * (if v.1 = v.1 then (1 : ℝ) else 0) = _
      rw [if_pos rfl, mul_one]
    · intro b _ hb
      show lam (Sum.inr (Sum.inl b)) * (if v.1 = b then (1 : ℝ) else 0) = 0
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ v.1) h
  have h4 : ∑ j, lam (Sum.inr (Sum.inr j)) * Kc E X Y (Sum.inr (Sum.inr j)) v =
      lam (Sum.inr (Sum.inr v.2)) := by
    rw [Finset.sum_eq_single v.2]
    · show lam (Sum.inr (Sum.inr v.2)) * (if v.2 = v.2 then (1 : ℝ) else 0) = _
      rw [if_pos rfl, mul_one]
    · intro b _ hb
      show lam (Sum.inr (Sum.inr b)) * (if v.2 = b then (1 : ℝ) else 0) = 0
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ v.2) h
  rw [h1, h2, h3, h4]

lemma sumE (lam : ((U × S) ⊕ (U × S)) ⊕ (U ⊕ S) → ℝ) :
    ∑ t, lam t * ec t = ∑ i, lam (Sum.inr (Sum.inl i)) + ∑ j, lam (Sum.inr (Sum.inr j)) := by
  rw [Fintype.sum_sum_type]
  have h0 : ∀ t : (U × S) ⊕ (U × S), lam (Sum.inl t) * ec (Sum.inl t) = 0 := by
    intro t
    show lam (Sum.inl t) * 0 = 0
    rw [mul_zero]
  have h1 : ∀ t : U ⊕ S, lam (Sum.inr t) * ec (Sum.inr t) = lam (Sum.inr t) := by
    intro t
    show lam (Sum.inr t) * 1 = lam (Sum.inr t)
    rw [mul_one]
  simp only [h0, h1, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sum_type]

lemma strong (E : U → S → Prop) (w : S → ℝ) (X : Finset U) (Y : Finset S) :
    ∃ (α : U → ℝ) (β : S → ℝ), IsDualFeasible E w X Y α β ∧
      dualObj X Y α β = maxWeightMatch E w X Y := by
  have hne : ∃ z : U × S → ℝ, ∀ t, ∑ v, Kc E X Y t v * z v ≤ ec t := by
    refine ⟨fun _ => 0, fun t => ?_⟩
    simp only [mul_zero, Finset.sum_const_zero]
    rcases t with t | t
    · show (0 : ℝ) ≤ 0
      exact le_refl _
    · show (0 : ℝ) ≤ 1
      norm_num
  have hval : ∀ z : U × S → ℝ, (∀ t, ∑ v, Kc E X Y t v * z v ≤ ec t) →
      ∑ v, (fun v : U × S => w v.2) v * z v ≤ maxWeightMatch E w X Y := by
    intro z hz
    have hA : ∀ e, 0 ≤ z e := by
      intro e
      have h1 := hz (Sum.inl (Sum.inl e))
      rw [sumA] at h1
      have h2 : ec (Sum.inl (Sum.inl e) : ((U × S) ⊕ (U × S)) ⊕ (U ⊕ S)) = 0 := rfl
      rw [h2] at h1
      linarith
    have hfm : IsFracMatching E X Y (fun i j => z (i, j)) := by
      refine ⟨fun i j => hA (i, j), ?_, ?_, ?_⟩
      · intro i j hne0
        by_contra hP
        have h1 := hz (Sum.inl (Sum.inr (i, j)))
        rw [sumB] at h1
        have h2 : ec (Sum.inl (Sum.inr (i, j)) : ((U × S) ⊕ (U × S)) ⊕ (U ⊕ S)) = 0 := rfl
        have h3 : cB E X Y (i, j) = 1 := by
          unfold cB
          rw [if_neg hP]
        rw [h2, h3, one_mul] at h1
        exact hne0 (le_antisymm h1 (hA (i, j)))
      · intro i
        have h1 := hz (Sum.inr (Sum.inl i))
        rw [sumC] at h1
        exact h1
      · intro j
        have h1 := hz (Sum.inr (Sum.inr j))
        rw [sumD] at h1
        exact h1
    have h1 := frac_le E w X Y (fun i j => z (i, j)) hfm
    have h2 : fracWeight w (fun i j => z (i, j)) = ∑ v, (fun v : U × S => w v.2) v * z v := by
      unfold fracWeight
      rw [← Fintype.sum_prod_type' (fun a b => z (a, b) * w b)]
      apply Finset.sum_congr rfl
      intro v _
      exact mul_comm _ _
    rw [← h2]
    exact h1
  obtain ⟨lam, hlam, ha, hb⟩ := farkasT (Kc E X Y) ec (fun v : U × S => w v.2)
    (maxWeightMatch E w X Y) hne hval
  refine ⟨fun i => lam (Sum.inr (Sum.inl i)), fun j => lam (Sum.inr (Sum.inr j)),
    ⟨fun i _ => hlam _, fun j _ => hlam _, ?_⟩, ?_⟩
  · intro i hi j hj hE
    have h1 := ha (i, j)
    rw [sumK] at h1
    have h2 : cB E X Y (i, j) = 0 := by
      unfold cB
      rw [if_pos ⟨hE, hi, hj⟩]
    rw [h2, mul_zero, add_zero] at h1
    have h3 := hlam (Sum.inl (Sum.inl (i, j)))
    show w j ≤ lam (Sum.inr (Sum.inl i)) + lam (Sum.inr (Sum.inr j))
    have h4 : w j = -lam (Sum.inl (Sum.inl (i, j))) +
        (lam (Sum.inr (Sum.inl i)) + lam (Sum.inr (Sum.inr j))) := h1
    linarith
  · apply le_antisymm
    · rw [sumE] at hb
      unfold dualObj
      have hX : ∑ i ∈ X, lam (Sum.inr (Sum.inl i)) ≤ ∑ i, lam (Sum.inr (Sum.inl i)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hlam _)
      have hY : ∑ j ∈ Y, lam (Sum.inr (Sum.inr j)) ≤ ∑ j, lam (Sum.inr (Sum.inr j)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hlam _)
      linarith
    · exact weak E w X Y (fun i => lam (Sum.inr (Sum.inl i)))
        (fun j => lam (Sum.inr (Sum.inr j))) ⟨fun i _ => hlam _, fun j _ => hlam _, by
        intro i hi j hj hE
        have h1 := ha (i, j)
        rw [sumK] at h1
        have h2 : cB E X Y (i, j) = 0 := by
          unfold cB
          rw [if_pos ⟨hE, hi, hj⟩]
        rw [h2, mul_zero, add_zero] at h1
        have h3 := hlam (Sum.inl (Sum.inl (i, j)))
        have h4 : w j = -lam (Sum.inl (Sum.inl (i, j))) +
            (lam (Sum.inr (Sum.inl i)) + lam (Sum.inr (Sum.inr j))) := h1
        show w j ≤ lam (Sum.inr (Sum.inl i)) + lam (Sum.inr (Sum.inr j))
        linarith⟩

end Aux_LP1

open TwoStageMatch in
theorem solution {U S : Type*} [Fintype U] [Fintype S] [DecidableEq S]
    (E : U → S → Prop) (w : S → ℝ) (hw : ∀ j, 0 ≤ w j) (X : Finset U) (Y : Finset S) :
    ((∃ x : U → S → ℝ, IsFracMatching E X Y x ∧ fracWeight w x = maxWeightMatch E w X Y) ∧
      ∀ x : U → S → ℝ, IsFracMatching E X Y x → fracWeight w x ≤ maxWeightMatch E w X Y) ∧
    (∃ (α : U → ℝ) (β : S → ℝ), IsDualFeasible E w X Y α β ∧
      dualObj X Y α β = maxWeightMatch E w X Y) ∧
    (∀ (α : U → ℝ) (β : S → ℝ), IsDualFeasible E w X Y α β →
      maxWeightMatch E w X Y ≤ dualObj X Y α β) := by
  classical
  exact ⟨⟨Aux_LP1.attain E w X Y, fun x hx => Aux_LP1.frac_le E w X Y x hx⟩,
    Aux_LP1.strong E w X Y, fun α β h => Aux_LP1.weak E w X Y α β h⟩

