-- Prove2me | solution 1 for ThresholdTheorem.exRec_disjoint_pair_matching
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:17:05.213319+00:00
-- url     : https://prove2.me/submissions/40a44be0-408b-4faf-bb56-dee7e3730911

import Mathlib
import Definitions.Def_threshold_theorem_joint_faults

set_option autoImplicit false
open ThresholdTheorem

private lemma arity_le_two (op : Operation) : op.arity ≤ 2 := by
  cases op with
  | gate g => cases g <;> decide
  | prep => decide
  | wait => decide

private lemma layer_eq_of_support_eq {Q : Type} [DecidableEq Q] (L : Layer Q)
    {j₁ j₂ : ℕ} {l₁ l₂ : Location Q} (hj₁ : L.locs[j₁]? = some l₁) (hj₂ : L.locs[j₂]? = some l₂)
    {i₁ : Fin l₁.op.arity} {i₂ : Fin l₂.op.arity} (hq : l₁.support i₁ = l₂.support i₂) :
    j₁ = j₂ := by
  have hlt_false : ∀ {a b : ℕ} {la lb : Location Q},
      L.locs[a]? = some la → L.locs[b]? = some lb →
      ∀ (ia : Fin la.op.arity) (ib : Fin lb.op.arity), la.support ia = lb.support ib → a < b → False := by
    intro a b la lb ha hb ia ib hab hlt
    obtain ⟨ha_lt, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨hb_lt, rfl⟩ := List.getElem?_eq_some_iff.mp hb
    set q := L.locs[a].support ia
    have hmem1 : L.locs[a] ∈ L.locs.take (a + 1) := by
      have hlen : a < (L.locs.take (a + 1)).length := by simp; omega
      have hget : (L.locs.take (a + 1))[a] = L.locs[a] := List.getElem_take
      rw [← hget]
      exact List.getElem_mem hlen
    have hmem2 : L.locs[b] ∈ L.locs.drop (a + 1) := by
      have hlen : b - (a + 1) < (L.locs.drop (a + 1)).length := by simp; omega
      have hget : (L.locs.drop (a + 1))[b - (a + 1)] = L.locs[b] := by
        rw [List.getElem_drop]
        congr 1
        omega
      rw [← hget]
      exact List.getElem_mem hlen
    have hq1 : q ∈ (L.locs.take (a + 1)).flatMap (fun ℓ => List.ofFn ℓ.support) := by
      rw [List.mem_flatMap]
      exact ⟨L.locs[a], hmem1, List.mem_ofFn.mpr ⟨ia, rfl⟩⟩
    have hq2 : q ∈ (L.locs.drop (a + 1)).flatMap (fun ℓ => List.ofFn ℓ.support) := by
      rw [List.mem_flatMap]
      exact ⟨L.locs[b], hmem2, List.mem_ofFn.mpr ⟨ib, hab.symm⟩⟩
    have hc1 : 0 < ((L.locs.take (a + 1)).flatMap (fun ℓ => List.ofFn ℓ.support)).count q :=
      List.count_pos_iff.mpr hq1
    have hc2 : 0 < ((L.locs.drop (a + 1)).flatMap (fun ℓ => List.ofFn ℓ.support)).count q :=
      List.count_pos_iff.mpr hq2
    have hpart := L.partition q
    rw [← List.take_append_drop (a + 1) L.locs, List.flatMap_append, List.count_append] at hpart
    omega
  rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
  · exact False.elim (hlt_false hj₁ hj₂ i₁ i₂ hq hlt)
  · rfl
  · exact False.elim (hlt_false hj₂ hj₁ i₂ i₁ hq.symm hgt)

private lemma locAt_eq_of_support_eq {Q : Type} [DecidableEq Q] (C : Circuit Q)
    {t j₁ j₂ : ℕ} {l₁ l₂ : Location Q}
    (hj₁ : locAt C (t, j₁) = some l₁) (hj₂ : locAt C (t, j₂) = some l₂)
    {i₁ : Fin l₁.op.arity} {i₂ : Fin l₂.op.arity} (hq : l₁.support i₁ = l₂.support i₂) :
    j₁ = j₂ := by
  simp only [locAt, Option.bind_eq_some_iff] at hj₁ hj₂
  obtain ⟨L, hL, hj₁⟩ := hj₁
  obtain ⟨L', hL', hj₂⟩ := hj₂
  rw [hL] at hL'
  injection hL' with hLL'
  subst hLL'
  exact layer_eq_of_support_eq L hj₁ hj₂ hq

private lemma locAt_snd_lt_size {Q : Type} [DecidableEq Q] (C : Circuit Q) {ℓ : ℕ × ℕ} {l : Location Q}
    (h : locAt C ℓ = some l) : ℓ.2 < C.size := by
  simp only [locAt, Option.bind_eq_some_iff] at h
  obtain ⟨L, hL, hl⟩ := h
  obtain ⟨h2_lt, _⟩ := List.getElem?_eq_some_iff.mp hl
  obtain ⟨h1_lt, rfl⟩ := List.getElem?_eq_some_iff.mp hL
  have hmem : C[ℓ.1].locs.length ∈ C.map (fun L => L.locs.length) :=
    List.mem_map.mpr ⟨C[ℓ.1], List.getElem_mem h1_lt, rfl⟩
  have hle : C[ℓ.1].locs.length ≤ C.size := List.le_sum_of_mem hmem
  omega

open Classical in
private lemma card_filter_locAt_le_two {Q : Type} [DecidableEq Q] (C : Circuit Q)
    (t : ℕ) (l₀ : Location Q) :
    ((Finset.range C.size).filter fun j =>
      ∃ l : Location Q, locAt C (t, j) = some l ∧
        ∃ (i₀ : Fin l₀.op.arity) (i : Fin l.op.arity), l₀.support i₀ = l.support i).card ≤ 2 := by
  set J := (Finset.range C.size).filter fun j =>
    ∃ l : Location Q, locAt C (t, j) = some l ∧
      ∃ (i₀ : Fin l₀.op.arity) (i : Fin l.op.arity), l₀.support i₀ = l.support i
  have hsub : ∀ j ∈ J, ∃ i₀ : Fin l₀.op.arity, ∃ l : Location Q,
      locAt C (t, j) = some l ∧ ∃ i : Fin l.op.arity, l₀.support i₀ = l.support i := by
    intro j hj
    obtain ⟨_, l, hl, i₀, i, hi⟩ := Finset.mem_filter.mp hj
    exact ⟨i₀, l, hl, i, hi⟩
  let g : ℕ → Option (Fin l₀.op.arity) := fun j =>
    if hj : j ∈ J then some (Classical.choose (hsub j hj)) else none
  have hinj : Set.InjOn g J := by
    intro j₁ hj₁ j₂ hj₂ hgj
    simp only [g, Finset.mem_coe.mp hj₁, Finset.mem_coe.mp hj₂, ↓reduceDIte, Option.some.injEq] at hgj
    obtain ⟨l₁, hl₁, i₁, hi₁⟩ := Classical.choose_spec (hsub j₁ (Finset.mem_coe.mp hj₁))
    obtain ⟨l₂, hl₂, i₂, hi₂⟩ := Classical.choose_spec (hsub j₂ (Finset.mem_coe.mp hj₂))
    have hq : l₁.support i₁ = l₂.support i₂ := by
      rw [← hi₁, hgj, hi₂]
    exact locAt_eq_of_support_eq C hl₁ hl₂ hq
  have himg_sub : J.image g ⊆ Finset.univ.image some := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    simp [g, hj]
  calc J.card
    _ = (J.image g).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ.image (some : Fin l₀.op.arity → Option (Fin l₀.op.arity))).card :=
        Finset.card_le_card himg_sub
    _ ≤ (Finset.univ : Finset (Fin l₀.op.arity)).card := Finset.card_image_le
    _ = l₀.op.arity := by simp
    _ ≤ 2 := arity_le_two l₀.op

open Classical in
private lemma card_predLocs_singleton_le_two {Q : Type} [DecidableEq Q] (C : Circuit Q) (ℓ : ℕ × ℕ) :
    (predLocs C {ℓ}).card ≤ 2 := by
  rw [predLocs, Finset.singleton_biUnion]
  cases hℓ : locAt C ℓ with
  | none =>
    simp
  | some l₀ =>
    refine Finset.card_image_le.trans ?_
    refine (Finset.card_le_card ?_).trans (card_filter_locAt_le_two C (ℓ.1 - 1) l₀)
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    obtain ⟨hj_range, _, l, l', hl, hl', i, i', hsup⟩ := hj
    injection hl' with hll'
    subst hll'
    exact ⟨hj_range, l, hl, i', i, hsup.symm⟩

open Classical in
private noncomputable def succLocs {Q : Type} [DecidableEq Q] (C : Circuit Q) (ℓ₀ : ℕ × ℕ) :
    Finset (ℕ × ℕ) :=
  ((Finset.range C.size).filter fun j' =>
    ∃ l l' : Location Q, locAt C ℓ₀ = some l ∧ locAt C (ℓ₀.1 + 1, j') = some l' ∧
      ∃ i i', l.support i = l'.support i').image fun j' => (ℓ₀.1 + 1, j')

open Classical in
private lemma mem_succLocs_of_mem_predLocs_singleton {Q : Type} [DecidableEq Q] (C : Circuit Q)
    {ℓ₀ ℓ : ℕ × ℕ} (h : ℓ₀ ∈ predLocs C {ℓ}) : ℓ ∈ succLocs C ℓ₀ := by
  rw [predLocs, Finset.singleton_biUnion, Finset.mem_image] at h
  obtain ⟨j, hj, rfl⟩ := h
  rw [Finset.mem_filter] at hj
  obtain ⟨_, hpos, l, l', hl, hl', i, i', hsup⟩ := hj
  have hℓ2 : ℓ.2 < C.size := locAt_snd_lt_size C hl'
  rw [succLocs, Finset.mem_image]
  refine ⟨ℓ.2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hℓ2, l, l', hl, ?_, i, i', hsup⟩, ?_⟩
  · have h1 : ℓ.1 - 1 + 1 = ℓ.1 := Nat.sub_add_cancel hpos
    rw [h1]
    exact hl'
  · ext <;> simp [Nat.sub_add_cancel hpos]

open Classical in
private lemma card_succLocs_le_two {Q : Type} [DecidableEq Q] (C : Circuit Q) (ℓ₀ : ℕ × ℕ) :
    (succLocs C ℓ₀).card ≤ 2 := by
  rw [succLocs]
  cases hℓ₀ : locAt C ℓ₀ with
  | none =>
    simp
  | some l₀ =>
    refine Finset.card_image_le.trans ?_
    refine (Finset.card_le_card ?_).trans (card_filter_locAt_le_two C (ℓ₀.1 + 1) l₀)
    intro j' hj'
    rw [Finset.mem_filter] at hj' ⊢
    obtain ⟨hj'_range, l, l', hl, hl', i, i', hsup⟩ := hj'
    injection hl with hll
    subst hll
    exact ⟨hj'_range, l', hl', i, i', hsup⟩

open Classical in
theorem solution {Q : Type} [DecidableEq Q]
    (R_max : ℕ) (C : Circuit Q)
    (exRec : ℕ × ℕ → Finset (ℕ × ℕ))
    (Ψ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ))
    (h_card : ∀ ℓ, (exRec ℓ).card ≤ R_max)
    (h_overlap : ∀ ℓ₁ ℓ₂, (exRec ℓ₁ ∩ exRec ℓ₂).Nonempty →
      ℓ₁ = ℓ₂ ∨ ℓ₁ ∈ predLocs C {ℓ₂} ∨ ℓ₂ ∈ predLocs C {ℓ₁})
    (h_bad : ∀ F ℓ, ℓ ∈ Ψ F → 30 ≤ (exRec ℓ ∩ F).card) :
    ∃ pairs : ℕ × ℕ → Finset (Finset (ℕ × ℕ)),
      (∀ ℓ, (pairs ℓ).card ≤ (3 * R_max).choose 2) ∧
      (∀ ℓ, ∀ p ∈ pairs ℓ, p.card = 2) ∧
      ∀ (F S : Finset (ℕ × ℕ)), S ⊆ Ψ F ∪ predLocs C (Ψ F) →
        ∃ g : ℕ × ℕ → Finset (ℕ × ℕ),
          (∀ ℓ ∈ S, g ℓ ∈ pairs ℓ ∧ g ℓ ⊆ F) ∧
          ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → Disjoint (g ℓ₁) (g ℓ₂) := by
  let candSet : ℕ × ℕ → Finset (ℕ × ℕ) :=
    fun ℓ₀ => exRec ℓ₀ ∪ (succLocs C ℓ₀).biUnion exRec
  let pairs : ℕ × ℕ → Finset (Finset (ℕ × ℕ)) :=
    fun ℓ₀ => (candSet ℓ₀).powersetCard 2
  refine ⟨pairs, ?_, ?_, ?_⟩
  · intro ℓ₀
    have hbi : ((succLocs C ℓ₀).biUnion exRec).card ≤ 2 * R_max := by
      calc ((succLocs C ℓ₀).biUnion exRec).card
        _ ≤ ∑ ℓ ∈ succLocs C ℓ₀, (exRec ℓ).card := Finset.card_biUnion_le
        _ ≤ ∑ _ℓ ∈ succLocs C ℓ₀, R_max := Finset.sum_le_sum (fun ℓ _ => h_card ℓ)
        _ = (succLocs C ℓ₀).card * R_max := by simp [Finset.sum_const]
        _ ≤ 2 * R_max := Nat.mul_le_mul_right R_max (card_succLocs_le_two C ℓ₀)
    have hun : (candSet ℓ₀).card ≤ 3 * R_max := by
      calc (candSet ℓ₀).card
        _ ≤ (exRec ℓ₀).card + ((succLocs C ℓ₀).biUnion exRec).card := Finset.card_union_le _ _
        _ ≤ R_max + 2 * R_max := Nat.add_le_add (h_card ℓ₀) hbi
        _ = 3 * R_max := by omega
    rw [Finset.card_powersetCard]
    exact Nat.choose_le_choose 2 hun
  · intro ℓ₀ p hp
    exact (Finset.mem_powersetCard.mp hp).2
  · intro F S hS
    have hw_ex : ∀ s ∈ S, ∃ w ∈ Ψ F, s = w ∨ s ∈ predLocs C {w} := by
      intro s hs
      rcases Finset.mem_union.mp (hS hs) with hsΨ | hspred
      · exact ⟨s, hsΨ, Or.inl rfl⟩
      · rw [predLocs, Finset.mem_biUnion] at hspred
        obtain ⟨w, hwΨ, hsw⟩ := hspred
        refine ⟨w, hwΨ, Or.inr ?_⟩
        rw [predLocs, Finset.singleton_biUnion]
        exact hsw
    let w : ℕ × ℕ → ℕ × ℕ := fun s =>
      if hs : s ∈ S then Classical.choose (hw_ex s hs) else (0, 0)
    have hw_mem : ∀ s ∈ S, w s ∈ Ψ F := by
      intro s hs
      simp only [w, hs, ↓reduceDIte]
      exact (Classical.choose_spec (hw_ex s hs)).1
    have hw_rel : ∀ s ∈ S, s = w s ∨ s ∈ predLocs C {w s} := by
      intro s hs
      simp only [w, hs, ↓reduceDIte]
      exact (Classical.choose_spec (hw_ex s hs)).2
    have hw_cand : ∀ s ∈ S, exRec (w s) ⊆ candSet s := by
      intro s hs x hx
      rcases hw_rel s hs with heq | hpred
      · rw [← heq] at hx
        exact Finset.mem_union_left _ hx
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w s, ?_, hx⟩)
        exact mem_succLocs_of_mem_predLocs_singleton C hpred
    have h_ind : ∀ T : Finset (ℕ × ℕ), T ⊆ S →
        ∃ g : ℕ × ℕ → Finset (ℕ × ℕ),
          (∀ s ∈ T, (g s).card = 2 ∧ g s ⊆ exRec (w s) ∩ F) ∧
          ∀ s₁ ∈ T, ∀ s₂ ∈ T, s₁ ≠ s₂ → Disjoint (g s₁) (g s₂) := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro _
        exact ⟨fun _ => ∅, ⟨by simp, by simp⟩⟩
      | @insert a T ha_not_mem ih =>
        intro haT
        have hTS : T ⊆ S := (Finset.subset_insert a T).trans haT
        have haS : a ∈ S := haT (Finset.mem_insert_self a T)
        obtain ⟨g, hg_prop, hg_disj⟩ := ih hTS
        let N_a : Finset (ℕ × ℕ) := T.filter fun s => (exRec (w a) ∩ g s).Nonempty
        let L_a : Finset (ℕ × ℕ) := insert (w a) (predLocs C {w a} ∪ succLocs C (w a))
        have hLa_card : L_a.card ≤ 5 := by
          calc L_a.card
            _ ≤ (predLocs C {w a} ∪ succLocs C (w a)).card + 1 := Finset.card_insert_le _ _
            _ ≤ (predLocs C {w a}).card + (succLocs C (w a)).card + 1 :=
                Nat.add_le_add_right (Finset.card_union_le _ _) 1
            _ ≤ 2 + 2 + 1 := by
                have h1 := card_predLocs_singleton_le_two C (w a)
                have h2 := card_succLocs_le_two C (w a)
                omega
            _ = 5 := by omega
        have hNa_sub : insert a N_a ⊆ L_a.biUnion (fun ℓ => insert ℓ (predLocs C {ℓ})) := by
          intro s hs
          have hsS : s ∈ S := by
            rcases Finset.mem_insert.mp hs with rfl | hsN
            · exact haS
            · exact hTS (Finset.mem_of_mem_filter s hsN)
          have hws_La : w s ∈ L_a := by
            rcases Finset.mem_insert.mp hs with rfl | hsN
            · exact Finset.mem_insert_self _ _
            · obtain ⟨_, hne⟩ := Finset.mem_filter.mp hsN
              have hgs_sub : g s ⊆ exRec (w s) :=
                ((hg_prop s (Finset.mem_of_mem_filter s hsN)).2).trans Finset.inter_subset_left
              have hne_ex : (exRec (w a) ∩ exRec (w s)).Nonempty := by
                obtain ⟨x, hx⟩ := hne
                exact ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hgs_sub (Finset.mem_inter.mp hx).2⟩⟩
              rcases h_overlap (w a) (w s) hne_ex with heq | hpred | hsucc
              · rw [← heq]
                exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
                  (mem_succLocs_of_mem_predLocs_singleton C hpred))
              · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hsucc)
          refine Finset.mem_biUnion.mpr ⟨w s, hws_La, ?_⟩
          rcases hw_rel s hsS with heq | hpred
          · exact Finset.mem_insert.mpr (Or.inl heq)
          · exact Finset.mem_insert_of_mem hpred
        have hNa_ins_card : (insert a N_a).card ≤ 15 := by
          calc (insert a N_a).card
            _ ≤ (L_a.biUnion (fun ℓ => insert ℓ (predLocs C {ℓ}))).card :=
                Finset.card_le_card hNa_sub
            _ ≤ ∑ ℓ ∈ L_a, (insert ℓ (predLocs C {ℓ})).card := Finset.card_biUnion_le
            _ ≤ ∑ _ℓ ∈ L_a, 3 := by
                refine Finset.sum_le_sum fun ℓ _ => ?_
                calc (insert ℓ (predLocs C {ℓ})).card
                  _ ≤ (predLocs C {ℓ}).card + 1 := Finset.card_insert_le _ _
                  _ ≤ 2 + 1 := Nat.add_le_add_right (card_predLocs_singleton_le_two C ℓ) 1
                  _ = 3 := rfl
            _ = L_a.card * 3 := by simp [Finset.sum_const]
            _ ≤ 5 * 3 := Nat.mul_le_mul_right 3 hLa_card
            _ = 15 := rfl
        have ha_not_Na : a ∉ N_a := fun h => ha_not_mem (Finset.mem_of_mem_filter a h)
        have hNa_card : N_a.card ≤ 14 := by
          rw [Finset.card_insert_of_notMem ha_not_Na] at hNa_ins_card
          omega
        have hbi_card : (N_a.biUnion g).card ≤ 28 := by
          calc (N_a.biUnion g).card
            _ ≤ ∑ s ∈ N_a, (g s).card := Finset.card_biUnion_le
            _ = ∑ _s ∈ N_a, 2 := by
                refine Finset.sum_congr rfl fun s hs => ?_
                exact (hg_prop s (Finset.mem_of_mem_filter s hs)).1
            _ = N_a.card * 2 := by simp [Finset.sum_const]
            _ ≤ 14 * 2 := Nat.mul_le_mul_right 2 hNa_card
            _ = 28 := rfl
        have hwa_bad : 30 ≤ (exRec (w a) ∩ F).card := h_bad F (w a) (hw_mem a haS)
        have hsdiff_card : 2 ≤ ((exRec (w a) ∩ F) \ N_a.biUnion g).card := by
          have hle := Finset.card_le_card_sdiff_add_card (s := exRec (w a) ∩ F) (t := N_a.biUnion g)
          omega
        obtain ⟨p_a, hp_a_sub, hp_a_card⟩ := Finset.exists_subset_card_eq hsdiff_card
        let g' : ℕ × ℕ → Finset (ℕ × ℕ) := fun s => if s = a then p_a else g s
        have hp_a_disj : ∀ s ∈ T, Disjoint p_a (g s) := by
          intro s hsT
          rw [Finset.disjoint_left]
          intro x hx_pa hx_gs
          have hx_sdiff := hp_a_sub hx_pa
          rw [Finset.mem_sdiff] at hx_sdiff
          by_cases hsN : s ∈ N_a
          · exact hx_sdiff.2 (Finset.mem_biUnion.mpr ⟨s, hsN, hx_gs⟩)
          · have hnot : ¬ (exRec (w a) ∩ g s).Nonempty := by
              intro hne
              exact hsN (Finset.mem_filter.mpr ⟨hsT, hne⟩)
            exact hnot ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx_sdiff.1).1, hx_gs⟩⟩
        refine ⟨g', ⟨?_, ?_⟩⟩
        · intro s hs
          rcases Finset.mem_insert.mp hs with rfl | hsT
          · simp only [g', ↓reduceIte]
            exact ⟨hp_a_card, hp_a_sub.trans Finset.sdiff_subset⟩
          · have hne : s ≠ a := fun h => ha_not_mem (h ▸ hsT)
            simp only [g', hne, ↓reduceIte]
            exact hg_prop s hsT
        · intro s₁ hs₁ s₂ hs₂ hne
          rcases Finset.mem_insert.mp hs₁ with rfl | hs₁T
          · rcases Finset.mem_insert.mp hs₂ with rfl | hs₂T
            · exact False.elim (hne rfl)
            · simp only [g', ↓reduceIte, hne.symm]
              exact hp_a_disj s₂ hs₂T
          · have hne₁ : s₁ ≠ a := fun h => ha_not_mem (h ▸ hs₁T)
            rcases Finset.mem_insert.mp hs₂ with rfl | hs₂T
            · simp only [g', hne₁, ↓reduceIte]
              exact (hp_a_disj s₁ hs₁T).symm
            · have hne₂ : s₂ ≠ a := fun h => ha_not_mem (h ▸ hs₂T)
              simp only [g', hne₁, hne₂, ↓reduceIte]
              exact hg_disj s₁ hs₁T s₂ hs₂T hne
    obtain ⟨g, hg_prop, hg_disj⟩ := h_ind S Finset.Subset.rfl
    refine ⟨g, ⟨?_, hg_disj⟩⟩
    intro s hs
    obtain ⟨hcard, hsub⟩ := hg_prop s hs
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, hcard⟩, hsub.trans Finset.inter_subset_right⟩
    exact (hsub.trans Finset.inter_subset_left).trans (hw_cand s hs)
