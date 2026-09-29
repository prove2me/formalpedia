-- Prove2me | solution 1 for OPG500Counterexample.core_link_rank_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-07T16:12:15.838418+00:00
-- url     : https://prove2.me/submissions/46b944c5-57a9-47d7-aa06-558a77981d2f

import Mathlib
import Definitions.Def_opg500_weighted_cycle_models


open Finset SimpleGraph

namespace RankGap

/-! ### Lower bounds for the number of connected components -/

lemma eq_of_walk {W : Type*} {H : SimpleGraph W} {β : Type*} (φ : W → β)
    (hφ : ∀ x y, H.Adj x y → φ x = φ y) :
    ∀ {v w : W} (_ : H.Walk v w), φ v = φ w := by
  intro v w p
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hφ _ _ hadj).trans ih

lemma eq_of_reachable {W : Type*} {H : SimpleGraph W} {β : Type*} (φ : W → β)
    (hφ : ∀ x y, H.Adj x y → φ x = φ y) {v w : W} (h : H.Reachable v w) : φ v = φ w := by
  obtain ⟨p⟩ := h
  exact eq_of_walk φ hφ p

lemma card_le_cc {W : Type*} [Finite W] [DecidableEq W] (H : SimpleGraph W)
    (t : Finset W) (ht : ∀ x ∈ t, ∀ y ∈ t, H.Reachable x y → x = y) :
    t.card ≤ Nat.card H.ConnectedComponent := by
  classical
  have hinj : Function.Injective
      (fun x : (t : Set W) => H.connectedComponentMk (x : W)) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    exact Subtype.ext (ht x hx y hy (SimpleGraph.ConnectedComponent.exact h))
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

/-! ### Edge bookkeeping -/

variable {F : SimpleGraph (Fin 4)} [DecidableRel F.Adj] {N : Fin 4 → Finset (Fin 4)}

def Eavoid (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj] (i : Fin 4) :
    Finset (Sym2 (Fin 4)) := F.edgeFinset ∩ (univ.erase i).sym2

def Ein (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj] (N : Fin 4 → Finset (Fin 4))
    (i : Fin 4) : Finset (Sym2 (Fin 4)) := F.edgeFinset ∩ (N i).sym2

def Xset (N : Fin 4 → Finset (Fin 4)) (i : Fin 4) : Finset (Fin 4) := univ.erase i \ N i

def Ecross (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj] (N : Fin 4 → Finset (Fin 4))
    (i : Fin 4) : Finset (Sym2 (Fin 4)) :=
  (Eavoid F i \ Ein F N i) \ (Xset N i).sym2

lemma mem_Eavoid {i : Fin 4} {s : Sym2 (Fin 4)} :
    s ∈ Eavoid F i ↔ s ∈ F.edgeFinset ∧ i ∉ s := by
  simp only [Eavoid, Finset.mem_inter, Finset.mem_sym2_iff, Finset.mem_erase, Finset.mem_univ,
    and_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hi => (h2 i hi) rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun y hy => by rintro rfl; exact h2 hy⟩

lemma mem_Ein {i : Fin 4} {s : Sym2 (Fin 4)} :
    s ∈ Ein F N i ↔ s ∈ F.edgeFinset ∧ ∀ x ∈ s, x ∈ N i := by
  simp [Ein, Finset.mem_sym2_iff]

lemma card_avoiders {s : Sym2 (Fin 4)} (hs : s ∈ F.edgeFinset) :
    (univ.filter (fun i => i ∉ s)).card = 2 := by
  classical
  rw [SimpleGraph.mem_edgeFinset] at hs
  induction s with
  | _ u v =>
    have huv : u ≠ v := F.ne_of_adj hs
    have hrw : (univ.filter (fun i => i ∉ (s(u, v) : Sym2 (Fin 4))))
        = univ \ ({u, v} : Finset (Fin 4)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff, not_or]
    rw [hrw, Finset.card_sdiff, Finset.inter_univ, Finset.card_pair huv]
    simp

lemma sum_Eavoid_le : ∑ i : Fin 4, (Eavoid F i).card ≤ 2 * F.edgeFinset.card := by
  classical
  have h1 : ∀ i : Fin 4, (Eavoid F i).card
      = ∑ s ∈ F.edgeFinset, (if i ∉ s then 1 else 0) := by
    intro i
    rw [Finset.sum_boole]
    congr 1
    ext s
    simp [mem_Eavoid]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ s ∈ F.edgeFinset, (∑ _i : Fin 4, (if _i ∉ s then 1 else 0)) = 2 := by
    intro s hs
    rw [Finset.sum_boole]
    exact_mod_cast card_avoiders hs
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

lemma cross_add_in_le (i : Fin 4) (hav : i ∉ N i) :
    (Ein F N i).card + (Ecross F N i).card ≤ (Eavoid F i).card := by
  classical
  have hEin : Ein F N i ⊆ Eavoid F i := by
    intro s hs
    rw [mem_Ein] at hs
    rw [mem_Eavoid]
    exact ⟨hs.1, fun hi => hav (hs.2 i hi)⟩
  have hsub : Ein F N i ∪ Ecross F N i ⊆ Eavoid F i := by
    intro s hs
    rcases Finset.mem_union.mp hs with h | h
    · exact hEin h
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1
  have hdisj : Disjoint (Ein F N i) (Ecross F N i) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hs').1).2 hs
  calc (Ein F N i).card + (Ecross F N i).card = (Ein F N i ∪ Ecross F N i).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (Eavoid F i).card := Finset.card_le_card hsub

/-! ### Components versus internal edges -/

lemma one_le_Ein {i : Fin 4} {a b : Fin 4} (ha : a ∈ N i) (hb : b ∈ N i)
    (hab : F.Adj a b) : 1 ≤ (Ein F N i).card := by
  refine Finset.card_pos.mpr ⟨s(a, b), ?_⟩
  rw [mem_Ein]
  refine ⟨SimpleGraph.mem_edgeFinset.mpr hab, ?_⟩
  intro x hx
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact ha
  · exact hb

lemma two_le_Ein {i : Fin 4} {a b c d : Fin 4} (ha : a ∈ N i) (hb : b ∈ N i)
    (hc : c ∈ N i) (hd : d ∈ N i) (hab : F.Adj a b) (hcd : F.Adj c d)
    (hne : s(a, b) ≠ s(c, d)) : 2 ≤ (Ein F N i).card := by
  classical
  have hsub : ({s(a, b), s(c, d)} : Finset (Sym2 (Fin 4))) ⊆ Ein F N i := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [mem_Ein]
      exact ⟨SimpleGraph.mem_edgeFinset.mpr hab, by
        intro x hx; rcases Sym2.mem_iff.mp hx with rfl | rfl; exacts [ha, hb]⟩
    · rw [mem_Ein]
      exact ⟨SimpleGraph.mem_edgeFinset.mpr hcd, by
        intro x hx; rcases Sym2.mem_iff.mp hx with rfl | rfl; exacts [hc, hd]⟩
  calc (2 : ℕ) = ({s(a, b), s(c, d)} : Finset (Sym2 (Fin 4))).card :=
        (Finset.card_pair hne).symm
    _ ≤ (Ein F N i).card := Finset.card_le_card hsub

lemma card_le_cc_add_Ein (i : Fin 4) (hav : ∀ v ∈ N i, v ≠ i) :
    (N i).card
      ≤ Nat.card (F.induce {v | v ∈ N i}).ConnectedComponent + (Ein F N i).card := by
  classical
  set S : Finset (Fin 4) := N i with hSdef
  set H : SimpleGraph ↥({v | v ∈ S} : Set (Fin 4)) := F.induce {v | v ∈ S} with hHdef
  have hAdj : ∀ a b : ↥({v | v ∈ S} : Set (Fin 4)), H.Adj a b → F.Adj (a : Fin 4) (b : Fin 4) :=
    fun _ _ h => h
  have sep : ∀ {β : Type} [DecidableEq β] (ψ : Fin 4 → β),
      (∀ x y : Fin 4, x ∈ S → y ∈ S → F.Adj x y → ψ x = ψ y) →
      ∀ (t : Finset ↥({v | v ∈ S} : Set (Fin 4))),
      (∀ a ∈ t, ∀ b ∈ t, ψ (a : Fin 4) = ψ (b : Fin 4) → a = b) →
      t.card ≤ Nat.card H.ConnectedComponent := by
    intro β _ ψ hψ t ht
    refine card_le_cc H t ?_
    intro a ha b hb hr
    exact ht a ha b hb
      (eq_of_reachable (fun x : ↥({v | v ∈ S} : Set (Fin 4)) => ψ (x : Fin 4))
        (fun x y hxy => hψ _ _ x.2 y.2 (hAdj x y hxy)) hr)
  have hpos : S.Nonempty → 1 ≤ Nat.card H.ConnectedComponent := by
    rintro ⟨u, hu⟩
    haveI : Nonempty ↥({v | v ∈ S} : Set (Fin 4)) := ⟨⟨u, hu⟩⟩
    exact Nat.card_pos
  have hle3 : S.card ≤ 3 := by
    have hsub : S ⊆ univ.erase i := fun v hv => Finset.mem_erase.mpr ⟨hav v hv, Finset.mem_univ v⟩
    calc S.card ≤ (univ.erase i).card := Finset.card_le_card hsub
      _ = 3 := by rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hcases with hc | hc | hc | hc
  · simp [hc]
  · have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have := hpos hne
    omega
  · obtain ⟨u, v, huv, hSuv⟩ := Finset.card_eq_two.mp hc
    have hu : u ∈ S := by rw [hSuv]; simp
    have hv : v ∈ S := by rw [hSuv]; simp
    have hmem : ∀ x, x ∈ S → x = u ∨ x = v := by
      intro x hx; rw [hSuv] at hx; simpa using hx
    by_cases hadj : F.Adj u v
    · have h1 := one_le_Ein hu hv hadj
      have h2 := hpos ⟨u, hu⟩
      omega
    · have hcc : 2 ≤ Nat.card H.ConnectedComponent := by
        have := sep (β := Bool) (fun x => decide (x = u)) ?_
          ({⟨u, hu⟩, ⟨v, hv⟩} : Finset ↥({v | v ∈ S} : Set (Fin 4))) ?_
        · rwa [Finset.card_pair (by simp [Subtype.ext_iff, huv])] at this
        · intro x y hx hy hxy
          exfalso
          rcases hmem x hx with rfl | rfl <;> rcases hmem y hy with rfl | rfl
          · exact F.irrefl hxy
          · exact hadj hxy
          · exact hadj hxy.symm
          · exact F.irrefl hxy
        · intro a ha b hb hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
            first
              | rfl
              | (exfalso; simp only [decide_eq_decide] at hab; simp [huv, Ne.symm huv] at hab)
      omega
  · obtain ⟨u, v, w, huv, huw, hvw, hSuvw⟩ := Finset.card_eq_three.mp hc
    have hu : u ∈ S := by rw [hSuvw]; simp
    have hv : v ∈ S := by rw [hSuvw]; simp
    have hw : w ∈ S := by rw [hSuvw]; simp
    have hmem : ∀ x, x ∈ S → x = u ∨ x = v ∨ x = w := by
      intro x hx; rw [hSuvw] at hx; simpa using hx
    by_cases h1 : F.Adj u v <;> by_cases h2 : F.Adj u w <;> by_cases h3 : F.Adj v w
    · have := two_le_Ein hu hv hu hw h1 h2 (by simp [Sym2.eq_iff]; tauto)
      have := hpos ⟨u, hu⟩
      omega
    · have := two_le_Ein hu hv hu hw h1 h2 (by simp [Sym2.eq_iff]; tauto)
      have := hpos ⟨u, hu⟩
      omega
    · have := two_le_Ein hu hv hv hw h1 h3 (by simp [Sym2.eq_iff]; tauto)
      have := hpos ⟨u, hu⟩
      omega
    · -- only u~v
      have hE := one_le_Ein hu hv h1
      have hcc : 2 ≤ Nat.card H.ConnectedComponent := by
        have := sep (β := Bool) (fun x => decide (x = w)) ?_
          ({⟨u, hu⟩, ⟨w, hw⟩} : Finset ↥({v | v ∈ S} : Set (Fin 4))) ?_
        · rwa [Finset.card_pair (by simp [Subtype.ext_iff, huw])] at this
        · intro x y hx hy hxy
          rcases hmem x hx with rfl | rfl | rfl <;> rcases hmem y hy with rfl | rfl | rfl <;>
            first
              | rfl
              | (exfalso; first
                  | exact F.irrefl hxy | exact h2 hxy | exact h3 hxy
                  | exact h2 hxy.symm | exact h3 hxy.symm)
              | simp [huv, huw, hvw, Ne.symm huv, Ne.symm huw, Ne.symm hvw]
        · intro a ha b hb hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
            first
              | rfl
              | (exfalso; simp only [decide_eq_decide] at hab;
                 simp [huv, huw, hvw, Ne.symm huv, Ne.symm huw, Ne.symm hvw] at hab)
      omega
    · have := two_le_Ein hu hw hv hw h2 h3 (by simp [Sym2.eq_iff]; tauto)
      have := hpos ⟨u, hu⟩
      omega
    · -- only u~w
      have hE := one_le_Ein hu hw h2
      have hcc : 2 ≤ Nat.card H.ConnectedComponent := by
        have := sep (β := Bool) (fun x => decide (x = v)) ?_
          ({⟨u, hu⟩, ⟨v, hv⟩} : Finset ↥({v | v ∈ S} : Set (Fin 4))) ?_
        · rwa [Finset.card_pair (by simp [Subtype.ext_iff, huv])] at this
        · intro x y hx hy hxy
          rcases hmem x hx with rfl | rfl | rfl <;> rcases hmem y hy with rfl | rfl | rfl <;>
            first
              | rfl
              | (exfalso; first
                  | exact F.irrefl hxy | exact h1 hxy | exact h3 hxy
                  | exact h1 hxy.symm | exact h3 hxy.symm)
              | simp [huv, huw, hvw, Ne.symm huv, Ne.symm huw, Ne.symm hvw]
        · intro a ha b hb hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
            first
              | rfl
              | (exfalso; simp only [decide_eq_decide] at hab;
                 simp [huv, huw, hvw, Ne.symm huv, Ne.symm huw, Ne.symm hvw] at hab)
      omega
    · -- only v~w
      have hE := one_le_Ein hv hw h3
      have hcc : 2 ≤ Nat.card H.ConnectedComponent := by
        have := sep (β := Bool) (fun x => decide (x = u)) ?_
          ({⟨u, hu⟩, ⟨v, hv⟩} : Finset ↥({v | v ∈ S} : Set (Fin 4))) ?_
        · rwa [Finset.card_pair (by simp [Subtype.ext_iff, huv])] at this
        · intro x y hx hy hxy
          rcases hmem x hx with rfl | rfl | rfl <;> rcases hmem y hy with rfl | rfl | rfl <;>
            first
              | rfl
              | (exfalso; first
                  | exact F.irrefl hxy | exact h1 hxy | exact h2 hxy
                  | exact h1 hxy.symm | exact h2 hxy.symm)
              | simp [huv, huw, hvw, Ne.symm huv, Ne.symm huw, Ne.symm hvw]
        · intro a ha b hb hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
            first
              | rfl
              | (exfalso; simp only [decide_eq_decide] at hab;
                 simp [huv, huw, hvw, Ne.symm huv, Ne.symm huw, Ne.symm hvw] at hab)
      omega
    · -- no edges
      have hcc : 3 ≤ Nat.card H.ConnectedComponent := by
        have := sep (β := Fin 4) (fun x => x) ?_
          ({⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩} : Finset ↥({v | v ∈ S} : Set (Fin 4))) ?_
        · rwa [show ({⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩} :
              Finset ↥({v | v ∈ S} : Set (Fin 4))).card = 3 by
            rw [Finset.card_insert_of_notMem (by simp [Subtype.ext_iff, huv, huw]),
              Finset.card_pair (by simp [Subtype.ext_iff, hvw])]] at this
        · intro x y hx hy hxy
          exfalso
          rcases hmem x hx with rfl | rfl | rfl <;> rcases hmem y hy with rfl | rfl | rfl <;>
            first
              | exact F.irrefl hxy | exact h1 hxy | exact h2 hxy | exact h3 hxy
              | exact h1 hxy.symm | exact h2 hxy.symm | exact h3 hxy.symm
        · intro a ha b hb hab
          exact Subtype.ext hab
      omega

/-! ### The domination bound and the final count -/

lemma card_N_add_cross (i : Fin 4) (hav : ∀ v ∈ N i, v ≠ i)
    (hdom : ∀ j, j ≠ i → j ∉ N i → ∃ k, k ∈ N i ∧ F.Adj j k) :
    3 ≤ (N i).card + (Ecross F N i).card := by
  classical
  have hsubN : N i ⊆ univ.erase i :=
    fun v hv => Finset.mem_erase.mpr ⟨hav v hv, Finset.mem_univ v⟩
  have hcard3 : (N i).card ≤ 3 := by
    calc (N i).card ≤ (univ.erase i).card := Finset.card_le_card hsubN
      _ = 3 := by rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
  have hX : (N i).card + (Xset N i).card = 3 := by
    rw [Xset, Finset.card_sdiff, Finset.inter_eq_left.mpr hsubN,
      Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hex : ∀ j ∈ Xset N i, ∃ k, k ∈ N i ∧ F.Adj j k := by
    intro j hj
    rw [Xset, Finset.mem_sdiff, Finset.mem_erase] at hj
    exact hdom j hj.1.1 hj.2
  choose! g hg1 hg2 using hex
  have hle : (Xset N i).card ≤ (Ecross F N i).card := by
    refine Finset.card_le_card_of_injOn (fun j => s(j, g j)) ?_ ?_
    · intro j hj
      have hjX := hj
      simp only [Finset.mem_coe, Xset, Finset.mem_sdiff, Finset.mem_erase] at hjX
      have hgj : g j ∈ N i := hg1 j hj
      have hadj : F.Adj j (g j) := hg2 j hj
      simp only [Finset.mem_coe, Ecross, Finset.mem_sdiff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [mem_Eavoid]
        refine ⟨SimpleGraph.mem_edgeFinset.mpr hadj, ?_⟩
        intro hi
        rcases Sym2.mem_iff.mp hi with h | h
        · exact hjX.1.1 h.symm
        · exact hav (g j) hgj h.symm
      · rw [mem_Ein]
        rintro ⟨-, hall⟩
        exact hjX.2 (hall j (Sym2.mem_mk_left j (g j)))
      · rw [Finset.mem_sym2_iff]
        intro hall
        have := hall (g j) (Sym2.mem_mk_right j (g j))
        rw [Xset, Finset.mem_sdiff] at this
        exact this.2 hgj
    · intro a ha b hb hab
      have haX := ha
      have hbX := hb
      simp only [Finset.mem_coe] at ha hb
      simp only [Finset.mem_coe, Xset, Finset.mem_sdiff] at haX hbX
      rcases Sym2.eq_iff.mp hab with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · exact absurd (h1 ▸ hg1 b hb) haX.2
  omega

theorem main (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj] (N : Fin 4 → Finset (Fin 4))
    (havoids : ∀ i v, v ∈ N i → v ≠ i)
    (hdominates : ∀ i j, j ≠ i → j ∉ N i → ∃ k, k ∈ N i ∧ F.Adj j k) :
    7 < F.edgeFinset.card + ∑ i, Nat.card (F.induce {v | v ∈ N i}).ConnectedComponent := by
  classical
  set c : Fin 4 → ℕ := fun i => Nat.card (F.induce {v | v ∈ N i}).ConnectedComponent with hcdef
  show 7 < F.edgeFinset.card + ∑ i, c i
  have h1 : ∀ i, 1 ≤ c i := by
    intro i
    have hne : (N i).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      obtain ⟨j, hj⟩ : ∃ j : Fin 4, j ≠ i := by
        refine ⟨if i = 0 then 1 else 0, ?_⟩
        fin_cases i <;> decide
      obtain ⟨k, hk, -⟩ := hdominates i j hj (by rw [hemp]; simp)
      rw [hemp] at hk
      simp at hk
    obtain ⟨u, hu⟩ := hne
    haveI : Nonempty ↥({v | v ∈ N i} : Set (Fin 4)) := ⟨⟨u, hu⟩⟩
    exact Nat.card_pos
  have h2 : ∀ i, (N i).card ≤ c i + (Ein F N i).card :=
    fun i => card_le_cc_add_Ein i (fun v hv => havoids i v hv)
  have h3 : ∀ i, 3 ≤ (N i).card + (Ecross F N i).card :=
    fun i => card_N_add_cross i (fun v hv => havoids i v hv)
      (fun j hj hj' => hdominates i j hj hj')
  have h4 : ∀ i, (Ein F N i).card + (Ecross F N i).card ≤ (Eavoid F i).card :=
    fun i => cross_add_in_le i (fun hmem => havoids i i hmem rfl)
  have h5 : ∑ i : Fin 4, (Eavoid F i).card ≤ 2 * F.edgeFinset.card := sum_Eavoid_le
  have hsum : 12 ≤ (∑ i, c i) + 2 * F.edgeFinset.card := by
    have step : (12 : ℕ) ≤ ∑ i : Fin 4, (c i + (Eavoid F i).card) := by
      calc (12 : ℕ) = ∑ _i : Fin 4, 3 := by simp
        _ ≤ ∑ i : Fin 4, (c i + (Eavoid F i).card) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have a2 := h2 i
            have a3 := h3 i
            have a4 := h4 i
            omega
    rw [Finset.sum_add_distrib] at step
    omega
  have h6 : 4 ≤ ∑ i, c i := by
    calc (4 : ℕ) = ∑ _i : Fin 4, 1 := by simp
      _ ≤ ∑ i, c i := Finset.sum_le_sum (fun i _ => h1 i)
  omega

end RankGap

open Finset SimpleGraph in
/-- **The four-core link obstruction has a strictly positive rank gap.** -/
theorem solution
    (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj]
    (N : Fin 4 → Finset (Fin 4))
    (htriangleFree : ∀ ⦃a b c : Fin 4⦄,
      a ≠ b → b ≠ c → a ≠ c →
        ¬ (F.Adj a b ∧ F.Adj b c ∧ F.Adj c a))
    (havoids : ∀ i v, v ∈ N i → v ≠ i)
    (hdominates : ∀ i j, j ≠ i → j ∉ N i →
      ∃ k, k ∈ N i ∧ F.Adj j k) :
    7 < F.edgeFinset.card +
      ∑ i, Nat.card (F.induce {v | v ∈ N i}).ConnectedComponent :=
  RankGap.main F N havoids hdominates
