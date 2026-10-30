-- Prove2me | solution 1 for RendezvousKn.Sym.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:38:44.338635+00:00
-- url     : https://prove2.me/submissions/0c598c26-960d-499d-a6e6-502f9b322c38

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model
import Theorems.Thm_RendezvousKn_Sym_lemma_8
import Theorems.Thm_RendezvousKn_Sym_lemma_9

open RendezvousKn.Sym Finset

lemma deg_le_image_snd {n : ℕ} (τA τB : Tactic n) (a : Fin n) :
    ((pairSet τA τB).filter fun e => e.1 = a).card ≤ (univ.image τB).card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro e he
    simp only [coe_filter, Set.mem_setOf_eq, pairSet, mem_image, mem_univ, true_and] at he
    obtain ⟨⟨i, rfl⟩, _⟩ := he
    simp
  · intro e he f hf hef
    simp only [coe_filter, Set.mem_setOf_eq] at he hf
    exact Prod.ext (he.2.trans hf.2.symm) hef

lemma deg_le_image_fst {n : ℕ} (τA τB : Tactic n) (b : Fin n) :
    ((pairSet τA τB).filter fun e => e.2 = b).card ≤ (univ.image τA).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro e he
    simp only [coe_filter, Set.mem_setOf_eq, pairSet, mem_image, mem_univ, true_and] at he
    obtain ⟨⟨i, rfl⟩, _⟩ := he
    simp
  · intro e he f hf hef
    simp only [coe_filter, Set.mem_setOf_eq] at he hf
    exact Prod.ext hef (he.2.trans hf.2.symm)

lemma deg_active_fst {n : ℕ} (τA τB : Tactic n) (a : Fin n) :
    ((pairSet τA τB).filter fun e => e.1 = a).card + (univ.image τA).card ≤ n + 1 := by
  have h1 := Finset.card_filter_add_card_filter_not (s := pairSet τA τB) (fun e => e.1 = a)
  have h2 : (pairSet τA τB).card ≤ n := by
    unfold pairSet
    calc _ ≤ (univ : Finset (Fin n)).card := card_image_le
      _ = n := by simp
  have h3 : ((univ.image τA).erase a).card ≤
      ((pairSet τA τB).filter fun e => ¬ e.1 = a).card := by
    apply Finset.card_le_card_of_surjOn Prod.fst
    intro x hx
    simp only [coe_erase, coe_image, coe_univ, Set.image_univ, Set.mem_diff, Set.mem_range,
      Set.mem_singleton_iff] at hx
    obtain ⟨⟨i, rfl⟩, hne⟩ := hx
    refine ⟨(τA i, τB i), ?_, rfl⟩
    simp only [coe_filter, Set.mem_setOf_eq, pairSet, mem_image, mem_univ, true_and]
    exact ⟨⟨i, rfl⟩, hne⟩
  have h4 := Finset.pred_card_le_card_erase (s := univ.image τA) (a := a)
  omega

lemma deg_active_snd {n : ℕ} (τA τB : Tactic n) (b : Fin n) :
    ((pairSet τA τB).filter fun e => e.2 = b).card + (univ.image τB).card ≤ n + 1 := by
  have h1 := Finset.card_filter_add_card_filter_not (s := pairSet τA τB) (fun e => e.2 = b)
  have h2 : (pairSet τA τB).card ≤ n := by
    unfold pairSet
    calc _ ≤ (univ : Finset (Fin n)).card := card_image_le
      _ = n := by simp
  have h3 : ((univ.image τB).erase b).card ≤
      ((pairSet τA τB).filter fun e => ¬ e.2 = b).card := by
    apply Finset.card_le_card_of_surjOn Prod.snd
    intro x hx
    simp only [coe_erase, coe_image, coe_univ, Set.image_univ, Set.mem_diff, Set.mem_range,
      Set.mem_singleton_iff] at hx
    obtain ⟨⟨i, rfl⟩, hne⟩ := hx
    refine ⟨(τA i, τB i), ?_, rfl⟩
    simp only [coe_filter, Set.mem_setOf_eq, pairSet, mem_image, mem_univ, true_and]
    exact ⟨⟨i, rfl⟩, hne⟩
  have h4 := Finset.pred_card_le_card_erase (s := univ.image τB) (a := b)
  omega

lemma dpc_ge {n : ℕ} (F E₁ E₂ : Finset (Fin n × Fin n)) (h1 : E₁ ⊆ F) (h2 : E₂ ⊆ F)
    (hd : Disjoint E₁ E₂) (hdisj : ∀ e ∈ E₁, ∀ f ∈ E₂, e.1 ≠ f.1 ∧ e.2 ≠ f.2) :
    E₁.card * E₂.card ≤ disjointPairCount F := by
  unfold disjointPairCount
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun p => ({p.1, p.2} : Finset (Fin n × Fin n)))
  · rintro ⟨e, f⟩ hp
    simp only [coe_product, Set.mem_prod, mem_coe] at hp
    have hne : e ≠ f := fun h => Finset.disjoint_left.1 hd hp.1 (h ▸ hp.2)
    simp only [coe_filter, Set.mem_setOf_eq, mem_powersetCard]
    refine ⟨⟨?_, card_pair hne⟩, ?_⟩
    · intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1 hp.1
      · exact h2 hp.2
    · intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      have hD := hdisj e hp.1 f hp.2
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hD
      · exact ⟨Ne.symm hD.1, Ne.symm hD.2⟩
      · exact absurd rfl hxy
  · rintro ⟨e, f⟩ hp ⟨e', f'⟩ hp' heq
    simp only [coe_product, Set.mem_prod, mem_coe] at hp hp'
    simp only at heq
    have he : e ∈ ({e', f'} : Finset _) := heq ▸ (by simp)
    have hf : f ∈ ({e', f'} : Finset _) := heq ▸ (by simp)
    simp only [mem_insert, mem_singleton] at he hf
    have he' : e = e' := by
      rcases he with h | h
      · exact h
      · exact absurd (h ▸ hp'.2) (Finset.disjoint_left.1 hd hp.1)
    have hf' : f = f' := by
      rcases hf with h | h
      · exact absurd (h ▸ hp'.1) (Finset.disjoint_right.1 hd hp.2)
      · exact h
    rw [he', hf']

theorem solution (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n)
    (hkind : IsPassive τA ↔ IsPassive τB)
    (hF : (11 / 12 : ℝ) * n ≤ ((pairSet τA τB).card : ℝ)) :
    1 / 32 ≤ varX (pairSet τA τB) := by
  have hFn : (pairSet τA τB).card ≤ n := by
    unfold pairSet
    calc _ ≤ (univ : Finset (Fin n)).card := card_image_le
      _ = n := by simp
  have hdeg : (∀ a : Fin n, (((pairSet τA τB).filter fun e => e.1 = a).card : ℝ) ≤ 2 / 3 * n) ∧
      (∀ b : Fin n, (((pairSet τA τB).filter fun e => e.2 = b).card : ℝ) ≤ 2 / 3 * n) := by
    unfold IsPassive at hkind
    by_cases hp : 2 * (univ.image τA).card ≤ n
    · have hq := hkind.1 hp
      constructor
      · intro a
        have := deg_le_image_snd τA τB a
        have : 3 * ((pairSet τA τB).filter fun e => e.1 = a).card ≤ 2 * n := by omega
        have : (3:ℝ) * ((pairSet τA τB).filter fun e => e.1 = a).card ≤ 2 * n := by
          exact_mod_cast this
        linarith
      · intro b
        have := deg_le_image_fst τA τB b
        have : 3 * ((pairSet τA τB).filter fun e => e.2 = b).card ≤ 2 * n := by omega
        have : (3:ℝ) * ((pairSet τA τB).filter fun e => e.2 = b).card ≤ 2 * n := by
          exact_mod_cast this
        linarith
    · have hq : ¬ 2 * (univ.image τB).card ≤ n := fun h => hp (hkind.2 h)
      constructor
      · intro a
        have := deg_active_fst τA τB a
        have : 3 * ((pairSet τA τB).filter fun e => e.1 = a).card ≤ 2 * n := by omega
        have : (3:ℝ) * ((pairSet τA τB).filter fun e => e.1 = a).card ≤ 2 * n := by
          exact_mod_cast this
        linarith
      · intro b
        have := deg_active_snd τA τB b
        have : 3 * ((pairSet τA τB).filter fun e => e.2 = b).card ≤ 2 * n := by omega
        have : (3:ℝ) * ((pairSet τA τB).filter fun e => e.2 = b).card ≤ 2 * n := by
          exact_mod_cast this
        linarith
  obtain ⟨E₁, E₂, h1, h2, hd, hc1, hc2, hdisj⟩ :=
    lemma_9 (A := Fin n) (B := Fin n) n (by simp) (by simp) (pairSet τA τB) hF hFn hdeg.1 hdeg.2
  have hD := dpc_ge (pairSet τA τB) E₁ E₂ h1 h2 hd hdisj
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hprod : (n : ℝ) / 8 * ((n : ℝ) / 8) ≤ (E₁.card : ℝ) * E₂.card :=
    mul_le_mul hc1 hc2 (by positivity) (by positivity)
  have hDR : (E₁.card : ℝ) * E₂.card ≤ disjointPairCount (pairSet τA τB) := by
    exact_mod_cast hD
  apply lemma_8 n hn τA τB (1 / 32) (by norm_num)
  rw [Nat.cast_choose_two]
  nlinarith
