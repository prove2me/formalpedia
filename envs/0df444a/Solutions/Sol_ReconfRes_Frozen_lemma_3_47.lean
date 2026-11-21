-- Prove2me | solution 1 for ReconfRes.Frozen.lemma_3_47
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:48:31.561768+00:00
-- url     : https://prove2.me/submissions/b08095a1-ca5a-4328-9689-5338b51804d9

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Theorems.Thm_ReconfRes_Frozen_lemma_3_8

section
open MultiplierAssoc206.Resolution
namespace ReconfRes.Frozen
namespace Dev.L347
variable {V : Type} [DecidableEq V]

theorem mem_consumers (R : ProofDag V) (i j : Fin R.n) : j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem lean_consumers (R : ProofDag V) (hl : R.IsLean) (i : Fin R.n) (hi : i ≠ R.sink) :
    1 ≤ (R.consumers i).card := by
  have := hl i
  unfold ProofDag.Anc at this
  rcases Relation.ReflTransGen.cases_head this with h | ⟨c, hc, _⟩
  · exact absurd h hi
  · apply Finset.card_pos.mpr
    exact ⟨c, by simp [ProofDag.consumers, hc]⟩

theorem readOnce_of (F : CNF V) (M : Multiset (Clause V)) (R : ProofDag V)
    (hR : R.IsRefutationOf F) (hlean : R.IsLean) (hM : R.axiomMultiset = M)
    (hs : R.size + 1 ≤ 2 * Multiset.card M) : R.IsReadOnce := by
  have h := lemma_3_8 F R hR hlean
  dsimp only at h
  obtain ⟨hX, hρ, hsz, hge⟩ := h
  have hα : ((Finset.univ.filter fun i => R.parents i = ∅).card : ℤ) = Multiset.card M := by
    rw [← hM]; simp [ProofDag.axiomMultiset]; rfl
  rw [hα] at hsz
  have hω0 : (0 : ℤ) ≤ ((Finset.univ.filter fun i => (R.parents i).card = 1).card : ℤ) := by positivity
  have hs' : (R.size : ℤ) + 1 ≤ 2 * Multiset.card M := by exact_mod_cast hs
  have hωz : ((Finset.univ.filter fun i => (R.parents i).card = 1).card : ℤ) = 0 := by omega
  have hXz : ∑ i ∈ Finset.univ.filter (fun i => i ≠ R.sink), (((R.consumers i).card : ℤ) - 1) = 0 := by
    omega
  refine ⟨hlean, ?_, ?_⟩
  · intro i hi
    have : i ∈ Finset.univ.filter fun i => (R.parents i).card = 1 := by simpa [ProofDag.IsWeakeningNode] using hi
    have h0 : (Finset.univ.filter fun i => (R.parents i).card = 1).card = 0 := by exact_mod_cast hωz
    rw [Finset.card_eq_zero] at h0
    rw [h0] at this; simp at this
  · intro i hi
    have hnn : ∀ j ∈ Finset.univ.filter (fun i => i ≠ R.sink), (0 : ℤ) ≤ (((R.consumers j).card : ℤ) - 1) := by
      intro j hj
      have := lean_consumers R hlean j (Finset.mem_filter.mp hj).2
      omega
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hXz i (by simpa using hi)
    omega

theorem ancIn_anc (R : ProofDag V) {Q : Finset (Fin R.n)} {a b : Fin R.n} (h : R.AncIn Q a b) :
    R.Anc a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail hs.2.2

theorem mem_inputs (R : ProofDag V) (Q : Finset (Fin R.n)) (i : Fin R.n) :
    i ∈ R.inputs Q ↔ i ∉ Q ∧ ∃ j ∈ Q, (i, j) ∈ R.edges := by
  simp [ProofDag.inputs]

theorem sum_swap (R : ProofDag V) (P : Fin R.n → Prop) [DecidablePred P] (T : Finset (Fin R.n)) :
    ∑ j ∈ T, ((R.parents j).filter P).card =
      ∑ p ∈ Finset.univ.filter P, ((R.consumers p).filter (· ∈ T)).card := by
  have h1 : ∀ j, ((R.parents j).filter P).card = ∑ p ∈ Finset.univ.filter P, if (p, j) ∈ R.edges then 1 else 0 := by
    intro j
    rw [← Finset.card_filter]
    congr 1; ext p; simp [ProofDag.parents, and_comm]
  have h2 : ∀ p, ((R.consumers p).filter (· ∈ T)).card = ∑ j ∈ T, if (p, j) ∈ R.edges then 1 else 0 := by
    intro p
    rw [← Finset.card_filter]
    congr 1; ext j; simp [ProofDag.consumers, and_comm]
  simp only [h1, h2]
  exact Finset.sum_comm

theorem sink_consumers (F : CNF V) (R : ProofDag V) (hR : R.IsRefutationOf F) :
    R.consumers R.sink = ∅ := hR.2.2.2.1

theorem count (F : CNF V) (R : ProofDag V) (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    (k : ℕ) (Q : Finset (Fin R.n)) (q : Fin R.n) (hb : R.IsBlock k Q q)
    (hres : ∀ i ∈ Q, R.IsResolutionNode i) :
    (R.inputs Q).card = Q.card + 1 ∧
      ∀ p ∈ R.inputs Q, ((R.consumers p).filter (· ∈ Q)).card = 1 := by
  obtain ⟨_, ⟨hqQ, hout⟩, hbq⟩ := hb
  have hone : ∀ p, p ≠ R.sink → (R.consumers p).card = 1 := hro.2.2
  have hnosink : ∀ p ∈ Q, p ≠ q → p ≠ R.sink := by
    intro p hp hpq hps
    subst hps
    have := hout R.sink hp
    unfold ProofDag.AncIn at this
    rcases Relation.ReflTransGen.cases_head this with h | ⟨c, hc, _⟩
    · exact hpq h
    · have : c ∈ R.consumers R.sink := (mem_consumers R _ _).2 hc.2.2
      rw [sink_consumers F R hR] at this; simp at this
  have hA : ∑ j ∈ Q, ((R.parents j).filter (· ∈ Q)).card = Q.card - 1 := by
    rw [sum_swap R (· ∈ Q) Q]
    have : Finset.univ.filter (· ∈ Q) = Q := by ext; simp
    rw [this]
    have hterm : ∀ p ∈ Q, ((R.consumers p).filter (· ∈ Q)).card = if p = q then 0 else 1 := by
      intro p hp
      by_cases hpq : p = q
      · subst hpq
        simp only [if_true]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro c hc hcQ
        have hcq : R.Anc c p := ancIn_anc R (hout c hcQ)
        exact hR.1 p c ((mem_consumers R _ _).1 hc) hcq
      · simp only [hpq, if_false]
        rw [Finset.filter_true_of_mem (fun c hc => hbq p hp hpq hc)]
        exact hone p (hnosink p hp hpq)
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite]
    simp only [Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, mul_one, zero_add]
    have : (Q.filter (fun p => ¬ p = q)) = Q.erase q := by ext; simp [and_comm]
    rw [this, Finset.card_erase_of_mem hqQ]
  have hterm2 : ∀ p, p ∉ Q →
        ((R.consumers p).filter (· ∈ Q)).card = if p ∈ R.inputs Q then 1 else 0 := by
      intro p hpQ
      by_cases hin : p ∈ R.inputs Q
      · simp only [hin, if_true]
        obtain ⟨_, j, hj, hje⟩ := (mem_inputs R Q p).1 hin
        have hps : p ≠ R.sink := by
          intro h; subst h
          have : j ∈ R.consumers R.sink := (mem_consumers R _ _).2 hje
          rw [sink_consumers F R hR] at this; simp at this
        have hle : ((R.consumers p).filter (· ∈ Q)).card ≤ 1 :=
          (Finset.card_filter_le _ _).trans (hone p hps).le
        have hge : 1 ≤ ((R.consumers p).filter (· ∈ Q)).card :=
          Finset.card_pos.mpr ⟨j, by simp [mem_consumers, hje, hj]⟩
        omega
      · simp only [hin, if_false]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro c hc hcQ
        exact hin ((mem_inputs R Q p).2 ⟨hpQ, c, hcQ, (mem_consumers R _ _).1 hc⟩)
  have hB : ∑ j ∈ Q, ((R.parents j).filter (· ∉ Q)).card = (R.inputs Q).card := by
    rw [sum_swap R (· ∉ Q) Q]
    have hterm : ∀ p ∈ Finset.univ.filter (· ∉ Q),
        ((R.consumers p).filter (· ∈ Q)).card = if p ∈ R.inputs Q then 1 else 0 :=
      fun p hp => hterm2 p (by simpa using hp)
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite]
    simp only [Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, mul_one, add_zero]
    congr 1
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨((mem_inputs R Q p).1 h).1, h⟩
  have hsum : ∑ j ∈ Q, (R.parents j).card = 2 * Q.card := by
    rw [Finset.sum_congr rfl (fun j hj => hres j hj)]; simp [mul_comm]
  have hsplit : ∑ j ∈ Q, (R.parents j).card =
      ∑ j ∈ Q, ((R.parents j).filter (· ∈ Q)).card + ∑ j ∈ Q, ((R.parents j).filter (· ∉ Q)).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => (Finset.card_filter_add_card_filter_not _).symm)
  have hQpos : 1 ≤ Q.card := Finset.card_pos.mpr ⟨q, hqQ⟩
  refine ⟨by omega, ?_⟩
  intro p hp
  have hpQ : p ∉ Q := ((mem_inputs R Q p).1 hp).1
  have := hterm2 p hpQ
  simpa [hp] using this

theorem parents_card_le (F : CNF V) (R : ProofDag V) (hR : R.IsRefutationOf F) (i : Fin R.n) :
    (R.parents i).card = 0 ∨ (R.parents i).card = 1 ∨ (R.parents i).card = 2 := by
  obtain ⟨_, _, h3, _, _⟩ := hR
  rcases h3 i with ⟨h, _⟩ | ⟨p₁, p₂, hne, h, _⟩ | ⟨p, h, _⟩
  · left; simp [h]
  · right; right; rw [h]; exact Finset.card_pair hne
  · right; left; rw [h]; simp

theorem fwd {k : ℕ} (F : CNF V) {R R' : ProofDag V} {Q : Finset (Fin R.n)} {Q' : Finset (Fin R'.n)}
    {φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}} (hRr : R.IsRefutationOf F) (hro' : R'.IsReadOnce)
    (hro : R.IsReadOnce) (hm : MoveVia k R R' Q Q' φ)
    (i : {i // i ∉ Q}) (hi : i.1 ∈ R.inputs Q) : (φ i).1 ∈ R'.inputs Q' := by
  obtain ⟨q, q', hb, hb', _, _, hed, _, _, hs1, hs2⟩ := hm
  obtain ⟨_, j, hj, hje⟩ := (mem_inputs R Q i.1).1 hi
  have his : i.1 ≠ R.sink := by
    intro h
    have : j ∈ R.consumers R.sink := (mem_consumers R _ _).2 (h ▸ hje)
    rw [sink_consumers F R hRr] at this; simp at this
  have hne : (φ i).1 ≠ R'.sink := by
    by_cases hs : R.sink ∈ Q
    · obtain ⟨_, e2⟩ := hs2 hs
      intro h
      have := hb'.2.1.1
      rw [← e2, ← h] at this
      exact (φ i).2 this
    · intro h
      have := Subtype.ext (hs1 hs ▸ h : (φ i).1 = (φ ⟨R.sink, hs⟩).1)
      exact his (congrArg Subtype.val (φ.injective this))
  have hc1 : (R'.consumers (φ i).1).card = 1 := hro'.2.2 _ hne
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < (R'.consumers (φ i).1).card)
  have hce := (mem_consumers R' _ _).1 hc
  rw [mem_inputs]
  refine ⟨(φ i).2, ?_⟩
  by_cases hcQ : c ∈ Q'
  · exact ⟨c, hcQ, hce⟩
  · exfalso
    obtain ⟨c0, hc0⟩ := φ.surjective ⟨c, hcQ⟩
    have hc0' : c = (φ c0).1 := by rw [hc0]
    rw [hc0'] at hce
    have := (hed i c0).1 hce
    have h1 : j ∈ R.consumers i.1 := (mem_consumers R _ _).2 hje
    have h2 : c0.1 ∈ R.consumers i.1 := (mem_consumers R _ _).2 this
    have := Finset.card_le_one.mp (hro.2.2 i.1 his).le
    have := (Finset.card_eq_one.mp (hro.2.2 i.1 his))
    obtain ⟨z, hz⟩ := this
    rw [hz] at h1 h2
    simp at h1 h2
    exact c0.2 (h2 ▸ h1 ▸ hj)

theorem part2 {k : ℕ} (F : CNF V) (M : Multiset (Clause V)) (R R' : ProofDag V)
    (Q : Finset (Fin R.n)) (Q' : Finset (Fin R'.n)) (φ : {i // i ∉ Q} ≃ {j // j ∉ Q'})
    (hRr : R.IsRefutationOf F) (hRl : R.IsLean) (hRM : R.axiomMultiset = M)
    (hRs : R.size + 1 ≤ 2 * Multiset.card M)
    (hRr' : R'.IsRefutationOf F) (hRl' : R'.IsLean) (hRM' : R'.axiomMultiset = M)
    (hRs' : R'.size + 1 ≤ 2 * Multiset.card M)
    (hmv : FrozenMoveVia k R R' Q Q' φ) :
    Q'.card = Q.card ∧
      (∀ i ∈ Q, R.IsResolutionNode i) ∧ (∀ j ∈ Q', R'.IsResolutionNode j) ∧
      (R.inputs Q).card = Q.card + 1 ∧
      (∀ i : {i // i ∉ Q}, i.1 ∈ R.inputs Q ↔ (φ i).1 ∈ R'.inputs Q') ∧
      (∀ i ∈ R.inputs Q, ((R.consumers i).filter (· ∈ Q)).card = 1) ∧
      (∀ j ∈ R'.inputs Q', ((R'.consumers j).filter (· ∈ Q')).card = 1) ∧
      FrozenMoveVia k R' R Q' Q φ.symm := by
  have hro := readOnce_of F M R hRr hRl hRM hRs
  have hro' := readOnce_of F M R' hRr' hRl' hRM' hRs'
  obtain ⟨hm, hQ, hQ'⟩ := hmv
  have hm0 := hm
  obtain ⟨q, q', hb, hb', hlab, hl, hed, hin, hcons, hs1, hs2⟩ := hm0
  have hresR : ∀ i ∈ Q, R.IsResolutionNode i := by
    intro i hi
    have h1 := hQ i hi
    have h2 := hro.2.1 i
    have := parents_card_le F R hRr i
    unfold ProofDag.IsAxiomNode at h1
    unfold ProofDag.IsWeakeningNode at h2
    have h0 : (R.parents i).card ≠ 0 := fun h => h1 (Finset.card_eq_zero.mp h)
    unfold ProofDag.IsResolutionNode; omega
  have hresR' : ∀ j ∈ Q', R'.IsResolutionNode j := by
    intro i hi
    have h1 := hQ' i hi
    have h2 := hro'.2.1 i
    have := parents_card_le F R' hRr' i
    unfold ProofDag.IsAxiomNode at h1
    unfold ProofDag.IsWeakeningNode at h2
    have h0 : (R'.parents i).card ≠ 0 := fun h => h1 (Finset.card_eq_zero.mp h)
    unfold ProofDag.IsResolutionNode; omega
  obtain ⟨hc1, hc2⟩ := count F R hRr hro k Q q hb hresR
  obtain ⟨hc1', hc2'⟩ := count F R' hRr' hro' k Q' q' hb' hresR'
  have he : ∀ i : {i // i ∉ Q}, i.1 ∈ R.inputs Q ↔ (φ i).1 ∈ R'.inputs Q' := by
    intro i
    constructor
    · exact fwd F hRr hro' hro hm i
    · intro h
      obtain ⟨_, j, hj, hje⟩ := (mem_inputs R' Q' _).1 h
      exact hin i j hj hje
  have hcard : (R.inputs Q).card = (R'.inputs Q').card := by
    refine Finset.card_bij (fun i hi => (φ ⟨i, ((mem_inputs R Q i).1 hi).1⟩).1) ?_ ?_ ?_
    · intro i hi
      exact (he ⟨i, ((mem_inputs R Q i).1 hi).1⟩).1 hi
    · intro a ha b hb hab
      have := φ.injective (Subtype.ext hab)
      simpa using this
    · intro b hb
      have hbQ := ((mem_inputs R' Q' b).1 hb).1
      refine ⟨(φ.symm ⟨b, hbQ⟩).1, ?_, ?_⟩
      · exact (he (φ.symm ⟨b, hbQ⟩)).2 (by simpa using hb)
      · simp
  refine ⟨by omega, hresR, hresR', hc1, he, hc2, hc2', ?_⟩
  refine ⟨⟨q', q, hb', hb, hlab.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩, hQ', hQ⟩
  · intro i
    simpa using (hl (φ.symm i)).symm
  · intro i j
    have := hed (φ.symm i) (φ.symm j)
    simpa using this.symm
  · intro i j hj hje
    have hi : (φ.symm i).1 ∈ R.inputs Q := (mem_inputs R Q _).2 ⟨(φ.symm i).2, j, hj, hje⟩
    have := fwd F hRr hro' hro hm (φ.symm i) hi
    simpa using this
  · intro c
    have := hcons (φ.symm c)
    simpa using this.symm
  · intro h
    by_cases hs : R.sink ∈ Q
    · exfalso
      obtain ⟨_, e2⟩ := hs2 hs
      exact h (e2 ▸ hb'.2.1.1)
    · have e := hs1 hs
      have : φ ⟨R.sink, hs⟩ = ⟨R'.sink, h⟩ := Subtype.ext e
      have h2 : φ.symm ⟨R'.sink, h⟩ = ⟨R.sink, hs⟩ := (Equiv.symm_apply_eq φ).2 this.symm
      rw [h2]
  · intro h
    by_cases hs : R.sink ∈ Q
    · obtain ⟨e1, e2⟩ := hs2 hs
      exact ⟨e2, e1⟩
    · exfalso
      have e := hs1 hs
      exact (φ ⟨R.sink, hs⟩).2 (e ▸ h)
end Dev.L347

theorem chk_lemma_3_47 {V : Type} [DecidableEq V] (F : CNF V) (M : Multiset (Clause V))
    (hM : 1 ≤ Multiset.card M) :
    (∀ R : ProofDag V, R.IsRefutationOf F → R.IsLean → R.axiomMultiset = M →
      R.size + 1 ≤ 2 * Multiset.card M → R.IsReadOnce) ∧
    (∀ (k : ℕ) (R R' : ProofDag V) (Q : Finset (Fin R.n)) (Q' : Finset (Fin R'.n))
      (φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}), 1 ≤ k →
      R.IsRefutationOf F → R.IsLean → R.axiomMultiset = M → R.size + 1 ≤ 2 * Multiset.card M →
      R'.IsRefutationOf F → R'.IsLean → R'.axiomMultiset = M →
      R'.size + 1 ≤ 2 * Multiset.card M →
      FrozenMoveVia k R R' Q Q' φ →
      Q'.card = Q.card ∧
      (∀ i ∈ Q, R.IsResolutionNode i) ∧ (∀ j ∈ Q', R'.IsResolutionNode j) ∧
      (R.inputs Q).card = Q.card + 1 ∧
      (∀ i : {i // i ∉ Q}, i.1 ∈ R.inputs Q ↔ (φ i).1 ∈ R'.inputs Q') ∧
      (∀ i ∈ R.inputs Q, ((R.consumers i).filter (· ∈ Q)).card = 1) ∧
      (∀ j ∈ R'.inputs Q', ((R'.consumers j).filter (· ∈ Q')).card = 1) ∧
      FrozenMoveVia k R' R Q' Q φ.symm) := by
  refine ⟨fun R hr hl hM' hs => Dev.L347.readOnce_of F M R hr hl hM' hs, ?_⟩
  intro k R R' Q Q' φ _ hr hl hM1 hs hr' hl' hM2 hs' hmv
  exact Dev.L347.part2 F M R R' Q Q' φ hr hl hM1 hs hr' hl' hM2 hs' hmv
end ReconfRes.Frozen
end

theorem solution : type_of% @ReconfRes.Frozen.chk_lemma_3_47 := @ReconfRes.Frozen.chk_lemma_3_47
