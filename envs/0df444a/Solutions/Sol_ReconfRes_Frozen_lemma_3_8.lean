-- Prove2me | solution 1 for ReconfRes.Frozen.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:44:00.245377+00:00
-- url     : https://prove2.me/submissions/29dc639e-c22c-4c53-b7b4-577e2a0a5aac

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation

section
open MultiplierAssoc206.Resolution
namespace ReconfRes.Frozen
namespace Dev.L38
variable {V : Type} [DecidableEq V]

theorem parents_card_le (F : CNF V) (R : ProofDag V) (hR : R.IsRefutationOf F) (i : Fin R.n) :
    (R.parents i).card = 0 ∨ (R.parents i).card = 1 ∨ (R.parents i).card = 2 := by
  obtain ⟨_, _, h3, _, _⟩ := hR
  rcases h3 i with ⟨h, _⟩ | ⟨p₁, p₂, hne, h, _⟩ | ⟨p, h, _⟩
  · left; simp [h]
  · right; right; rw [h]; exact Finset.card_pair hne
  · right; left; rw [h]; simp

theorem sum_consumers (R : ProofDag V) :
    ∑ i, (R.consumers i).card = ∑ i, (R.parents i).card := by
  simp only [ProofDag.consumers, ProofDag.parents, Finset.card_filter]
  exact Finset.sum_comm

theorem lean_consumers (R : ProofDag V) (hl : R.IsLean) (i : Fin R.n) (hi : i ≠ R.sink) :
    1 ≤ (R.consumers i).card := by
  have := hl i
  unfold ProofDag.Anc at this
  rcases Relation.ReflTransGen.cases_head this with h | ⟨c, hc, _⟩
  · exact absurd h hi
  · apply Finset.card_pos.mpr
    exact ⟨c, by simp [ProofDag.consumers, hc]⟩

theorem main (F : CNF V) (R : ProofDag V)
    (hR : R.IsRefutationOf F) (hlean : R.IsLean) :
    let α : ℤ := ((Finset.univ.filter fun i => R.parents i = ∅).card : ℤ)
    let ρ : ℤ := ((Finset.univ.filter fun i => (R.parents i).card = 2).card : ℤ)
    let ω : ℤ := ((Finset.univ.filter fun i => (R.parents i).card = 1).card : ℤ)
    let X : ℤ := ∑ i ∈ Finset.univ.filter (fun i => i ≠ R.sink), (((R.consumers i).card : ℤ) - 1)
    0 ≤ X ∧ ρ = α - 1 + X ∧ (R.size : ℤ) = 2 * α - 1 + X + ω ∧ 2 * α - 1 ≤ (R.size : ℤ) := by
  intro α ρ ω X
  have hsink : (R.consumers R.sink).card = 0 := by rw [hR.2.2.2.1]; rfl
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun i hi => by
    have := lean_consumers R hlean i (Finset.mem_filter.mp hi).2
    omega)
  have hc : ∀ i, ((R.parents i).card : ℤ) =
      2 * (if (R.parents i).card = 2 then 1 else 0) + (if (R.parents i).card = 1 then 1 else 0) := by
    intro i
    rcases parents_card_le F R hR i with h | h | h <;> simp [h]
  have h1 : ∀ i, (1 : ℤ) = (if R.parents i = ∅ then 1 else 0) +
      (if (R.parents i).card = 2 then 1 else 0) + (if (R.parents i).card = 1 then 1 else 0) := by
    intro i
    rcases parents_card_le F R hR i with h | h | h
    · have : R.parents i = ∅ := Finset.card_eq_zero.mp h
      simp [this, h]
    · have : R.parents i ≠ ∅ := fun e => by simp [e] at h
      simp [this, h]
    · have : R.parents i ≠ ∅ := fun e => by simp [e] at h
      simp [this, h]
  have hn : (R.n : ℤ) = α + ρ + ω := by
    have := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin R.n)) = Finset.univ) (fun i _ => h1 i)
    simp only [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin] at this
    simp only [α, ρ, ω]; simpa using this
  have hsp : ∑ i, ((R.parents i).card : ℤ) = 2 * ρ + ω := by
    simp only [hc, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp only [ρ, ω]
  have hsc : ∑ i, ((R.consumers i).card : ℤ) = 2 * ρ + ω := by
    rw [← hsp]; exact_mod_cast sum_consumers R
  have hXeq : X = ∑ i, ((R.consumers i).card : ℤ) - R.n + 1 := by
    have : (Finset.univ.filter (fun i => i ≠ R.sink)) = Finset.univ.erase R.sink := by
      ext i; simp
    simp only [X, this]
    have h2 := Finset.add_sum_erase Finset.univ (fun i => (((R.consumers i).card : ℤ) - 1))
      (Finset.mem_univ R.sink)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hsink] at h2 ⊢
    simp at h2 ⊢
    omega
  have hω : 0 ≤ ω := by positivity
  refine ⟨hX0, ?_, ?_, ?_⟩ <;> (try simp only [ProofDag.size]) <;> omega
end Dev.L38

theorem chk_lemma_3_8 {V : Type} [DecidableEq V] (F : CNF V) (R : ProofDag V)
    (hR : R.IsRefutationOf F) (hlean : R.IsLean) :
    let α : ℤ := ((Finset.univ.filter fun i => R.parents i = ∅).card : ℤ)
    let ρ : ℤ := ((Finset.univ.filter fun i => (R.parents i).card = 2).card : ℤ)
    let ω : ℤ := ((Finset.univ.filter fun i => (R.parents i).card = 1).card : ℤ)
    let X : ℤ := ∑ i ∈ Finset.univ.filter (fun i => i ≠ R.sink), (((R.consumers i).card : ℤ) - 1)
    0 ≤ X ∧ ρ = α - 1 + X ∧ (R.size : ℤ) = 2 * α - 1 + X + ω ∧ 2 * α - 1 ≤ (R.size : ℤ) :=
  Dev.L38.main F R hR hlean
end ReconfRes.Frozen
end

theorem solution : type_of% @ReconfRes.Frozen.chk_lemma_3_8 := @ReconfRes.Frozen.chk_lemma_3_8
