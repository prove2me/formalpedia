-- Prove2me | solution 1 for SerialBatchTardy.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:52:03.75131+00:00
-- url     : https://prove2.me/submissions/5965c1d9-2b34-4642-887a-8b30bd3e5ac2

import Mathlib
import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace Aux_SerialBatchTardy_lemma_7

open SerialBatchTardy

theorem job_eq {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (j : Fin (hardInstance xs t k L).jobs.length) :
    (hardInstance xs t k L).job j = labelJob xs t k (labelOf xs t k L j) := by
  unfold Instance.job labelOf
  simp only [List.get_eq_getElem]
  simp only [hardInstance, List.getElem_map]
  rfl

theorem labelOf_mem {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (j : Fin (hardInstance xs t k L).jobs.length) :
    labelOf xs t k L j ∈ hardLabels xs k L :=
  List.get_mem _ _

theorem mem_hardLabels_normal {xs : List ℕ} {k : ℕ} {L : List ℕ} {ℓ x h : ℕ}
    (hm : JobLabel.normal ℓ x h ∈ hardLabels xs k L) :
    x ∈ xs ∧ ℓ < k := by
  unfold hardLabels at hm
  rcases List.mem_append.mp hm with h1 | h1
  · obtain ⟨e, _, he⟩ := List.mem_map.mp h1
    cases he
  · obtain ⟨ℓ', hℓ', h2⟩ := List.mem_flatMap.mp h1
    obtain ⟨x', hx', h3⟩ := List.mem_flatMap.mp h2
    unfold gadgetLabels at h3
    obtain ⟨h', _, h4⟩ := List.mem_flatMap.mp h3
    have h5 := (List.mem_replicate.mp h4).2
    cases h5
    exact ⟨hx', List.mem_range.mp hℓ'⟩

theorem gadget_some {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    {j : Fin (hardInstance xs t k L).jobs.length} {ℓ : ℕ}
    (hg : (labelOf xs t k L j).gadget? = some ℓ) :
    ∃ x h, labelOf xs t k L j = .normal ℓ x h ∧ x ∈ xs ∧ ℓ < k := by
  have hm := labelOf_mem (xs := xs) (t := t) (k := k) (L := L) j
  obtain ⟨lab, hlab⟩ : ∃ lab, labelOf xs t k L j = lab := ⟨_, rfl⟩
  rw [hlab] at hg hm
  rw [hlab]
  cases lab with
  | leftover e => simp [JobLabel.gadget?] at hg
  | normal ℓ' x h =>
    simp only [JobLabel.gadget?, Option.some.injEq] at hg
    subst hg
    obtain ⟨hx, hℓ⟩ := mem_hardLabels_normal hm
    exact ⟨x, h, rfl, hx, hℓ⟩

theorem job_normal {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    {j : Fin (hardInstance xs t k L).jobs.length} {ℓ x h : ℕ}
    (hl : labelOf xs t k L j = .normal ℓ x h) :
    (hardInstance xs t k L).job j =
      { p := xs.length ^ h, w := xs.length ^ h * (xs.prod + xs.prod / x),
        r := ((ℓ * (3 * t) : ℕ) : ℤ), d := ((ℓ * (3 * t) + t + x : ℕ) : ℤ) } := by
  rw [job_eq, hl]
  rfl

theorem batchLen_ge {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (σ : Schedule (hardInstance xs t k L)) (b : ℕ) : (t : ℤ) ≤ σ.batchLen b := by
  have h0 : (0 : ℤ) ≤ ∑ j ∈ σ.batchJobs b, (((hardInstance xs t k L).job j).p : ℤ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hs : ((hardInstance xs t k L).setup : ℤ) = t := rfl
  have hb : σ.batchLen b = ((hardInstance xs t k L).setup : ℤ) +
      ∑ j ∈ σ.batchJobs b, (((hardInstance xs t k L).job j).p : ℤ) := rfl
  linarith

theorem early_window {xs : List ℕ} {t k : ℕ} {L : List ℕ} (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    {j : Fin (hardInstance xs t k L).jobs.length} {ℓ : ℕ} (hj : j ∈ earlyType σ ℓ) :
    (ℓ : ℤ) * (3 * t) ≤ σ.start (σ.batch j) ∧ σ.start (σ.batch j) + t ≤ σ.comp (σ.batch j) ∧
      σ.comp (σ.batch j) < (ℓ : ℤ) * (3 * t) + 2 * t := by
  simp only [earlyType, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨hg, hnt⟩ := hj
  obtain ⟨x, h, hl, hx, -⟩ := gadget_some hg
  have hxt : (x : ℤ) < t := by exact_mod_cast hlt x hx
  have hr := hσ.1 j
  have hd : ¬ ((hardInstance xs t k L).job j).d < σ.comp (σ.batch j) := hnt
  have hd2 := not_lt.mp hd
  rw [job_normal hl] at hr hd2
  have hr' : (ℓ : ℤ) * (3 * t) ≤ σ.start (σ.batch j) := by
    have := hr
    push_cast at this
    linarith
  have hd' : σ.comp (σ.batch j) ≤ (ℓ : ℤ) * (3 * t) + t + x := by
    have := hd2
    push_cast at this
    linarith
  have hlen := batchLen_ge σ (σ.batch j)
  have hc : σ.comp (σ.batch j) = σ.start (σ.batch j) + σ.batchLen (σ.batch j) := rfl
  refine ⟨hr', by linarith, by linarith⟩

end Aux_SerialBatchTardy_lemma_7

open SerialBatchTardy Aux_SerialBatchTardy_lemma_7 in
theorem solution (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible) (ℓ : ℕ)
    (hE : (earlyType σ ℓ).Nonempty) :
    ∃! b : ℕ, (∀ j ∈ earlyType σ ℓ, σ.batch j = b) ∧
      ∀ ℓ' : ℕ, ℓ' ≠ ℓ → ∀ j ∈ earlyType σ ℓ', σ.batch j ≠ b := by
  obtain ⟨j0, hj0⟩ := hE
  refine ⟨σ.batch j0, ⟨?_, ?_⟩, ?_⟩
  · intro j hj
    by_contra hne
    have hU1 : σ.Used (σ.batch j) := ⟨j, rfl⟩
    have hU0 : σ.Used (σ.batch j0) := ⟨j0, rfl⟩
    obtain ⟨a1, a2, a3⟩ := early_window hlt σ hσ hj
    obtain ⟨b1, b2, b3⟩ := early_window hlt σ hσ hj0
    rcases hσ.2 _ _ hU1 hU0 hne with h | h
    · linarith
    · linarith
  · intro ℓ' hne j hj heq
    obtain ⟨a1, a2, a3⟩ := early_window hlt σ hσ hj
    obtain ⟨b1, b2, b3⟩ := early_window hlt σ hσ hj0
    rw [heq] at a1 a2 a3
    have ht0 : (0 : ℤ) ≤ 3 * t := by positivity
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h' : (ℓ' : ℤ) + 1 ≤ ℓ := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_right h' ht0
      linarith
    · have h' : (ℓ : ℤ) + 1 ≤ ℓ' := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_right h' ht0
      linarith
  · intro b hb
    exact (hb.1 j0 hj0).symm
