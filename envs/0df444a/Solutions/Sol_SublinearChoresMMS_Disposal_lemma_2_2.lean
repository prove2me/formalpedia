-- Prove2me | solution 1 for SublinearChoresMMS.Disposal.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:41:55.356205+00:00
-- url     : https://prove2.me/submissions/08fb0abb-cefd-4408-8e65-c6af1e72b855

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Setting

section
set_option autoImplicit false
noncomputable section

namespace SublinearChoresMMS.Disposal.Dev.L22

open SublinearChoresMMS.Disposal

/-- the cost share is invariant under reindexing the chores -/
theorem costShare_perm {m : ℕ} (u : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (d : ℕ) :
    costShare (fun r => u (σ r)) d = costShare u d := by
  classical
  unfold costShare LittleCharity.MMS.mms
  congr 1
  have key : ∀ (f : Fin m → Fin d) (j : Fin d),
      (∑ e ∈ Finset.univ.filter (fun g => f g = j), u (σ e)) =
      ∑ e ∈ Finset.univ.filter (fun g => (f ∘ σ.symm) g = j), u e := by
    intro f j
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Equiv.sum_comp σ (fun e => if (f ∘ σ.symm) e = j then u e else 0)]
    simp
  let e : (Fin m → Fin d) ≃ (Fin m → Fin d) := Equiv.arrowCongr σ (Equiv.refl (Fin d))
  refine Eq.trans ?_ (Equiv.iSup_comp e)
  apply iSup_congr
  intro f
  apply iInf_congr
  intro j
  have := key f j
  simp only [e, Equiv.arrowCongr_apply, Equiv.coe_refl]
  rw [this]
  rfl

/-- Hall: ranks can be matched injectively to chores that are no costlier than the
sorted cost at the rank. -/
theorem exists_transfer {n m : ℕ} (c : Cost n m) (σ : Fin n → Equiv.Perm (Fin m))
    (hσ : ∀ i, Antitone (fun r => c i (σ i r))) (A : Allocation n m) :
    ∃ τ : Equiv.Perm (Fin m), ∀ r, c (A r) (τ r) ≤ c (A r) (σ (A r) r) := by
  classical
  let t : Fin m → Finset (Fin m) := fun r =>
    Finset.univ.filter (fun e => c (A r) e ≤ c (A r) (σ (A r) r))
  have hall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    obtain ⟨r0, hr0, hmin⟩ := s.exists_min_image (fun r => r.val) hs
    have hsub : s ⊆ Finset.univ.filter (fun r : Fin m => r0 ≤ r) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.le_def.2 (hmin r hr)
    have h1 : s.card ≤ (Finset.univ.filter (fun r : Fin m => r0 ≤ r)).card :=
      Finset.card_le_card hsub
    have h2 : ((Finset.univ.filter (fun r : Fin m => r0 ≤ r)).image (σ (A r0))) ⊆ s.biUnion t := by
      intro e he
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨r', hr', rfl⟩ := he
      rw [Finset.mem_biUnion]
      refine ⟨r0, hr0, ?_⟩
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hσ (A r0) hr'
    have h3 : ((Finset.univ.filter (fun r : Fin m => r0 ≤ r)).image (σ (A r0))).card =
        (Finset.univ.filter (fun r : Fin m => r0 ≤ r)).card :=
      Finset.card_image_of_injective _ (σ (A r0)).injective
    calc s.card ≤ (Finset.univ.filter (fun r : Fin m => r0 ≤ r)).card := h1
      _ = _ := h3.symm
      _ ≤ _ := Finset.card_le_card h2
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun r => ?_⟩
  have := hft r
  simpa [t] using this

theorem main {n m : ℕ} (hn : 0 < n) (c : Cost n m) (hc : Nonnegative c) :
    ∃ (d : Cost n m) (rowPerm : Fin n → Equiv.Perm (Fin m)),
      IDO d ∧ (∀ i r, d i r = c i (rowPerm i r)) ∧
      (∀ i, mu d i = mu c i ∧ cost d i Finset.univ = cost c i Finset.univ) ∧
      ∀ A : Allocation n m, ∃ transfer : Equiv.Perm (Fin m),
        (∀ r, c (A r) (transfer r) ≤ d (A r) r) ∧
        ∀ i, cost c i (bundle (fun e => A (transfer.symm e)) i) ≤ cost d i (bundle A i) := by
  classical
  let σ : Fin n → Equiv.Perm (Fin m) := fun i => Tuple.sort (fun r => -c i r)
  have hmono : ∀ i, Monotone ((fun r => -c i r) ∘ σ i) := fun i => Tuple.monotone_sort _
  have hσ : ∀ i, Antitone (fun r => c i (σ i r)) := by
    intro i a b hab
    have := hmono i hab
    simp only [Function.comp] at this
    linarith
  refine ⟨fun i r => c i (σ i r), σ, hσ, fun i r => rfl, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · exact costShare_perm (c i) (σ i) n
    · simp only [cost, ChoresEFX.cost]
      exact Equiv.sum_comp (σ i) (c i)
  · intro A
    obtain ⟨τ, hτ⟩ := exists_transfer c σ hσ A
    refine ⟨τ, hτ, fun i => ?_⟩
    simp only [cost, ChoresEFX.cost, bundle, ChoresEFX.bundle]
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Equiv.sum_comp τ (fun g => if A (τ.symm g) = i then c i g else 0)]
    refine Finset.sum_le_sum fun r _ => ?_
    simp only [Equiv.symm_apply_apply]
    split_ifs with h
    · subst h; exact hτ r
    · exact le_rfl

end SublinearChoresMMS.Disposal.Dev.L22
end
end

section
noncomputable section

namespace SublinearChoresMMS.Disposal

theorem chk_lemma_2_2 {n m : ℕ} (hn : 0 < n) (c : Cost n m) (hc : Nonnegative c) :
    ∃ (d : Cost n m) (rowPerm : Fin n → Equiv.Perm (Fin m)),
      IDO d ∧ (∀ i r, d i r = c i (rowPerm i r)) ∧
      (∀ i, mu d i = mu c i ∧ cost d i Finset.univ = cost c i Finset.univ) ∧
      ∀ A : Allocation n m, ∃ transfer : Equiv.Perm (Fin m),
        (∀ r, c (A r) (transfer r) ≤ d (A r) r) ∧
        ∀ i, cost c i (bundle (fun e => A (transfer.symm e)) i) ≤ cost d i (bundle A i) :=
  Dev.L22.main hn c hc

end SublinearChoresMMS.Disposal
end
end

theorem solution : type_of% @SublinearChoresMMS.Disposal.chk_lemma_2_2 := @SublinearChoresMMS.Disposal.chk_lemma_2_2
