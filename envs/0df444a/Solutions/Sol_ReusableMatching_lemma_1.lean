-- Prove2me | solution 1 for ReusableMatching.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:54:01.006263+00:00
-- url     : https://prove2.me/submissions/105f2742-4dcb-43db-a187-8af4c16806ac

import Mathlib
import Definitions.Def_ReusableMatching_OPT
import Definitions.Def_ReusableMatching_window

open ReusableMatching in
theorem solution {V : Type*} [Fintype V] {n : ℕ} (I : OBMRRInstance V n) (P : ℝ)
    (α : V → Fin n → ℝ) (βd : Fin n → ℝ) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ ≤ 1)
    (hα : ∀ i t, 0 ≤ α i t) (hβ : ∀ j, 0 ≤ βd j)
    (h_rev : (∑ i, ∑ t, α i t) + ∑ j, βd j ≤ P)
    (h_feas : ∀ i j, (i, j) ∈ I.E → Γ * I.r i ≤ βd j + ∑ t ∈ window I j, α i t) :
    Γ * OPT I ≤ P := by
  classical
  have key : ∀ M : Finset (V × Fin n), IsFeasibleMatching I M →
      Γ * ∑ p ∈ M, I.r p.1 ≤ P := by
    intro M hM
    obtain ⟨hsub, hinj, hgap⟩ : M ⊆ I.E ∧ (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q) ∧
        (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p.2 < q.2 → (p.2 : ℕ) + I.d ≤ (q.2 : ℕ)) := hM
    have h1 : Γ * ∑ p ∈ M, I.r p.1 ≤
        ∑ p ∈ M, (βd p.2 + ∑ t ∈ window I p.2, α p.1 t) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun p hp => h_feas p.1 p.2 (hsub hp))
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ p ∈ M, βd p.2 ≤ ∑ j, βd j := by
      have hinjon : Set.InjOn Prod.snd (M : Set (V × Fin n)) := by
        intro p hp q hq h
        exact hinj p hp q hq h
      rw [← Finset.sum_image (f := βd) hinjon]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hβ j)
    have h3 : ∑ p ∈ M, ∑ t ∈ window I p.2, α p.1 t ≤ ∑ i, ∑ t, α i t := by
      have hdisj : (M : Set (V × Fin n)).PairwiseDisjoint
          (fun p => ({p.1} : Finset V) ×ˢ window I p.2) := by
        intro p hp q hq hpq
        show Disjoint (({p.1} : Finset V) ×ˢ window I p.2) (({q.1} : Finset V) ×ˢ window I q.2)
        rw [Finset.disjoint_left]
        rintro ⟨a, t⟩ ha hb
        rw [Finset.mem_product, Finset.mem_singleton] at ha hb
        have hpq1 : p.1 = q.1 := ha.1.symm.trans hb.1
        have hne2 : p.2 ≠ q.2 := fun h => hpq (hinj p hp q hq h)
        have hwa := ha.2
        have hwb := hb.2
        unfold window at hwa hwb
        rw [Finset.mem_filter] at hwa hwb
        obtain ⟨-, hta, hda⟩ := hwa
        obtain ⟨-, htb, hdb⟩ := hwb
        have hta' : (t : ℕ) ≤ (p.2 : ℕ) := hta
        have htb' : (t : ℕ) ≤ (q.2 : ℕ) := htb
        have hda' : (p.2 : ℕ) < (t : ℕ) + I.d := hda
        have hdb' : (q.2 : ℕ) < (t : ℕ) + I.d := hdb
        rcases lt_or_gt_of_ne hne2 with hlt | hlt
        · have := hgap p hp q hq hpq1 hlt
          omega
        · have := hgap q hq p hp hpq1.symm hlt
          omega
      calc ∑ p ∈ M, ∑ t ∈ window I p.2, α p.1 t
          = ∑ p ∈ M, ∑ q ∈ ({p.1} : Finset V) ×ˢ window I p.2, α q.1 q.2 := by
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [Finset.sum_product, Finset.sum_singleton]
        _ = ∑ q ∈ M.biUnion (fun p => ({p.1} : Finset V) ×ˢ window I p.2), α q.1 q.2 :=
            (Finset.sum_biUnion hdisj).symm
        _ ≤ ∑ q : V × Fin n, α q.1 q.2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun q _ _ => hα q.1 q.2)
        _ = ∑ i, ∑ t, α i t := Fintype.sum_prod_type _
    linarith
  unfold OPT
  rw [← le_div_iff₀' hΓ0]
  apply Finset.sup'_le
  intro M hM
  rw [le_div_iff₀' hΓ0]
  exact key M (Finset.mem_filter.1 hM).2
