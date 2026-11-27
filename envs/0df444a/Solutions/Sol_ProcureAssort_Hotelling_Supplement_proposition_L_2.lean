-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.proposition_L_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:42:59.801789+00:00
-- url     : https://prove2.me/submissions/5fe09d95-a830-4c57-ab9b-4c09d257c7b2

import Definitions.Def_ProcureAssort_Hotelling_Supplement_CommonHotelling

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 2 ≤ n) (Θ : Fin n → Finset ℝ)
    (f : Fin n → ℝ → ℝ) (hTypes : ValidTypes Θ f) (hReg : Regular Θ f)
    (loc : Fin n → ℝ) (hloc : StrictMono loc) (hunit : ∀ i, loc i ∈ Set.Icc (0 : ℝ) 1)
    (delta : ℝ) (hdelta : 0 < delta)
    (a : Profile Θ → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (hDep : RowDependence f (activeSet Θ f loc delta) (xstar Θ f loc delta)
      (fun θ => differenceA (activeSet Θ f loc delta θ)) a b) :
    ∀ θ : Profile Θ,
      (∑ j ∈ activeSet Θ f loc delta θ,
        b j (θ j) * probOthers f j θ * xstar Θ f loc delta θ j) = 0 ∧
      ∀ i, ReducedRow (activeSet Θ f loc delta θ) i →
        a θ i = ∑ j ∈ (activeSet Θ f loc delta θ).filter (· ≤ i),
          b j (θ j) * probOthers f j θ * xstar Θ f loc delta θ j := by
            classical
            intro θ
            obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, ∀ j,
                c j = b j (θ j) * probOthers f j θ * xstar Θ f loc delta θ j := ⟨_, fun j => rfl⟩
            have h := hDep θ
            simp only [← hc] at h ⊢
            generalize activeSet Θ f loc delta θ = Q at h ⊢
            have hcj : ∀ j ∈ Q, c j = -∑ k ∈ Q.filter (fun k => ReducedRow Q k), a θ k * differenceA Q k j := by
              intro j hj
              have := h j hj
              linarith
            have hsum : ∀ S ⊆ Q, ∑ j ∈ S, c j =
                -∑ k ∈ Q.filter (fun k => ReducedRow Q k), a θ k * ∑ j ∈ S, differenceA Q k j := by
              intro S hS
              rw [Finset.sum_congr rfl (fun j hj => hcj j (hS hj)), Finset.sum_neg_distrib, Finset.sum_comm]
              congr 1
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [Finset.mul_sum]
            have hD : ∀ k, ReducedRow Q k → ∀ S : Finset (Fin n),
                ∃ m ∈ Q, k < m ∧ (∀ j ∈ Q, k < j → m ≤ j) ∧
                  ∑ j ∈ S, differenceA Q k j = (if m ∈ S then 1 else 0) - (if k ∈ S then 1 else 0) := by
              intro k hk S
              obtain ⟨hkQ, j0, hj0Q, hkj0⟩ := hk
              have hne : (Q.filter (k < ·)).Nonempty := ⟨j0, Finset.mem_filter.mpr ⟨hj0Q, hkj0⟩⟩
              have hmem := Finset.min'_mem _ hne
              rw [Finset.mem_filter] at hmem
              refine ⟨(Q.filter (k < ·)).min' hne, hmem.1, hmem.2, ?_, ?_⟩
              · intro j hj hkj
                exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj, hkj⟩)
              · unfold differenceA
                simp only [dif_pos hne]
                rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
            refine ⟨?_, ?_⟩
            · rw [hsum Q (subset_refl _)]
              rw [neg_eq_zero]
              apply Finset.sum_eq_zero
              intro k hk
              rw [Finset.mem_filter] at hk
              obtain ⟨m, hmQ, -, -, he⟩ := hD k hk.2 Q
              rw [he, if_pos hmQ, if_pos hk.1]
              ring
            · intro i hi
              rw [hsum _ (Finset.filter_subset _ _)]
              rw [Finset.sum_eq_single_of_mem i (Finset.mem_filter.mpr ⟨hi.1, hi⟩)]
              · obtain ⟨m, hmQ, hkm, -, he⟩ := hD i hi (Q.filter (· ≤ i))
                rw [he]
                have h1 : m ∉ Q.filter (· ≤ i) := by
                  rw [Finset.mem_filter]; intro h; exact absurd h.2 (not_le.mpr hkm)
                have h2 : i ∈ Q.filter (· ≤ i) := Finset.mem_filter.mpr ⟨hi.1, le_refl i⟩
                rw [if_neg h1, if_pos h2]
                ring
              · intro k hk hki
                rw [Finset.mem_filter] at hk
                obtain ⟨m, hmQ, hkm, hmin, he⟩ := hD k hk.2 (Q.filter (· ≤ i))
                rw [he]
                simp only [Finset.mem_filter, hmQ, hk.1, true_and]
                rcases lt_or_gt_of_ne hki with hlt | hgt
                · have : m ≤ i := hmin i hi.1 hlt
                  rw [if_pos this, if_pos hlt.le]; ring
                · rw [if_neg (not_le.mpr hgt), if_neg (not_le.mpr (hgt.trans hkm))]; ring
