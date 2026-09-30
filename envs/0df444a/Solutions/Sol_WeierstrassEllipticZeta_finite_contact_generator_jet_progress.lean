-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_generator_jet_progress
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T17:15:00.615082+00:00
-- url     : https://prove2.me/submissions/5e864fb5-8604-453e-86ba-846838e158de

import Theorems.Thm_WeierstrassEllipticZeta_finite_contact_generator_jets
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

noncomputable section
open WeierstrassEllipticZeta

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n : V → ℕ) (r : ℕ)
    (f : Fin r → MvPolynomial (Fin 4) ℂ)
    (hgen : Ideal.span (Set.range f) =
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) (k : ℕ) :
    let F : ℕ → Ideal (MvPolynomial (Fin 4) ℂ) := fun a =>
      Ideal.span (Set.range (fun i : Fin (a + 1) × Fin r =>
        (extensionChartDerivation g₂ g₃ c)^[i.1.val] (f i.2)))
    F k ≤ F (k + 1) ∧
      (F k = F (k + 1) ↔ F k = ⊤) ∧
      (F k < F (k + 1) ↔ ∃ v : V, k < n v) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ F k) =
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ F (k + 1)) +
          (Finset.univ.filter (fun v : V => k < n v)).card := by
  classical
  let F : ℕ → Ideal (MvPolynomial (Fin 4) ℂ) := fun a =>
    Ideal.span (Set.range (fun i : Fin (a + 1) × Fin r =>
      (extensionChartDerivation g₂ g₃ c)^[i.1.val] (f i.2)))
  have hrank (a : ℕ) :
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ F a) = ∑ v : V, (n v - a) :=
    (finite_contact_generator_jets g₂ g₃ c V n r f hgen a).2.2.2.1
  have htop (a : ℕ) : F a = ⊤ ↔ ∀ v : V, n v ≤ a :=
    (finite_contact_generator_jets g₂ g₃ c V n r f hgen a).2.2.2.2.2
  have hmono : F k ≤ F (k + 1) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨(⟨i.1.val, by have := i.1.isLt; omega⟩, i.2), rfl⟩
  have hdrop : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ F k) =
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ F (k + 1)) +
        (Finset.univ.filter (fun v : V => k < n v)).card := by
    rw [hrank k, hrank (k + 1), Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : k < n v
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      omega
  have hstable : F k = F (k + 1) ↔ F k = ⊤ := by
    constructor
    · intro heq
      have hzero : (Finset.univ.filter (fun v : V => k < n v)).card = 0 := by
        rw [heq] at hdrop
        omega
      apply (htop k).mpr
      simpa only [Finset.card_filter_eq_zero_iff, Finset.mem_univ, forall_const,
        not_lt] using hzero
    · intro hfull
      have hnext : F (k + 1) = ⊤ := top_unique (hfull ▸ hmono)
      exact hfull.trans hnext.symm
  have hstrict : F k < F (k + 1) ↔ ∃ v : V, k < n v := by
    constructor
    · intro hs
      by_contra hnone
      have hfull : F k = ⊤ := (htop k).mpr fun v =>
        Nat.le_of_not_gt (fun hv => hnone ⟨v, hv⟩)
      exact hs.ne (hstable.mpr hfull)
    · rintro ⟨v, hv⟩
      apply lt_iff_le_not_ge.mpr
      refine ⟨hmono, ?_⟩
      intro hrev
      have hfull := hstable.mp (le_antisymm hmono hrev)
      exact (not_le_of_gt hv) ((htop k).mp hfull v)
  exact ⟨hmono, hstable, hstrict, hdrop⟩

