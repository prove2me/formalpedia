-- Prove2me | solution 1 for PureDPQR.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T14:04:42.51361+00:00
-- url     : https://prove2.me/submissions/e0cb519d-7759-4a13-a823-31a3e03895bf

import Mathlib

theorem solution {K : ℕ} (hK : 0 < K) (a : Fin K → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    let P : Fin K → ℝ := fun i => Real.exp (lam * a i) / ∑ j, Real.exp (lam * a j)
    (⨆ i, a i) - ∑ i, P i * a i ≤ Real.log K / lam := by
  classical
  dsimp only
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  set Z : ℝ := ∑ j, Real.exp (lam * a j) with hZ
  set P : Fin K → ℝ := fun i => Real.exp (lam * a i) / Z with hP
  have hne : (Finset.univ : Finset (Fin K)).Nonempty :=
    ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hZpos : 0 < Z := by
    rw [hZ]
    exact Finset.sum_pos (fun j _ => Real.exp_pos _) hne
  have hPpos : ∀ i, 0 < P i := by
    intro i
    rw [hP]
    exact div_pos (Real.exp_pos _) hZpos
  have hPsum : ∑ i, P i = 1 := by
    rw [hP]
    simp only
    rw [← Finset.sum_div, ← hZ]
    exact div_self (ne_of_gt hZpos)
  -- entropy bound
  have hentropy : -Real.log K ≤ ∑ i, P i * Real.log (P i) := by
    have hineq : ∑ i, P i * Real.log (1 / ((K : ℝ) * P i)) ≤
        ∑ i, ((1 : ℝ) / (K : ℝ) - P i) := by
      apply Finset.sum_le_sum
      intro i _
      have hpos : 0 < 1 / ((K : ℝ) * P i) := by positivity
      have h1 : Real.log (1 / ((K : ℝ) * P i)) ≤ 1 / ((K : ℝ) * P i) - 1 :=
        Real.log_le_sub_one_of_pos hpos
      calc P i * Real.log (1 / ((K : ℝ) * P i)) ≤
            P i * (1 / ((K : ℝ) * P i) - 1) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt (hPpos i))
        _ = 1 / (K : ℝ) - P i := by
            field_simp [ne_of_gt (hPpos i)]
    have hlhs : ∑ i, P i * Real.log (1 / ((K : ℝ) * P i)) =
        -(Real.log K) * (∑ i, P i) - ∑ i, P i * Real.log (P i) := by
      have hterm : ∀ i, P i * Real.log (1 / ((K : ℝ) * P i)) =
          -(Real.log K) * P i - P i * Real.log (P i) := by
        intro i
        rw [Real.log_div one_ne_zero (by positivity),
          Real.log_mul (by positivity) (ne_of_gt (hPpos i)), Real.log_one]
        ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    have hrhs : ∑ i, ((1 : ℝ) / (K : ℝ) - P i) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hPsum, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    rw [hlhs, hrhs, hPsum] at hineq
    linarith
  -- a maximizing index
  obtain ⟨i0, -, hi0⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin K)) a hne
  have hle : ∀ i, a i ≤ a i0 := by
    intro i
    exact hi0 i (Finset.mem_univ i)
  have hbdd : BddAbove (Set.range a) := by
    exact ⟨a i0, by rintro _ ⟨i, rfl⟩; exact hle i⟩
  have hsup : (⨆ i, a i) = a i0 :=
    le_antisymm (ciSup_le hle) (le_ciSup hbdd i0)
  -- log of the partition function
  have hexp_le : Real.exp (lam * a i0) ≤ Z := by
    rw [hZ]
    exact Finset.single_le_sum (f := fun j => Real.exp (lam * a j))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i0)
  have hlogZ : lam * a i0 ≤ Real.log Z := by
    have h := Real.log_le_log (Real.exp_pos _) hexp_le
    rwa [Real.log_exp] at h
  have hlogP : ∀ i, Real.log (P i) = lam * a i - Real.log Z := by
    intro i
    rw [hP, Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZpos), Real.log_exp]
  have hE : ∑ i, P i * Real.log (P i) = lam * (∑ i, P i * a i) - Real.log Z := by
    calc ∑ i, P i * Real.log (P i) = ∑ i, P i * (lam * a i - Real.log Z) := by
          exact Finset.sum_congr rfl (fun i _ => by rw [hlogP i])
      _ = ∑ i, (lam * (P i * a i) - P i * Real.log Z) := by
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = lam * (∑ i, P i * a i) - Real.log Z * (∑ i, P i) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
      _ = lam * (∑ i, P i * a i) - Real.log Z := by rw [hPsum, mul_one]
  have hkey : lam * (a i0 - ∑ i, P i * a i) ≤ Real.log K := by
    have h1 : lam * a i0 - Real.log Z ≤ 0 := by linarith
    have h2 : -(∑ i, P i * Real.log (P i)) ≤ Real.log K := by linarith
    have : lam * (a i0 - ∑ i, P i * a i) =
        (lam * a i0 - Real.log Z) - ∑ i, P i * Real.log (P i) := by
      rw [hE]; ring
    rw [this]; linarith
  rw [hsup]
  exact (le_div_iff₀ hlam).mpr (by linarith)
