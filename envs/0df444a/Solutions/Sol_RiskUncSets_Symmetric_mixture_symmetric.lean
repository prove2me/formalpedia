-- Prove2me | solution 1 for RiskUncSets.Symmetric.mixture_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:23:26.348592+00:00
-- url     : https://prove2.me/submissions/3e145452-088b-4dc7-9412-836e417238f8

import Mathlib
import Definitions.Def_RiskUncSets_Symmetric_Setting

namespace RiskUncSets.Symmetric

lemma b3e_qbar_rev {N : ℕ} (j : Fin (Nhat N)) (i : Fin N) :
    2 / (N : ℝ) - qbar j i = qbar j (Fin.rev i) := by
  have hj : (j : ℕ) < N / 2 + 1 := j.isLt
  have hi : (i : ℕ) < N := i.isLt
  unfold qbar
  simp only [Fin.val_rev]
  split_ifs <;> first | ring1 | (exfalso; omega)

lemma b3e_qbar_nonneg {N : ℕ} (j : Fin (Nhat N)) (i : Fin N) : 0 ≤ qbar j i := by
  unfold qbar
  split_ifs <;> positivity

lemma b3e_qbar_anti {N : ℕ} (j : Fin (Nhat N)) : Antitone (qbar j) := by
  intro a b hab
  have hab' : (a : ℕ) ≤ b := hab
  have h1 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have h2 : 1 / (N : ℝ) ≤ 2 / (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N); norm_num
  unfold qbar
  split_ifs <;> first | exact le_refl _ | linarith | (exfalso; omega)

end RiskUncSets.Symmetric

open RiskUncSets.Symmetric in
theorem solution {N : ℕ} (hN : 0 < N)
    (lam : Fin (Nhat N) → ℝ) (h0 : ∀ j, 0 ≤ lam j)
    (h1 : ∑ j, lam j = 1) :
    (∀ i : Fin N, 2 / (N : ℝ) - (∑ j, lam j • qbar j) i =
      (∑ j, lam j • qbar j) (Fin.rev i)) ∧
    (∑ j, lam j • qbar j) ∈ symRestrictedSimplex N := by
  set q : Fin N → ℝ := ∑ j, lam j • qbar j with hqdef
  have hq : ∀ i, q i = ∑ j, lam j * qbar j i := by
    intro i; simp [hqdef, Finset.sum_apply, smul_eq_mul]
  have hsym : ∀ i : Fin N, 2 / (N : ℝ) - q i = q (Fin.rev i) := by
    intro i
    rw [hq, hq]
    have : 2 / (N : ℝ) = ∑ j, lam j * (2 / (N : ℝ)) := by
      rw [← Finset.sum_mul, h1, one_mul]
    rw [this, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← b3e_qbar_rev, mul_sub]
  refine ⟨hsym, ⟨⟨⟨?_, ?_⟩, ?_⟩, Fin.revPerm, ?_⟩⟩
  · intro i
    rw [hq]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (h0 j) (b3e_qbar_nonneg j i))
  · have hrev : ∑ i, q (Fin.rev i) = ∑ i, q i :=
      Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)
    have hsum : ∑ i, (2 / (N : ℝ) - q i) = ∑ i, q (Fin.rev i) :=
      Finset.sum_congr rfl (fun i _ => hsym i)
    rw [hrev, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (N : ℝ) * (2 / (N : ℝ)) = 2 := by field_simp
    linarith
  · intro a b hab
    rw [hq, hq]
    exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (b3e_qbar_anti j hab) (h0 j))
  · funext i
    show q i = 2 / (N : ℝ) - q (Fin.revPerm i)
    rw [Fin.revPerm_apply, ← hsym]
    ring
