-- Prove2me | solution 1 for ReluMIP.Ideal.system7c_redundant
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:13:43.395847+00:00
-- url     : https://prove2.me/submissions/08bc910a-bae4-4e0a-b6ef-76a8ab7fd9ea

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting

namespace ReluMIP.Ideal

lemma wLb_le {η : ℕ} (w L U x : Fin η → ℝ) (hx : x ∈ box L U) (i : Fin η) :
    w i * Lbrev w L U i ≤ w i * x i := by
  obtain ⟨h1, h2⟩ := hx i
  unfold Lbrev
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h1 h
  · exact mul_le_mul_of_nonpos_left h2 (le_of_lt (not_le.mp h))

lemma le_wUb {η : ℕ} (w L U x : Fin η → ℝ) (hx : x ∈ box L U) (i : Fin η) :
    w i * x i ≤ w i * Ubrev w L U i := by
  obtain ⟨h1, h2⟩ := hx i
  unfold Ubrev
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h2 h
  · exact mul_le_mul_of_nonpos_left h1 (le_of_lt (not_le.mp h))

/-- Core inequality (7c) for any index set. -/
lemma rhs7c_le {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ) (y z : ℝ)
    (h6a : affineFn w b x ≤ y) (hx : x ∈ box L U) (hy : 0 ≤ y) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (I : Finset (Fin η)) : rhs7c w b L U I x z ≤ y := by
  have hsplit : ∀ f : Fin η → ℝ, ∑ i ∈ Finset.univ \ I, f i + ∑ i ∈ I, f i = ∑ i, f i :=
    fun f => Finset.sum_sdiff (Finset.subset_univ I)
  set XI := ∑ i ∈ I, w i * x i
  set XJ := ∑ i ∈ Finset.univ \ I, w i * x i
  set UI := ∑ i ∈ I, w i * Ubrev w L U i
  set LJ := ∑ i ∈ Finset.univ \ I, w i * Lbrev w L U i
  have hXI : XI ≤ UI := Finset.sum_le_sum fun i _ => le_wUb w L U x hx i
  have hXJ : LJ ≤ XJ := Finset.sum_le_sum fun i _ => wLb_le w L U x hx i
  have hwx : ∑ i, w i * x i = XI + XJ := by rw [← hsplit]; ring
  have hr : rhs7c w b L U I x z = XI - UI * (1 - z) + (b + LJ) * z := by
    unfold rhs7c
    have : ∑ i ∈ I, w i * (x i - Ubrev w L U i * (1 - z)) =
        ∑ i ∈ I, (w i * x i - w i * Ubrev w L U i * (1 - z)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [this, Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold affineFn at h6a
  rw [hr]
  rcases le_or_gt 0 (b + LJ + UI) with h | h
  · have := mul_nonneg (sub_nonneg.mpr hz1) h
    nlinarith
  · have := mul_nonpos_of_nonneg_of_nonpos hz0 h.le
    nlinarith

end ReluMIP.Ideal

open ReluMIP.Ideal in
theorem solution {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    ∀ p ∈ relax6 w b L U, ∀ I : Finset (Fin η), I ⊆ supp w →
      rhs7c w b L U I p.1 p.2.2 ≤ p.2.1 := by
  rintro ⟨x, y, z⟩ ⟨h6a, _, hx, hy, hz0, hz1⟩ I _
  exact rhs7c_le w b L U x y z h6a hx hy hz0 hz1 I
