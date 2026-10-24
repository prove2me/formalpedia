-- Prove2me | solution 1 for PermInvConvex.Sparsity.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:40:23.721007+00:00
-- url     : https://prove2.me/submissions/e23021eb-405c-420b-a0d1-76cc3da98264

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting
import Theorems.Thm_PermInvConvex_Sparsity_theorem_3_2

open PermInvConvex.Sparsity ModernConvex.Spectral

namespace SparseFormulaAux

lemma norm_nonneg {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (x : Fin n → ℝ) : 0 ≤ ns x := by
  let p : Seminorm ℝ (Fin n → ℝ) :=
    Seminorm.of ns hns.add_le (by simpa only [Real.norm_eq_abs] using hns.smul)
  exact apply_nonneg p x

lemma largest_smul {n : ℕ} (a : ℝ) (ha : 0 ≤ a) (j : ℕ) (x : Fin n → ℝ) :
    sumLargest j (a • x) = a * sumLargest j x := by
  unfold sumLargest
  simp_rw [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  exact (Real.mul_iSup_of_nonneg ha _).symm

lemma feas_smul {n : ℕ} (K : ℕ) (a : ℝ) (ha : 0 ≤ a) {x u : Fin n → ℝ}
    (hu : u ∈ Feas11 K x) : a • u ∈ Feas11 K (a • x) := by
  have habs : absVec (a • x) = a • absVec x := by
    ext i
    simp only [absVec, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij hj
    exact mul_le_mul_of_nonneg_left (hu.1 i j hij hj) ha
  · intro i hi
    exact mul_nonneg ha (hu.2.1 i hi)
  · intro i hi
    simp only [Pi.smul_apply, smul_eq_mul, hu.2.2.1 i hi, mul_zero]
  · intro j hj1 hjn
    rw [habs, largest_smul a ha, largest_smul a ha]
    exact mul_le_mul_of_nonneg_left (hu.2.2.2 j hj1 hjn) ha

lemma optimal_smul {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ)
    (hopt : ∀ x : Fin n → ℝ, uVec K x ∈ Feas11 K x ∧
      ∀ u ∈ Feas11 K x, ns (uVec K x) ≤ ns u)
    (a : ℝ) (ha : 0 < a) (x : Fin n → ℝ) :
    ns (uVec K (a • x)) = a * ns (uVec K x) := by
  have hforward := (hopt (a • x)).2 (a • uVec K x) (feas_smul K a ha.le (hopt x).1)
  rw [hns.smul, abs_of_pos ha] at hforward
  have hbackfeas : a⁻¹ • uVec K (a • x) ∈ Feas11 K x := by
    have h := feas_smul K a⁻¹ (inv_nonneg.mpr ha.le) (hopt (a • x)).1
    simpa only [inv_smul_smul₀ ha.ne'] using h
  have hback := (hopt x).2 _ hbackfeas
  rw [hns.smul, abs_of_pos (inv_pos.mpr ha)] at hback
  apply le_antisymm hforward
  have hscaled := mul_le_mul_of_nonneg_left hback ha.le
  simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] using hscaled

theorem formula_of_main {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ)
    (hmain : ∀ x : Fin n → ℝ,
      (uVec K x ∈ Feas11 K x ∧ ∀ u ∈ Feas11 K x, ns (uVec K x) ≤ ns u) ∧
      (x ∈ convexHull ℝ (NK ns K) ↔ ns (uVec K x) ≤ 1))
    (x : Fin n → ℝ) : normC ns K x = ns (uVec K x) := by
  have hopt := fun y => (hmain y).1
  have hnonneg : 0 ≤ ns (uVec K x) := norm_nonneg ns hns _
  have hadmissible (r : ℝ) (hr : 0 < r) (hxr : ns (uVec K x) ≤ r) :
      r⁻¹ • x ∈ convexHull ℝ (NK ns K) := by
    apply (hmain (r⁻¹ • x)).2.mpr
    rw [optimal_smul ns hns K hopt r⁻¹ (inv_pos.mpr hr) x]
    exact (inv_mul_le_iff₀ hr).mpr (by simpa only [mul_one] using hxr)
  have hnonempty : {r ∈ Set.Ioi (0 : ℝ) | r⁻¹ • x ∈ convexHull ℝ (NK ns K)}.Nonempty := by
    have hr : 0 < ns (uVec K x) + 1 := by positivity
    exact ⟨ns (uVec K x) + 1, hr, hadmissible _ hr (by linarith)⟩
  rw [normC, gauge_def']
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hr : 0 < ns (uVec K x) + ε := add_pos_of_nonneg_of_pos hnonneg hε
    exact csInf_le ⟨0, fun r hr => hr.1.le⟩
      ⟨hr, hadmissible _ hr (le_add_of_nonneg_right hε.le)⟩
  · refine le_csInf hnonempty ?_
    intro r hr
    have hrpos : 0 < r := hr.1
    have hbound := (hmain (r⁻¹ • x)).2.mp hr.2
    rw [optimal_smul ns hns K hopt r⁻¹ (inv_pos.mpr hrpos) x] at hbound
    simpa only [mul_one] using (inv_mul_le_iff₀ hrpos).mp hbound

end SparseFormulaAux

theorem solution {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) :
    normC ns K x = ns (uVec K x) := by
  exact SparseFormulaAux.formula_of_main ns hns K
    (fun y => PermInvConvex.Sparsity.theorem_3_2 ns hns K hK hKn y) x
