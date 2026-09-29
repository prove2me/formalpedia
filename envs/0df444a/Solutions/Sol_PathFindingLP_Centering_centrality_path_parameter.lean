-- Prove2me | solution 1 for PathFindingLP.Centering.centrality_path_parameter
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:39:05.021062+00:00
-- url     : https://prove2.me/submissions/d78191bb-4f5d-4f90-9b83-c501ab3fdd4e

import Mathlib
import Definitions.Def_PathFindingLP_Centering_SlackSensitivity
import Definitions.Def_PathFindingLP_Centering_WeightedCentralPath

open Matrix


namespace PathFindingLP.Centering

lemma pf_inj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) :
    Function.Injective A.mulVec := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 : Module.finrank ℝ (LinearMap.range A.mulVecLin) = n := hA
  rw [h2, Module.finrank_fin_fun] at h1
  have h3 : LinearMap.ker A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  exact LinearMap.ker_eq_bot.mp h3

lemma pf_quad {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) (u v : Fin n → ℝ) :
    u ⬝ᵥ (weightedGram A s w *ᵥ v) =
      ∑ i, w i * ((A *ᵥ u) i / s i) * ((A *ᵥ v) i / s i) := by
  unfold weightedGram
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]
  simp only [mulVec_diagonal, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]; ring

lemma pf_cs {m : ℕ} (w X Y : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * X i * Y i) ^ 2 ≤ (∑ i, w i * X i * X i) * (∑ i, w i * Y i * Y i) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i) * X i)
    (fun i => Real.sqrt (w i) * Y i)
  have e : ∀ i, Real.sqrt (w i) * Real.sqrt (w i) = w i := fun i => Real.mul_self_sqrt (hw i)
  have e1 : ∑ i, w i * X i * Y i = ∑ i, Real.sqrt (w i) * X i * (Real.sqrt (w i) * Y i) :=
    Finset.sum_congr rfl fun i _ => by linear_combination (-(X i * Y i)) * e i
  have e2 : ∑ i, w i * X i * X i = ∑ i, (Real.sqrt (w i) * X i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by linear_combination (-(X i ^ 2)) * e i
  have e3 : ∑ i, w i * Y i * Y i = ∑ i, (Real.sqrt (w i) * Y i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by linear_combination (-(Y i ^ 2)) * e i
  rw [e1, e2, e3]; exact this

lemma pf_cs_abs {m : ℕ} (w X Y : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |∑ i, w i * X i * Y i| ≤
      Real.sqrt (∑ i, w i * X i * X i) * Real.sqrt (∑ i, w i * Y i * Y i) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => by
    have := hw i; have := mul_self_nonneg (X i); nlinarith)]
  apply Real.abs_le_sqrt
  exact pf_cs w X Y hw

lemma pf_nonneg {m : ℕ} (w X : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ ∑ i, w i * X i * X i :=
  Finset.sum_nonneg fun i _ => by have := hw i; have := mul_self_nonneg (X i); nlinarith

lemma pf_tri {m : ℕ} (w X Y : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Real.sqrt (∑ i, w i * (X i + Y i) * (X i + Y i)) ≤
      Real.sqrt (∑ i, w i * X i * X i) + Real.sqrt (∑ i, w i * Y i * Y i) := by
  have ha := pf_nonneg w X hw
  have hb := pf_nonneg w Y hw
  have hc := le_trans (le_abs_self _) (pf_cs_abs w X Y hw)
  have e : ∑ i, w i * (X i + Y i) * (X i + Y i) =
      (∑ i, w i * X i * X i) + 2 * (∑ i, w i * X i * Y i) + ∑ i, w i * Y i * Y i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [e]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith

lemma pf_smul {m : ℕ} (w X : Fin m → ℝ) (c : ℝ) :
    Real.sqrt (∑ i, w i * (c * X i) * (c * X i)) = |c| * Real.sqrt (∑ i, w i * X i * X i) := by
  have e : ∑ i, w i * (c * X i) * (c * X i) = c ^ 2 * ∑ i, w i * X i * X i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma pf_unit {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (s w : Fin m → ℝ)
    (hs : ∀ i, 0 < s i) (hw : ∀ i, 0 < w i) : IsUnit (weightedGram A s w) := by
  rw [← mulVec_injective_iff_isUnit]
  intro u v huv
  have hsub : weightedGram A s w *ᵥ (u - v) = 0 := by rw [mulVec_sub, huv, sub_self]
  have hq := pf_quad A s w (u - v) (u - v)
  rw [hsub, dotProduct_zero] at hq
  have hz : ∀ i, (A *ᵥ (u - v)) i = 0 := by
    intro i
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
      have := hw j; have := mul_self_nonneg ((A *ᵥ (u - v)) j / s j); nlinarith)).mp
        hq.symm i (Finset.mem_univ _)
    have h1 : (A *ᵥ (u - v)) i / s i * ((A *ᵥ (u - v)) i / s i) = 0 := by
      rw [mul_assoc] at hterm
      exact (mul_eq_zero.mp hterm).resolve_left (hw i).ne'
    have h2 := mul_self_eq_zero.mp h1
    rwa [div_eq_zero_iff, or_iff_left (hs i).ne'] at h2
  have h3 : A *ᵥ (u - v) = A *ᵥ 0 := by ext i; simp [hz i]
  exact sub_eq_zero.mp (pf_inj A hA h3)

lemma pf_inv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (s w : Fin m → ℝ)
    (hs : ∀ i, 0 < s i) (hw : ∀ i, 0 < w i) (v : Fin n → ℝ) :
    weightedGram A s w *ᵥ ((weightedGram A s w)⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (pf_unit A hA s w hs hw)),
    one_mulVec]

lemma pf_mn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) (v : Fin n → ℝ) :
    matNorm (weightedGram A s w) v =
      Real.sqrt (∑ i, w i * ((A *ᵥ v) i / s i) * ((A *ᵥ v) i / s i)) := by
  rw [matNorm, pf_quad]

lemma pf_mn_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i)
    (u v : Fin n → ℝ) :
    matNorm (weightedGram A s w) (u + v) ≤
      matNorm (weightedGram A s w) u + matNorm (weightedGram A s w) v := by
  simp only [pf_mn]
  have e : ∀ i, (A *ᵥ (u + v)) i / s i = (A *ᵥ u) i / s i + (A *ᵥ v) i / s i := by
    intro i; rw [mulVec_add, Pi.add_apply, add_div]
  simp_rw [e]
  exact pf_tri w (fun i => (A *ᵥ u) i / s i) (fun i => (A *ᵥ v) i / s i) hw

lemma pf_mn_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) (c : ℝ)
    (v : Fin n → ℝ) :
    matNorm (weightedGram A s w) (c • v) = |c| * matNorm (weightedGram A s w) v := by
  simp only [pf_mn]
  have e : ∀ i, (A *ᵥ (c • v)) i / s i = c * ((A *ᵥ v) i / s i) := by
    intro i; rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]
  simp_rw [e]
  exact pf_smul w (fun i => (A *ᵥ v) i / s i) c

theorem cpp_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n) (x : Fin n → ℝ) (w : Fin m → ℝ)
    (hxw : IsFeasible A b x w) (α t : ℝ) (hα : 0 ≤ α) (ht : 0 ≤ t) :
    centrality A b c ((1 + α) * t) x w ≤
      (1 + α) * centrality A b c t x w + α * Real.sqrt (∑ i, |w i|) := by
  obtain ⟨hx, hw⟩ := hxw
  have hs : ∀ i, 0 < slack A b x i := hx
  have hwn : ∀ i, 0 ≤ w i := fun i => (hw i).le
  obtain ⟨s, hsd⟩ : ∃ s, s = slack A b x := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = weightedGram A s w := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin n → ℝ, q = Aᵀ *ᵥ (diagonal (fun i => (s i)⁻¹) *ᵥ w) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = H⁻¹ *ᵥ q := ⟨_, rfl⟩
  have hsplit : newtonStep A b c ((1+α)*t) x w = (1+α) • newtonStep A b c t x w + α • k := by
    unfold newtonStep weightedGradient
    rw [hk, hH, hq, hsd, ← mulVec_smul, ← mulVec_smul, ← mulVec_add]
    congr 1
    ext j; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  unfold centrality
  rw [hsplit, ← hsd, ← hH]
  have hkb : matNorm H k ≤ Real.sqrt (∑ i, |w i|) := by
    have hs' : ∀ i, 0 < s i := by rw [hsd]; exact hs
    have hHk : H *ᵥ k = q := by rw [hk, hH]; exact pf_inv A hA s w hs' hw q
    have hT := pf_quad A s w k k
    rw [← hH, hHk] at hT
    have hT2 : k ⬝ᵥ q = ∑ i, w i * ((A *ᵥ k) i / s i) * 1 := by
      rw [hq, dotProduct_mulVec, vecMul_transpose]
      simp only [mulVec_diagonal, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_eq_mul_inv]; ring
    have hcs := pf_cs w (fun i => (A *ᵥ k) i / s i) (fun _ => 1) hwn
    rw [← hT2, ← hT] at hcs
    have hT0 : 0 ≤ k ⬝ᵥ q := by rw [hT]; exact pf_nonneg w _ hwn
    have hle : k ⬝ᵥ q ≤ ∑ i, |w i| := by
      have e : ∑ i, w i * 1 * 1 = ∑ i, |w i| :=
        Finset.sum_congr rfl fun i _ => by rw [abs_of_pos (hw i)]; ring
      rw [e] at hcs
      rcases hT0.lt_or_eq with h | h
      · nlinarith
      · rw [← h]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [matNorm, hHk]
    exact Real.sqrt_le_sqrt hle
  calc matNorm H ((1 + α) • newtonStep A b c t x w + α • k)
      ≤ matNorm H ((1 + α) • newtonStep A b c t x w) + matNorm H (α • k) := by
        rw [hH]; exact pf_mn_add A s w hwn _ _
    _ = (1 + α) * matNorm H (newtonStep A b c t x w) + α * matNorm H k := by
        rw [hH, pf_mn_smul, pf_mn_smul, abs_of_nonneg (by linarith), abs_of_nonneg hα]
    _ ≤ _ := by gcongr

end PathFindingLP.Centering

open PathFindingLP.Centering


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n) (x : Fin n → ℝ) (w : Fin m → ℝ)
    (hxw : IsFeasible A b x w) (α t : ℝ) (hα : 0 ≤ α) (ht : 0 ≤ t) :
    centrality A b c ((1 + α) * t) x w ≤
      (1 + α) * centrality A b c t x w + α * Real.sqrt (∑ i, |w i|) := by
  exact cpp_core A b c hA x w hxw α t hα ht
