-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.selective_convex_implies_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:55:05.544404+00:00
-- url     : https://prove2.me/submissions/a1f24e80-50db-44a1-88eb-7f561684fa74

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P04
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.2–3: (C2b) and (C3) imply (C2a); no (C1) premise is required. -/
theorem gk_kraus_density {a d e : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : IsDensityMatrix rho) : IsDensityMatrix (krausApply K rho) := by
  refine ⟨?_, ?_⟩
  · unfold krausApply
    exact Matrix.posSemidef_sum _ (fun i _ => hrho.1.mul_mul_conjTranspose_same (K i))
  · unfold krausApply
    rw [Matrix.trace_sum]
    have : ∀ i, (K i * rho * (K i)ᴴ).trace = ((K i)ᴴ * K i * rho).trace := by
      intro i; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]
    exact hrho.2

theorem gk_psd_trace {e : ℕ} (X : Matrix (Fin e) (Fin e) ℂ) (hX : X.PosSemidef) :
    X.trace = ((X.trace.re : ℝ) : ℂ) ∧ 0 ≤ X.trace.re := by
  have h := hX.trace_nonneg
  rw [Complex.nonneg_iff] at h
  refine ⟨Complex.ext (by simp) (by simp [h.2]), h.1⟩

theorem gk_default_density {e : ℕ} (he : 0 < e) :
    IsDensityMatrix (Matrix.diagonal (Pi.single (⟨0, he⟩ : Fin e) (1 : ℂ))) := by
  refine ⟨Matrix.PosSemidef.diagonal ?_, ?_⟩
  · intro i
    by_cases h : i = ⟨0, he⟩
    · subst h; simp
    · simp [Pi.single_apply, h]
  · rw [Matrix.trace_diagonal]
    simp

theorem solution (C : (d : ℕ) → CoherenceMatrix d → ℝ)
    (hC : CoherenceNonnegative C)
    (hselective : CoherenceSelective C) (hconvex : CoherenceConvex C) :
    CoherenceMonotone C := by
  intro d e hd he a K hK rho hrho
  set p : Fin a → ℝ := fun i => branchProbability (K i) rho with hpdef
  have hXpsd : ∀ i, (conjSuperop (K i) rho).PosSemidef :=
    fun i => hrho.1.mul_mul_conjTranspose_same (K i)
  have htr : ∀ i, (conjSuperop (K i) rho).trace = ((p i : ℝ) : ℂ) :=
    fun i => (gk_psd_trace _ (hXpsd i)).1
  have hp0 : ∀ i, 0 ≤ p i := fun i => (gk_psd_trace _ (hXpsd i)).2
  have hkd := gk_kraus_density K hK.1 rho hrho
  have hp : Learning.IsDistribution p := by
    refine ⟨hp0, ?_⟩
    have h2 := hkd.2
    unfold krausApply at h2
    rw [Matrix.trace_sum] at h2
    have : ∀ i, (K i * rho * (K i)ᴴ).trace = ((p i : ℝ) : ℂ) := htr
    simp_rw [this] at h2
    exact_mod_cast h2
  set tau := Matrix.diagonal (Pi.single (⟨0, he⟩ : Fin e) (1 : ℂ))
  have htau : IsDensityMatrix tau := gk_default_density he
  set sigma : Fin a → CoherenceMatrix e := fun i =>
    if 0 < p i then ((p i)⁻¹ : ℂ) • conjSuperop (K i) rho else tau with hsig
  have hsigma : ∀ i, IsDensityMatrix (sigma i) := by
    intro i
    by_cases hi : 0 < p i
    · simp only [hsig, if_pos hi]
      refine ⟨(hXpsd i).smul ?_, ?_⟩
      · have : (0 : ℝ) ≤ (p i)⁻¹ := inv_nonneg.2 hi.le
        exact_mod_cast this
      · rw [Matrix.trace_smul, htr i, smul_eq_mul]
        have : (p i : ℂ) ≠ 0 := by exact_mod_cast hi.ne'
        field_simp
    · simp only [hsig, if_neg hi]; exact htau
  have hzero : ∀ i, ¬ 0 < p i → conjSuperop (K i) rho = 0 := by
    intro i hi
    have : p i = 0 := le_antisymm (not_lt.1 hi) (hp0 i)
    apply ((hXpsd i).trace_eq_zero_iff).1
    rw [htr i, this]; simp
  have hmix : ensembleMixture p sigma = krausApply K rho := by
    unfold ensembleMixture krausApply
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < p i
    · simp only [hsig, if_pos hi, smul_smul]
      have : (p i : ℂ) ≠ 0 := by exact_mod_cast hi.ne'
      rw [mul_inv_cancel₀ this, one_smul]
      rfl
    · have h0 : p i = 0 := le_antisymm (not_lt.1 hi) (hp0 i)
      have := hzero i hi
      simp only [conjSuperop] at this
      rw [this, h0]; simp
  have hconv := hconvex e he a p sigma hp hsigma
  have hsel := hselective d hd a (fun _ => e) (fun _ => he) K hK rho hrho
  rw [hmix] at hconv
  have hsum : ∑ i, p i * C e (sigma i) = ∑ i, selectiveContribution C (K i) rho := by
    apply Finset.sum_congr rfl
    intro i _
    unfold selectiveContribution
    by_cases hi : 0 < p i
    · simp only [hsig, if_pos hi]
      simp only [hpdef] at hi ⊢
      rw [if_pos hi]
    · have h0 : p i = 0 := le_antisymm (not_lt.1 hi) (hp0 i)
      simp only [hpdef] at hi h0 ⊢
      rw [if_neg hi, h0, zero_mul]
  linarith

