-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P97.bound_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:52:16.460082+00:00
-- url     : https://prove2.me/submissions/ecdc9deb-c4b4-4096-86ec-785502511523

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P97

noncomputable section

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Intakenext100.P97 in
theorem solution {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    MonotoneOn (cloningBound N M f) (Set.Icc (f ^ M) 1) ∧
    cloningBound N M f (f ^ M) = 0 ∧
    (∀ phi ∈ Set.Icc (f ^ M) 1,
      0 ≤ cloningBound N M f phi ∧ cloningBound N M f phi ≤ cloningBound N M f 1) ∧
    cloningBound 1 1 f 1 = standardBound f := by
  have hfM0 : 0 ≤ f ^ M := pow_nonneg hf0 M
  have hmono : MonotoneOn (cloningBound N M f) (Set.Icc (f ^ M) 1) := by
    intro a ha b hb hab
    unfold cloningBound
    have ha0 : 0 ≤ a := le_trans hfM0 ha.1
    have h1 : f ^ (2 * N) * a ^ 2 ≤ f ^ (2 * N) * b ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 hab 2) (pow_nonneg hf0 _)
    have h2 : Real.sqrt (1 - f ^ (2 * N) * b ^ 2) ≤ Real.sqrt (1 - f ^ (2 * N) * a ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have h3 : f ^ (N + M) * Real.sqrt (1 - f ^ (2 * N) * b ^ 2) ≤
        f ^ (N + M) * Real.sqrt (1 - f ^ (2 * N) * a ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (pow_nonneg hf0 _)
    have h4 := div_le_div_of_nonneg_right h3 (Real.sqrt_nonneg (1 - f ^ (2 * (N + M))))
    have h5 : f ^ N * a ≤ f ^ N * b := mul_le_mul_of_nonneg_left hab (pow_nonneg hf0 _)
    linarith
  have hlt : f ^ (2 * (N + M)) < 1 := pow_lt_one₀ hf0 hf1 (by omega)
  have hpos : 0 < Real.sqrt (1 - f ^ (2 * (N + M))) := Real.sqrt_pos.mpr (by linarith)
  have hend : cloningBound N M f (f ^ M) = 0 := by
    unfold cloningBound
    rw [show f ^ (2 * N) * (f ^ M) ^ 2 = f ^ (2 * (N + M)) by ring, mul_div_assoc,
      div_self hpos.ne', mul_one]
    ring
  have hMmem : f ^ M ∈ Set.Icc (f ^ M) 1 := ⟨le_rfl, pow_le_one₀ hf0 hf1.le⟩
  have h1mem : (1 : ℝ) ∈ Set.Icc (f ^ M) 1 := ⟨pow_le_one₀ hf0 hf1.le, le_rfl⟩
  refine ⟨hmono, hend, fun phi hphi => ⟨?_, hmono hphi h1mem hphi.2⟩, ?_⟩
  · rw [← hend]; exact hmono hMmem hphi hphi.1
  · unfold cloningBound standardBound
    have hA : 0 < 1 - f ^ (2 * 1) * 1 ^ 2 := by
      rw [show f ^ (2 * 1) * (1 : ℝ) ^ 2 = f * f by ring]; nlinarith
    have hsA : Real.sqrt (1 - f ^ (2 * 1) * 1 ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
    have e : Real.sqrt (1 - f ^ (2 * (1 + 1))) =
        Real.sqrt (1 + f ^ 2) * Real.sqrt (1 - f ^ (2 * 1) * 1 ^ 2) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      ring
    rw [e, mul_div_mul_right _ _ hsA]
    ring
