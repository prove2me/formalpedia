-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P50.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:48:08.719706+00:00
-- url     : https://prove2.me/submissions/48315ac9-c60d-4eb8-a9bf-2a3659f98cdd

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50
noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set



attribute [local instance] Classical.propDecidable Classical.decEq

open scoped Matrix MatrixOrder

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Bridge50.P50

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)





lemma p5_comb (e mu : ℝ) (hmu : 0 < mu ∧ mu < 1-e)
    (M : ℕ) (hM : 0 < M) (p q : Fin M → ℝ) (hq0 : ∀ m, 0 ≤ q m) (hq1 : ∑ m, q m = 1)
    (hp : (1 - e) * M ≤ ∑ m, p m) (hp1 : ∀ m, p m ≤ 1) :
    ∃ m, 1 - (e + mu) ≤ p m ∧ M * mu * q m ≤ e + mu := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ m, p m < (1 - e - mu) + M * mu * q m := by
    intro m
    by_cases hg : 1 - (e + mu) ≤ p m
    · have := hcon m hg
      have := hp1 m
      linarith
    · push Not at hg
      have : 0 ≤ (M:ℝ) * mu * q m := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hmu.1.le) (hq0 m)
      linarith
  have hne : (Finset.univ : Finset (Fin M)).Nonempty := ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  have := Finset.sum_lt_sum_of_nonempty hne (fun m _ => hlt m)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq1] at this
  simp at this
  nlinarith

lemma p5_tr_nonneg {I : Type*} [Fintype I] [DecidableEq I] {P Q : Matrix I I ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace.re := by
  have hP0 : (0 : Matrix I I ℂ) ≤ P := by
    rw [Matrix.nonneg_iff_posSemidef]; exact hP
  set R := CFC.sqrt P
  have hRR : R * R = P := CFC.sqrt_mul_sqrt_self P hP0
  have hRH : R.IsHermitian := (CFC.sqrt_nonneg P).isSelfAdjoint
  have h1 : (P * Q).trace = (R.conjTranspose * Q * R).trace := by
    rw [← hRR, hRH.eq, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h2 := (hQ.conjTranspose_mul_mul_same R).trace_nonneg
  rw [h1]
  exact (Complex.nonneg_iff.mp h2).1

lemma p5_sum_psd {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ} (D : Fin M → Matrix I I ℂ)
    (hD : ∀ m, (D m).PosSemidef) (s : Finset (Fin M)) : (∑ m ∈ s, D m).PosSemidef := by
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (hD a).add ih

lemma p5_effect {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ} (D : Fin M → Matrix I I ℂ)
    (hD : ∀ m, (D m).PosSemidef) (hsum : ∑ m, D m = 1) (m : Fin M) :
    QAlgorithms.IsEffect (D m) := by
  refine ⟨hD m, ?_⟩
  have : 1 - D m = ∑ m' ∈ Finset.univ.erase m, D m' := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ m)]; abel
  rw [this]
  exact p5_sum_psd D hD _

theorem solution {X I : Type*} [Nonempty X] [Fintype I] [DecidableEq I] [Nonempty I]
    (W : X → Mat I) (hW : ∀ x, QAlgorithms.IsDensityMatrix (W x))
    (e mu : ℝ) (he : 0 < e ∧ e < 1) (hmu : 0 < mu ∧ mu < 1-e) :
    ENNReal.ofReal (logTwo (cqOptimalMessages W e)) ≤ testingRadius (Set.range W) (e+mu) +
      ENNReal.ofReal (logTwo ((e+mu)/(mu*(1-e-mu)))) := by
  by_cases hM0 : cqOptimalMessages W e = 0
  · rw [hM0]; simp [logTwo]
  have hmem : cqOptimalMessages W e ∈ {M | ∃ C : CqTransmissionCode X I M, cqAverageError W C ≤ e} := by
    apply Nat.sSup_mem
    · by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      apply hM0; unfold cqOptimalMessages; rw [hne]; simp
    · by_contra hb
      apply hM0; unfold cqOptimalMessages; exact Nat.sSup_of_not_bddAbove hb
  set M := cqOptimalMessages W e with hMdef
  obtain ⟨C, hC⟩ := hmem
  have hMpos : 0 < M := C.positive
  have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hMpos
  set δ := 1 - e - mu with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith [hmu.2]
  unfold testingRadius
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro sigma
  have hs := sigma.2
  let p : Fin M → ℝ := fun m => QAlgorithms.effectProb (C.decode m) (W (C.encode m))
  let q : Fin M → ℝ := fun m => QAlgorithms.effectProb (C.decode m) sigma.1
  have hq0 : ∀ m, 0 ≤ q m := fun m => p5_tr_nonneg (C.positiveDecode m) hs.1
  have hq1 : ∑ m, q m = 1 := by
    simp only [q, QAlgorithms.effectProb]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, C.complete, Matrix.one_mul, hs.2]
    simp
  have hp1 : ∀ m, p m ≤ 1 := by
    intro m
    have h1 := p5_tr_nonneg (p5_effect C.decode C.positiveDecode C.complete m).2 (hW (C.encode m)).1
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, (hW (C.encode m)).2, Complex.sub_re] at h1
    simp only [p, QAlgorithms.effectProb]
    simp at h1
    linarith
  have hp : (1 - e) * M ≤ ∑ m, p m := by
    unfold cqAverageError at hC
    have : (M:ℝ)⁻¹ * ∑ m, p m ≥ 1 - e := by simp only [p]; linarith
    rw [ge_iff_le, ← div_eq_inv_mul, le_div_iff₀ hMr] at this
    linarith
  obtain ⟨m, hpm, hqm⟩ := p5_comb e mu hmu M hMpos p q hq0 hq1 hp hp1
  let x := C.encode m
  have hfeas : q m ∈ {b | ∃ Q : Mat I, QAlgorithms.IsEffect Q ∧ 1 - (e + mu) ≤ QAlgorithms.effectProb Q (W x) ∧
      b = QAlgorithms.effectProb Q sigma.1} :=
    ⟨C.decode m, p5_effect C.decode C.positiveDecode C.complete m, hpm, rfl⟩
  have hbdd : BddBelow {b | ∃ Q : Mat I, QAlgorithms.IsEffect Q ∧ 1 - (e + mu) ≤ QAlgorithms.effectProb Q (W x) ∧
      b = QAlgorithms.effectProb Q sigma.1} := by
    refine ⟨0, ?_⟩
    rintro b ⟨Q, hQ, -, rfl⟩
    exact p5_tr_nonneg hQ.1 hs.1
  have hβle : testingBeta (e + mu) (W x) sigma.1 ≤ q m := csInf_le hbdd hfeas
  have hβ0 : 0 ≤ testingBeta (e + mu) (W x) sigma.1 := by
    apply le_csInf ⟨_, hfeas⟩
    rintro b ⟨Q, hQ, -, rfl⟩
    exact p5_tr_nonneg hQ.1 hs.1
  refine le_trans ?_ (add_le_add (le_iSup (fun rho : Set.range W => normalizedTestingDivergence (e + mu) rho.1 sigma.1) ⟨W x, ⟨x, rfl⟩⟩) le_rfl)
  unfold normalizedTestingDivergence
  simp only
  split_ifs with hb0
  · simp
  have hβpos : 0 < testingBeta (e + mu) (W x) sigma.1 := lt_of_le_of_ne hβ0 (Ne.symm hb0)
  set β := testingBeta (e + mu) (W x) sigma.1
  refine le_trans ?_ ENNReal.ofReal_add_le
  apply ENNReal.ofReal_le_ofReal
  have hδ' : 1 - (e + mu) = δ := by rw [hδ]; ring
  rw [hδ']
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold logTwo
  rw [← neg_div, ← add_div]
  apply div_le_div_of_nonneg_right _ hl2.le
  have hMβ : (M:ℝ) * β ≤ (e + mu) / mu := by
    rw [le_div_iff₀ hmu.1]; nlinarith
  have key : Real.log (M * (β / δ)) ≤ Real.log ((e + mu) / (mu * δ)) := by
    apply Real.log_le_log (mul_pos hMr (div_pos hβpos hδpos))
    rw [mul_div_assoc', div_le_div_iff₀ hδpos (mul_pos hmu.1 hδpos)]
    rw [le_div_iff₀ hmu.1] at hMβ
    nlinarith
  rw [Real.log_mul hMr.ne' (div_pos hβpos hδpos).ne'] at key
  linarith
