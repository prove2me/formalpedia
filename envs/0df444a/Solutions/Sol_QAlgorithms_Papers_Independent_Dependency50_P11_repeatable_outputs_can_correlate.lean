-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P11.repeatable_outputs_can_correlate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:00:34.342995+00:00
-- url     : https://prove2.me/submissions/24a1fa5c-6ac3-4763-ba59-3609e049aca1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

set_option maxHeartbeats 1000000 in

/-- Section IV, PDF p.5: an explicit repeatable shared fair I/Z device correlates two
independent plus inputs. This witnesses "may"; no assertion about adaptive measurements
or complete process distance is made. -/
theorem solution :
    ∃ D : MemoryDevice 2 2,
      D.initial = totalMixture 2 ∧
      (D.unitary : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = sharedControlledZ ∧
      Repeatable D dephasingChannel ∧
      IsChannel dephasingChannel ∧
      IsDensityMatrix (signDensity false) ∧
      twoOutputState D (signDensity false) (signDensity false) = correlatedSigns ∧
      correlatedSigns ≠ Matrix.kronecker (dephasingChannel (signDensity false))
        (dephasingChannel (signDensity false)) := by
  have hU : sharedControlledZ ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext ⟨a, b⟩ ⟨c, e⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
      simp [sharedControlledZ, controlledFamily, qubitZ, pauliZ, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]
  have hI : IsDensityMatrix (totalMixture 2) := by
    refine ⟨Matrix.PosSemidef.one.smul (by rw [Complex.nonneg_iff]; norm_num), ?_⟩
    simp [totalMixture, Matrix.trace_smul]
  let D : MemoryDevice 2 2 :=
    { memory_pos := by norm_num
      unitary := ⟨sharedControlledZ, hU⟩
      initial := totalMixture 2
      initial_density := hI }
  have hjs : ∀ rho : Operator 2, jointStep D (totalMixture 2) rho =
      Matrix.of fun p q => if p.1 = q.1 then
        (2⁻¹ : ℂ) * (if p.1 = 0 then rho p.2 q.2 else (qubitZ * rho * qubitZᴴ) p.2 q.2) else 0 := by
    intro rho
    ext ⟨a, b⟩ ⟨c, e⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
      simp [D, jointStep, sharedControlledZ, controlledFamily, qubitZ, pauliZ, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kronecker, totalMixture,
        Matrix.conjTranspose_apply] <;> ring
  have hmem : ∀ input : ℕ → Operator 2, (∀ j, IsDensityMatrix (input j)) →
      ∀ j, memoryState D input j = totalMixture 2 := by
    intro input hin j
    induction j with
    | zero => rfl
    | succ j ih =>
      show traceRight (jointStep D (memoryState D input j) (input j)) = _
      rw [ih, hjs]
      have ht := (hin j).2
      simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag] at ht
      ext c c'
      fin_cases c <;> fin_cases c' <;>
        simp [traceRight, totalMixture, qubitZ, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.conjTranspose_apply] <;> linear_combination (2⁻¹ : ℂ) * ht
  have hrep : Repeatable D dephasingChannel := by
    intro n input hin j _
    show traceLeft (jointStep D (memoryState D input j) (input j)) = _
    rw [hmem input hin j, hjs]
    ext a a'
    fin_cases a <;> fin_cases a' <;>
      simp [traceLeft, dephasingChannel, Fin.sum_univ_two] <;> ring
  have hdeph : IsChannel dephasingChannel := by
    refine ⟨2, fun i => if i = 0 then ((Real.sqrt 2)⁻¹ : ℂ) • (1 : Operator 2)
      else ((Real.sqrt 2)⁻¹ : ℂ) • qubitZ, ?_, ?_⟩
    · have h2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
        rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
      unfold IsKrausFamily
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Fin.sum_univ_two, qubitZ, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.one_apply] <;> linear_combination h2 + h2
    · intro rho
      have h2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
        rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
      have hc2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = 2⁻¹ := by rw [sq]; exact h2
      unfold krausApply dephasingChannel
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Fin.sum_univ_two, qubitZ, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
        ring_nf <;> (try simp only [hc2]) <;> ring_nf
  refine ⟨D, rfl, rfl, hrep, hdeph, ?_, ?_, ?_⟩
  · have e : signDensity false = (2⁻¹ : ℂ) • Matrix.vecMulVec (fun _ : Fin 2 => (1 : ℂ))
        (star fun _ : Fin 2 => (1 : ℂ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [signDensity, Matrix.vecMulVec] <;> norm_num
    refine ⟨?_, ?_⟩
    · rw [e]
      exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by rw [Complex.nonneg_iff]; norm_num)
    · simp [Matrix.trace, Fin.sum_univ_two, signDensity]
  · let V : Fin 2 → Operator 2 := fun c => if c = 0 then 1 else qubitZ
    have hSC : ∀ p q : Fin 2 × (Fin 2 × Fin 2), secondCollision D p q =
        if p.1 = q.1 ∧ p.2.1 = q.2.1 then V p.1 p.2.2 q.2.2 else 0 := by
      intro p q
      by_cases h1 : p.2.1 = q.2.1 <;> by_cases h2 : p.1 = q.1 <;>
        simp [secondCollision, D, sharedControlledZ, controlledFamily, V, h1, h2]
    have hLa : ∀ (Y : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ) p q,
        (secondCollision D * Y) p q = ∑ b1, V p.1 p.2.2 b1 * Y (p.1, (p.2.1, b1)) q := by
      intro Y p q
      rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single p.1]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single p.2.1]
        · simp [hSC]
        · intro a _ ha; refine Finset.sum_eq_zero fun b _ => ?_; simp [hSC, Ne.symm ha]
        · simp
      · intro c _ hc
        refine Finset.sum_eq_zero fun r _ => ?_
        simp [hSC, Ne.symm hc]
      · simp
    have hLb : ∀ (Y : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ) p q,
        (Y * (secondCollision D)ᴴ) p q = ∑ b2, Y p (q.1, (q.2.1, b2)) * star (V q.1 q.2.2 b2) := by
      intro Y p q
      rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single q.1]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single q.2.1]
        · simp [hSC, Matrix.conjTranspose_apply]
        · intro a _ ha; refine Finset.sum_eq_zero fun b _ => ?_
          simp [hSC, Matrix.conjTranspose_apply, Ne.symm ha]
        · simp
      · intro c _ hc
        refine Finset.sum_eq_zero fun r _ => ?_
        simp [hSC, Matrix.conjTranspose_apply, Ne.symm hc]
      · simp
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [twoOutputState, traceLeft, Matrix.of_apply, hLb, hLa]
    have hD : D.initial = totalMixture 2 := rfl
    simp only [hD, hjs]
    fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
      simp [Fin.sum_univ_two, Matrix.kronecker, correlatedSigns, signDensity, V,
        qubitZ, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply] <;> norm_num
  · intro h
    have := congrFun (congrFun h (0, 0)) (1, 1)
    simp [correlatedSigns, signDensity, dephasingChannel, Matrix.kronecker, qubitZ, pauliZ,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at this


end

