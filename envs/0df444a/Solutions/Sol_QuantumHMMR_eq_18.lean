-- Prove2me | solution 1 for QuantumHMMR.eq_18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T20:34:46.327081+00:00
-- url     : https://prove2.me/submissions/fc4028d0-eabf-4118-a60d-0d95c35b18a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Theorems.Thm_QuantumHMMR_lemma_4_3
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QuantumHMMR_IsAcceptanceMatrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_QuantumHMMR_stepLaw
import Definitions.Def_QuantumHMMR_walkLaw
import Definitions.Def_QuantumHMMR_IsCliffordGenSet
import Theorems.Thm_QuantumHMMR_eq_16
import Theorems.Thm_QuantumHMMR_eq_17


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000

open scoped Matrix ComplexConjugate BigOperators

namespace PRUSpectral

/-- Powers after removing an absorbing projection. -/
lemma sub_projection_pow {R : Type*} [Ring R] (M P : R)
    (hMP : M * P = P) (hPM : P * M = P) (hPP : P * P = P) :
    ∀ j : ℕ, 1 ≤ j → (M - P) ^ j = M ^ j - P := by
  have hMPall : ∀ j : ℕ, M ^ j * P = P := by
    intro j
    induction j with
    | zero => simp
    | succ j ihj => rw [pow_succ, mul_assoc, hMP, ihj]
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>

    rw [pow_succ, ih, sub_mul, mul_sub, mul_sub, hMPall j, hPM, hPP, pow_succ]
    abel

/-- The coefficients in the trace-power expansion in an eigenbasis. -/
lemma trace_power_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B X : Matrix ι ι ℂ) (hB : B.IsHermitian) (j : ℕ) :
    (X * B ^ j).trace =
      ∑ i, ((star (hB.eigenvectorUnitary : Matrix ι ι ℂ)) * X *
        (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i i * (hB.eigenvalues i : ℂ) ^ j := by
  have hpow : B ^ j = Unitary.conjStarAlgAut ℂ _ hB.eigenvectorUnitary
      (Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ) ^ j)) := by
    conv_lhs => rw [hB.spectral_theorem, ← map_pow]
    congr 1
    simp only [Matrix.diagonal_pow, Function.comp_def]
    rfl
  rw [hpow, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [← Matrix.mul_assoc, Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]

/-- The part supported on eigenvalues at most eta has the expected geometric bound. -/
lemma tail_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b lam : ι → ℂ) (S : Finset ι) (η W : ℝ) (hη : 0 ≤ η)
    (hlam : ∀ i ∉ S, ‖lam i‖ ≤ η) (hW : ∑ i, ‖b i‖ ≤ W) (j : ℕ) :
    ‖(∑ i, b i * lam i ^ j) - ∑ i ∈ S, b i * lam i ^ j‖ ≤ W * η ^ j := by
  classical
  have heq : (∑ i, b i * lam i ^ j) - ∑ i ∈ S, b i * lam i ^ j =
      ∑ i ∈ Finset.univ \ S, b i * lam i ^ j := by
    exact (eq_sub_iff_add_eq.mpr (Finset.sum_sdiff (Finset.subset_univ S))).symm
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.univ \ S, ‖b i * lam i ^ j‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.univ \ S, ‖b i‖ * ‖lam i‖ ^ j := by simp only [norm_mul, norm_pow]
    _ ≤ ∑ i ∈ Finset.univ \ S, ‖b i‖ * η ^ j := by
      apply Finset.sum_le_sum
      intro i hi
      have hiS := (Finset.mem_sdiff.mp hi).2
      gcongr
      exact hlam i hiS
    _ = (∑ i ∈ Finset.univ \ S, ‖b i‖) * η ^ j := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ‖b i‖) * η ^ j := by
      gcongr
      exact Finset.sdiff_subset
    _ ≤ W * η ^ j := mul_le_mul_of_nonneg_right hW (by positivity)

/-- The power-sum estimate remains valid with an upper bound on the number of roots. -/
lemma power_sum_cap (k D : ℕ) (hk : 1 ≤ k) (hkD : k ≤ D)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (b lam : Fin k → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ ρ) (B : ℝ)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ k → ‖∑ i, b i * lam i ^ j‖ ≤ B)
    (j : ℕ) (hj : D ≤ j) :
    ‖∑ i, b i * lam i ^ j‖ ≤ B * D * 2 ^ D *
      ((j + D - 2).choose (D - 1) : ℝ) * ρ ^ (j - D) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 le_rfl hk)
  have hchoose : (j + k - 2).choose (k - 1) ≤ (j + D - 2).choose (D - 1) := by
    have he1 : j + k - 2 - (k - 1) = j - 1 := by omega
    have he2 : j + D - 2 - (D - 1) = j - 1 := by omega
    rw [← Nat.choose_symm (by omega : k - 1 ≤ j + k - 2), he1,
      ← Nat.choose_symm (by omega : D - 1 ≤ j + D - 2), he2]
    exact Nat.choose_le_choose _ (by omega)
  have hp : ρ ^ (j - k) ≤ ρ ^ (j - D) :=
    pow_le_pow_of_le_one (le_of_lt hρ0) (le_of_lt hρ1) (by omega)
  apply (QuantumHMMR.lemma_4_3 k hk ρ hρ0 hρ1 b lam hlam B hB j (by omega)).trans
  gcongr
  norm_num

/-- A power-sum estimate on any finite set of at most D indices. -/
lemma subset_power_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b lam : ι → ℂ) (S : Finset ι) (D : ℕ) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hlam : ∀ i ∈ S, ‖lam i‖ ≤ ρ)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ D → ‖∑ i ∈ S, b i * lam i ^ j‖ ≤ B)
    (j : ℕ) (hj : D ≤ j) :
    ‖∑ i ∈ S, b i * lam i ^ j‖ ≤ B * D * 2 ^ D *
      ((j + D - 2).choose (D - 1) : ℝ) * ρ ^ (j - D) := by
  classical
  by_cases hS : S.Nonempty
  · let k : ℕ := Fintype.card S
    let e : Fin k ≃ S := (Fintype.equivFin S).symm
    have hk : 1 ≤ k := by
      change 0 < Fintype.card S
      simpa only [Fintype.card_coe] using hS.card_pos
    have hkD : k ≤ D := by simpa only [k, Fintype.card_coe] using hSD
    have heq (r : ℕ) : (∑ i : Fin k, b (e i) * lam (e i) ^ r) =
        ∑ i ∈ S, b i * lam i ^ r := by
      calc
        _ = ∑ i : S, b i * lam i ^ r := Fintype.sum_equiv e _ _ (fun _ => rfl)
        _ = _ := Finset.sum_coe_sort S (fun i => b i * lam i ^ r)
    have h := power_sum_cap k D hk hkD ρ hρ0 hρ1
      (fun i => b (e i)) (fun i => lam (e i)) (fun i => hlam (e i) (e i).property) B
      (fun r hr hrk => by rw [heq]; exact hB r hr (hrk.trans hkD)) j hj
    simpa only [heq] using h
  · have hs0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hs0, Finset.sum_empty, norm_zero]
    positivity

/-- Combining the slow roots with a bounded fast tail. -/
lemma split_power_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b lam : ι → ℂ) (S : Finset ι) (D : ℕ) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (ρ η W ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hslow : ∀ i ∈ S, ‖lam i‖ ≤ ρ) (hfast : ∀ i ∉ S, ‖lam i‖ ≤ η)
    (hW : ∑ i, ‖b i‖ ≤ W)
    (hinitial : ∀ j : ℕ, 1 ≤ j → j ≤ D → ‖∑ i, b i * lam i ^ j‖ ≤ 1)
    (htail : ∀ j : ℕ, 1 ≤ j → W * η ^ j ≤ ε)
    (j : ℕ) (hj : D ≤ j) :
    ‖∑ i, b i * lam i ^ j‖ ≤ (1 + ε) * D * 2 ^ D *
      ((j + D - 2).choose (D - 1) : ℝ) * ρ ^ (j - D) + ε := by
  have htail' (r : ℕ) (hr : 1 ≤ r) :
      ‖(∑ i, b i * lam i ^ r) - ∑ i ∈ S, b i * lam i ^ r‖ ≤ ε :=
    (tail_bound b lam S η W hη hfast hW r).trans (htail r hr)
  have hinit : ∀ r : ℕ, 1 ≤ r → r ≤ D → ‖∑ i ∈ S, b i * lam i ^ r‖ ≤ 1 + ε := by
    intro r hr hrD
    have heq : (∑ i ∈ S, b i * lam i ^ r) =
        (∑ i, b i * lam i ^ r) - ((∑ i, b i * lam i ^ r) - ∑ i ∈ S, b i * lam i ^ r) := by abel
    calc
      _ = _ := congrArg norm heq
      _ ≤ _ := norm_sub_le _ _
      _ ≤ 1 + ε := add_le_add (hinitial r hr hrD) (htail' r hr)
  have hslow' := subset_power_sum_bound b lam S D hD hSD ρ hρ0 hρ1 hslow
    (1 + ε) (by positivity) hinit j hj
  have heq : (∑ i, b i * lam i ^ j) = (∑ i ∈ S, b i * lam i ^ j) +
      ((∑ i, b i * lam i ^ j) - ∑ i ∈ S, b i * lam i ^ j) := by abel
  calc
    _ = _ := congrArg norm heq
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hslow' (htail' j (hD.trans hj))

/-- The eigenbasis supplied by the spectral theorem gives genuine eigenvalues
for the ordinary matrix linear map used in the paper's target. -/
lemma has_eigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (i : ι) :
    Module.End.HasEigenvalue (Matrix.toLin' B) (hB.eigenvalues i : ℂ) := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin',
    hB.spectrum_eq_image_range]
  exact ⟨hB.eigenvalues i, ⟨i, rfl⟩, rfl⟩

/-- The matrix form of the slow/fast expansion, including multiplicities
and the fact that every slow mode is a genuine eigenvalue. -/
theorem spectral_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B X : Matrix ι ι ℂ) (hB : B.IsHermitian) (D : ℕ)
    (ρ η W : ℝ) (hη : 0 ≤ η)
    (hρ : ∀ i, |hB.eigenvalues i| ≤ ρ)
    (hcount : (Finset.univ.filter fun i => η < |hB.eigenvalues i|).card ≤ D)
    (hW : ∑ i, ‖((star (hB.eigenvectorUnitary : Matrix ι ι ℂ)) * X *
      (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i i‖ ≤ W) :
    ∃ k ≤ D, ∃ b lam : Fin k → ℂ,
      (∀ i, Module.End.HasEigenvalue (Matrix.toLin' B) (lam i) ∧
        η < ‖lam i‖ ∧ ‖lam i‖ ≤ ρ) ∧
      ∀ j : ℕ, ‖(X * B ^ j).trace - ∑ i, b i * lam i ^ j‖ ≤ W * η ^ j := by
  classical
  let S : Finset ι := Finset.univ.filter fun i => η < |hB.eigenvalues i|
  let k : ℕ := Fintype.card S
  let e : Fin k ≃ S := (Fintype.equivFin S).symm
  let c : ι → ℂ := fun i => ((star (hB.eigenvectorUnitary : Matrix ι ι ℂ)) * X *
    (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i i
  let lam : ι → ℂ := fun i => hB.eigenvalues i
  have hk : k ≤ D := by simpa only [k, Fintype.card_coe] using hcount
  refine ⟨k, hk, (fun i => c (e i)), (fun i => lam (e i)), ?_, ?_⟩
  · intro i
    have hi := (Finset.mem_filter.mp (e i).property).2
    refine ⟨has_eigenvalue B hB (e i), ?_, ?_⟩
    · simpa only [lam, Complex.norm_real, Real.norm_eq_abs] using hi
    · simpa only [lam, Complex.norm_real, Real.norm_eq_abs] using hρ (e i)
  · intro j
    have heq : (∑ i : Fin k, c (e i) * lam (e i) ^ j) = ∑ i ∈ S, c i * lam i ^ j := by
      calc
        _ = ∑ i : S, c i * lam i ^ j := Fintype.sum_equiv e _ _ (fun _ => rfl)
        _ = _ := Finset.sum_coe_sort S (fun i => c i * lam i ^ j)
    rw [heq, trace_power_expansion B X hB]
    apply tail_bound c lam S η W hη _ hW j
    intro i hi
    have hi' : ¬ η < |hB.eigenvalues i| := by simpa only [S, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
    simpa only [lam, Complex.norm_real, Real.norm_eq_abs] using le_of_not_gt hi'

/-- The analytic estimate in Eq. (18), after supplying a bound on the
absolute diagonal coefficients in the eigenbasis. -/
theorem trace_power_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B X : Matrix ι ι ℂ) (hB : B.IsHermitian) (D : ℕ) (hD : 1 ≤ D)
    (ρ η W ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hρ : ∀ i, |hB.eigenvalues i| ≤ ρ)
    (hcount : (Finset.univ.filter fun i => η < |hB.eigenvalues i|).card ≤ D)
    (hW : ∑ i, ‖((star (hB.eigenvectorUnitary : Matrix ι ι ℂ)) * X *
      (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i i‖ ≤ W)
    (hinitial : ∀ j : ℕ, 1 ≤ j → j ≤ D → ‖(X * B ^ j).trace‖ ≤ 1)
    (htail : ∀ j : ℕ, 1 ≤ j → W * η ^ j ≤ ε)
    (j : ℕ) (hj : D ≤ j) :
    ‖(X * B ^ j).trace‖ ≤ (1 + ε) * D * 2 ^ D *
      ((j + D - 2).choose (D - 1) : ℝ) * ρ ^ (j - D) + ε := by
  classical
  let S : Finset ι := Finset.univ.filter fun i => η < |hB.eigenvalues i|
  let c : ι → ℂ := fun i => ((star (hB.eigenvectorUnitary : Matrix ι ι ℂ)) * X *
    (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i i
  let lam : ι → ℂ := fun i => hB.eigenvalues i
  rw [trace_power_expansion B X hB]
  apply split_power_sum_bound c lam S D hD hcount ρ η W ε hρ0 hρ1 hη hε _ _ hW _ htail j hj
  · intro i _
    simpa only [lam, Complex.norm_real, Real.norm_eq_abs] using hρ i
  · intro i hi
    have hi' : ¬ η < |hB.eigenvalues i| := by simpa only [S, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
    simpa only [lam, Complex.norm_real, Real.norm_eq_abs] using le_of_not_gt hi'
  · intro r hr hrD
    simpa only [trace_power_expansion B X hB, c, lam] using hinitial r hr hrD

end PRUSpectral



set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

open scoped Matrix ComplexConjugate BigOperators

namespace PRUTraceNorm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma column_norm_sq (X : Matrix ι ι ℂ) (k : ι) :
    ∑ i, ‖X i k‖ ^ 2 = ((Xᴴ * X) k k).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
    Complex.normSq_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma trace_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * X * star (U : Matrix ι ι ℂ)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

/-- The trace of the functional calculus is the sum of its spectral values. -/
lemma trace_cfc (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace.re = ∑ i, f (hX.eigenvalues i) := by
  rw [hX.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    trace_unitary_conj]
  simp [Matrix.trace, Function.comp_def]

/-- The sum of absolute diagonal entries is bounded by the trace norm. -/
theorem diagonal_le_traceNorm (X : Matrix ι ι ℂ) :
    ∑ i, ‖X i i‖ ≤ (cfc Real.sqrt (Xᴴ * X)).trace.re := by
  classical
  let hG : (Xᴴ * X).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self X
  let V : Matrix.unitaryGroup ι ℂ := hG.eigenvectorUnitary
  let C : Matrix ι ι ℂ := X * (V : Matrix ι ι ℂ)
  have hdiag : Cᴴ * C = Matrix.diagonal (fun k => (hG.eigenvalues k : ℂ)) := by
    have h := hG.conjStarAlgAut_star_eigenvectorUnitary
    simpa only [C, V, Matrix.conjTranspose_mul, Unitary.conjStarAlgAut_star_apply,
      Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Function.comp_def] using! h
  have hC (k : ι) : ∑ i, ‖C i k‖ ^ 2 = hG.eigenvalues k := by
    rw [column_norm_sq, hdiag]
    simp
  have hV (k : ι) : ∑ i, ‖(V : Matrix ι ι ℂ) i k‖ ^ 2 = 1 := by
    rw [column_norm_sq]
    change ((star (V : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)) k k).re = 1
    rw [Unitary.coe_star_mul_self]
    simp
  have hX : C * star (V : Matrix ι ι ℂ) = X := by
    dsimp [C]
    rw [Matrix.mul_assoc]
    simp
  calc
    ∑ i, ‖X i i‖ = ∑ i, ‖∑ k, C i k * star ((V : Matrix ι ι ℂ) i k)‖ := by
      conv_lhs => rw [← hX]
      simp only [Matrix.mul_apply, Matrix.star_apply]
    _ ≤ ∑ i, ∑ k, ‖C i k‖ * ‖(V : Matrix ι ι ℂ) i k‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_mul, norm_star] using
        norm_sum_le (Finset.univ : Finset ι) (fun k => C i k * star ((V : Matrix ι ι ℂ) i k))
    _ = ∑ k, ∑ i, ‖C i k‖ * ‖(V : Matrix ι ι ℂ) i k‖ := Finset.sum_comm
    _ ≤ ∑ k, Real.sqrt (hG.eigenvalues k) := by
      apply Finset.sum_le_sum
      intro k _
      have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun i => ‖C i k‖) (fun i => ‖(V : Matrix ι ι ℂ) i k‖)
      simpa only [hC, hV, Real.sqrt_one, mul_one] using h
    _ = (cfc Real.sqrt (Xᴴ * X)).trace.re := (trace_cfc _ hG _).symm

/-- Unitary conjugation preserves the trace norm, including singular matrices. -/
lemma traceNorm_unitary_conj (X : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    let Y := star (U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)
    (cfc Real.sqrt (Yᴴ * Y)).trace.re = (cfc Real.sqrt (Xᴴ * X)).trace.re := by
  dsimp only
  let Y := star (U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)
  let hG := Matrix.isHermitian_conjTranspose_mul_self X
  let hH := Matrix.isHermitian_conjTranspose_mul_self Y
  have hgram : Yᴴ * Y = star (U : Matrix ι ι ℂ) * (Xᴴ * X) * (U : Matrix ι ι ℂ) := by
    dsimp [Y]
    simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star, Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc (U : Matrix ι ι ℂ) (star (U : Matrix ι ι ℂ)),
      ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]
  have hchar : (Yᴴ * Y).charpoly = (Xᴴ * X).charpoly := by
    rw [hgram, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
    simp
  have heig := (hH.eigenvalues_eq_eigenvalues_iff hG).mpr hchar
  change (cfc Real.sqrt (Yᴴ * Y)).trace.re = _
  rw [trace_cfc _ hH, trace_cfc _ hG, heig]

/-- Absolute diagonal coefficients in any orthonormal basis are trace-norm bounded. -/
theorem coefficients_le_traceNorm (X : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    ∑ i, ‖(star (U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)) i i‖ ≤
      (cfc Real.sqrt (Xᴴ * X)).trace.re := by
  exact (diagonal_le_traceNorm _).trans_eq (traceNorm_unitary_conj X U)

/-- The acceptance-matrix convention uses the adjoint; diagonal norms are unchanged. -/
theorem adjoint_coefficients_le_traceNorm (X : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    ∑ i, ‖(star (U : Matrix ι ι ℂ) * Xᴴ * (U : Matrix ι ι ℂ)) i i‖ ≤
      (cfc Real.sqrt (Xᴴ * X)).trace.re := by
  have heq : star (U : Matrix ι ι ℂ) * Xᴴ * (U : Matrix ι ι ℂ) =
      (star (U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ))ᴴ := by
    simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star, Matrix.mul_assoc]
  rw [heq]
  simpa only [Matrix.conjTranspose_apply, norm_star] using coefficients_le_traceNorm X U

end PRUTraceNorm



set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

open scoped Matrix ComplexConjugate BigOperators

namespace PRUEq18

/-- A one-step fast-tail estimate is uniform over all positive powers. -/
lemma geometric_tail (W η ε : ℝ) (hW : 0 ≤ W) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hsmall : W * η ≤ ε) (j : ℕ) (hj : 1 ≤ j) : W * η ^ j ≤ ε := by
  apply le_trans _ hsmall
  apply mul_le_mul_of_nonneg_left _ hW
  simpa only [pow_one] using pow_le_pow_of_le_one hη0 hη1 hj

/-- The powers in Eq. (18) follow from the two absorbing-projection identities. -/
lemma segment_powers {R : Type*} [Ring R] (M P : R)
    (hMP : M * P = P) (hPM : P * M = P) (hPP : P * P = P)
    (m j : ℕ) (hj : 1 ≤ j) : (M ^ m - P) ^ j = M ^ (m * j) - P := by
  have hleft : ∀ r : ℕ, M ^ r * P = P := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, mul_assoc, hMP, ih]
  have hright : ∀ r : ℕ, P * M ^ r = P := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, ← mul_assoc, ih, hPM]
  rw [PRUSpectral.sub_projection_pow (M ^ m) P (hleft m) (hright m) hPP j hj,
    ← pow_mul]

/-- Eq. (18)'s spectral conclusion under the paper's trace-norm hypothesis.
Only Hermiticity, the eigenvalue estimates, and the initial trace bounds remain inputs. -/
theorem spectral_conclusion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B Λ : Matrix ι ι ℂ) (hB : B.IsHermitian) (D : ℕ) (hD : 1 ≤ D)
    (ρ η W ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hW0 : 0 ≤ W)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hρ : ∀ i, |hB.eigenvalues i| ≤ ρ)
    (hcount : (Finset.univ.filter fun i => η < |hB.eigenvalues i|).card ≤ D)
    (hW : QAlgorithms.traceNorm Λ ≤ W)
    (hinitial : ∀ j : ℕ, 1 ≤ j → j ≤ D → ‖(Λᴴ * B ^ j).trace‖ ≤ 1)
    (htail : W * η ≤ ε) :
    (∃ k ≤ D, ∃ b lam : Fin k → ℂ,
      (∀ i, Module.End.HasEigenvalue (Matrix.toLin' B) (lam i) ∧
        η < ‖lam i‖ ∧ ‖lam i‖ ≤ ρ) ∧
      ∀ j ≥ 1, ‖(Λᴴ * B ^ j).trace - ∑ i, b i * lam i ^ j‖ ≤ W * η ^ j ∧
        W * η ^ j ≤ ε) ∧
    (∀ j ≥ D, ‖(Λᴴ * B ^ j).trace‖ ≤ 2 * D * 2 ^ D *
      ((j + D - 2).choose (D - 1) : ℝ) * ρ ^ (j - D) + ε) := by
  have hcoeff : ∑ i, ‖(star (hB.eigenvectorUnitary : Matrix ι ι ℂ) * Λᴴ *
      (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i i‖ ≤ W :=
    (PRUTraceNorm.adjoint_coefficients_le_traceNorm Λ hB.eigenvectorUnitary).trans hW
  have htail' := geometric_tail W η ε hW0 hη0 hη1 htail
  constructor
  · obtain ⟨k, hk, b, lam, hspec, herr⟩ :=
      PRUSpectral.spectral_split B Λᴴ hB D ρ η W hη0 hρ hcount hcoeff
    exact ⟨k, hk, b, lam, hspec, fun j hj => ⟨herr j, htail' j hj⟩⟩
  · intro j hj
    apply (PRUSpectral.trace_power_bound B Λᴴ hB D hD ρ η W ε hρ0 hρ1 hη0 hε0
      hρ hcount hcoeff hinitial htail' j hj).trans
    gcongr
    linarith

end PRUEq18



set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

open QAlgorithms QuantumHMMR
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

namespace PRUAcceptance

/-- Separating selected wires from untouched wires is a bijective change of basis. -/
noncomputable def wireSplit {k n : ℕ} (w : Fin k ↪ Fin n) :
    Qubits n ≃ (Qubits k × ({a : Fin n // a ∉ Set.range w} → Bool)) := by
  classical
  refine { toFun := fun y => (y ∘ w, fun a => y a)
           invFun := fun p a => if h : a ∈ Set.range w then p.1 h.choose else p.2 ⟨a,h⟩
           left_inv := ?_, right_inv := ?_ }
  · intro y
    funext a
    dsimp only
    split_ifs with h
    · exact congrArg y h.choose_spec
    · rfl
  · intro p
    apply Prod.ext
    · funext b
      dsimp only [Function.comp_def]
      rw [dif_pos (Set.mem_range_self b)]
      exact congrArg p.1 (w.injective (Exists.choose_spec (Set.mem_range_self b)))
    · funext a
      exact dif_neg a.property

lemma embed_eq_kronecker {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin n) :
    embedOp M w = (Matrix.kronecker M
      (1 : Matrix ({a : Fin n // a ∉ Set.range w} → Bool)
        ({a : Fin n // a ∉ Set.range w} → Bool) ℂ)).submatrix (wireSplit w) (wireSplit w) := by
  classical
  ext y z
  have heq : (∀ a : Fin n, a ∉ Set.range w → y a = z a) ↔
      (fun a : {a : Fin n // a ∉ Set.range w} => y a) = (fun a : {a : Fin n // a ∉ Set.range w} => z a) := by
    constructor
    · intro h; funext a; exact h a a.property
    · intro h a ha; exact congrFun h ⟨a,ha⟩
  change (if ∀ a : Fin n, a ∉ Set.range w → y a = z a then M (y ∘ w) (z ∘ w) else 0) =
    M (y ∘ w) (z ∘ w) * (if (fun a : {a : Fin n // a ∉ Set.range w} => y a) =
      (fun a : {a : Fin n // a ∉ Set.range w} => z a) then 1 else 0)
  simp only [heq, mul_ite, mul_one, mul_zero]

lemma unitary_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (M : Matrix ι ι ℂ)
    (hM : M ∈ Matrix.unitaryGroup ι ℂ) (e : κ ≃ ι) :
    M.submatrix e e ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  simpa! [Matrix.star_eq_conjTranspose] using congrArg (fun X : Matrix ι ι ℂ => X.submatrix e e) hM.1

theorem embed_unitary {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  classical
  rw [embed_eq_kronecker]
  apply unitary_submatrix
  exact Matrix.kronecker_mem_unitary hM (Submonoid.one_mem _)

lemma orderedProd_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    (U : Fin t → Matrix ι ι ℂ) (hU : ∀ i, U i ∈ Matrix.unitaryGroup ι ℂ) :
    orderedProd U ∈ Matrix.unitaryGroup ι ℂ := by
  apply Submonoid.list_prod_mem
  intro M hM
  simp only [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨i,rfl⟩ := hM
  exact hU i

theorem adaptiveState_isState {n t : ℕ} (alg : AdaptiveAlg n t)
    (U : QAlgorithms.Papers.Independent.Extend50.P45.QMat n)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) : IsState (adaptiveState alg U) := by
  unfold adaptiveState IsState
  rw [act_norm_of_mem_unitaryGroup]
  · simp [zeroKet, ket]
  · apply Submonoid.mul_mem
    · exact (alg.A (Fin.last t)).property
    · apply orderedProd_unitary
      intro i
      exact Submonoid.mul_mem _ (embed_unitary U hU _) (alg.A i.castSucc).property

/-- The Born probability is the quadratic form of the effect. -/
lemma pure_effectProb {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    effectProb M (pureDensity ψ) = (star (WithLp.ofLp ψ) ⬝ᵥ (M *ᵥ WithLp.ofLp ψ)).re := by
  unfold effectProb
  congr 1
  simp only [pureDensity, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
    Complex.star_def]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem effectProb_mem_unitInterval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : IsEffect M) (ψ : EuclideanSpace ℂ ι) (hψ : IsState ψ) :
    0 ≤ effectProb M (pureDensity ψ) ∧ effectProb M (pureDensity ψ) ≤ 1 := by
  rw [pure_effectProb]
  have hlo := hM.1.dotProduct_mulVec_nonneg (WithLp.ofLp ψ)
  have hhi := hM.2.dotProduct_mulVec_nonneg (WithLp.ofLp ψ)
  have hn : (star (WithLp.ofLp ψ) ⬝ᵥ WithLp.ofLp ψ).re = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
    simp [show ‖ψ‖ = 1 from hψ]
  constructor
  · exact (Complex.nonneg_iff.mp hlo).1
  · have hhi' := (Complex.nonneg_iff.mp hhi).1
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re, hn] at hhi'
    linarith

theorem acceptProb_mem_unitInterval {n t : ℕ} (alg : AdaptiveAlg n t)
    (M : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ) (hM : IsEffect M)
    (U : QAlgorithms.Papers.Independent.Extend50.P45.QMat n)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    0 ≤ acceptProb alg M U ∧ acceptProb alg M U ≤ 1 :=
  effectProb_mem_unitInterval M hM _ (adaptiveState_isState alg U hU)

open MeasureTheory QAlgorithms.Papers.Independent.Extend50.P45
attribute [local instance] qubitMatrixMeasurable

theorem expected_acceptance_mem_unitInterval {n t : ℕ} (alg : AdaptiveAlg n t)
    (M : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ) (hM : IsEffect M)
    (μ : Measure (QMat n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    0 ≤ ∫ U, acceptProb alg M U ∂μ ∧ (∫ U, acceptProb alg M U ∂μ) ≤ 1 := by
  have hlo : ∀ᵐ U ∂μ, 0 ≤ acceptProb alg M U :=
    hμ.mono fun U hU => (acceptProb_mem_unitInterval alg M hM U hU).1
  have hhi : ∀ᵐ U ∂μ, acceptProb alg M U ≤ 1 :=
    hμ.mono fun U hU => (acceptProb_mem_unitInterval alg M hM U hU).2
  refine ⟨integral_nonneg_of_ae hlo, ?_⟩
  simpa using integral_mono_of_nonneg hlo (integrable_const (1 : ℝ)) hhi

theorem acceptance_difference_le_one {n t : ℕ} (alg : AdaptiveAlg n t)
    (M : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ) (hM : IsEffect M)
    (μ ν : Measure (QMat n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hν : ∀ᵐ U ∂ν, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    |(∫ U, acceptProb alg M U ∂μ) - ∫ U, acceptProb alg M U ∂ν| ≤ 1 := by
  have h1 := expected_acceptance_mem_unitInterval alg M hM μ hμ
  have h2 := expected_acceptance_mem_unitInterval alg M hM ν hν
  rw [abs_le]
  constructor <;> linarith

end PRUAcceptance



set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix ComplexConjugate BigOperators Matrix.Norms.Elementwise

namespace PRUMoments

attribute [local instance] qubitMatrixMeasurable qubitMatrixBorel

def rep {n : ℕ} (t : ℕ) (U : QMat n) :
    Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
      ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ :=
  Matrix.kronecker (qubitTensorPower t U) ((qubitTensorPower t U).map (starRingEnd ℂ))

lemma rep_apply {n : ℕ} (t : ℕ) (U : QMat n) (x y) :
    rep t U x y = qubitTensorPower t U x.1 y.1 * conj (qubitTensorPower t U x.2 y.2) := rfl

lemma tensor_mul {n : ℕ} (t : ℕ) (U V : QMat n) :
    qubitTensorPower t (U * V) = qubitTensorPower t U * qubitTensorPower t V := by
  ext x y
  simp only [qubitTensorPower, Matrix.mul_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

lemma rep_mul {n : ℕ} (t : ℕ) (U V : QMat n) : rep t (U * V) = rep t U * rep t V := by
  simp only [rep, tensor_mul, Matrix.map_mul]
  exact Matrix.mul_kronecker_mul _ _ _ _

lemma tensor_one {n : ℕ} (t : ℕ) : qubitTensorPower t (1 : QMat n) = 1 := by
  ext x y
  classical
  by_cases h : x = y
  · subst y; simp [qubitTensorPower]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [qubitTensorPower, Matrix.one_apply, if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma rep_one {n : ℕ} (t : ℕ) : rep t (1 : QMat n) = 1 := by
  simp [rep, tensor_one]

lemma continuous_rep_entry {n : ℕ} (t : ℕ) (x y) : Continuous (fun U : QMat n => rep t U x y) := by
  simp only [rep_apply, qubitTensorPower]
  fun_prop

lemma unitary_entry_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (x y : ι) : ‖U x y‖ ≤ 1 :=
  entry_norm_bound_of_unitary hU x y

lemma tensor_entry_bound {n : ℕ} (t : ℕ) (U : QMat n)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (x y) : ‖qubitTensorPower t U x y‖ ≤ 1 := by
  simp only [qubitTensorPower, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => unitary_entry_bound U hU _ _)

lemma rep_entry_bound {n : ℕ} (t : ℕ) (U : QMat n)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (x y) : ‖rep t U x y‖ ≤ 1 := by
  rw [rep_apply, norm_mul, Complex.norm_conj]
  exact mul_le_one₀ (tensor_entry_bound t U hU _ _) (norm_nonneg _) (tensor_entry_bound t U hU _ _)

lemma rep_integrable {n : ℕ} (t : ℕ) (μ : Measure (QMat n)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (x y) :
    Integrable (fun U => rep t U x y) μ := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_rep_entry t x y).aestronglyMeasurable
  exact hμ.mono fun U hU => rep_entry_bound t U hU x y

theorem moment_convolve {n : ℕ} (t : ℕ) (μ ν : Measure (QMat n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hν : ∀ᵐ U ∂ν, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    balancedUnitaryMoment (convolve μ ν) t = balancedUnitaryMoment μ t * balancedUnitaryMoment ν t := by
  ext x y
  change (∫ U, rep t U x y ∂Measure.map (fun p : QMat n × QMat n => p.1 * p.2) (μ.prod ν)) = _
  rw [integral_map (by fun_prop) (continuous_rep_entry t x y).aestronglyMeasurable]
  simp_rw [rep_mul, Matrix.mul_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_prod_mul (fun U : QMat n => rep t U x i) (fun V : QMat n => rep t V i y)
  · intro i _
    exact (rep_integrable t μ hμ x i).mul_prod (rep_integrable t ν hν i y)

lemma unitary_measurableSet (n : ℕ) : MeasurableSet
    {U : QMat n | U ∈ Matrix.unitaryGroup (Qubits n) ℂ} :=
  (isClosed_unitary : IsClosed (Matrix.unitaryGroup (Qubits n) ℂ : Set (QMat n))).measurableSet

lemma convolve_probability {n : ℕ} (μ ν : Measure (QMat n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (convolve μ ν) := by
  apply Measure.isProbabilityMeasure_map
  fun_prop

lemma convolve_unitary {n : ℕ} (μ ν : Measure (QMat n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hν : ∀ᵐ U ∂ν, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    ∀ᵐ U ∂convolve μ ν, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold convolve
  apply (ae_map_iff (by fun_prop) (unitary_measurableSet n)).2
  apply (Measure.ae_prod_iff_ae_ae ((unitary_measurableSet n).preimage (by fun_prop))).2
  exact hμ.mono fun U hU => hν.mono fun V hV => Submonoid.mul_mem _ hU hV

lemma steps_probability {n : ℕ} (μ : Measure (QMat n)) [IsProbabilityMeasure μ] (r : ℕ) :
    IsProbabilityMeasure (steps μ r) := by
  induction r with
  | zero => simp only [steps]; infer_instance
  | succ r ih => letI := ih; exact convolve_probability μ (steps μ r)

lemma steps_unitary {n : ℕ} (μ : Measure (QMat n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (r : ℕ) :
    ∀ᵐ U ∂steps μ r, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  induction r with
  | zero =>
    exact (ae_dirac_iff (unitary_measurableSet n)).2 (Submonoid.one_mem (Matrix.unitaryGroup (Qubits n) ℂ))
  | succ r ih =>
    letI := steps_probability μ r
    exact convolve_unitary μ (steps μ r) hμ ih

theorem moment_steps {n : ℕ} (t : ℕ) (μ : Measure (QMat n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (r : ℕ) :
    balancedUnitaryMoment (steps μ r) t = balancedUnitaryMoment μ t ^ r := by
  induction r with
  | zero =>
    ext x y
    change (∫ U, rep t U x y ∂Measure.dirac (1 : QMat n)) = _
    simp [rep_one]
  | succ r ih =>
    letI := steps_probability μ r
    rw [steps, moment_convolve t μ (steps μ r) hμ (steps_unitary μ hμ r), ih, pow_succ']

lemma haarMap_continuous (n : ℕ) :
    Continuous (fun U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ =>
      (fun x y => U.val (bitsEquivFin n x) (bitsEquivFin n y) : QMat n)) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)

lemma haar_probability (n : ℕ) : IsProbabilityMeasure (haarLaw n) := by
  letI : IsProbabilityMeasure (Schur.unitaryHaar (2 ^ n)) := ⟨Measure.haarMeasure_self⟩
  exact Measure.isProbabilityMeasure_map (Continuous.measurable (γ := QMat n) (haarMap_continuous n)).aemeasurable

lemma haar_unitary (n : ℕ) : ∀ᵐ U ∂haarLaw n, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold haarLaw
  apply (ae_map_iff (Continuous.measurable (γ := QMat n) (haarMap_continuous n)).aemeasurable (unitary_measurableSet n)).2
  exact Filter.Eventually.of_forall fun U =>
    PRUAcceptance.unitary_submatrix U.val U.property (bitsEquivFin n)

end PRUMoments



set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

open QAlgorithms QuantumHMMR QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix ComplexConjugate BigOperators ENNReal

namespace PRUWalkLaws

attribute [local instance] qubitMatrixMeasurable qubitMatrixBorel

lemma nextWire_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : nextWire i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  unfold nextWire at hv
  split_ifs at hv <;> simp only at hv <;> omega

def edgeWires {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : Fin 2 ↪ Fin n where
  toFun j := if j.val = 0 then i else nextWire i
  inj' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [nextWire_ne hn i, Ne.symm (nextWire_ne hn i)]


lemma edgeLift_eq_embed {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (U : QMat 2) :
    edgeLift i U = embedOp U (edgeWires hn i) := by
  ext x y
  have hrange (q : Fin n) : q ∈ Set.range (edgeWires hn i) ↔ q = i ∨ q = nextWire i := by
    simp only [Set.mem_range, Fin.exists_fin_two, edgeWires, Function.Embedding.coeFn_mk]
    simp [eq_comm]
  have houtside : (∀ q, q ≠ i → q ≠ nextWire i → x q = y q) ↔
      (∀ q, q ∉ Set.range (edgeWires hn i) → x q = y q) := by
    simp only [hrange, not_or, and_imp]
  simp only [edgeLift, embedOp, Matrix.of_apply, ← houtside]
  split_ifs
  · congr 1 <;> funext j <;> fin_cases j <;> simp [edgeWires, Function.comp_def]
  · rfl

lemma edgeLift_unitary {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (U : QMat 2)
    (hU : U ∈ Matrix.unitaryGroup (Qubits 2) ℂ) :
    edgeLift i U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [edgeLift_eq_embed hn]
  exact PRUAcceptance.embed_unitary U hU _

lemma firstWireLift_unitary (n : ℕ) (U : QMat 1)
    (hU : U ∈ Matrix.unitaryGroup (Qubits 1) ℂ) :
    firstWireLift n U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  by_cases hn : 0 < n
  · let w : Fin 1 ↪ Fin n := ⟨fun _ => ⟨0,hn⟩, fun _ _ _ => Subsingleton.elim _ _⟩
    have heq : firstWireLift n U = embedOp U w := by
      ext x y
      have hrange (q : Fin n) : q ∈ Set.range w ↔ q.val = 0 := by
        constructor
        · rintro ⟨j,rfl⟩; rfl
        · intro h; exact ⟨0, Fin.ext h.symm⟩
      simp only [firstWireLift, dif_pos hn, embedOp, Matrix.of_apply, hrange]
      split_ifs <;> rfl
    rw [heq]
    exact PRUAcceptance.embed_unitary U hU w
  · have heq : firstWireLift n U = 1 := by ext x y; simp [firstWireLift, hn]
    rw [heq]; exact Submonoid.one_mem _

lemma rotZ_unitary (φ : ℝ) : rotZ φ ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [rotZ, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext x y
  by_cases h : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]
    split_ifs
    all_goals
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp [Complex.norm_exp]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

lemma continuous_firstWireLift (n : ℕ) : Continuous (firstWireLift n) := by
  apply continuous_pi; intro x
  apply continuous_pi; intro y
  simp only [firstWireLift]
  split_ifs <;> fun_prop

lemma continuous_rotZ : Continuous rotZ := by
  apply continuous_pi; intro x
  apply continuous_pi; intro y
  simp only [rotZ, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

lemma chi_probability (G : Finset (Clifford.ProjectiveGroup 2)) (n : ℕ)
    (hG : G.Nonempty) (hn : 0 < n) : IsProbabilityMeasure (chiLaw G n) := by
  constructor
  have hg : (G.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hG.card_pos.ne'
  have hn' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  simp [chiLaw, Measure.smul_apply, Measure.finsetSum_apply, hg, hn', ENNReal.inv_mul_cancel]

lemma chi_unitary (G : Finset (Clifford.ProjectiveGroup 2)) (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ U ∂chiLaw G n, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold chiLaw
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i _
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro g hg
  apply (ae_dirac_iff (PRUMoments.unitary_measurableSet n)).2
  exact edgeLift_unitary hn i _ (Clifford.representative g).val.property

lemma xi_probability (n : ℕ) : IsProbabilityMeasure (xiLaw n) := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  letI : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite (by simp only [Real.volume_Ico, sub_zero, ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr hp)
      (by simp only [Real.volume_Ico, sub_zero]; exact ENNReal.ofReal_ne_top)
  unfold xiLaw
  apply Measure.isProbabilityMeasure_map
  exact (Continuous.measurable (γ := QMat n)
    ((continuous_firstWireLift n).comp continuous_rotZ)).aemeasurable

lemma xi_unitary (n : ℕ) : ∀ᵐ U ∂xiLaw n, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold xiLaw
  apply (ae_map_iff (Continuous.measurable (γ := QMat n)
    ((continuous_firstWireLift n).comp continuous_rotZ)).aemeasurable
    (PRUMoments.unitary_measurableSet n)).2
  exact Filter.Eventually.of_forall fun φ => firstWireLift_unitary n _ (rotZ_unitary φ)

lemma step_probability (G : Finset (Clifford.ProjectiveGroup 2)) (n m : ℕ)
    (hG : G.Nonempty) (hn : 0 < n) (hm : 1 ≤ m) : IsProbabilityMeasure (stepLaw G n m) := by
  letI := chi_probability G n hG hn
  letI := xi_probability n
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hinv0 : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  have hinv1 : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm'
  constructor
  simp only [stepLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hinv1) hinv0]
  simp

lemma step_unitary (G : Finset (Clifford.ProjectiveGroup 2)) (n m : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ U ∂stepLaw G n m, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold stepLaw
  rw [ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure (chi_unitary G n hn) _,
    Measure.ae_smul_measure (xi_unitary n) _⟩

theorem walk_probability (G : Finset (Clifford.ProjectiveGroup 2)) (n m r : ℕ)
    (hG : G.Nonempty) (hn : 0 < n) (hm : 1 ≤ m) : IsProbabilityMeasure (walkLaw G n m r) := by
  letI := step_probability G n m hG hn hm
  exact PRUMoments.steps_probability (stepLaw G n m) r

theorem walk_unitary (G : Finset (Clifford.ProjectiveGroup 2)) (n m r : ℕ)
    (hG : G.Nonempty) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    ∀ᵐ U ∂walkLaw G n m r, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  letI := step_probability G n m hG (by omega) hm
  exact PRUMoments.steps_unitary (stepLaw G n m) (step_unitary G n m hn) r

theorem walk_moment (G : Finset (Clifford.ProjectiveGroup 2)) (n m r t : ℕ)
    (hG : G.Nonempty) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    balancedUnitaryMoment (walkLaw G n m r) t = balancedUnitaryMoment (stepLaw G n m) t ^ r := by
  letI := step_probability G n m hG (by omega) hm
  exact PRUMoments.moment_steps t (stepLaw G n m) (step_unitary G n m hn) r

end PRUWalkLaws



set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

open QAlgorithms QuantumHMMR QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix ComplexConjugate BigOperators
attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

theorem solution [∀ n, Fintype (Clifford.ProjectiveGroup n)]
    (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (t : ℕ) (ht : 4 ≤ t) (γ a : ℝ) (hga : IsGapPair G t γ a) (A : ℕ) (hA1 : 1 ≤ A)
    (hA : ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((2 : ℝ) ^ n) ^ (2 * t) * (1 - (1 - ((A * n ^ 2 : ℕ) : ℝ)⁻¹) * γ / n) ^ (A * n ^ 2)
        ≤ Real.exp (-(n : ℝ))) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ alg : AdaptiveAlg n t,
      ∀ Meff : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ, IsEffect Meff →
      ∀ Λ : Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
          ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ,
        IsAcceptanceMatrix alg Meff Λ → traceNorm Λ ≤ ((2 : ℝ) ^ n) ^ (2 * t) →
        let m := A * n ^ 2
        let p : ℝ := (m : ℝ)⁻¹
        let M := balancedUnitaryMoment (stepLaw G n m) t
        let MH := balancedUnitaryMoment (haarLaw n) t
        let B := M ^ m - MH
        let η : ℝ := (1 - (1 - p) * γ / n) ^ m
        let aj : ℕ → ℂ := fun j => (Λᴴ * B ^ j).trace
        (∀ j ≥ 1, B ^ j = M ^ (m * j) - MH) ∧
        (∀ j ≥ 1,
          aj j = (((∫ U, acceptProb alg Meff U ∂walkLaw G n m (m * j)) -
            ∫ U, acceptProb alg Meff U ∂haarLaw n : ℝ) : ℂ) ∧
          |(∫ U, acceptProb alg Meff U ∂walkLaw G n m (m * j)) -
            ∫ U, acceptProb alg Meff U ∂haarLaw n| ≤ 1) ∧
        (∃ k ≤ Dt t, ∃ b lam : Fin k → ℂ,
          (∀ i, Module.End.HasEigenvalue (Matrix.toLin' B) (lam i) ∧
            η < ‖lam i‖ ∧ ‖lam i‖ ≤ Real.exp (-(a / 2))) ∧
          ∀ j ≥ 1, ‖aj j - ∑ i, b i * lam i ^ j‖ ≤ ((2 : ℝ) ^ n) ^ (2 * t) * η ^ j ∧
            ((2 : ℝ) ^ n) ^ (2 * t) * η ^ j ≤ Real.exp (-(n : ℝ))) ∧
        ∀ j ≥ Dt t, ‖aj j‖ ≤ 2 * Dt t * 2 ^ Dt t * ((j + Dt t - 2).choose (Dt t - 1) : ℝ) *
          Real.exp (-(a / 2)) ^ (j - Dt t) + Real.exp (-(n : ℝ)) := by
  classical

  obtain ⟨n16, h16⟩ := QuantumHMMR.eq_16 G hG t ht γ a hga A hA1
  obtain ⟨hspec, hρ1, _⟩ := QuantumHMMR.eq_17 G hG t ht γ a hga
  obtain ⟨n17, h17⟩ := hspec A hA1
  obtain ⟨nA, hAtail⟩ := hA
  refine ⟨max (max (max n16 n17) nA) (max ⌈γ⌉₊ 2), ?_⟩
  intro n hn alg Meff hMeff Λ hΛ hΛnorm
  have hn16 : n16 ≤ n := by omega
  have hn17 : n17 ≤ n := by omega
  have hnA : nA ≤ n := by omega
  have hnγ : ⌈γ⌉₊ ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hγn : γ ≤ (n : ℝ) := (Nat.le_ceil γ).trans (by exact_mod_cast hnγ)
  let m : ℕ := A * n ^ 2
  let M := balancedUnitaryMoment (stepLaw G n m) t
  let MH := balancedUnitaryMoment (haarLaw n) t
  let B := M ^ m - MH
  let η : ℝ := (1 - (1 - (m : ℝ)⁻¹) * γ / n) ^ m
  have hm : 1 ≤ m := by dsimp [m]; nlinarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  have hp1 : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hmR
  have hγ0 : 0 < γ := hga.1
  have hdiv0 : 0 ≤ γ / (n : ℝ) := div_nonneg hγ0.le hnR.le
  have hdiv1 : γ / (n : ℝ) ≤ 1 := (div_le_one hnR).mpr hγn
  have hbase0 : 0 ≤ 1 - (1 - (m : ℝ)⁻¹) * γ / n := by
    rw [mul_div_assoc]
    nlinarith [mul_nonneg hp0 hdiv0]
  have hbase1 : 1 - (1 - (m : ℝ)⁻¹) * γ / n ≤ 1 := by
    rw [mul_div_assoc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) hdiv0]
  have hη0 : 0 ≤ η := pow_nonneg hbase0 m
  have hη1 : η ≤ 1 := pow_le_one₀ hbase0 hbase1
  have hgen : G.Nonempty := ⟨_, hG.1⟩
  obtain ⟨hMP, hPM, _⟩ := h16 n hn16
  obtain ⟨hBP, hB, heigs, _⟩ := h17 n hn17
  change M * MH = MH at hMP
  change MH * M = MH at hPM
  change B * MH = 0 at hBP
  change B.IsHermitian at hB
  have hMpow : ∀ r : ℕ, M ^ r * MH = MH := by
    intro r
    induction r with
    | zero => simp
    | succ r ihr => rw [pow_succ, mul_assoc, hMP, ihr]
  have hPP : MH * MH = MH := by
    change (M ^ m - MH) * MH = 0 at hBP
    rw [sub_mul, hMpow] at hBP
    exact (sub_eq_zero.mp hBP).symm
  have hpower (j : ℕ) (hj : 1 ≤ j) : B ^ j = M ^ (m * j) - MH :=
    PRUEq18.segment_powers M MH hMP hPM hPP m j hj
  have haccept (j : ℕ) (hj : 1 ≤ j) :
      (Λᴴ * B ^ j).trace = (((∫ U, acceptProb alg Meff U ∂walkLaw G n m (m * j)) -
        ∫ U, acceptProb alg Meff U ∂haarLaw n : ℝ) : ℂ) ∧
      |(∫ U, acceptProb alg Meff U ∂walkLaw G n m (m * j)) -
        ∫ U, acceptProb alg Meff U ∂haarLaw n| ≤ 1 := by
    letI := PRUWalkLaws.walk_probability G n m (m * j) hgen (by omega) hm
    letI := PRUMoments.haar_probability n
    have hw := PRUWalkLaws.walk_unitary G n m (m * j) hgen hn2 hm
    have hh := PRUMoments.haar_unitary n
    constructor
    · rw [hpower j hj, Matrix.mul_sub, Matrix.trace_sub, Complex.ofReal_sub,
        hΛ (walkLaw G n m (m * j)) inferInstance hw, hΛ (haarLaw n) inferInstance hh,
        PRUWalkLaws.walk_moment G n m (m * j) t hgen hn2 hm]
    · exact PRUAcceptance.acceptance_difference_le_one alg Meff hMeff _ _ hw hh
  have hD : 1 ≤ Dt t := Nat.one_le_iff_ne_zero.mpr (by simp [Dt, Finset.prod_ne_zero_iff])
  have hρ0 := Real.exp_pos (-(a / 2))
  have heps0 := (Real.exp_pos (-(n : ℝ))).le
  have heps1 : Real.exp (-(n : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
  obtain ⟨hρ, hcount⟩ := heigs hB
  have hinitial (j : ℕ) (hj : 1 ≤ j) (_ : j ≤ Dt t) : ‖(Λᴴ * B ^ j).trace‖ ≤ 1 := by
    rw [(haccept j hj).1, Complex.norm_real, Real.norm_eq_abs]
    exact (haccept j hj).2
  have hs := PRUEq18.spectral_conclusion B Λ hB (Dt t) hD
    (Real.exp (-(a / 2))) η (((2 : ℝ) ^ n) ^ (2 * t)) (Real.exp (-(n : ℝ)))
    hρ0 hρ1 hη0 hη1 (by positivity) heps0 heps1 hρ hcount hΛnorm hinitial (hAtail n hnA)
  exact ⟨hpower, haccept, hs.1, hs.2⟩


#print axioms solution
