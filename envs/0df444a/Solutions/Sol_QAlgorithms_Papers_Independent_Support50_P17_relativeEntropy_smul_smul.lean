-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P17.relativeEntropy_smul_smul
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T10:46:34.454454+00:00
-- url     : https://prove2.me/submissions/058412da-f6e0-465e-9b21-61208bb47c89

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section
open scoped Matrix ComplexOrder

namespace P17Aux

open Matrix

lemma cfcCont {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact Set.Finite.continuousOn (Set.finite_range hA.eigenvalues) f

lemma psdCfc {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (cfc f A).PosSemidef := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have hd : (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues : I → ℂ)).PosSemidef := by
    rw [posSemidef_diagonal_iff]; intro i
    simpa using hf i
  simpa [star_eq_conjTranspose] using hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix I I ℂ)

lemma traceCfc {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  rfl

lemma minEig_le {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (i : I) : QAlgorithms.minEigenvalue A ≤ hA.eigenvalues i := by
  have h : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  simp only [QAlgorithms.minEigenvalue, dif_pos h, QAlgorithms.ascEigenvalues, dif_pos hA,
    IsHermitian.eigenvalues]
  apply hA.eigenvalues₀_antitone
  rw [Fin.le_def]; simp; omega


lemma specFin {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) : (spectrum ℝ A).Finite := by
  rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _

open QAlgorithms.Papers.Independent.Dependency50.P21 in
theorem rss_main {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : X.PosSemidef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    relativeEntropy ((a : ℂ) • X) ((b : ℂ) • X) =
      ((a * Real.log (a / b) * X.trace.re : ℝ) : EReal) := by
  have hH := hX.isHermitian
  have hsa : IsSelfAdjoint X := hH
  have hsupp : IsSupported ((a:ℂ)•X) ((b:ℂ)•X) := by
    intro v hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.smul_mulVec] at hv ⊢
    have hb' : (b:ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [(smul_eq_zero.mp hv).resolve_left hb', smul_zero]
  have e1 : cfc (fun x : ℝ => x * Real.log x) ((a:ℂ)•X) =
      cfc (fun x => (a*x) * Real.log (a*x)) X := by
    rw [Complex.coe_smul, ← cfc_comp_const_mul a (fun x : ℝ => x * Real.log x) X
      (Set.Finite.continuousOn ((specFin hH).image _) _)]
  have e2 : cfc Real.log ((b:ℂ)•X) = cfc (fun x => Real.log (b*x)) X := by
    rw [Complex.coe_smul, ← cfc_comp_const_mul b Real.log X
      (Set.Finite.continuousOn ((specFin hH).image _) _)]
  have e3 : (a:ℂ)•X = cfc (fun x => a*x) X := by rw [Complex.coe_smul, cfc_const_mul_id a X]
  have key : (cfc (fun x : ℝ => x * Real.log x) ((a:ℂ)•X) -
      (a:ℂ)•X * cfc Real.log ((b:ℂ)•X)).trace.re = a * Real.log (a / b) * X.trace.re := by
    rw [e1, e2, e3, ← cfc_mul (hf := cfcCont hH _) (hg := cfcCont hH _),
      ← cfc_sub (hf := cfcCont hH _) (hg := cfcCont hH _), traceCfc hH,
      hH.trace_eq_sum_eigenvalues, Complex.re_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.ofReal_re]
    have hl := hX.eigenvalues_nonneg i
    set l := hH.eigenvalues i
    rcases ha.eq_or_lt with rfl | ha'
    · simp
    rcases hl.eq_or_lt with hl0 | hl'
    · rw [← hl0]; simp
    rw [Real.log_mul ha'.ne' hl'.ne', Real.log_mul hb.ne' hl'.ne', Real.log_div ha'.ne' hb.ne']
    show a * l * (Real.log a + Real.log l) - a * l * (Real.log b + Real.log l) = a * (Real.log a - Real.log b) * l
    ring
  simp only [relativeEntropy, if_pos hsupp, key]

end P17Aux

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy) in
theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : X.PosSemidef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    relativeEntropy ((a : ℂ) • X) ((b : ℂ) • X) =
      ((a * Real.log (a / b) * X.trace.re : ℝ) : EReal) :=
  P17Aux.rss_main X hX ha hb

end
