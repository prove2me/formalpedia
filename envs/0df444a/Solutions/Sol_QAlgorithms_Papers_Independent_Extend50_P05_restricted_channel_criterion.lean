-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P05.restricted_channel_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:57:37.893076+00:00
-- url     : https://prove2.me/submissions/ef0a7fbc-cbaa-48c4-a136-4468909c7cc7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace S110P05

lemma choi_kraus {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (X Y : ι × κ) :
    choi (QAlgorithms.krausApply E) X Y = ∑ j, E j X.2 X.1 * star (E j Y.2 Y.1) := by
  simp only [choi, QAlgorithms.krausApply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma kraus_sum_apply {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (a b : ι) :
    (∑ j, (E j)ᴴ * E j) a b = ∑ x : κ, choi (QAlgorithms.krausApply E) (b, x) (a, x) := by
  simp only [choi_kraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
  ring


lemma ptrace_restricted (d : ℕ) (alpha beta : ℝ) (gamma : ℂ) (a : Fin d) :
    ∑ x : CloningOutputs d 2, restrictedChoi d alpha beta gamma (a, x) (a, x) =
      (((d : ℝ) * (alpha + beta) + 2 * gamma.re : ℝ) : ℂ) := by
  rw [← (finTwoArrowEquiv (Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  simp [restrictedChoi, cupOperatorOne, cupOperatorTwo, cycleOperator, cupOne, cupTwo,
    Finset.sum_add_distrib, ite_and]
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, ite_self]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [Complex.re_eq_add_conj]
  ring


lemma ptrace_restricted_ne (d : ℕ) (alpha beta : ℝ) (gamma : ℂ) (a b : Fin d) (hab : a ≠ b) :
    ∑ x : CloningOutputs d 2, restrictedChoi d alpha beta gamma (a, x) (b, x) = 0 := by
  rw [← (finTwoArrowEquiv (Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  simp [restrictedChoi, cupOperatorOne, cupOperatorTwo, cycleOperator, cupOne, cupTwo,
    Finset.sum_add_distrib, ite_and]
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', hab, Ne.symm hab]

lemma entries (d : ℕ) (hd : 2 ≤ d) (alpha beta : ℝ) (gamma : ℂ) :
    let i0 : Fin d := ⟨0, by omega⟩
    let i1 : Fin d := ⟨1, by omega⟩
    restrictedChoi d alpha beta gamma (i1, ![i1, i0]) (i1, ![i1, i0]) = alpha ∧
    restrictedChoi d alpha beta gamma (i1, ![i0, i1]) (i1, ![i0, i1]) = beta ∧
    restrictedChoi d alpha beta gamma (i1, ![i0, i1]) (i1, ![i1, i0]) = gamma ∧
    restrictedChoi d alpha beta gamma (i1, ![i1, i0]) (i1, ![i0, i1]) = conj gamma := by
  intro i0 i1
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h10 : i1 ≠ i0 := Ne.symm h01
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [restrictedChoi, cupOperatorOne, cupOperatorTwo, cycleOperator, cupOne, cupTwo, h01, h10,
    Finset.sum_ite_eq, Finset.sum_ite_eq']


lemma choi_psd {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) : (choi (QAlgorithms.krausApply E)).PosSemidef := by
  have : choi (QAlgorithms.krausApply E) =
      (Matrix.of fun (j : K) (X : ι × κ) => star (E j X.2 X.1))ᴴ *
        (Matrix.of fun (j : K) (X : ι × κ) => star (E j X.2 X.1)) := by
    ext X Y
    rw [choi_kraus]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma forward (d : ℕ) (hd : 2 ≤ d) (alpha beta : ℝ) (gamma : ℂ)
    (T : Superop (Fin d) (CloningOutputs d 2)) (hT : QAlgorithms.IsChannel T)
    (hC : choi T = restrictedChoi d alpha beta gamma) :
    (d : ℝ) * (alpha + beta) + 2 * gamma.re = 1 ∧ Complex.normSq gamma ≤ alpha * beta := by
  obtain ⟨m, E, hK, hTE⟩ := hT
  have hc : choi T = choi (QAlgorithms.krausApply E) := by
    have : T = QAlgorithms.krausApply E := funext hTE
    rw [this]
  rw [hc] at hC
  refine ⟨?_, ?_⟩
  · have h := congrFun (congrFun hK ⟨0, by omega⟩) ⟨0, by omega⟩
    rw [kraus_sum_apply, hC, ptrace_restricted, Matrix.one_apply_eq] at h
    exact_mod_cast h
  · have hP := (choi_psd E).submatrix
      (![((⟨1, by omega⟩ : Fin d), ![(⟨1, by omega⟩ : Fin d), ⟨0, by omega⟩]),
        ((⟨1, by omega⟩ : Fin d), ![(⟨0, by omega⟩ : Fin d), ⟨1, by omega⟩])] : Fin 2 → CloningChoiBasis d 2)
    have hdet := hP.det_nonneg
    obtain ⟨e1, e2, e3, e4⟩ := entries d hd alpha beta gamma
    rw [Matrix.det_fin_two] at hdet
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hC] at hdet
    rw [e1, e2, e3, e4] at hdet
    have : (alpha : ℂ) * beta - conj gamma * gamma = ((alpha * beta - Complex.normSq gamma : ℝ) : ℂ) := by
      push_cast; rw [Complex.normSq_eq_conj_mul_self]
    rw [this, Complex.zero_le_real] at hdet
    linarith


def coef (alpha beta : ℝ) (gamma : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![(Real.sqrt alpha : ℂ), gamma / (Real.sqrt alpha : ℂ)],
    ![0, (Real.sqrt (beta - Complex.normSq gamma / alpha) : ℂ)]]

def krausP (d : ℕ) (alpha beta : ℝ) (gamma : ℂ) (p : Fin 2 × Fin d) :
    Matrix (CloningOutputs d 2) (Fin d) ℂ :=
  fun x a => coef alpha beta gamma p.1 0 * cupOne d p.2 (a, x) +
    coef alpha beta gamma p.1 1 * cupTwo d p.2 (a, x)

lemma choi_krausP (d : ℕ) (alpha beta : ℝ) (gamma : ℂ) (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hg : Complex.normSq gamma ≤ alpha * beta) (h0 : alpha = 0 → gamma = 0) :
    choi (QAlgorithms.krausApply (fun j : Fin (2 * d) => krausP d alpha beta gamma (finProdFinEquiv.symm j))) =
      restrictedChoi d alpha beta gamma := by
  set s : ℂ := (Real.sqrt alpha : ℂ) with hs_def
  set g : ℂ := gamma / s with hg_def
  set r : ℂ := (Real.sqrt (beta - Complex.normSq gamma / alpha) : ℂ) with hr_def
  have hss : s * conj s = alpha := by
    rw [hs_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  have hsg : s * conj g = conj gamma := by
    rcases ha.eq_or_lt with h | h
    · have : s = 0 := by rw [hs_def, ← h]; simp
      rw [this, h0 h.symm]; simp
    · have : s ≠ 0 := by rw [hs_def]; exact_mod_cast (Real.sqrt_pos.mpr h).ne'
      rw [hg_def, map_div₀, hs_def, Complex.conj_ofReal, ← hs_def]; field_simp
  have hgs : g * conj s = gamma := by
    rcases ha.eq_or_lt with h | h
    · have : s = 0 := by rw [hs_def, ← h]; simp
      rw [this, h0 h.symm]; simp
    · have : s ≠ 0 := by rw [hs_def]; exact_mod_cast (Real.sqrt_pos.mpr h).ne'
      rw [hg_def, hs_def, Complex.conj_ofReal, ← hs_def]; field_simp
  have hgg : g * conj g + r * conj r = beta := by
    have hnn : 0 ≤ beta - Complex.normSq gamma / alpha := by
      rcases ha.eq_or_lt with h | h
      · rw [← h]; simpa using hb
      · rw [sub_nonneg, div_le_iff₀ h]; linarith
    rw [hr_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hnn, Complex.mul_conj,
      hg_def, div_eq_mul_inv, Complex.normSq_mul, Complex.normSq_inv, hs_def, Complex.normSq_ofReal,
      Real.mul_self_sqrt ha]
    push_cast
    rcases ha.eq_or_lt with h | h
    · rw [← h]; simp
    · field_simp; ring
  ext X Y
  rw [choi_kraus, Equiv.sum_comp finProdFinEquiv.symm
    (fun p => krausP d alpha beta gamma p X.2 X.1 * star (krausP d alpha beta gamma p Y.2 Y.1)),
    Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
  simp only [restrictedChoi, cupOperatorOne, cupOperatorTwo, cycleOperator, Matrix.add_apply,
    Matrix.smul_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.mul_sum, star_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [krausP, coef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, star_add, star_mul',
    Complex.star_def, map_mul, map_zero, zero_mul, zero_add, RingHomCompTriple.comp_apply, RingHom.id_apply,
    Complex.conj_conj]
  rw [← hs_def, ← hg_def, ← hr_def]
  linear_combination (cupOne d i X * conj (cupOne d i Y)) * hss + (cupTwo d i X * conj (cupOne d i Y)) * hgs +
    (cupOne d i X * conj (cupTwo d i Y)) * hsg + (cupTwo d i X * conj (cupTwo d i Y)) * hgg

end S110P05
end QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms in
open QAlgorithms.Papers.Independent.Extend50.P05 in
open QAlgorithms.Papers.Independent.Information100.P34 (choi) in
theorem solution (d : ℕ) (hd : 2 ≤ d)
    (alpha beta : ℝ) (gamma : ℂ) :
    (∃ T : Superop (Fin d) (CloningOutputs d 2),
      IsChannel T ∧ choi T = restrictedChoi d alpha beta gamma) ↔
      (d : ℝ) * (alpha + beta) + 2 * gamma.re = 1 ∧
      Complex.normSq gamma ≤ alpha * beta := by
  constructor
  · rintro ⟨T, hT, hC⟩
    exact S110P05.forward d hd alpha beta gamma T hT hC
  · rintro ⟨h1, h2⟩
    have hre := Complex.re_sq_le_normSq gamma
    have hns := Complex.normSq_nonneg gamma
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have ha : 0 ≤ alpha := by
      by_contra hneg
      replace hneg := lt_of_not_ge hneg
      have hb : beta ≤ 0 := by nlinarith
      nlinarith [sq_nonneg (2 * gamma.re + alpha + beta), sq_nonneg (alpha - beta)]
    have hb : 0 ≤ beta := by
      by_contra hneg
      replace hneg := lt_of_not_ge hneg
      have hb : alpha ≤ 0 := by nlinarith
      nlinarith [sq_nonneg (2 * gamma.re + alpha + beta), sq_nonneg (alpha - beta)]
    have h0 : alpha = 0 → gamma = 0 := by
      intro h
      rw [h, zero_mul] at h2
      exact Complex.normSq_eq_zero.mp (le_antisymm h2 hns)
    refine ⟨QAlgorithms.krausApply
      (fun j : Fin (2 * d) => S110P05.krausP d alpha beta gamma (finProdFinEquiv.symm j)), ?_,
      S110P05.choi_krausP d alpha beta gamma ha hb h2 h0⟩
    refine ⟨2 * d, _, ?_, fun ρ => rfl⟩
    ext a b
    rw [S110P05.kraus_sum_apply, S110P05.choi_krausP d alpha beta gamma ha hb h2 h0]
    by_cases hab : a = b
    · subst hab
      rw [S110P05.ptrace_restricted, Matrix.one_apply_eq, h1]; simp
    · rw [S110P05.ptrace_restricted_ne _ _ _ _ _ _ (Ne.symm hab), Matrix.one_apply_ne hab]
