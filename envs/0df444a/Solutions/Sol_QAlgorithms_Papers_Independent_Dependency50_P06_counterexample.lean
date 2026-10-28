-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P06.counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:19:22.988597+00:00
-- url     : https://prove2.me/submissions/a0b619b3-6caa-4f51-bbdb-231541ce9880

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_choi_cptni_iff

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P06C

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P06
namespace P06 export QAlgorithms.Papers.Independent.Dependency50.P06 (pauliY) end P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)

/-- the real singlet amplitude -/
def w : Fin 2 × Fin 2 → ℂ := fun p =>
  if p = (0, 1) then (Real.sqrt 2 : ℂ)⁻¹ else if p = (1, 0) then -(Real.sqrt 2 : ℂ)⁻¹ else 0

lemma s_sq : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

lemma sq2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma singlet_eq (p q : Fin 2 × Fin 2) : singlet p q = w p * w q := by
  simp only [singlet, w]
  congr 1
  split_ifs <;> simp [Complex.conj_ofReal]

lemma w00 : w (0, 0) = 0 := by simp [w]
lemma w01 : w (0, 1) = (Real.sqrt 2 : ℂ)⁻¹ := by simp [w]
lemma w10 : w (1, 0) = -(Real.sqrt 2 : ℂ)⁻¹ := by simp [w]
lemma w11 : w (1, 1) = 0 := by simp [w]

lemma mixed2 {d : DecidableEq (Fin 2)} (i j : Fin 2) :
    @mixed (Fin 2) _ d i j = if i = j then 1 / 2 else 0 := by
  simp only [mixed, Matrix.smul_apply, Matrix.one_apply, Fintype.card_fin]
  split_ifs <;> simp

lemma choi_lfc {I O : Type} [Fintype I] {d : DecidableEq I} (J : Op (I × O)) :
    @choi I O d (linearFromChoi J) = J := by
  ext p q
  change (∑ a, ∑ b, (Matrix.single p.1 q.1 (1 : ℂ)) a b * J (a, p.2) (b, q.2)) = J p q
  simp [Matrix.single_apply, ite_and]

lemma superChoi_eq : superChoi (counterSupermap (Fin 2)) = counterChoi (Fin 2) := by
  unfold superChoi counterSupermap
  exact choi_lfc (I := Fin 2 × Fin 2) (O := Fin 2 × Fin 2) _

lemma cc_eq (p q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :
    counterChoi (Fin 2) p q = (if p.1.1 = q.1.1 then 1 else 0) * (w (p.1.2, p.2.1) * w (q.1.2, q.2.1))
      * (if p.2.2 = q.2.2 then 1 / 2 else 0) := by
  simp only [counterChoi, singlet_eq]; rw [mixed2]; congr


lemma star_w (p : Fin 2 × Fin 2) : star (w p) = w p := by
  simp only [w]; split_ifs <;> simp [Complex.conj_ofReal]

/-- the PSD summands of the counterexample Choi matrix -/
def g (a0 b1 : Fin 2) : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) → ℂ := fun p =>
  (if p.1.1 = a0 then 1 else 0) * (if p.2.2 = b1 then 1 else 0) * w (p.1.2, p.2.1) *
    (Real.sqrt 2 : ℂ)⁻¹

lemma cc_sum : counterChoi (Fin 2) =
    ∑ a0 : Fin 2, ∑ b1 : Fin 2, Matrix.vecMulVec (g a0 b1) (star (g a0 b1)) := by
  ext p q
  rw [cc_eq]
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, g, Pi.star_apply, star_mul', star_w,
    apply_ite star, star_one, star_zero, Complex.star_def, map_inv₀, Complex.conj_ofReal]
  have h : ∀ a b : ℂ, a * b * (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = a * b * (1/2) := by
    intro a b; rw [mul_assoc, s_sq]
  simp only [Fin.sum_univ_two]
  rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rcases q with ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
  fin_cases a <;> fin_cases a' <;> fin_cases d <;> fin_cases d' <;>
    simp [sq2] <;> linear_combination (w (b, c) * w (b', c')) * s_sq.symm

lemma cc_psd : (counterChoi (Fin 2)).PosSemidef := by
  rw [cc_sum]
  exact Matrix.posSemidef_sum _ fun a0 _ => Matrix.posSemidef_sum _ fun b1 _ =>
    Matrix.posSemidef_vecMulVec_self_star _

lemma trace_mul_transpose {n : Type} [Fintype n] (M K : Op n) :
    (M * Kᵀ).trace = ∑ p, ∑ q, M p q * K p q := by
  simp [Matrix.trace, Matrix.mul_apply]

lemma sm_eq (p q : (Fin 2 × Fin 2) × Fin 2) :
    superMarginal (counterChoi (Fin 2)) p q =
      (if p.1.1 = q.1.1 then 1 else 0) * (w (p.1.2, p.2) * w (q.1.2, q.2)) := by
  simp only [superMarginal, cc_eq, Fin.sum_univ_two]
  simp
  split_ifs <;> ring


lemma one2 {d : DecidableEq (Fin 2)} : (1 : Op (Fin 2)) = Matrix.single 0 0 1 + Matrix.single 1 1 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Matrix.single_apply]

lemma chan_facts {d : DecidableEq (Fin 2)} (N : QMap (Fin 2) (Fin 2)) (hN : @IsChannel _ _ _ _ d N) (ρ : Op (Fin 2))
    (hρ : ρ.PosSemidef) : (N 1).trace = 2 ∧ 0 ≤ ((N 1) * ρ).trace.re := by
  obtain ⟨m, E, hK, hE⟩ := hN
  rw [hE]; simp only [krausApply, mul_one]
  constructor
  · rw [Matrix.trace_sum]
    simp_rw [Matrix.trace_mul_comm (E _)]
    rw [← Matrix.trace_sum]
    unfold IsKrausFamily at hK
    have hK' : ∑ j, (E j)ᴴ * E j = (1 : Op (Fin 2)) := by convert hK
    rw [hK']; simp
  · rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_nonneg; intro j _
    have h := (hρ.conjTranspose_mul_mul_same (E j)).trace_nonneg
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    exact (Complex.nonneg_iff.mp h).1

lemma choi_ap {d : DecidableEq (Fin 2)} (N : QMap (Fin 2) (Fin 2)) (p q : Fin 2 × Fin 2) :
    choi N p q = N (Matrix.single p.1 q.1 1) p.2 q.2 := rfl

lemma kr_ap {d : DecidableEq (Fin 2)} (N : QMap (Fin 2) (Fin 2)) (ρ : Op (Fin 2)) (p q : (Fin 2 × Fin 2) × Fin 2) :
    Matrix.kronecker (choi N) ρ p q = choi N p.1 q.1 * ρ p.2 q.2 := rfl

lemma tr_cond {d : DecidableEq (Fin 2)} (N : QMap (Fin 2) (Fin 2)) (hN : @IsChannel _ _ _ _ d N) (ρ : Op (Fin 2))
    (hρ : IsDensityMatrix ρ) :
    (superMarginal (counterChoi (Fin 2)) * (Matrix.kronecker (choi N) ρ).transpose).trace.re ≤ 1 := by
  obtain ⟨h2, hpos⟩ := chan_facts N hN ρ hρ.1
  have htr : ρ 0 0 + ρ 1 1 = 1 := by
    have := hρ.2; simpa [Matrix.trace, Fin.sum_univ_two] using this
  rw [one2, map_add] at h2 hpos
  simp only [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diag, Matrix.add_apply] at h2 hpos
  set A := N (Matrix.single 0 0 1)
  set B := N (Matrix.single 1 1 1)
  have key : (superMarginal (counterChoi (Fin 2)) * (Matrix.kronecker (choi N) ρ).transpose).trace =
      1 - (1 / 2) * ((A 0 0 + B 0 0) * ρ 0 0 + (A 0 1 + B 0 1) * ρ 1 0 +
        ((A 1 0 + B 1 0) * ρ 0 1 + (A 1 1 + B 1 1) * ρ 1 1)) := by
    rw [trace_mul_transpose]
    simp only [sm_eq, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, w00, w01,
      w10, w11, choi_ap, kr_ap]
    simp only [Fin.isValue, if_true, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, if_false,
      OfNat.ofNat_ne_one, one_ne_zero, zero_ne_one, zero_mul, mul_zero, one_mul, add_zero, zero_add]
    change _ = 1 - (1 / 2) * ((A 0 0 + B 0 0) * ρ 0 0 + (A 0 1 + B 0 1) * ρ 1 0 +
        ((A 1 0 + B 1 0) * ρ 0 1 + (A 1 1 + B 1 1) * ρ 1 1))
    linear_combination ((A 0 0 + B 0 0) * ρ 1 1 - (A 0 1 + B 0 1) * ρ 1 0 -
      (A 1 0 + B 1 0) * ρ 0 1 + (A 1 1 + B 1 1) * ρ 0 0) * s_sq +
      (1 / 2) * (A 0 0 + B 0 0 + A 1 1 + B 1 1) * htr + (1 / 2) * h2
  rw [key]
  generalize ((A 0 0 + B 0 0) * ρ 0 0 + (A 0 1 + B 0 1) * ρ 1 0 +
        ((A 1 0 + B 1 0) * ρ 0 1 + (A 1 1 + B 1 1) * ρ 1 1)) = T at hpos ⊢
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re]
  norm_num
  linarith


lemma pres : IsCPTNIPreserving (counterSupermap (Fin 2)) := by
  rw [choi_cptni_iff, superChoi_eq]
  exact ⟨cc_psd, fun N hN ρ hρ => tr_cond N hN ρ hρ⟩

def hv (a0 : Fin 2) : (Fin 2 × Fin 2) × Fin 2 → ℂ := fun p =>
  (if p.1.1 = a0 then 1 else 0) * w (p.1.2, p.2)

lemma sm_sum : superMarginal (counterChoi (Fin 2)) =
    ∑ a0 : Fin 2, Matrix.vecMulVec (hv a0) (star (hv a0)) := by
  ext p q
  rw [sm_eq]
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, hv, Pi.star_apply, star_mul', star_w,
    apply_ite star, star_one, star_zero, Fin.sum_univ_two]
  rcases p with ⟨⟨a, b⟩, c⟩; rcases q with ⟨⟨a', b'⟩, c'⟩
  fin_cases a <;> fin_cases a' <;> simp

lemma mixed_density : IsDensityMatrix (mixed (Fin 2)) := by
  refine ⟨?_, ?_⟩
  · unfold mixed
    exact Matrix.PosSemidef.one.smul (by simp)
  · simp [mixed, Matrix.trace_smul]

lemma tester : IsTester counterTester := by
  refine ⟨?_, mixed (Fin 2), mixed_density, ?_⟩
  · unfold counterTester
    rw [sm_sum]
    exact (Matrix.posSemidef_sum _ fun a0 _ => Matrix.posSemidef_vecMulVec_self_star _).transpose
  · ext p q
    rcases p with ⟨a, b⟩; rcases q with ⟨a', b'⟩
    simp only [testerMarginal, counterTester, Matrix.transpose_apply, sm_eq, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, mixed2, Matrix.one_apply]
    fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;>
      simp [w00, w01, w10, w11, s_sq, mixed2]

lemma tester_value :
    (superMarginal (counterChoi (Fin 2)) * counterTester.transpose).trace.re = 2 := by
  have : (superMarginal (counterChoi (Fin 2)) * counterTester.transpose).trace = 2 := by
    rw [trace_mul_transpose]
    simp only [counterTester, Matrix.transpose_apply, sm_eq, Fintype.sum_prod_type,
      Fin.sum_univ_two, w00, w01, w10, w11]
    simp
    linear_combination (8 : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ ^ 2 + 1 / 2) * s_sq
  rw [this]; simp


lemma s_sq' : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = 1 / 2 := by rw [sq, s_sq]

lemma lfc_ap {I O : Type} [Fintype I] (J : Op (I × O)) (X : Op I) (i j : O) :
    linearFromChoi J X i j = ∑ a, ∑ b, X a b * J (a, i) (b, j) := rfl

lemma mixed_eq {d : DecidableEq (Fin 2)} :
    mixed (Fin 2) = (1 / 2 : ℂ) • (Matrix.single 0 0 1 + Matrix.single 1 1 1 : Op (Fin 2)) := by
  ext i j; rw [mixed2]; fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

lemma action {d : DecidableEq (Fin 2)} (N : QMap (Fin 2) (Fin 2)) (X : Op (Fin 2)) :
    superApply (counterSupermap (Fin 2)) N X =
      (N (mixed (Fin 2)) * (P06.pauliY * X * P06.pauliY).transpose).trace • mixed (Fin 2) := by
  obtain rfl : d = Classical.decEq _ := Subsingleton.elim _ _
  ext i j
  simp only [superApply, counterSupermap, lfc_ap, cc_eq, choi_ap, Fintype.sum_prod_type,
    Fin.sum_univ_two, w00, w01, w10, w11]
  rw [mixed_eq, map_smul, map_add]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two, P06.pauliY, Matrix.single_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> simp only [s_sq', Complex.I_sq] <;> ring

/-- the trace-out-and-swap channel `R0 × A0 → R1 × A1` -/
def J0 : Op ((Fin 2 × Fin 2) × (Fin 1 × Fin 2)) := fun p q =>
  if p.1.1 = p.2.2 ∧ q.1.1 = q.2.2 ∧ p.1.2 = q.1.2 then 1 else 0

def N0 : QMap (Fin 2 × Fin 2) (Fin 1 × Fin 2) := linearFromChoi J0

def EK (k : Fin 2) : Matrix (Fin 1 × Fin 2) (Fin 2 × Fin 2) ℂ := fun o x =>
  if x.1 = o.2 ∧ x.2 = k then 1 else 0

lemma n0_chan {d : DecidableEq (Fin 2 × Fin 2)} : @IsChannel _ _ _ _ d N0 := by
  refine ⟨2, EK, ?_, ?_⟩
  · ext x x'
    rcases x with ⟨a, b⟩; rcases x' with ⟨a', b'⟩
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, EK,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, Fin.sum_univ_one]
    fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;> simp
  · intro ρ
    ext o o'
    rcases o with ⟨u, b⟩; rcases o' with ⟨u', b'⟩
    simp only [N0, lfc_ap, J0, krausApply, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, EK, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one]
    fin_cases u; fin_cases u'
    fin_cases b <;> fin_cases b' <;> simp

lemma singlet_density : IsDensityMatrix singlet := by
  have h : singlet = Matrix.vecMulVec w (star w) := by
    ext p q; rw [singlet_eq]; simp [Matrix.vecMulVec_apply, star_w]
  refine ⟨h ▸ Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  simp only [Matrix.trace, Matrix.diag, singlet_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
    w00, w01, w10, w11]
  ring_nf; simp only [s_sq']; norm_num

lemma ext_value :
    (superExtend (counterSupermap (Fin 2)) N0 singlet).trace = 2 := by
  have hc : ∀ d', @choi _ _ d' N0 = J0 := fun _ => choi_lfc _
  unfold superExtend
  simp only [Matrix.trace, Matrix.diag, lfc_ap, hc]
  simp only [counterSupermap, linearFromChoi, LinearMap.coe_mk, AddHom.coe_mk,
    QAlgorithms.Papers.Independent.Information100.P34.fromChoi, singlet_eq,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one, cc_eq, J0, w00, w01, w10, w11]
  simp
  ring_nf
  rw [show ((Real.sqrt 2 : ℂ))⁻¹ ^ 4 = (((Real.sqrt 2 : ℂ))⁻¹ ^ 2) ^ 2 by ring, s_sq']
  norm_num


lemma not_complete : ¬ IsCompletelyCPTNIPreserving (counterSupermap (Fin 2)) := by
  rintro ⟨_, h⟩
  have := (h 2 1 (by norm_num) (by norm_num) N0 n0_chan).2 singlet singlet_density
  rw [ext_value] at this
  norm_num at this

end X4P06C

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P06 in
open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed) in
open QAlgorithms.Papers.Independent.Information100.P34 (choi) in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution :
    IsCPP (counterSupermap (Fin 2)) ∧
    IsCPTNIPreserving (counterSupermap (Fin 2)) ∧
    ¬ IsCompletelyCPTNIPreserving (counterSupermap (Fin 2)) ∧
    superChoi (counterSupermap (Fin 2)) = counterChoi (Fin 2) ∧
    IsTester counterTester ∧
    (superMarginal (counterChoi (Fin 2)) * counterTester.transpose).trace.re = 2 ∧
    ∀ (N : QMap (Fin 2) (Fin 2)) (X : Op (Fin 2)),
      superApply (counterSupermap (Fin 2)) N X =
        (N (mixed (Fin 2)) * (pauliY * X * pauliY).transpose).trace • mixed (Fin 2) :=
  ⟨X4P06C.pres.1, X4P06C.pres, X4P06C.not_complete, X4P06C.superChoi_eq, X4P06C.tester,
    X4P06C.tester_value, fun N X => X4P06C.action N X⟩

end
