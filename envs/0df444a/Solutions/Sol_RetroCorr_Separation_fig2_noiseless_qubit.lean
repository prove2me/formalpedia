-- Prove2me | solution 1 for RetroCorr.Separation.fig2_noiseless_qubit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:36:29.147673+00:00
-- url     : https://prove2.me/submissions/bfb39f76-6ef5-4ad1-8bae-aa2a942e1674

import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel
import Definitions.Def_RetroCorr_Separation_TwoWay

open RetroCorr.Separation MeasureTheory

namespace M14Fig2

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

abbrev Q := QAlgorithms.Qubits 1

def σ : Q ≃ Fin 2 := (Equiv.funUnique (Fin 1) Bool).trans finTwoEquiv.symm

def eq8 : Fin 8 ≃ Fin 2 × (Fin 2 × Fin 2) := Fintype.equivOfCardEq (by simp)

def f2 : Fin 2 ≃ Fin 2 × Fin 1 := (Equiv.prodUnique (Fin 2) (Fin 1)).symm

def s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

lemma s_star : (starRingEnd ℂ) s = s := by simp [s]

lemma s_inv_mul : s⁻¹ * s⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, s, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  simp

lemma s_inv_sq : s⁻¹ * star s⁻¹ = (2 : ℂ)⁻¹ := by
  have h : star s = s := by simp [s]
  rw [star_inv₀, h, ← mul_inv, s, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  simp

/-- relabelling Q → Fin 2 -/
def Pσ : Matrix Q (Fin 2) ℂ := Matrix.of fun q x => if σ q = x then 1 else 0

lemma Pσ_H_Pσ : Pσᴴ * Pσ = 1 := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Pσ, Matrix.of_apply, Matrix.one_apply]
  rw [← σ.symm.sum_comp]
  simp [eq_comm]

lemma Pσ_Pσ_H : Pσ * Pσᴴ = 1 := by
  ext q q'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Pσ, Matrix.of_apply, Matrix.one_apply]
  simp [σ.injective.eq_iff]

/-- ebit-appending isometry -/
def J : Matrix (Fin 8) (Fin 2) ℂ := Matrix.of fun p x =>
  if (eq8 p).1 = (eq8 p).2.1 ∧ (eq8 p).2.2 = x then s⁻¹ else 0

lemma J_apply (r c x y : Fin 2) : J (eq8.symm (r, (c, x))) y = if r = c ∧ x = y then s⁻¹ else 0 := by
  simp [J]

lemma J_apply' (r : Fin 2) (ι : Fin 2 × Fin 2) (y : Fin 2) :
    J (eq8.symm (r, ι)) y = if r = ι.1 ∧ ι.2 = y then s⁻¹ else 0 := by
  simp [J]

lemma J_H_J : Jᴴ * J = 1 := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← eq8.symm.sum_comp]
  simp only [Fintype.sum_prod_type, J_apply]
  fin_cases x <;> fin_cases x' <;> simp [Fin.sum_univ_two, s_star, s_inv_mul]

def V : Matrix (Fin 8) Q ℂ := J * Pσᴴ

lemma V_H_V : Vᴴ * V = 1 := by
  rw [V, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Jᴴ, J_H_J, Matrix.one_mul, Pσ_Pσ_H]

def enc : QAlgorithms.Superop Q (Fin 8) := QAlgorithms.conjSuperop V

lemma enc_channel : QAlgorithms.IsChannel enc :=
  ⟨1, fun _ => V, by simp [QAlgorithms.IsKrausFamily, V_H_V],
    fun ρ => by simp [QAlgorithms.krausApply, enc, QAlgorithms.conjSuperop]⟩

def E (W : Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 2) : Matrix (Fin 1) (Fin 2) ℂ :=
  Matrix.of fun _ r => (W : Matrix (Fin 2) (Fin 2) ℂ) r i

lemma E_kraus (W : Matrix.unitaryGroup (Fin 2) ℂ) : QAlgorithms.IsKrausFamily (E W) := by
  have hU : (W : Matrix (Fin 2) (Fin 2) ℂ) * star (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp W.2
  unfold QAlgorithms.IsKrausFamily
  ext r r'
  have := congrFun (congrFun hU r') r
  simp only [Matrix.mul_apply, Matrix.star_apply] at this
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, E, Matrix.of_apply,
    Finset.univ_unique, Finset.sum_singleton]
  rw [Matrix.one_apply] at this ⊢
  rw [← Finset.sum_congr rfl fun _ _ => mul_comm _ _, this]
  simp [eq_comm]

def Dm (U : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix Q (Fin 2) ℂ :=
  Pσ * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ

lemma Dm_kraus (U : Matrix.unitaryGroup (Fin 2) ℂ) : (Dm U)ᴴ * Dm U = 1 := by
  have hU : (U : Matrix (Fin 2) (Fin 2) ℂ) * star (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  rw [Dm, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Pσᴴ, Pσ_H_Pσ, Matrix.one_mul]
  exact hU

def D (U : Matrix.unitaryGroup (Fin 2) ℂ) : QAlgorithms.Superop (Fin 2) Q :=
  QAlgorithms.conjSuperop (Dm U)

lemma D_channel (U : Matrix.unitaryGroup (Fin 2) ℂ) : QAlgorithms.IsChannel (D U) :=
  ⟨1, fun _ => Dm U, by simp [QAlgorithms.IsKrausFamily, Dm_kraus],
    fun ρ => by simp [QAlgorithms.krausApply, D, QAlgorithms.conjSuperop]⟩

def run : QAlgorithms.Superop (Fin 8 × Fin 1) Q :=
  fun X => ∫ k, (fun Y => ∑ i, (fun Z => D (k.2 i) (QAlgorithms.traceLeft Z))
      (aliceBranch (b := 2) (E k.1 i) Y))
    (sendVia eq8 f2 (retroBranch 2 2 k) X) ∂(flagLaw 2 2)

lemma alice_valid (k : Flag 2 2) :
    Adaptive (flagLaw 2 2) (retroBranch 2 2) 1 (n := 0)
      (fun Y => ∑ i, (fun Z => D (k.2 i) (QAlgorithms.traceLeft Z))
        (aliceBranch (b := 2) (E k.1 i) Y)) :=
  Adaptive.alice (n := 0) (a := 2) (b := 2) (h := 1) (r := 2) (E k.1) (E_kraus k.1)
    (fun i Z => D (k.2 i) (QAlgorithms.traceLeft Z))
    (fun i => Adaptive.finish (a := 1) (b := 2) (D (k.2 i)) (D_channel _))

lemma run_valid : Adaptive (flagLaw 2 2) (retroBranch 2 2) 1 (n := 1) run :=
  Adaptive.send (n := 0) (a := 8) (a' := 2) (b := 1) (b' := 2) eq8 f2 _ alice_valid

def code : TwoWayCode (flagLaw 2 2) (retroBranch 2 2) 1 1 where
  memory := 8
  encode := enc
  encode_channel := enc_channel
  run := run
  valid := run_valid


lemma enc_eq (ρ : Matrix Q Q ℂ) : enc ρ = J * (Pσᴴ * ρ * Pσ) * Jᴴ := by
  simp [enc, QAlgorithms.conjSuperop, V, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma X0_apply (ρ : Matrix Q Q ℂ) (r r' : Fin 2) (ι ι' : Fin 2 × Fin 2) (u u' : Fin 1) :
    Matrix.kronecker (enc ρ) (1 : Matrix (Fin 1) (Fin 1) ℂ) (eq8.symm (r, ι), u) (eq8.symm (r', ι'), u')
      = if r = ι.1 ∧ r' = ι'.1 then (2 : ℂ)⁻¹ * (Pσᴴ * ρ * Pσ) ι.2 ι'.2 else 0 := by
  rw [enc_eq]
  generalize Pσᴴ * ρ * Pσ = M
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    J_apply', Subsingleton.elim u u', Matrix.one_apply_eq, mul_one]
  by_cases h1 : r = ι.1 <;> by_cases h2 : r' = ι'.1 <;> simp [h1, h2]
  obtain ⟨c', y'⟩ := ι'
  fin_cases y' <;> simp [s_star] <;> rw [← s_inv_mul] <;> ring

lemma T_eq (W : Matrix.unitaryGroup (Fin 2) ℂ) (j r r' : Fin 2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    QAlgorithms.traceLeft (Matrix.kronecker (basisProj W j) (1 : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.of fun ι ι' : Fin 2 × Fin 2 => if r = ι.1 ∧ r' = ι'.1 then (2 : ℂ)⁻¹ * M ι.2 ι'.2 else 0)
      = ((2 : ℂ)⁻¹ * basisProj W j r' r) • M := by
  ext x x'
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Fin.sum_univ_two]
  fin_cases r <;> fin_cases r' <;> fin_cases x <;> simp <;> ring


lemma Z_eq (ρ : Matrix Q Q ℂ) (k : Flag 2 2) :
    sendVia eq8 f2 (retroBranch 2 2 k) (Matrix.kronecker (enc ρ) (1 : Matrix (Fin 1) (Fin 1) ℂ)) =
      Matrix.of fun p q => ∑ j, ((2 : ℂ)⁻¹ * basisProj k.1 j q.1 p.1) *
        ((k.2 j : Matrix (Fin 2) (Fin 2) ℂ) * (Pσᴴ * ρ * Pσ) * (k.2 j : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) p.2 q.2 := by
  ext p q
  have hY : (Matrix.of fun ι ι' : Fin 2 × Fin 2 =>
      Matrix.kronecker (enc ρ) (1 : Matrix (Fin 1) (Fin 1) ℂ) (eq8.symm (p.1, ι), (f2 p.2).2)
        (eq8.symm (q.1, ι'), (f2 q.2).2)) = Matrix.of fun ι ι' : Fin 2 × Fin 2 =>
      if p.1 = ι.1 ∧ q.1 = ι'.1 then (2 : ℂ)⁻¹ * (Pσᴴ * ρ * Pσ) ι.2 ι'.2 else 0 := by
    ext ι ι'
    exact X0_apply ρ p.1 q.1 ι ι' _ _
  simp only [sendVia]
  rw [hY]
  simp only [retroBranch, T_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  simp [f2]

lemma inner (W : Matrix.unitaryGroup (Fin 2) ℂ) (i j : Fin 2) :
    ∑ r, ∑ r', (W : Matrix (Fin 2) (Fin 2) ℂ) r i * basisProj W j r' r *
      star ((W : Matrix (Fin 2) (Fin 2) ℂ) r' i) = if j = i then 1 else 0 := by
  have hU : star (W : Matrix (Fin 2) (Fin 2) ℂ) * (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp W.2
  set M : Matrix (Fin 2) (Fin 2) ℂ := (W : Matrix (Fin 2) (Fin 2) ℂ) with hM
  have h1 : ∀ a b, ∑ r, star (M r a) * M r b = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun hU a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  calc _ = (∑ r, star (M r j) * M r i) * (∑ r', star (M r' i) * M r' j) := by
        simp only [basisProj, Matrix.of_apply, Fin.sum_univ_two, ← hM]; ring
    _ = _ := by rw [h1, h1]; split_ifs <;> simp_all

lemma B_eq (W : Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 2) (G : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    QAlgorithms.traceLeft (aliceBranch (b := 2) (E W i)
      (Matrix.of fun p q : Fin 2 × Fin 2 => ∑ j, ((2 : ℂ)⁻¹ * basisProj W j q.1 p.1) * G j p.2 q.2))
      = (2 : ℂ)⁻¹ • G i := by
  ext y y'
  simp only [QAlgorithms.traceLeft, aliceBranch, QAlgorithms.conjSuperop, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, E, Matrix.of_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul]
  simp
  have h0 := inner W i 0
  have h1 := inner W i 1
  simp only [Fin.sum_univ_two] at h0 h1
  fin_cases i <;> fin_cases y' <;> simp at h0 h1 ⊢ <;>
    first
    | linear_combination (2⁻¹ * G 0 y 0) * h0 + (2⁻¹ * G 1 y 0) * h1
    | linear_combination (2⁻¹ * G 0 y 1) * h0 + (2⁻¹ * G 1 y 1) * h1


lemma D_apply (U : Matrix.unitaryGroup (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    D U ((2 : ℂ)⁻¹ • ((U : Matrix (Fin 2) (Fin 2) ℂ) * M * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)) =
      (2 : ℂ)⁻¹ • (Pσ * M * Pσᴴ) := by
  have hUH : (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h' : ∀ X : Matrix (Fin 2) Q ℂ, (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * ((U : Matrix (Fin 2) (Fin 2) ℂ) * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hUH, Matrix.one_mul]
  have h'' : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * ((U : Matrix (Fin 2) (Fin 2) ℂ) * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hUH, Matrix.one_mul]
  simp only [D, QAlgorithms.conjSuperop, Dm, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h', h'']

lemma Pσ_conj (ρ : Matrix Q Q ℂ) : Pσ * (Pσᴴ * ρ * Pσ) * Pσᴴ = ρ := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Pσ_Pσ_H, Matrix.one_mul, Matrix.mul_assoc, Pσ_Pσ_H,
    Matrix.mul_one]

lemma branch_eq (ρ : Matrix Q Q ℂ) (k : Flag 2 2) :
    ∑ i, D (k.2 i) (QAlgorithms.traceLeft (aliceBranch (b := 2) (E k.1 i)
      (sendVia eq8 f2 (retroBranch 2 2 k) (Matrix.kronecker (enc ρ) (1 : Matrix (Fin 1) (Fin 1) ℂ))))) = ρ := by
  rw [Z_eq]
  have hB := fun i => B_eq k.1 i (fun j => (k.2 j : Matrix (Fin 2) (Fin 2) ℂ) * (Pσᴴ * ρ * Pσ) *
    (k.2 j : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
  have h2 : ∀ i, D (k.2 i) (QAlgorithms.traceLeft (aliceBranch (b := 2) (E k.1 i)
      (Matrix.of fun p q : Fin 2 × Fin 2 => ∑ j, ((2 : ℂ)⁻¹ * basisProj k.1 j q.1 p.1) *
        ((k.2 j : Matrix (Fin 2) (Fin 2) ℂ) * (Pσᴴ * ρ * Pσ) * (k.2 j : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) p.2 q.2)))
      = (2 : ℂ)⁻¹ • ρ := by
    intro i
    erw [hB i, D_apply, Pσ_conj]
  erw [Finset.sum_congr rfl fun i _ => h2 i]
  rw [Fin.sum_univ_two, ← add_smul]; norm_num

instance haarProb (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

instance flagProb : IsProbabilityMeasure (flagLaw 2 2) := by
  unfold flagLaw; infer_instance

lemma code_output (ρ : Matrix Q Q ℂ) : code.output ρ = ρ := by
  simp only [TwoWayCode.output, code, run]
  simp only [branch_eq]
  simp

end

end M14Fig2

theorem solution :
    ∃ P : TwoWayCode (flagLaw 2 2) (retroBranch 2 2) 1 1,
      ∀ ρ : Matrix (QAlgorithms.Qubits 1) (QAlgorithms.Qubits 1) ℂ,
        QAlgorithms.IsDensityMatrix ρ → P.output ρ = ρ :=
  ⟨M14Fig2.code, fun ρ _ => M14Fig2.code_output ρ⟩
