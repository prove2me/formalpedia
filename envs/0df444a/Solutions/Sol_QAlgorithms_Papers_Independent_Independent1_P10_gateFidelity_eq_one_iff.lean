-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P10.gateFidelity_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:25:31.820933+00:00
-- url     : https://prove2.me/submissions/43809fb6-bde0-4f1c-82a2-e94d3078b62d

import Theorems.Thm_QAlgorithms_Papers_RoadmapX07_averageFidelity_eq_entanglementFidelity
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P10 MeasureTheory

private lemma matrix_variance {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (∑ i, ∑ j, Complex.normSq (A i j - ((A.trace / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) i j)) =
      (∑ i, ∑ j, Complex.normSq (A i j)) - Complex.normSq A.trace / (d : ℝ) := by
  classical
  let c := A.trace / (d : ℂ)
  have h1 : (∑ i : Fin d, ∑ j : Fin d, Complex.normSq ((c • (1 : Matrix (Fin d) (Fin d) ℂ)) i j)) =
      (d : ℝ) * Complex.normSq c := by
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_one, mul_zero, apply_ite, map_zero]
    simp
  have h2 : (∑ i : Fin d, ∑ j : Fin d, (A i j * conj ((c • (1 : Matrix (Fin d) (Fin d) ℂ)) i j)).re) =
      (A.trace * conj c).re := by
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_one, mul_zero,
      apply_ite, map_zero, Complex.zero_re]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    change (∑ i, (A i i * conj c).re) = ((∑ i, A i i) * conj c).re
    rw [Finset.sum_mul, Complex.re_sum]
  change (∑ i, ∑ j, Complex.normSq (A i j - (c • (1 : Matrix (Fin d) (Fin d) ℂ)) i j)) = _
  simp_rw [Complex.normSq_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h1, h2]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hc : Complex.normSq c = Complex.normSq A.trace / (d : ℝ)^2 := by
    simp [c, pow_two]
  have ht : (A.trace * conj c).re = Complex.normSq A.trace / (d : ℝ) := by
    simp [c, Complex.normSq_apply]
    ring
  rw [hc, ht]
  field_simp
  ring

private lemma kraus_energy {d m : ℕ} (K : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hK : IsKrausFamily K) :
    (∑ a, ∑ i, ∑ j, Complex.normSq (K a i j)) = (d : ℝ) := by
  unfold IsKrausFamily at hK
  have ht := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => A.trace.re) hK
  change (∑ a, (K a)ᴴ * K a).trace.re = (1 : Matrix (Fin d) (Fin d) ℂ).trace.re at ht
  rw [Matrix.trace_sum, Complex.re_sum] at ht
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] at ht
  simp only [Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Complex.one_re] at ht
  convert ht using 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

private lemma entanglement_kraus (d : ℕ) (hd : 0 < d) (m : ℕ)
    (K : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    QuditFidelity.entanglementFidelity d hd (krausApply K) =
      (∑ a, Complex.normSq (K a).trace) / (d : ℝ)^2 := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let P := pureDensity (finiteMaxEntangled (Fin d))
  have hs : (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : ℂ)^2 = (d : ℂ)⁻¹ := by
    norm_cast
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hP (a b : Fin d × Fin d) :
      P a b = if a.1 = a.2 ∧ b.1 = b.2 then (d : ℂ)⁻¹ else 0 := by
    dsimp [P, pureDensity, finiteMaxEntangled]
    simp only [Fintype.card_fin, apply_ite, map_zero]
    split_ifs <;> simp_all [← pow_two]
  have hT (a i b j : Fin d) :
      idTensorSuperop (R := Fin d) (krausApply K) P (a,i) (b,j) =
        ∑ k, (d : ℂ)⁻¹ * K k i a * conj (K k j b) := by
    simp only [idTensorSuperop, Matrix.of_apply, krausApply, Matrix.sum_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, hP, ite_and]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq]
    apply Finset.sum_congr rfl
    intro k _
    simp [mul_comm, Finset.mem_univ]
  have htr : (P * idTensorSuperop (R := Fin d) (krausApply K) P).trace =
      (d : ℂ)⁻¹ ^ 2 * ∑ k, (K k).trace * conj (K k).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      hP, hT, ite_and]
    simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
    simp only [mul_assoc]
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  change effectProb P (idTensorSuperop (R := Fin d) (krausApply K) P) = _
  rw [effectProb, htr]
  simp only [Complex.mul_conj, ← Complex.ofReal_sum]
  have hr : (d : ℂ)⁻¹ ^ 2 = (((d : ℝ)⁻¹ ^ 2 : ℝ) : ℂ) := by simp
  rw [hr, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp [div_eq_mul_inv, inv_pow, mul_comm]

private lemma unit_entanglement_identity (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (hF : QuditFidelity.entanglementFidelity d hd E = 1) : E = id := by
  classical
  obtain ⟨m, K, hK, hE⟩ := hE
  have hEK : E = krausApply K := funext hE
  rw [hEK, entanglement_kraus d hd m K] at hF
  have htrace : (∑ a, Complex.normSq (K a).trace) = (d : ℝ)^2 :=
    (div_eq_one_iff_eq (by positivity)).mp hF
  let c := fun a : Fin m => (K a).trace / (d : ℂ)
  have hvar : (∑ a, ∑ i, ∑ j,
      Complex.normSq (K a i j - (c a • (1 : Matrix (Fin d) (Fin d) ℂ)) i j)) = 0 := by
    simp only [c, matrix_variance hd, Finset.sum_sub_distrib, ← Finset.sum_div]
    rw [kraus_energy K hK, htrace]
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    field_simp
    ring
  have hz (a : Fin m) (i j : Fin d) :
      Complex.normSq (K a i j - (c a • (1 : Matrix (Fin d) (Fin d) ℂ)) i j) = 0 := by
    have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)))).mp hvar a (Finset.mem_univ a)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))).mp ha i (Finset.mem_univ i)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp hi j (Finset.mem_univ j)
  have hscalar (a : Fin m) : K a = c a • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    ext i j
    exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp (hz a i j))
  have hnorm : ∑ a, conj (c a) * c a = 1 := by
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => A ⟨0, hd⟩ ⟨0, hd⟩) hK
    simpa [IsKrausFamily, hscalar, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.sum_apply, Matrix.smul_apply, mul_comm] using h
  rw [hEK]
  funext X
  simp only [krausApply, hscalar, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  simp only [starRingEnd_apply] at hnorm
  rw [← Finset.sum_smul, hnorm, one_smul]
  rfl

private lemma output_conjugate_channel {d : ℕ}
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsChannel (conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ)) ∘ E) := by
  obtain ⟨m, K, hK, hE⟩ := hE
  refine ⟨m, fun j => star (U : Matrix (Fin d) (Fin d) ℂ) * K j, ?_, ?_⟩
  · unfold IsKrausFamily at hK ⊢
    convert hK using 1
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (K j)ᴴ * ((U : Matrix (Fin d) (Fin d) ℂ) * star (U : Matrix (Fin d) (Fin d) ℂ)) * K j := by
        simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [(Matrix.mem_unitaryGroup_iff.mp U.property), Matrix.mul_one]
  · intro X
    simp only [Function.comp_apply, conjSuperop, hE, krausApply,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

private lemma entanglement_identity (d : ℕ) (hd : 0 < d) :
    QuditFidelity.entanglementFidelity d hd id = 1 := by
  have hk : krausApply (fun _ : Fin 1 => (1 : Matrix (Fin d) (Fin d) ℂ)) = id := by
    funext X
    simp [krausApply]
  rw [← hk, entanglement_kraus d hd 1]
  simp [Matrix.trace_one, pow_two, Nat.ne_of_gt hd]

/-- Nielsen's claim after Eq. (2), reduced to Eq. (3) using the equality case
of the Kraus trace bound. Equality holds on every operator. -/
theorem solution (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    gateFidelity d hd E U = 1 ↔ E = conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) := by
  have hC := output_conjugate_channel E hE U
  have hunit := Matrix.mem_unitaryGroup_iff.mp U.property
  have hinv := Matrix.mem_unitaryGroup_iff'.mp U.property
  change (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 at hunit
  change (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * (U : Matrix (Fin d) (Fin d) ℂ) = 1 at hinv
  have hformula := QAlgorithms.Papers.RoadmapX07.averageFidelity_eq_entanglementFidelity d hd _ hC
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hden : (d : ℝ) + 1 ≠ 0 := by positivity
  constructor
  · intro h
    change QuditFidelity.averageFidelity d hd
      (conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ)) ∘ E) = 1 at h
    rw [hformula] at h
    have heq := (div_eq_one_iff_eq hden).mp h
    have hF : QuditFidelity.entanglementFidelity d hd
        (conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ)) ∘ E) = 1 := by
      nlinarith
    have hId := unit_entanglement_identity d hd _ hC hF
    funext X
    have hX := congrArg (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ)) (congrFun hId X)
    simp only [Function.comp_apply, conjSuperop, id_eq, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hunit, Matrix.one_mul] at hX
    simpa only [conjSuperop, Matrix.mul_assoc, hunit, Matrix.mul_one] using hX
  · intro h
    have hId : conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ)) ∘ E = id := by
      rw [h]
      funext X
      simp only [Function.comp_apply, conjSuperop, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hinv, Matrix.one_mul, id_eq]
      simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]
    unfold gateFidelity
    rw [hformula, hId, entanglement_identity d hd]
    field_simp
