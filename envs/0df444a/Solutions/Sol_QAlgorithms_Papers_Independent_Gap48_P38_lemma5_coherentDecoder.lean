-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P38.lemma5_coherentDecoder
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:57:36.670064+00:00
-- url     : https://prove2.me/submissions/58068e1a-ee33-4e8f-87fb-fee544863a62

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder InnerProductSpace

namespace X4CD

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

variable {n : Type} [Fintype n] [DecidableEq n]

lemma act_apply (M : Matrix n n ℂ) (a : EuclideanSpace ℂ n) :
    act M a = WithLp.toLp 2 (M *ᵥ WithLp.ofLp a) := rfl

lemma inner_act (M : Matrix n n ℂ) (a b : EuclideanSpace ℂ n) :
    ⟪a, act M b⟫_ℂ = star (WithLp.ofLp a) ⬝ᵥ (M *ᵥ WithLp.ofLp b) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, act_apply, dotProduct_comm]

lemma adj (M : Matrix n n ℂ) (a b : EuclideanSpace ℂ n) :
    ⟪act M a, b⟫_ℂ = ⟪a, act Mᴴ b⟫_ℂ := by
  rw [inner_act, EuclideanSpace.inner_eq_star_dotProduct, act_apply]
  simp only [WithLp.ofLp_toLp]
  rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec]

lemma act_mul (M N : Matrix n n ℂ) (a : EuclideanSpace ℂ n) : act M (act N a) = act (M * N) a := by
  simp [act_apply, Matrix.mulVec_mulVec]

lemma act_smul (M : Matrix n n ℂ) (c : ℂ) (a : EuclideanSpace ℂ n) : act M (c • a) = c • act M a := by
  simp [act_apply, Matrix.mulVec_smul]

lemma act_sub (M : Matrix n n ℂ) (a b : EuclideanSpace ℂ n) : act M (a - b) = act M a - act M b := by
  simp [act_apply, Matrix.mulVec_sub]

lemma psd_re {P : Matrix n n ℂ} (hP : P.PosSemidef) (a : EuclideanSpace ℂ n) :
    0 ≤ (⟪a, act P a⟫_ℂ).re := by
  rw [inner_act]
  exact (Complex.nonneg_iff.1 (hP.dotProduct_mulVec_nonneg _)).1

lemma re_le {A B : Matrix n n ℂ} (h : (A - B).PosSemidef) (a : EuclideanSpace ℂ n) :
    (⟪a, act B a⟫_ℂ).re ≤ (⟪a, act A a⟫_ℂ).re := by
  have := psd_re h a
  rw [inner_act, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at this
  rw [inner_act, inner_act]; linarith

lemma act_one (a : EuclideanSpace ℂ n) : act (1 : Matrix n n ℂ) a = a := by
  simp [act_apply]

/-- `|⟪a, A v⟫| ≤ ‖v‖` when `A` is Hermitian with `A² ≤ 1` and `‖a‖ = 1`. -/
lemma bound_v {A L : Matrix n n ℂ} (hA : A.IsHermitian) (hAA : A * A = L)
    (h1 : (1 - L).PosSemidef) (a v : EuclideanSpace ℂ n) (ha : ‖a‖ = 1) :
    ‖⟪a, act A v⟫_ℂ‖ ≤ ‖v‖ := by
  have hAa : ‖act A a‖ ≤ 1 := by
    have e : ‖act A a‖ ^ 2 = (⟪a, act L a⟫_ℂ).re := by
      have h := adj A a (act A a)
      rw [hA.eq] at h
      rw [← hAA, ← act_mul, ← h]
      exact norm_sq_eq_re_inner (𝕜 := ℂ) _
    have := re_le h1 a
    have h11 : (⟪a, a⟫_ℂ).re = 1 := by rw [inner_self_eq_norm_sq_to_K, ha]; simp
    rw [act_one, h11] at this
    nlinarith [norm_nonneg (act A a)]
  calc ‖⟪a, act A v⟫_ℂ‖ = ‖⟪act A a, v⟫_ℂ‖ := by rw [adj, hA.eq]
    _ ≤ ‖act A a‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ 1 * ‖v‖ := by gcongr
    _ = ‖v‖ := one_mul _


lemma phase (w : ℂ) : ∃ c : ℂ, ‖c‖ = 1 ∧ c * w = (‖w‖ : ℂ) := by
  by_cases hw : w = 0
  · exact ⟨1, by simp, by simp [hw]⟩
  · have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
    refine ⟨conj w / ‖w‖, ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hw)]
    · rw [div_mul_eq_mul_div, mul_comm (conj w), Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp
      push_cast; ring

lemma key {A L : Matrix n n ℂ} (hA : A.IsHermitian) (hAA : A * A = L)
    (h1 : (1 - L).PosSemidef) (h2 : (A - L).PosSemidef) (a b : EuclideanSpace ℂ n)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (⟪a, act L a⟫_ℂ).re - Real.sqrt (2 * (1 - Complex.normSq ⟪a, b⟫_ℂ)) ≤ ‖⟪a, act A b⟫_ℂ‖ := by
  set w := ⟪a, b⟫_ℂ with hw
  obtain ⟨c, hc, hcw⟩ := phase w
  set φ := c • b with hφ
  have hφn : ‖φ‖ = 1 := by rw [hφ, norm_smul, hc, hb, one_mul]
  have hinφ : ⟪a, φ⟫_ℂ = (‖w‖ : ℂ) := by rw [hφ, inner_smul_right, hcw]
  have hsame : ‖⟪a, act A φ⟫_ℂ‖ = ‖⟪a, act A b⟫_ℂ‖ := by
    rw [hφ, act_smul, inner_smul_right, norm_mul, hc, one_mul]
  have hw1 : ‖w‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) a b
    rw [ha, hb, one_mul] at this; exact this
  have hd : ‖a - φ‖ ≤ Real.sqrt (2 * (1 - Complex.normSq w)) := by
    apply Real.le_sqrt_of_sq_le
    rw [@norm_sub_sq ℂ, ha, hφn, hinφ, Complex.normSq_eq_norm_sq]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    nlinarith [norm_nonneg w]
  have hre : (⟪a, act A φ⟫_ℂ).re = (⟪a, act A a⟫_ℂ).re - (⟪a, act A (a - φ)⟫_ℂ).re := by
    rw [act_sub, inner_sub_right, Complex.sub_re]; ring
  have hL := re_le h2 a
  have hv := bound_v hA hAA h1 a (a - φ) ha
  have hv' : (⟪a, act A (a - φ)⟫_ℂ).re ≤ ‖a - φ‖ := (Complex.re_le_norm _).trans hv
  have hn : (⟪a, act A φ⟫_ℂ).re ≤ ‖⟪a, act A φ⟫_ℂ‖ := Complex.re_le_norm _
  rw [← hsame]
  linarith


end X4CD

namespace X4CDS

open scoped Matrix.Norms.L2Operator MatrixOrder
set_option backward.isDefEq.respectTransparency false

variable {X : Type} [Fintype X] [DecidableEq X]

lemma cont (f : ℝ → ℝ) (A : Matrix X X ℂ) : ContinuousOn f (spectrum ℝ A) :=
  (Matrix.finite_real_spectrum (A := A)).continuousOn f

lemma sqrt_herm (P : Matrix X X ℂ) : (cfc Real.sqrt P).IsHermitian := cfc_predicate _ P

lemma sqrt_mul (P : Matrix X X ℂ) (hP : P.PosSemidef) : cfc Real.sqrt P * cfc Real.sqrt P = P := by
  have h0 : 0 ≤ P := hP.nonneg
  rw [← cfc_mul (hf := cont _ P) (hg := cont _ P)]
  conv_rhs => rw [← cfc_id' ℝ P]
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 hx)

lemma sqrt_sub (P : Matrix X X ℂ) (hP : P.PosSemidef) (h1 : (1 - P).PosSemidef) :
    (cfc Real.sqrt P - P).PosSemidef := by
  have h0 : 0 ≤ P := hP.nonneg
  have hle : P ≤ 1 := sub_nonneg.1 h1.nonneg
  have hsa : IsSelfAdjoint P := IsSelfAdjoint.of_nonneg h0
  have hspec : ∀ x ∈ spectrum ℝ P, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    refine ⟨spectrum_nonneg_of_nonneg h0 hx, ?_⟩
    exact (le_algebraMap_iff_spectrum_le (r := (1 : ℝ)) (a := P) hsa).1 (by simpa using hle) x hx
  have : P ≤ cfc Real.sqrt P := by
    conv_lhs => rw [← cfc_id' ℝ P]
    refine cfc_mono (fun x hx => ?_) (cont _ P) (cont _ P)
    obtain ⟨a, b⟩ := hspec x hx
    calc x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt a).symm
      _ ≤ Real.sqrt x * 1 := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg x)
          exact Real.sqrt_le_one.mpr b
      _ = Real.sqrt x := mul_one _
  exact Matrix.le_iff.1 this

end X4CDS

namespace X4CDM

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise InnerProductSpace Kronecker
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38 X4CD

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

lemma kron_herm {S : Matrix X X ℂ} (h : S.IsHermitian) : (S ⊗ₖ (1 : Matrix Y Y ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_kronecker, h.eq, Matrix.conjTranspose_one]

lemma kron_mul (A B : Matrix X X ℂ) :
    (A ⊗ₖ (1 : Matrix Y Y ℂ)) * (B ⊗ₖ (1 : Matrix Y Y ℂ)) = (A * B) ⊗ₖ (1 : Matrix Y Y ℂ) := by
  rw [← Matrix.mul_kronecker_mul, mul_one]

lemma kron_sub (A B : Matrix X X ℂ) :
    A ⊗ₖ (1 : Matrix Y Y ℂ) - B ⊗ₖ (1 : Matrix Y Y ℂ) = (A - B) ⊗ₖ (1 : Matrix Y Y ℂ) := by
  ext a b; simp [Matrix.kronecker_apply, sub_mul]

lemma one_sub_kron (B : Matrix X X ℂ) :
    (1 : Matrix (X × Y) (X × Y) ℂ) - B ⊗ₖ (1 : Matrix Y Y ℂ) = (1 - B) ⊗ₖ (1 : Matrix Y Y ℂ) := by
  rw [← kron_sub, Matrix.one_kronecker_one]

lemma kron_psd {P : Matrix X X ℂ} (h : P.PosSemidef) : (P ⊗ₖ (1 : Matrix Y Y ℂ)).PosSemidef :=
  h.kronecker Matrix.PosSemidef.one

lemma norm_loc (U : Matrix.unitaryGroup X ℂ) (psi : EuclideanSpace ℂ (X × Y)) :
    ‖localAct (U : Matrix X X ℂ) psi‖ = ‖psi‖ := by
  have hU : (U : Matrix X X ℂ)ᴴ * (U : Matrix X X ℂ) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem U.2
  have hM : ((U : Matrix X X ℂ) ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ * ((U : Matrix X X ℂ) ⊗ₖ (1 : Matrix Y Y ℂ)) = 1 := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, kron_mul, hU, Matrix.one_kronecker_one]
  have h2 : ‖localAct (U : Matrix X X ℂ) psi‖ ^ 2 = ‖psi‖ ^ 2 := by
    unfold localAct
    simp only [Matrix.kronecker] at *
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), adj, act_mul, hM, act_one]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

lemma err_eq (Λ : Matrix X X ℂ) (a : EuclideanSpace ℂ (X × Y)) :
    effectProb Λ (traceRight (pureDensity a)) = (⟪a, act (Λ ⊗ₖ (1 : Matrix Y Y ℂ)) a⟫_ℂ).re := by
  unfold effectProb
  congr 1
  rw [inner_act]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceRight, pureDensity, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul, ite_mul, zero_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun x1 _ => ?_
  simp only [RCLike.star_def]; ring

lemma overlap_eq {k : ℕ} (α : Fin k → ℂ) (U : Fin k → Matrix.unitaryGroup X ℂ) (Λ : Fin k → Matrix X X ℂ)
    (psi psi' : EuclideanSpace ℂ (X × Y)) (j : Fin k) :
    decoderOverlap psi (coherentDecoder α U Λ) psi' j =
      α j * ⟪localAct (U j : Matrix X X ℂ) psi,
        act (cfc Real.sqrt (Λ j) ⊗ₖ (1 : Matrix Y Y ℂ)) psi'⟫_ℂ := by
  unfold localAct
  simp only [Matrix.kronecker]
  rw [adj, act_mul, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, kron_mul, inner_act]
  simp only [decoderOverlap, coherentDecoder, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.star_apply, Finset.mul_sum, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  simp only [RCLike.star_def]; ring

lemma LL {k : ℕ} (α : Fin k → ℂ) (hα : ∀ j, ‖α j‖ = 1) (U : Fin k → Matrix.unitaryGroup X ℂ)
    (Λ : Fin k → Matrix X X ℂ) (hΛ : IsPOVM Λ) :
    (coherentDecoder α U Λ)ᴴ * coherentDecoder α U Λ = 1 := by
  set M : Fin k → Matrix X X ℂ := fun j => (U j : Matrix X X ℂ)ᴴ * cfc Real.sqrt (Λ j) with hMdef
  have hM : ∀ j, (M j)ᴴ * M j = Λ j := by
    intro j
    have hUU : (U j : Matrix X X ℂ) * (U j : Matrix X X ℂ)ᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem (U j).2
    simp only [hMdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (X4CDS.sqrt_herm (Λ j)).eq]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (U j : Matrix X X ℂ), hUU, Matrix.one_mul,
      X4CDS.sqrt_mul _ (hΛ.1 j)]
  have hαα : ∀ j, conj (α j) * α j = 1 := by
    intro j
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hα j]; simp
  have key : (coherentDecoder α U Λ)ᴴ * coherentDecoder α U Λ = ∑ j, (M j)ᴴ * M j := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.conjTranspose_apply, coherentDecoder,
      Fintype.sum_prod_type, hMdef]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
    rw [star_mul', RCLike.star_def, ← mul_assoc, mul_comm _ (α j), ← mul_assoc, mul_comm (α j), hαα, one_mul]
  rw [key]
  simp only [hM]
  exact hΛ.2

end X4CDM

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise InnerProductSpace Kronecker
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

theorem solution
    (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [Nonempty X] [Nonempty Y]
    (k : ℕ) (hk : 0 < k) (psi : EuclideanSpace ℂ (X × Y)) (hpsi : ‖psi‖ = 1)
    (U : Fin k → Matrix.unitaryGroup X ℂ)
    (psiPrime : Fin k → EuclideanSpace ℂ (X × Y))
    (hpsiPrime : ∀ j, ‖psiPrime j‖ = 1)
    (Lambda : Fin k → Matrix X X ℂ) (hLambda : IsPOVM Lambda) :
    ∃ alpha : Fin k → ℂ, (∀ j, ‖alpha j‖ = 1) ∧
      let L := coherentDecoder alpha U Lambda
      Lᴴ * L = 1 ∧
      (∀ j, (decoderOverlap psi L (psiPrime j) j).im = 0 ∧
        0 ≤ (decoderOverlap psi L (psiPrime j) j).re) ∧
      (k : ℝ)⁻¹ * ∑ j, (decoderOverlap psi L (psiPrime j) j).re ≥
        1 - 2 * (coherentMeasurementError psi U Lambda +
          Real.sqrt (1 - decodingFidelity psi U psiPrime)) := by
  set z : Fin k → ℂ := fun j => ⟪localAct (U j : Matrix X X ℂ) psi,
    act (cfc Real.sqrt (Lambda j) ⊗ₖ (1 : Matrix Y Y ℂ)) (psiPrime j)⟫_ℂ with hz
  choose c hc hcz using fun j => X4CD.phase (z j)
  refine ⟨c, hc, ?_⟩
  intro L
  have hov : ∀ j, decoderOverlap psi L (psiPrime j) j = (‖z j‖ : ℂ) := fun j => by
    rw [X4CDM.overlap_eq, ← hcz j]
  refine ⟨X4CDM.LL c hc U Lambda hLambda, fun j => by rw [hov]; simp, ?_⟩
  simp only [hov, Complex.ofReal_re]
  -- per-index data
  have h1L : ∀ j, (1 - Lambda j).PosSemidef := by
    intro j
    have : (1 : Matrix X X ℂ) - Lambda j = ∑ i ∈ Finset.univ.erase j, Lambda i := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), hLambda.2]
    rw [this]
    exact Matrix.posSemidef_sum _ fun i _ => hLambda.1 i
  set q : Fin k → ℝ := fun j => (⟪localAct (U j : Matrix X X ℂ) psi,
    act (Lambda j ⊗ₖ (1 : Matrix Y Y ℂ)) (localAct (U j : Matrix X X ℂ) psi)⟫_ℂ).re with hq
  set F : Fin k → ℝ := fun j =>
    Complex.normSq ⟪localAct (U j : Matrix X X ℂ) psi, psiPrime j⟫_ℂ with hF
  have hnorm : ∀ j, ‖localAct (U j : Matrix X X ℂ) psi‖ = 1 := fun j => by
    rw [X4CDM.norm_loc, hpsi]
  have hkey : ∀ j, q j - Real.sqrt (2 * (1 - F j)) ≤ ‖z j‖ := by
    intro j
    have hA := X4CDM.kron_herm (Y := Y) (X4CDS.sqrt_herm (Lambda j))
    have hAA : (cfc Real.sqrt (Lambda j) ⊗ₖ (1 : Matrix Y Y ℂ)) * (cfc Real.sqrt (Lambda j) ⊗ₖ 1) =
        Lambda j ⊗ₖ (1 : Matrix Y Y ℂ) := by
      rw [X4CDM.kron_mul, X4CDS.sqrt_mul _ (hLambda.1 j)]
    have h1 : (1 - Lambda j ⊗ₖ (1 : Matrix Y Y ℂ)).PosSemidef := by
      rw [X4CDM.one_sub_kron]; exact X4CDM.kron_psd (h1L j)
    have h2 : (cfc Real.sqrt (Lambda j) ⊗ₖ (1 : Matrix Y Y ℂ) - Lambda j ⊗ₖ 1).PosSemidef := by
      rw [X4CDM.kron_sub]; exact X4CDM.kron_psd (X4CDS.sqrt_sub _ (hLambda.1 j) (h1L j))
    exact X4CD.key hA hAA h1 h2 _ _ (hnorm j) (hpsiPrime j)
  have hq1 : ∀ j, q j ≤ 1 := by
    intro j
    have h1 : (1 - Lambda j ⊗ₖ (1 : Matrix Y Y ℂ)).PosSemidef := by
      rw [X4CDM.one_sub_kron]; exact X4CDM.kron_psd (h1L j)
    have := X4CD.re_le h1 (localAct (U j : Matrix X X ℂ) psi)
    rw [X4CD.act_one, inner_self_eq_norm_sq_to_K, hnorm j] at this
    simpa [hq] using this
  have hF1 : ∀ j, F j ≤ 1 := by
    intro j
    have := norm_inner_le_norm (𝕜 := ℂ) (localAct (U j : Matrix X X ℂ) psi) (psiPrime j)
    rw [hnorm j, hpsiPrime j, one_mul] at this
    simp only [hF, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (⟪localAct (U j : Matrix X X ℂ) psi, psiPrime j⟫_ℂ)]
  have hP : coherentMeasurementError psi U Lambda = 1 - (k : ℝ)⁻¹ * ∑ j, q j := by
    unfold coherentMeasurementError
    simp only [X4CDM.err_eq, hq]
  have hFd : decodingFidelity psi U psiPrime = (k : ℝ)⁻¹ * ∑ j, F j := rfl
  rw [hP, hFd]
  -- concavity of the square root
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hR : ∑ j, Real.sqrt (2 * (1 - F j)) ≤ k * Real.sqrt (2 * (1 - (k : ℝ)⁻¹ * ∑ j, F j)) := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => Real.sqrt (2 * (1 - F j)))
    simp only [Finset.card_univ, Fintype.card_fin] at hcs
    have hsq : ∀ j, Real.sqrt (2 * (1 - F j)) ^ 2 = 2 * (1 - F j) := fun j =>
      Real.sq_sqrt (by nlinarith [hF1 j])
    simp only [hsq] at hcs
    have hS : ∑ j : Fin k, 2 * (1 - F j) = k * (2 * (1 - (k : ℝ)⁻¹ * ∑ j, F j)) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp
    rw [hS] at hcs
    have hnn : 0 ≤ ∑ j, Real.sqrt (2 * (1 - F j)) := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
    have hin : 0 ≤ 2 * (1 - (k : ℝ)⁻¹ * ∑ j, F j) := by
      have : ∑ j, F j ≤ k := by
        calc ∑ j, F j ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum fun j _ => hF1 j
          _ = k := by simp
      have : (k : ℝ)⁻¹ * ∑ j, F j ≤ 1 := by
        rw [inv_mul_le_iff₀ hkpos]; linarith
      linarith
    have hsq2 : (k * Real.sqrt (2 * (1 - (k : ℝ)⁻¹ * ∑ j, F j))) ^ 2 =
        k * (k * (2 * (1 - (k : ℝ)⁻¹ * ∑ j, F j))) := by
      rw [mul_pow, Real.sq_sqrt hin]; ring
    rw [← hsq2] at hcs
    exact (pow_le_pow_iff_left₀ hnn (by positivity) two_ne_zero).1 hcs
  have hsum : ∑ j, q j - ∑ j, Real.sqrt (2 * (1 - F j)) ≤ ∑ j, ‖z j‖ := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_le_sum fun j _ => hkey j
  have hQ : ∑ j, q j ≤ k := by
    calc ∑ j, q j ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum fun j _ => hq1 j
      _ = k := by simp
  set Fa := (k : ℝ)⁻¹ * ∑ j, F j
  have hFa : Fa ≤ 1 := by
    have : ∑ j, F j ≤ k := by
      calc ∑ j, F j ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum fun j _ => hF1 j
        _ = k := by simp
    simp only [Fa]; rw [inv_mul_le_iff₀ hkpos]; linarith
  have hs2 : Real.sqrt (2 * (1 - Fa)) ≤ 2 * Real.sqrt (1 - Fa) := by
    rw [Real.sqrt_mul (by norm_num)]
    gcongr
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsq0 : 0 ≤ Real.sqrt (1 - Fa) := Real.sqrt_nonneg _
  have e1 : (k : ℝ)⁻¹ * ∑ j, ‖z j‖ ≥ (k : ℝ)⁻¹ * ∑ j, q j - Real.sqrt (2 * (1 - Fa)) := by
    have : (k : ℝ)⁻¹ * (∑ j, q j - ∑ j, Real.sqrt (2 * (1 - F j))) ≤ (k : ℝ)⁻¹ * ∑ j, ‖z j‖ :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2 : (k : ℝ)⁻¹ * ∑ j, Real.sqrt (2 * (1 - F j)) ≤ Real.sqrt (2 * (1 - Fa)) := by
      rw [inv_mul_le_iff₀ hkpos]; exact hR
    rw [mul_sub] at this
    linarith
  have hQk : (k : ℝ)⁻¹ * ∑ j, q j ≤ 1 := by rw [inv_mul_le_iff₀ hkpos]; linarith
  linarith
