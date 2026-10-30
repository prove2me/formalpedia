-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P17.qubitObservables
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:57:07.973977+00:00
-- url     : https://prove2.me/submissions/4080759a-2195-424c-ade1-76b147cbe147

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17
noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P17

open scoped ComplexOrder MatrixOrder

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

lemma pf_sqrt_unique {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hB : B.PosSemidef) (h : B * B = A) : cfc Real.sqrt A = B := by
  have hA : A.PosSemidef := by
    rw [← h]; have := Matrix.posSemidef_conjTranspose_mul_self B; rwa [hB.1.eq] at this
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_unique h hB.nonneg

lemma pf_sqrt_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (cfc Real.sqrt A).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)

lemma pf_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma pf_dot_self {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    star w ⬝ᵥ w = ((star w ⬝ᵥ w).re : ℂ) ∧ 0 ≤ (star w ⬝ᵥ w).re := by
  have h0 : (0 : ℂ) ≤ star w ⬝ᵥ w := dotProduct_star_self_nonneg w
  exact ⟨(Complex.ext rfl (by simpa using ((Complex.nonneg_iff.mp h0).2).symm)),
    (Complex.nonneg_iff.mp h0).1⟩

lemma pf_sqrt_rank1 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℂ) :
    (cfc Real.sqrt (Matrix.vecMulVec w (star w))).trace.re = Real.sqrt (star w ⬝ᵥ w).re := by
  set t := (star w ⬝ᵥ w).re with ht
  obtain ⟨hdt, ht0⟩ := pf_dot_self w
  rcases eq_or_lt_of_le ht0 with h | h
  · have hw : w = 0 := by
      have : star w ⬝ᵥ w = 0 := by rw [hdt, ← h]; simp
      exact dotProduct_star_self_eq_zero.mp this
    subst hw; simp [ht]
  · have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr h
    have key : cfc Real.sqrt (Matrix.vecMulVec w (star w)) =
        ((Real.sqrt t)⁻¹ : ℂ) • Matrix.vecMulVec w (star w) := by
      apply pf_sqrt_unique
      · refine Matrix.PosSemidef.smul (Matrix.posSemidef_vecMulVec_self_star w) ?_
        have : (0:ℝ) ≤ (Real.sqrt t)⁻¹ := by positivity
        exact_mod_cast this
      · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, hdt, smul_smul,
          Matrix.vecMulVec_smul]
        congr 1
        rw [← ht]
        have : ((Real.sqrt t : ℂ))^2 = (t : ℂ) := by
          rw [← Complex.ofReal_pow, Real.sq_sqrt ht0]
        have hne : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
        rw [← this]; field_simp
        rw [smul_smul, one_div, inv_mul_cancel₀ (pow_ne_zero 2 hne), one_smul]
    rw [key, Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_comm, hdt, ← ht, smul_eq_mul,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
    have := Real.sq_sqrt ht0
    field_simp
    linarith [this]

lemma pf_rootFid_pure {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (ψ : ι → ℂ) :
    fidelity ρ (Matrix.vecMulVec ψ (star ψ)) = (star ψ ⬝ᵥ (ρ *ᵥ ψ)).re := by
  show rootFidelity _ _ ^ 2 = _
  set S := cfc Real.sqrt ρ
  have hS : S.IsHermitian := (pf_sqrt_psd ρ).1
  have h1 : S * Matrix.vecMulVec ψ (star ψ) * S =
      Matrix.vecMulVec (S *ᵥ ψ) (star (S *ᵥ ψ)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec, hS.eq]
  have h2 : star (S *ᵥ ψ) ⬝ᵥ (S *ᵥ ψ) = star ψ ⬝ᵥ (ρ *ᵥ ψ) := by
    rw [Matrix.star_mulVec, hS.eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      pf_sqrt_sq hρ]
  unfold rootFidelity
  rw [h1, pf_sqrt_rank1, h2, Real.sq_sqrt]
  rw [← h2]; exact (pf_dot_self _).2

lemma pf_twirl {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] (V : ι → Matrix I I ℂ) (c : ℂ)
    (hc : ∀ s x z y, ∑ j, V j s x * star (V j z y) = if s = z ∧ x = y then c else 0)
    (A B : Matrix I I ℂ) :
    ∑ j, (A * (V j)ᴴ * B * V j).trace = c * A.trace * B.trace := by
  have h1 : ∀ j, (A * (V j)ᴴ * B * V j).trace =
      ∑ x, ∑ s, ∑ z, ∑ y, A x y * B z s * (V j s x * star (V j z y)) := by
    intro j
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  simp_rw [h1]
  calc ∑ j, ∑ x, ∑ s, ∑ z, ∑ y, A x y * B z s * (V j s x * star (V j z y))
      = ∑ x, ∑ s, ∑ z, ∑ y, ∑ j, A x y * B z s * (V j s x * star (V j z y)) := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ x, ∑ s, ∑ z, ∑ y, A x y * B z s * (if s = z ∧ x = y then c else 0) := by
        simp_rw [← Finset.mul_sum, hc]
    _ = c * A.trace * B.trace := by
        simp only [ite_and, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
          Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_eq_single x]
        · simp; ring
        · intro b _ hb; simp [Ne.symm hb]
        · simp

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

lemma pf_choi_entry {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ)
    (p q : I × I) :
    normalizedProcessState E p q =
      (∑ j, K j p.2 p.1 * conj (K j q.2 q.1)) / (Fintype.card I : ℂ) := by
  simp only [normalizedProcessState, idTensorSuperop, Matrix.of_apply, hE, krausApply,
    pureDensity, finiteMaxEntangled]
  rw [Matrix.sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp [apply_ite (starRingEnd ℂ), mul_ite, ite_mul, Finset.sum_ite_eq]
  have hd : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ^ 2 = (Fintype.card I : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have hd0 : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  rw [← hd]
  field_simp

lemma pf_choi_eq {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) :
    normalizedProcessState E = (Fintype.card I : ℂ)⁻¹ •
      ∑ j, Matrix.vecMulVec (fun p : I × I => K j p.2 p.1) (star fun p : I × I => K j p.2 p.1) := by
  ext p q
  rw [pf_choi_entry K E hE]
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, div_eq_inv_mul]

lemma pf_psd {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).PosSemidef := by
  rw [pf_choi_eq K E hE]
  refine Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ fun j _ =>
    Matrix.posSemidef_vecMulVec_self_star _) ?_
  exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)

lemma pf_sqd : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) * ((Real.sqrt (Fintype.card I) : ℝ) : ℂ)
    = (Fintype.card I : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp

lemma pf_choiU (U : Matrix I I ℂ) :
    normalizedProcessState (conjSuperop U) =
      Matrix.vecMulVec (fun p : I × I => U p.2 p.1 / (Real.sqrt (Fintype.card I) : ℂ))
        (star fun p : I × I => U p.2 p.1 / (Real.sqrt (Fintype.card I) : ℂ)) := by
  ext p q
  rw [pf_choi_entry (fun _ : Fin 1 => U) _ (fun ρ => by simp [krausApply, conjSuperop])]
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, Finset.univ_unique, Finset.sum_singleton,
    star_div₀, Complex.star_def, Complex.conj_ofReal]
  rw [← pf_sqd]
  have hd0 : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  field_simp

lemma pf_dot (U K : Matrix I I ℂ) :
    star (fun p : I × I => U p.2 p.1 / (Real.sqrt (Fintype.card I) : ℂ)) ⬝ᵥ
      (fun p : I × I => K p.2 p.1) = ((Real.sqrt (Fintype.card I) : ℂ))⁻¹ * (Uᴴ * K).trace := by
  simp only [dotProduct, Pi.star_apply, star_div₀, Complex.star_def, Complex.conj_ofReal,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  simp [div_eq_mul_inv]; ring

lemma pf_dot' (U K : Matrix I I ℂ) :
    star (fun p : I × I => K p.2 p.1) ⬝ᵥ
      (fun p : I × I => U p.2 p.1 / (Real.sqrt (Fintype.card I) : ℂ)) =
      ((Real.sqrt (Fintype.card I) : ℂ))⁻¹ * (Kᴴ * U).trace := by
  simp only [dotProduct, Pi.star_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  simp [div_eq_mul_inv]; ring

theorem pf_main (E : FiniteProcess I I) (U : Matrix.unitaryGroup I ℂ) {ι : Type*} [Fintype ι]
    (V : ι → Matrix I I ℂ)
    (hc : ∀ s x z y, ∑ j, V j s x * star (V j z y) =
      if s = z ∧ x = y then (Fintype.card I : ℂ) else 0) :
    (proFidelity E.val (conjSuperop (U : Matrix I I ℂ)) : ℂ) =
      (Fintype.card I : ℂ)⁻¹ ^ 3 *
        ∑ j, ((U : Matrix I I ℂ) * (V j)ᴴ * (U : Matrix I I ℂ)ᴴ * E.val (V j)).trace := by
  obtain ⟨m, K, hK, hE⟩ := E.2
  set ψ : I × I → ℂ := fun p => (U : Matrix I I ℂ) p.2 p.1 / (Real.sqrt (Fintype.card I) : ℂ)
  have hρ := pf_psd K _ hE
  have hF : proFidelity E.val (conjSuperop (U : Matrix I I ℂ)) =
      (star ψ ⬝ᵥ (normalizedProcessState E.val *ᵥ ψ)).re := by
    unfold proFidelity; rw [pf_choiU]; exact pf_rootFid_pure hρ ψ
  have hreal : star ψ ⬝ᵥ (normalizedProcessState E.val *ᵥ ψ) =
      ((star ψ ⬝ᵥ (normalizedProcessState E.val *ᵥ ψ)).re : ℂ) := by
    have h0 := hρ.dotProduct_mulVec_nonneg ψ
    exact Complex.ext rfl (by simpa using ((Complex.nonneg_iff.mp h0).2).symm)
  rw [hF, ← hreal, pf_choi_eq K _ hE]
  have hd0 : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hdc : (Fintype.card I : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hR : ∀ j, ((U : Matrix I I ℂ) * (V j)ᴴ * (U : Matrix I I ℂ)ᴴ * E.val (V j)).trace =
      ∑ k, ((K k)ᴴ * U * (V j)ᴴ * ((U : Matrix I I ℂ)ᴴ * K k) * V j).trace := by
    intro j
    rw [hE, krausApply, Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp_rw [hR]
  rw [Finset.sum_comm]
  simp_rw [pf_twirl V _ hc]
  simp only [Matrix.smul_mulVec, Matrix.sum_mulVec, dotProduct_smul, dotProduct_sum,
    Matrix.vecMulVec_mulVec, smul_eq_mul]
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  simp only [ψ, pf_dot, pf_dot']
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← pf_sqd]; field_simp

lemma pf_compl (V : I × I → Matrix.unitaryGroup I ℂ)
    (hv : ∀ j k, ((V j : Matrix I I ℂ)ᴴ * (V k : Matrix I I ℂ)).trace =
      if j = k then (Fintype.card I : ℂ) else 0) :
    ∀ s x z y, ∑ j, (V j : Matrix I I ℂ) s x * star ((V j : Matrix I I ℂ) z y) =
      if s = z ∧ x = y then (Fintype.card I : ℂ) else 0 := by
  have hdc : (Fintype.card I : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  let M : Matrix (I × I) (I × I) ℂ := Matrix.of fun p j => (V j : Matrix I I ℂ) p.1 p.2
  have h1 : ((Fintype.card I : ℂ)⁻¹ • Mᴴ) * M = 1 := by
    ext j k
    rw [Matrix.smul_mul, Matrix.smul_apply]
    have : (Mᴴ * M) j k = ((V j : Matrix I I ℂ)ᴴ * (V k : Matrix I I ℂ)).trace := by
      simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
    rw [this, hv, Matrix.one_apply]
    split_ifs <;> simp [hdc]
  have h2 := mul_eq_one_comm.mp h1
  intro s x z y
  have h3 := congrArg (fun A => A (s, x) (z, y)) h2
  simp only [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    M, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul] at h3
  have h4 : ∑ j, (V j : Matrix I I ℂ) s x * star ((V j : Matrix I I ℂ) z y) =
      (Fintype.card I : ℂ) * ∑ j, (V j : Matrix I I ℂ) s x *
        ((Fintype.card I : ℂ)⁻¹ * star ((V j : Matrix I I ℂ) z y)) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; field_simp
  rw [h4, h3]; split_ifs <;> simp

lemma pf_lin (E : FiniteProcess I I) {κ : Type*} [Fintype κ] (c : κ → ℂ) (X : κ → Matrix I I ℂ) :
    E.val (∑ k, c k • X k) = ∑ k, c k • E.val (X k) := by
  obtain ⟨m, K, hK, hE⟩ := E.2
  simp only [hE, krausApply, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]
  rw [Finset.sum_comm]

abbrev qσ (a : Fin 4) : Matrix Bool Bool ℂ := (inputPauliLabel a).mat

lemma q_S1 (p q r w : Bool) :
    ∑ a : Fin 4, qσ a p q * star (qσ a r w) = if p = r ∧ q = w then 2 else 0 := by
  rw [Fin.sum_univ_four]
  cases p <;> cases q <;> cases r <;> cases w <;>
    simp [qσ, inputPauliLabel, QAlgorithms.Stabilizer.Pauli.mat, pauliX, pauliY, pauliZ] <;> norm_num

def qc (b a : Fin 4) : ℝ := if b = 0 then (if a = 0 then 2 else 0)
    else if a = b then 2 else if a = 0 then -2 else 0

lemma q_S2 (b : Fin 4) (p q : Bool) :
    ∑ a : Fin 4, (qc b a : ℂ) * tomographyQubitInput a p q = qσ b p q := by
  rw [Fin.sum_univ_four]
  fin_cases b <;> cases p <;> cases q <;>
    simp [qc, qσ, tomographyQubitInput, inputPauliLabel, QAlgorithms.Stabilizer.Pauli.mat, pauliX,
      pauliY, pauliZ] <;> norm_num

lemma q_S3 (a : Fin 4) (p q : Bool) : star (qσ a q p) = qσ a p q := by
  fin_cases a <;> cases p <;> cases q <;>
    simp [qσ, inputPauliLabel, QAlgorithms.Stabilizer.Pauli.mat, pauliX, pauliY, pauliZ]

def qw (a : Fin 4) (c : Bool) (p : Bool) : ℂ :=
  if a = 0 then (if p = c then ((Real.sqrt 2)⁻¹ : ℂ) else 0)
  else if c then 0
  else if a = 1 then ((Real.sqrt 2)⁻¹ : ℂ)
  else if a = 2 then (if p then Complex.I * ((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ))
  else (if p then 0 else 1)

lemma q_S4 (a : Fin 4) (p q : Bool) :
    tomographyQubitInput a p q = ∑ c : Bool, qw a c p * star (qw a c q) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have h0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by simp
  fin_cases a <;> cases p <;> cases q <;>
    simp [qw, tomographyQubitInput, inputPauliLabel, QAlgorithms.Stabilizer.Pauli.mat, pauliX,
      pauliY, pauliZ]
  all_goals (try field_simp)
  all_goals (try simp only [sq, h2])
  all_goals (try ring_nf)
  all_goals (try simp [Complex.I_sq])

lemma q_S5 (a : Fin 4) : ∑ p : Bool, tomographyQubitInput a p p = 1 := by
  fin_cases a <;>
    simp [tomographyQubitInput, inputPauliLabel, QAlgorithms.Stabilizer.Pauli.mat, pauliX,
      pauliY, pauliZ] <;> norm_num

lemma q_entry (n : ℕ) (j : Fin n → Fin 4) (x y : Qubits n) :
    productPauli n j x y = ∏ t, qσ (j t) (x t) (y t) := by
  simp [productPauli, QAlgorithms.Stabilizer.PauliString.toMatrix, qσ]

lemma q_ite_prod (n : ℕ) (s x z y : Qubits n) :
    ∏ t, (if s t = z t ∧ x t = y t then (2 : ℂ) else 0) =
      if s = z ∧ x = y then (Fintype.card (Qubits n) : ℂ) else 0 := by
  by_cases h : s = z ∧ x = y
  · obtain ⟨rfl, rfl⟩ := h; simp [Fintype.card_fun]
  · rw [if_neg h]
    have : ∃ t, ¬ (s t = z t ∧ x t = y t) := by
      by_contra hc; push_neg at hc
      exact h ⟨funext fun t => (hc t).1, funext fun t => (hc t).2⟩
    obtain ⟨t, ht⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)

lemma q_compl (n : ℕ) (s x z y : Qubits n) :
    ∑ j, productPauli n j s x * star (productPauli n j z y) =
      if s = z ∧ x = y then (Fintype.card (Qubits n) : ℂ) else 0 := by
  rw [← q_ite_prod]
  simp_rw [← q_S1, q_entry, Complex.star_def, map_prod, ← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]

lemma q_expand (n : ℕ) (j : Fin n → Fin 4) :
    productPauli n j = ∑ k : Fin n → Fin 4,
      (productCoefficient n j k : ℂ) • tomographyProductInput n k := by
  ext x y
  have hc : ∀ k, (productCoefficient n j k : ℂ) = ∏ t, (qc (j t) (k t) : ℂ) := by
    intro k; simp [productCoefficient, qc]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hc, tomographyProductInput,
    Matrix.of_apply, ← Finset.prod_mul_distrib, q_entry]
  rw [← Fintype.prod_sum (f := fun t a => (qc (j t) a : ℂ) * tomographyQubitInput a (x t) (y t))]
  exact Finset.prod_congr rfl fun t _ => (q_S2 _ _ _).symm

lemma q_density (n : ℕ) (k : Fin n → Fin 4) : IsDensityMatrix (tomographyProductInput n k) := by
  constructor
  · have : tomographyProductInput n k = ∑ c : Fin n → Bool,
        Matrix.vecMulVec (fun x : Qubits n => ∏ t, qw (k t) (c t) (x t))
          (star fun x : Qubits n => ∏ t, qw (k t) (c t) (x t)) := by
      ext x y
      simp only [tomographyProductInput, Matrix.of_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, Pi.star_apply, q_S4, Complex.star_def, map_prod,
        ← Finset.prod_mul_distrib]
      rw [Fintype.prod_sum]
    rw [this]
    exact Matrix.posSemidef_sum _ fun c _ => Matrix.posSemidef_vecMulVec_self_star _
  · simp only [Matrix.trace, Matrix.diag, tomographyProductInput, Matrix.of_apply]
    rw [← Fintype.prod_sum (f := fun t b => tomographyQubitInput (k t) b b)]
    exact Finset.prod_eq_one fun t _ => q_S5 (k t)

lemma q_herm (n : ℕ) (j : Fin n → Fin 4) : (productPauli n j)ᴴ = productPauli n j := by
  ext x y
  simp only [Matrix.conjTranspose_apply, q_entry, Complex.star_def, map_prod]
  simp_rw [← Complex.star_def, q_S3]

theorem solution (n : ℕ) (E : FiniteProcess (Qubits n) (Qubits n))
    (U : Matrix.unitaryGroup (Qubits n) ℂ) :
    (∀ k, IsDensityMatrix (tomographyProductInput n k) ∧ (productObservable n U k).IsHermitian) ∧
    (∀ j, productPauli n j = ∑ k : Fin n → Fin 4,
      (productCoefficient n j k : ℂ) • tomographyProductInput n k) ∧
    proFidelity E.val (conjSuperop (U : Matrix (Qubits n) (Qubits n) ℂ)) =
      (2 ^ n : ℝ)⁻¹ ^ 3 * ∑ k : Fin n → Fin 4,
        effectProb (productObservable n U k) (E.val (tomographyProductInput n k)) ∧
    Fintype.card (Fin n → Fin 4) = (2 ^ n) ^ 2 := by
  refine ⟨fun k => ⟨q_density n k, ?_⟩, q_expand n, ?_, ?_⟩
  · unfold productObservable
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, q_herm, Complex.star_def,
      Complex.conj_ofReal, Matrix.mul_assoc]
  · have hmain := pf_main E U (fun j => productPauli n j) (fun s x z y => q_compl n s x z y)
    have hsum : ∑ k : Fin n → Fin 4, (productObservable n U k * E.val (tomographyProductInput n k)).trace =
        ∑ j : Fin n → Fin 4, ((U : Matrix (Qubits n) (Qubits n) ℂ) * (productPauli n j)ᴴ *
          (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ * E.val (productPauli n j)).trace := by
      simp only [productObservable, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
        Matrix.trace_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hEj : E.val (productPauli n j) = ∑ k, (productCoefficient n j k : ℂ) •
          E.val (tomographyProductInput n k) := by
        conv_lhs => rw [q_expand n j]
        exact pf_lin E _ _
      rw [hEj, Matrix.mul_sum, Matrix.trace_sum]
      simp only [Matrix.mul_smul, Matrix.trace_smul]
    rw [← hsum] at hmain
    have := congrArg Complex.re hmain
    rw [Complex.ofReal_re] at this
    rw [this]
    simp only [effectProb]
    have : ((Fintype.card (Qubits n) : ℂ))⁻¹ ^ 3 = (((2 ^ n : ℝ)⁻¹ ^ 3 : ℝ) : ℂ) := by
      simp [Fintype.card_fun]
    rw [this, Complex.re_ofReal_mul, Complex.re_sum]
  · simp; rw [← pow_mul, mul_comm, pow_mul]; norm_num
