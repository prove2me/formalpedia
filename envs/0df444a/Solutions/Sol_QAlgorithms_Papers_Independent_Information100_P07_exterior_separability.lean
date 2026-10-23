-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P07.exterior_separability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:46:01.041169+00:00
-- url     : https://prove2.me/submissions/b4b1d1f8-6a2c-4aa0-8469-6cd481803d42

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7ExtSep

open Matrix

lemma psd_eq_mul_conj {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : ∃ V : Matrix n n ℂ, A = V * Vᴴ := by
  have hs := hA.1.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hs
  set U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  refine ⟨U * diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ)), ?_⟩
  rw [conjTranspose_mul, diagonal_conjTranspose, mul_assoc, ← mul_assoc (diagonal _),
    diagonal_mul_diagonal, ← star_eq_conjTranspose, ← mul_assoc]
  conv_lhs => rw [hs]
  congr 2
  congr 1
  funext i
  simp only [Function.comp, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]
  rfl

lemma psd_mul_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {A P : Matrix n n ℂ}
    (hA : A.PosSemidef) (hP : Pᴴ = P) (h : P * A * P = 0) : A * P = 0 ∧ P * A = 0 := by
  obtain ⟨V, rfl⟩ := psd_eq_mul_conj hA
  have h1 : (Vᴴ * P)ᴴ * (Vᴴ * P) = 0 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hP]
    simpa [mul_assoc] using h
  have h2 : Vᴴ * P = 0 := conjTranspose_mul_self_eq_zero.1 h1
  have h3 : V * Vᴴ * P = 0 := by rw [mul_assoc, h2, mul_zero]
  refine ⟨h3, ?_⟩
  have := congrArg conjTranspose h3
  simpa [conjTranspose_mul, hP, mul_assoc] using this

lemma sep_add {X Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ}
    (hX : IsSeparablePositive X) (hY : IsSeparablePositive Y) :
    IsSeparablePositive (X + Y) := by
  obtain ⟨q1, w1, A1, B1, hw1, hd1, rfl⟩ := hX
  obtain ⟨q2, w2, A2, B2, hw2, hd2, rfl⟩ := hY
  refine ⟨q1 + q2, Fin.append w1 w2, Fin.append A1 A2, Fin.append B1 B2, ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hw1 i
    · simpa using hw2 i
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hd1 i
    · simpa using hd2 i
  · rw [Fin.sum_univ_add]
    simp

lemma trace_real_of_psd {n : Type*} [Fintype n] {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    A.trace = ((A.trace.re : ℝ) : ℂ) ∧ 0 ≤ A.trace.re := by
  have ht := hA.trace_nonneg
  rw [Complex.nonneg_iff] at ht
  refine ⟨Complex.ext (by simp) (by simp [← ht.2]), by simpa using ht.1⟩

lemma sep_kron_left {A B : Matrix (Fin 3) (Fin 3) ℂ} (hA : A.PosSemidef)
    (hB : IsDensityMatrix B) : IsSeparablePositive (A ⊗ₖ B) := by
  by_cases h0 : A.trace = 0
  · have : A = 0 := (hA.trace_eq_zero_iff).1 h0
    subst this
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, ?_⟩
    simp
  · obtain ⟨htc, htn⟩ := trace_real_of_psd hA
    set t := A.trace.re with ht
    have tpos : 0 < t := by
      rcases htn.lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [htc, ← h]; simp) h0
    have tne : (t : ℂ) ≠ 0 := by exact_mod_cast tpos.ne'
    refine ⟨1, fun _ => t, fun _ => ((t : ℂ)⁻¹) • A, fun _ => B, fun _ => tpos.le,
      fun _ => ⟨⟨?_, ?_⟩, hB⟩, ?_⟩
    · have : ((t : ℂ)⁻¹) = (((t⁻¹ : ℝ)) : ℂ) := by simp
      rw [this]
      exact hA.smul (by exact_mod_cast (inv_pos.2 tpos).le)
    · rw [trace_smul, htc, smul_eq_mul, inv_mul_cancel₀ tne]
    · simp only [Finset.univ_unique, Finset.sum_singleton]
      show _ = (t : ℂ) • ((((t : ℂ)⁻¹) • A) ⊗ₖ B)
      rw [smul_kronecker, smul_smul, mul_inv_cancel₀ tne, one_smul]

lemma sep_kron_right {A B : Matrix (Fin 3) (Fin 3) ℂ} (hA : IsDensityMatrix A)
    (hB : B.PosSemidef) : IsSeparablePositive (A ⊗ₖ B) := by
  by_cases h0 : B.trace = 0
  · have : B = 0 := (hB.trace_eq_zero_iff).1 h0
    subst this
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, ?_⟩
    simp
  · obtain ⟨htc, htn⟩ := trace_real_of_psd hB
    set t := B.trace.re with ht
    have tpos : 0 < t := by
      rcases htn.lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [htc, ← h]; simp) h0
    have tne : (t : ℂ) ≠ 0 := by exact_mod_cast tpos.ne'
    refine ⟨1, fun _ => t, fun _ => A, fun _ => ((t : ℂ)⁻¹) • B, fun _ => tpos.le,
      fun _ => ⟨hA, ⟨?_, ?_⟩⟩, ?_⟩
    · have : ((t : ℂ)⁻¹) = (((t⁻¹ : ℝ)) : ℂ) := by simp
      rw [this]
      exact hB.smul (by exact_mod_cast (inv_pos.2 tpos).le)
    · rw [trace_smul, htc, smul_eq_mul, inv_mul_cancel₀ tne]
    · simp only [Finset.univ_unique, Finset.sum_singleton]
      show _ = (t : ℂ) • (A ⊗ₖ (((t : ℂ)⁻¹) • B))
      rw [kronecker_smul, smul_smul, mul_inv_cancel₀ tne, one_smul]

lemma vmv_density (z : Fin 3 → ℂ) (hz : star z ⬝ᵥ z = 1) :
    IsDensityMatrix (vecMulVec z (star z)) := by
  refine ⟨posSemidef_vecMulVec_self_star z, ?_⟩
  rw [← hz]
  simp [Matrix.trace, vecMulVec_apply, dotProduct, mul_comm]

/-- product support on the right factor. -/
lemma sep_of_right_support (z : Fin 3 → ℂ) (hz : star z ⬝ᵥ z = 1)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hY : ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ vecMulVec z (star z)) * Y = Y) :
    IsSeparablePositive (Y * Yᴴ) := by
  set w : Matrix (Fin 3) (Fin 3 × Fin 3) ℂ := fun i c => ∑ d, star (z d) * Y (i, d) c
  have hYe : ∀ i a c, Y (i, a) c = z a * w i c := by
    intro i a c
    rw [← hY]
    simp [w, Matrix.mul_apply, kroneckerMap_apply, Fintype.sum_prod_type, one_apply,
      vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have hYY : Y * Yᴴ = (w * wᴴ) ⊗ₖ vecMulVec z (star z) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp only [Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, vecMulVec_apply,
      hYe, star_mul', Finset.sum_mul, Pi.star_apply]
    refine Finset.sum_congr rfl (fun c _ => by ring)
  rw [hYY]
  exact sep_kron_left (posSemidef_self_mul_conjTranspose w) (vmv_density z hz)

lemma sep_of_left_support (z : Fin 3 → ℂ) (hz : star z ⬝ᵥ z = 1)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hY : (vecMulVec z (star z) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) * Y = Y) :
    IsSeparablePositive (Y * Yᴴ) := by
  set w : Matrix (Fin 3) (Fin 3 × Fin 3) ℂ := fun i c => ∑ d, star (z d) * Y (d, i) c
  have hYe : ∀ i a c, Y (a, i) c = z a * w i c := by
    intro i a c
    rw [← hY]
    simp [w, Matrix.mul_apply, kroneckerMap_apply, Fintype.sum_prod_type, one_apply,
      vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have hYY : Y * Yᴴ = vecMulVec z (star z) ⊗ₖ (w * wᴴ) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, vecMulVec_apply,
      hYe, star_mul', Finset.mul_sum, Pi.star_apply]
    refine Finset.sum_congr rfl (fun c _ => by ring)
  rw [hYY]
  exact sep_kron_right (vmv_density z hz) (posSemidef_self_mul_conjTranspose w)

lemma rank_two_proj (Q : Matrix (Fin 3) (Fin 3) ℂ) (hQ : Q.IsHermitian ∧ Q * Q = Q)
    (hr : Q.rank = 2) :
    ∃ z : Fin 3 → ℂ, star z ⬝ᵥ z = 1 ∧ 1 - Q = vecMulVec z (star z) := by
  have hs := hQ.1.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hs
  have hUU0 : star (↑hQ.1.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) *
      (↑hQ.1.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hQ.1.eigenvectorUnitary.2
  have hUU1 : (↑hQ.1.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) *
      star (↑hQ.1.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem hQ.1.eigenvectorUnitary.2
  have hrk := hQ.1.rank_eq_card_non_zero_eigs
  generalize (↑hQ.1.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) = U at hs hUU0 hUU1
  generalize hQ.1.eigenvalues = μ at hs hrk
  have hUU := hUU0
  have hUU' := hUU1
  set D : Matrix (Fin 3) (Fin 3) ℂ := diagonal (RCLike.ofReal ∘ μ) with hDdef
  have hD : D * D = D := by
    have h2 : star U * (Q * Q) * U = star U * Q * U := by rw [hQ.2]
    rw [hs] at h2
    have e : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, star U * (U * X * star U) * U = X := by
      intro X
      calc star U * (U * X * star U) * U = (star U * U) * X * (star U * U) := by
            simp only [mul_assoc]
        _ = X := by rw [hUU, one_mul, mul_one]
    have : U * D * star U * (U * D * star U) = U * (D * D) * star U := by
      calc U * D * star U * (U * D * star U) = U * D * (star U * U) * D * star U := by
            simp only [mul_assoc]
        _ = U * (D * D) * star U := by rw [hUU, mul_one]; simp only [mul_assoc]
    rw [this, e, e] at h2
    exact h2
  have hμ : ∀ i, μ i = 0 ∨ μ i = 1 := by
    intro i
    have := congrFun (congrFun hD i) i
    simp only [hDdef, diagonal_mul_diagonal, diagonal_apply_eq, Function.comp] at this
    have h' : (μ i) * (μ i) = μ i := by exact_mod_cast this
    have h'' : μ i * (μ i - 1) = 0 := by linear_combination h'
    rcases mul_eq_zero.1 h'' with h | h
    · left; exact h
    · right; linarith
  have hcard : Fintype.card {i // μ i ≠ 0} = 2 := by
    rw [← hrk]; exact hr
  have hcard0 : Fintype.card {i // μ i = 0} = 1 := by
    have := Fintype.card_subtype_compl (fun i => μ i = 0)
    simp only [Fintype.card_fin] at this
    have h3 : Fintype.card {i // ¬ μ i = 0} = 2 := hcard
    omega
  obtain ⟨⟨i0, hi0⟩, huniq⟩ := Fintype.card_eq_one_iff.1 hcard0
  have hμe : ∀ i, (1 : ℂ) - (μ i : ℂ) = if i = i0 then 1 else 0 := by
    intro i
    by_cases h : i = i0
    · subst h; simp [hi0]
    · rw [if_neg h]
      rcases hμ i with h1 | h1
      · exact absurd (congrArg Subtype.val (huniq ⟨i, h1⟩)) h
      · simp [h1]
  refine ⟨fun k => U k i0, ?_, ?_⟩
  · have := congrFun (congrFun hUU i0) i0
    simpa [Matrix.mul_apply, dotProduct, star_apply] using this
  · ext k l
    have e1 := congrFun (congrFun hUU' k) l
    have e2 := congrFun (congrFun hs k) l
    rw [hDdef] at e2
    simp only [Matrix.mul_apply, star_apply, diagonal_apply, Function.comp, mul_ite,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e1 e2
    rw [Matrix.sub_apply, e2, ← e1, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i0]
    · simp [vecMulVec_apply, hi0]
    · intro i _ hi
      rcases hμ i with h | h
      · exact absurd (congrArg Subtype.val (huniq ⟨i, h⟩)) hi
      · simp [h]
    · simp

lemma proj_exists (MA MB : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (h : MA * MBᴴ = 0) :
    ∃ Pr : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ,
      Prᴴ = Pr ∧ Pr * Pr = Pr ∧ MA * Pr = MA ∧ MB * Pr = 0 := by
  have hN := isHermitian_conjTranspose_mul_self MA
  have hs := hN.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hs
  set U : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := ↑hN.eigenvectorUnitary
  set μ := hN.eigenvalues
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hN.eigenvectorUnitary.2
  obtain ⟨f, hf⟩ : ∃ f : (Fin 3 × Fin 3) → ℂ, f = fun i => if μ i = 0 then 0 else 1 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (Fin 3 × Fin 3) → ℂ,
    g = fun i => if μ i = 0 then 0 else ((μ i : ℂ))⁻¹ := ⟨_, rfl⟩
  have hfs : star f = f := by
    funext i; simp only [hf, Pi.star_apply]; split_ifs <;> simp
  have hff : (fun i => f i * f i) = f := by
    funext i; simp only [hf]; split_ifs <;> simp
  have hDf : (fun i => (RCLike.ofReal ∘ μ) i * f i) = (RCLike.ofReal ∘ μ) := by
    funext i; simp only [hf, Function.comp]; split_ifs with h1
    · simp [h1]
    · simp
  have hDg : (fun i => (RCLike.ofReal ∘ μ) i * g i) = f := by
    funext i; simp only [hf, hg, Function.comp]; split_ifs with h1
    · simp
    · have : (μ i : ℂ) ≠ 0 := by exact_mod_cast h1
      exact mul_inv_cancel₀ this
  have e : ∀ X Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ,
      U * X * star U * (U * Y * star U) = U * (X * Y) * star U := by
    intro X Y
    calc U * X * star U * (U * Y * star U) = U * X * (star U * U) * Y * star U := by
          simp only [mul_assoc]
      _ = U * (X * Y) * star U := by rw [hUU, mul_one]; simp only [mul_assoc]
  have hPr : (U * diagonal f * star U)ᴴ = U * diagonal f * star U := by
    rw [conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose, hfs,
      ← star_eq_conjTranspose, ← star_eq_conjTranspose, star_star, mul_assoc]
  have hNP : MAᴴ * MA * (U * diagonal f * star U) = MAᴴ * MA := by
    rw [hs, e, diagonal_mul_diagonal, hDf]
  have hNG : MAᴴ * MA * (U * diagonal g * star U) = U * diagonal f * star U := by
    rw [hs, e, diagonal_mul_diagonal, hDg]
  refine ⟨U * diagonal f * star U, hPr, ?_, ?_, ?_⟩
  · rw [e, diagonal_mul_diagonal, hff]
  · set Pr := U * diagonal f * star U
    have hK : (MA * (1 - Pr))ᴴ * (MA * (1 - Pr)) = 0 := by
      rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPr]
      calc (1 - Pr) * MAᴴ * (MA * (1 - Pr)) = (1 - Pr) * (MAᴴ * MA - MAᴴ * MA * Pr) := by
            simp only [mul_sub, mul_one, mul_assoc]
        _ = 0 := by rw [hNP, sub_self, mul_zero]
    have := conjTranspose_mul_self_eq_zero.1 hK
    rw [mul_sub, mul_one, sub_eq_zero] at this
    exact this.symm
  · rw [← hNG, ← mul_assoc, ← mul_assoc MB]
    have : MB * MAᴴ = 0 := by
      have := congrArg conjTranspose h
      simpa [conjTranspose_mul] using this
    rw [this, zero_mul, zero_mul]

lemma kron_sub_right (A B C : Matrix (Fin 3) (Fin 3) ℂ) : A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext ⟨a, b⟩ ⟨c, d⟩; simp [kroneckerMap_apply, mul_sub]

lemma kron_sub_left (A B C : Matrix (Fin 3) (Fin 3) ℂ) : (B - C) ⊗ₖ A = B ⊗ₖ A - C ⊗ₖ A := by
  ext ⟨a, b⟩ ⟨c, d⟩; simp [kroneckerMap_apply, sub_mul]

lemma kron3 (P Q P' Q' X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    (P ⊗ₖ Q) * (X ⊗ₖ Y) * (P' ⊗ₖ Q') = (P * X * P') ⊗ₖ (Q * Y * Q') := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul]

theorem main (P Q : Matrix (Fin 3) (Fin 3) ℂ) (T : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hP : P.IsHermitian ∧ P * P = P) (hQ : Q.IsHermitian ∧ Q * Q = Q)
    (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hT : T.PosSemidef)
    (hsupp : (1 - Matrix.kronecker P Q) * T * (1 - Matrix.kronecker P Q) = T) :
    IsSeparablePositive T ↔ Matrix.kronecker P (1 - Q) * T * Matrix.kronecker (1 - P) Q = 0 := by
  have hk : ∀ A B : Matrix (Fin 3) (Fin 3) ℂ, Matrix.kronecker A B = A ⊗ₖ B := fun _ _ => rfl
  simp only [hk] at hsupp ⊢
  have hPh : Pᴴ = P := hP.1
  have hQh : Qᴴ = Q := hQ.1
  have hGG : (P ⊗ₖ Q) * (P ⊗ₖ Q) = P ⊗ₖ Q := by rw [← mul_kronecker_mul, hP.2, hQ.2]
  have hGh : (P ⊗ₖ Q)ᴴ = P ⊗ₖ Q := by rw [conjTranspose_kronecker, hPh, hQh]
  have hG1 : (P ⊗ₖ Q) * (1 - P ⊗ₖ Q) = 0 := by rw [mul_sub, mul_one, hGG, sub_self]
  have hGT : (P ⊗ₖ Q) * T = 0 := by
    calc (P ⊗ₖ Q) * T = (P ⊗ₖ Q) * ((1 - P ⊗ₖ Q) * T * (1 - P ⊗ₖ Q)) := by rw [hsupp]
      _ = ((P ⊗ₖ Q) * (1 - P ⊗ₖ Q)) * T * (1 - P ⊗ₖ Q) := by simp only [mul_assoc]
      _ = 0 := by rw [hG1, zero_mul, zero_mul]
  constructor
  · rintro ⟨q, w, A, B, hw, hd, hTe⟩
    simp only [hk] at hTe
    have hGTG : (P ⊗ₖ Q) * T * (P ⊗ₖ Q) = 0 := by rw [hGT, zero_mul]
    rw [hTe, Finset.mul_sum, Finset.sum_mul] at hGTG
    simp only [mul_smul_comm, smul_mul_assoc, kron3] at hGTG
    have htr := congrArg Matrix.trace hGTG
    simp only [trace_sum, trace_smul, trace_kronecker, trace_zero, smul_eq_mul] at htr
    have hnn : ∀ j ∈ Finset.univ, (0 : ℂ) ≤ (w j : ℂ) * ((P * A j * P).trace * (Q * B j * Q).trace) := by
      intro j _
      have h1 : (P * A j * P).PosSemidef := by
        simpa [hPh] using (hd j).1.1.conjTranspose_mul_mul_same P
      have h2 : (Q * B j * Q).PosSemidef := by
        simpa [hQh] using (hd j).2.1.conjTranspose_mul_mul_same Q
      exact mul_nonneg (Complex.zero_le_real.2 (hw j)) (mul_nonneg h1.trace_nonneg h2.trace_nonneg)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 htr
    rw [hTe, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [mul_smul_comm, smul_mul_assoc, kron3]
    have hj0 := hz j hj
    rcases mul_eq_zero.1 hj0 with h0 | h0
    · rw [h0, zero_smul]
    rcases mul_eq_zero.1 h0 with h0 | h0
    · have h1 : (P * A j * P).PosSemidef := by
        simpa [hPh] using (hd j).1.1.conjTranspose_mul_mul_same P
      have := h1.trace_eq_zero_iff.1 h0
      have hPA := (psd_mul_eq_zero (hd j).1.1 hPh this).2
      rw [hPA, zero_mul, zero_kronecker, smul_zero]
    · have h2 : (Q * B j * Q).PosSemidef := by
        simpa [hQh] using (hd j).2.1.conjTranspose_mul_mul_same Q
      have := h2.trace_eq_zero_iff.1 h0
      have hBQ := (psd_mul_eq_zero (hd j).2.1 hQh this).1
      rw [mul_assoc (1 - Q), hBQ, mul_zero, kronecker_zero, smul_zero]
  · intro hwing
    obtain ⟨V, hV⟩ := psd_eq_mul_conj hT
    have hGV : (P ⊗ₖ Q) * V = 0 := by
      apply self_mul_conjTranspose_eq_zero.1
      rw [conjTranspose_mul, hGh, ← mul_assoc, mul_assoc _ V, ← hV, hGT, zero_mul]
    have hFh : ((1 - P) ⊗ₖ Q)ᴴ = (1 - P) ⊗ₖ Q := by
      rw [conjTranspose_kronecker, conjTranspose_sub, conjTranspose_one, hPh, hQh]
    have hAB : (P ⊗ₖ (1 - Q) * V) * ((1 - P) ⊗ₖ Q * V)ᴴ = 0 := by
      rw [conjTranspose_mul, hFh, ← mul_assoc, mul_assoc _ V, ← hV, hwing]
    obtain ⟨Pr, hPrh, hPrPr, hA, hB⟩ := proj_exists _ _ hAB
    obtain ⟨z, hz, hzQ⟩ := rank_two_proj Q hQ hrQ
    obtain ⟨n, hn, hnP⟩ := rank_two_proj P hP hrP
    have h1 : Pr * Prᴴ = Pr := by rw [hPrh, hPrPr]
    have h2 : (1 - Pr) * (1 - Pr)ᴴ = 1 - Pr := by
      rw [conjTranspose_sub, conjTranspose_one, hPrh, sub_mul, mul_sub, mul_sub, hPrPr]
      simp
    have hdec : T = (V * Pr) * (V * Pr)ᴴ + (V * (1 - Pr)) * (V * (1 - Pr))ᴴ := by
      calc T = V * (Pr + (1 - Pr)) * Vᴴ := by rw [hV]; simp
        _ = V * (Pr * Prᴴ) * Vᴴ + V * ((1 - Pr) * (1 - Pr)ᴴ) * Vᴴ := by
          rw [h1, h2, mul_add, add_mul]
        _ = _ := by simp only [conjTranspose_mul, mul_assoc]
    rw [hdec]
    apply sep_add
    · apply sep_of_right_support z hz
      have e1 : (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ Q = P ⊗ₖ Q + (1 - P) ⊗ₖ Q := by
        rw [← add_kronecker]; simp
      rw [← hzQ, kron_sub_right, one_kronecker_one, sub_mul, one_mul, e1, add_mul,
        ← mul_assoc, hGV, zero_mul, ← mul_assoc, hB, add_zero, sub_zero]
    · apply sep_of_left_support n hn
      have e1 : P ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) = P ⊗ₖ Q + P ⊗ₖ (1 - Q) := by
        rw [← kronecker_add]; simp
      have e2 : P ⊗ₖ (1 - Q) * V * (1 - Pr) = 0 := by rw [mul_sub, mul_one, hA, sub_self]
      rw [← hnP, kron_sub_left, one_kronecker_one, sub_mul, one_mul, e1, add_mul,
        ← mul_assoc, hGV, zero_mul, ← mul_assoc, e2, add_zero, sub_zero]

end X7ExtSep

open QAlgorithms.Papers.Independent.Information100.P07 in
/-- arXiv:2610.05234v1, PDF pp.18–19, Lemma S5: exact exterior separability test. -/
theorem solution (P Q : Local) (T : Joint)
    (hP : IsProjection P) (hQ : IsProjection Q) (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hT : T.PosSemidef) (hsupp : (1 - Matrix.kronecker P Q) * T * (1 - Matrix.kronecker P Q) = T) :
    IsSeparablePositive T ↔ Matrix.kronecker P (1 - Q) * T * Matrix.kronecker (1 - P) Q = 0 :=
  X7ExtSep.main P Q T hP hQ hrP hrQ hT hsupp
