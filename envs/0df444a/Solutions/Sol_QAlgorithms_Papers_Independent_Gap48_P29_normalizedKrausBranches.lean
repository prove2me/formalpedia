-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P29.normalizedKrausBranches
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:43:01.236033+00:00
-- url     : https://prove2.me/submissions/d29e2f1c-cc00-4417-939b-d0aa509f73b0

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7P29_lin_expand {I J : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (X : Matrix I I ℂ) :
    L X = ∑ i, ∑ j, X i j • L (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem X7P29_choi_psd {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (h : Entanglement.IsCompletelyPositive L) :
    (Matrix.of fun (p q : I × J) => L (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef := by
  let e := Fintype.equivFin I
  let Ω : Fin (Fintype.card I) × I → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : (Matrix.of fun (p q : I × J) => L (Matrix.single p.1 q.1 1) p.2 q.2) =
      (idTensorSuperop L (Matrix.vecMulVec Ω (star Ω))).submatrix
      (fun q : I × J => (e q.1, q.2)) (fun q => (e q.1, q.2)) := by
    ext ⟨i, o⟩ ⟨i', o'⟩
    rw [Matrix.submatrix_apply, Matrix.of_apply]
    show L (Matrix.single i i' 1) o o' =
      L (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) o o'
    have hX : (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) =
        Matrix.single i i' 1 := by
      ext j j'
      by_cases h1 : i = j <;> by_cases h2 : i' = j' <;>
        simp [Matrix.single_apply, Matrix.vecMulVec_apply, Ω, h1, h2, Ne.symm, eq_comm]
    rw [hX]
  rw [hE]
  exact hY.submatrix _

theorem X7P29_perm3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ l, f a b l = ∑ l, ∑ b, ∑ a, f a b l := by
  calc ∑ a, ∑ b, ∑ l, f a b l = ∑ a, ∑ l, ∑ b, f a b l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, f a b l := Finset.sum_comm
    _ = ∑ l, ∑ b, ∑ a, f a b l := Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem X7P29_kraus {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (h : Entanglement.IsCompletelyPositive L) :
    ∃ m : ℕ, ∃ K : Fin m → Matrix J I ℂ, ∀ X, L X = krausApply K X := by
  obtain ⟨m, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (X7P29_choi_psd L h)
  have hMij : ∀ i j o o', L (Matrix.single i j 1) o o' =
      ∑ l, g l (i, o) * star (g l (j, o')) := by
    intro i j o o'
    have := congrFun (congrFun hg (i, o)) (j, o')
    rw [Matrix.of_apply] at this
    rw [this, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  refine ⟨m, fun l => Matrix.of fun o i => g l (i, o), fun X => ?_⟩
  ext o o'
  rw [X7P29_lin_expand]
  simp only [krausApply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hMij,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [X7P29_perm3]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

theorem X7P29_entry {I : Type*} [Fintype I] [DecidableEq I] (K : Matrix I I ℂ) (i j k l : I) :
    (K * (Matrix.single j l (1:ℂ) : Matrix I I ℂ) * Kᴴ) i k = K i j * conj (K k l) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

theorem X7P29_fe {I : Type*} [Fintype I] [DecidableEq I] {κ : Type*} [Fintype κ]
    (rho : Matrix I I ℂ) (A : Superop I I) (K : κ → Matrix I I ℂ)
    (hA : ∀ X, A X = krausApply K X) :
    fe rho A = ∑ a, Complex.normSq ((K a * rho).trace) := by
  unfold fe
  have h5 : ∀ f : I → I → I → I → κ → ℂ, ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, f i j k l a =
      ∑ a, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l a := by
    intro f
    calc _ = ∑ i, ∑ j, ∑ k, ∑ a, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ a, ∑ k, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ k, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have ht : ∀ a, (K a * rho).trace = ∑ i, ∑ j, K a i j * rho j i := by
    intro a; simp [Matrix.trace, Matrix.mul_apply]
  have key : (∑ i, ∑ j, ∑ k, ∑ l, rho j i * conj (rho l k) * A (Matrix.single j l (1:ℂ)) i k) =
      ∑ a, (K a * rho).trace * conj ((K a * rho).trace) := by
    simp only [hA, krausApply, Matrix.sum_apply, X7P29_entry, Finset.mul_sum]
    rw [h5]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ht, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul]
    ring
  rw [key, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re]

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7P29_rot {I J : Type*} [Fintype J] {m : ℕ} (K : Fin m → Matrix I J ℂ) (c : Fin m → ℂ)
    (hc : ∑ a, c a * conj (c a) = 1 ∨ c = 0) (X : Matrix J J ℂ) :
    krausApply (Fin.cons (∑ a, c a • K a) (fun j => K j - conj (c j) • ∑ a, c a • K a) :
      Fin (m + 1) → Matrix I J ℂ) X = krausApply K X := by
  set K0 := ∑ a, c a • K a with hK0
  unfold krausApply
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have expand : ∀ j, (K j - conj (c j) • K0) * X * (K j - conj (c j) • K0)ᴴ =
      K j * X * (K j)ᴴ - c j • (K j * X * K0ᴴ) - conj (c j) • (K0 * X * (K j)ᴴ) +
        (c j * conj (c j)) • (K0 * X * K0ᴴ) := by
    intro j
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul]
    simp only [Complex.star_def, Complex.conj_conj, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, smul_sub, smul_smul]
    module
  have s1 : ∑ j, c j • (K j * X * K0ᴴ) = K0 * X * K0ᴴ := by
    simp only [hK0, Matrix.sum_mul, Matrix.smul_mul]
  have hK0h : K0ᴴ = ∑ j, conj (c j) • (K j)ᴴ := by
    rw [hK0, Matrix.conjTranspose_sum]
    simp [Matrix.conjTranspose_smul]
  have s2 : ∑ j, conj (c j) • (K0 * X * (K j)ᴴ) = K0 * X * K0ᴴ := by
    rw [hK0h, Matrix.mul_sum]
    simp only [Matrix.mul_smul]
  have s3 : ∑ j, (c j * conj (c j)) • (K0 * X * K0ᴴ) = (∑ j, c j * conj (c j)) • (K0 * X * K0ᴴ) := by
    rw [Finset.sum_smul]
  rw [Finset.sum_congr rfl (fun j _ => expand j)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [s1, s2, s3]
  rcases hc with h | h
  · rw [h, one_smul]; abel
  · have : K0 = 0 := by simp [hK0, h]
    simp [this]

theorem X7P29_main {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (A : Superop I I) (hA : TraceNonincreasingCPMap A) :
    ∃ m : ℕ, ∃ K : Fin (m + 1) → Matrix I I ℂ,
      Represents K A ∧ fe rho A = operatorFe rho (K 0) := by
  obtain ⟨⟨L, hL, hcp⟩, -⟩ := hA
  obtain ⟨m, K, hK⟩ := X7P29_kraus L hcp
  have hAK : ∀ X, A X = krausApply K X := fun X => by rw [← hL, hK]
  set v : Fin m → ℂ := fun a => (K a * rho).trace with hv
  set S : ℝ := ∑ a, Complex.normSq (v a) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  set s : ℝ := Real.sqrt S with hs
  set c : Fin m → ℂ := fun a => conj (v a) / (s : ℂ) with hc
  have hcv : ∑ a, c a * v a = (S : ℂ) / s := by
    simp only [hc, div_mul_eq_mul_div, ← Finset.sum_div, hS, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm, Complex.mul_conj]
  have hcc : ∑ a, c a * conj (c a) = 1 ∨ c = 0 := by
    by_cases h0 : s = 0
    · right; funext a; simp [hc, h0]
    · left
      have hS' : S ≠ 0 := by intro h; apply h0; rw [hs, h, Real.sqrt_zero]
      have : ∑ a, c a * conj (c a) = (S : ℂ) / (s : ℂ) ^ 2 := by
        simp only [hc, map_div₀, Complex.conj_ofReal, Complex.conj_conj, hS, Complex.ofReal_sum]
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Complex.mul_conj, mul_comm (v a)]
        field_simp
      rw [this]
      have : (s : ℂ) ^ 2 = S := by
        rw [← Complex.ofReal_pow, hs, Real.sq_sqrt hS0]
      rw [this, div_self (by exact_mod_cast hS')]
  refine ⟨m, Fin.cons (∑ a, c a • K a) (fun j => K j - conj (c j) • ∑ a, c a • K a),
    fun X => by rw [hAK, X7P29_rot K c hcc X], ?_⟩
  rw [X7P29_fe rho A K hAK, Fin.cons_zero]
  unfold operatorFe
  have htr : ((∑ a, c a • K a) * rho).trace = ∑ a, c a * v a := by
    simp [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, hv]
  rw [htr, hcv]
  by_cases h0 : s = 0
  · have : S = 0 := by
      have := Real.sq_sqrt hS0
      rw [← hs, h0] at this
      linarith
    simp only [h0, Complex.ofReal_zero, div_zero, map_zero]
    rw [← hS, this]
  · have hss : (S : ℂ) / s = s := by
      have : (s : ℂ) ^ 2 = S := by
        rw [← Complex.ofReal_pow, hs, Real.sq_sqrt hS0]
      rw [← this]
      field_simp [show (s : ℂ) ≠ 0 by exact_mod_cast h0]
    rw [hss, Complex.normSq_ofReal, ← hS, ← sq, hs, Real.sq_sqrt hS0]

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7P29b_comp {I J : Type*} [Fintype I] [Fintype J] {ma me : ℕ}
    (A : Superop J I) (E : Superop I J) (AK : Fin ma → Matrix I J ℂ) (EK : Fin me → Matrix J I ℂ)
    (hA : ∀ X, A X = krausApply AK X) (hE : ∀ X, E X = krausApply EK X) (X : Matrix I I ℂ) :
    (A ∘ E) X = krausApply (fun q : Fin ma × Fin me => AK q.1 * EK q.2) X := by
  simp only [Function.comp, hA, hE, krausApply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem X7P29b_branch {I J : Type*} [Fintype I] [Fintype J] (rho : Matrix I I ℂ)
    (hrho : rho.PosSemidef) (E : Matrix J I ℂ) :
    0 ≤ (E * rho * Eᴴ).trace.re ∧ ((E * rho * Eᴴ).trace.re = 0 → E * rho = 0) := by
  obtain ⟨n, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hrho
  let G : Matrix I (Fin n) ℂ := Matrix.of fun i l => g l i
  have hG : rho = G * Gᴴ := by
    rw [hg]; ext i i'
    simp [G, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Matrix.conjTranspose_apply]
  have hM : E * rho * Eᴴ = (E * G) * (E * G)ᴴ := by
    rw [hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  constructor
  · rw [hM]
    have := (Matrix.posSemidef_self_mul_conjTranspose (E * G)).trace_nonneg
    exact (Complex.nonneg_iff.mp this).1
  · intro h0
    have htr : ((E * G) * (E * G)ᴴ).trace = 0 := by
      rw [← hM]
      apply Complex.ext
      · simpa using h0
      · have := (Matrix.posSemidef_self_mul_conjTranspose (E * G)).trace_nonneg
        rw [← hM] at this
        simpa using ((Complex.nonneg_iff.mp this).2).symm
    have hz := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp htr
    rw [hG, ← Matrix.mul_assoc, hz, Matrix.zero_mul]

theorem X7P29b_conc {m : ℕ} (v : Fin m → ℂ) :
    let S : ℝ := ∑ a, Complex.normSq (v a)
    let c : Fin m → ℂ := fun a => conj (v a) / ((Real.sqrt S : ℝ) : ℂ)
    (∑ a, c a * conj (c a) = 1 ∨ c = 0) ∧ Complex.normSq (∑ a, c a * v a) = S := by
  intro S c
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  set s : ℝ := Real.sqrt S with hs
  have hcv : ∑ a, c a * v a = (S : ℂ) / s := by
    simp only [c, div_mul_eq_mul_div, ← Finset.sum_div, S, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm, Complex.mul_conj]
  have hs2 : (s : ℂ) ^ 2 = S := by
    rw [← Complex.ofReal_pow, hs, Real.sq_sqrt hS0]
  constructor
  · by_cases h0 : s = 0
    · right; funext a; simp [c, ← hs, h0]
    · left
      have hS' : S ≠ 0 := by intro h; apply h0; rw [hs, h, Real.sqrt_zero]
      have : ∑ a, c a * conj (c a) = (S : ℂ) / (s : ℂ) ^ 2 := by
        simp only [c, ← hs, map_div₀, Complex.conj_ofReal, Complex.conj_conj, S,
          Complex.ofReal_sum]
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Complex.mul_conj, mul_comm (v a)]
        field_simp
      rw [this, hs2, div_self (by exact_mod_cast hS')]
  · rw [hcv]
    by_cases h0 : s = 0
    · have : S = 0 := by
        have := Real.sq_sqrt hS0
        rw [← hs, h0] at this
        linarith
      simp only [h0, Complex.ofReal_zero, div_zero, map_zero]
      exact this.symm
    · have hss : (S : ℂ) / s = s := by
        rw [← hs2]
        field_simp [show (s : ℂ) ≠ 0 by exact_mod_cast h0]
      rw [hss, Complex.normSq_ofReal, ← sq, hs, Real.sq_sqrt hS0]

theorem X7P29b_main {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (A : Superop J I) (hA : IsChannel A) (E : Superop I J) (hE : FiniteCPMap E)
    (hnorm : (E rho).trace = 1) :
    ∃ a e : ℕ, ∃ AK : Fin (a + 1) → Matrix I J ℂ,
      ∃ EK : Fin (e + 1) → Matrix J I ℂ,
        Represents AK A ∧ Represents EK E ∧
        0 < (conjSuperop (EK 0) rho).trace.re ∧
        fe rho (A ∘ E) ≤ operatorFe rho
          (AK 0 * ((((Real.sqrt ((conjSuperop (EK 0) rho).trace.re))⁻¹ : ℝ) : ℂ) • EK 0)) := by
  obtain ⟨ma, AK0, -, hAK⟩ := hA
  obtain ⟨L, hL, hcp⟩ := hE
  obtain ⟨me, EK0, hEK⟩ := X7P29_kraus L hcp
  have hEK' : ∀ X, E X = krausApply EK0 X := fun X => by rw [← hL, hEK]
  let p : Fin me → ℝ := fun e => (conjSuperop (EK0 e) rho).trace.re
  have hp0 : ∀ e, 0 ≤ p e := fun e => (X7P29b_branch rho hrho.1 (EK0 e)).1
  have hpz : ∀ e, p e = 0 → EK0 e * rho = 0 := fun e => (X7P29b_branch rho hrho.1 (EK0 e)).2
  have hpsum : ∑ e, p e = 1 := by
    have := congrArg Complex.re hnorm
    rw [hEK', krausApply, Matrix.trace_sum, Complex.re_sum] at this
    simpa [p, conjSuperop] using this
  let v : Fin ma → Fin me → ℂ := fun a e => (AK0 a * EK0 e * rho).trace
  have hfe : fe rho (A ∘ E) = ∑ e, ∑ a, Complex.normSq (v a e) := by
    rw [X7P29_fe rho (A ∘ E) (fun q : Fin ma × Fin me => AK0 q.1 * EK0 q.2)
      (X7P29b_comp A E AK0 EK0 hAK hEK'), Fintype.sum_prod_type, Finset.sum_comm]
  let F : Fin me → ℝ := fun e => (∑ a, Complex.normSq (v a e)) / p e
  have hne : (Finset.univ.filter fun e => 0 < p e).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    have : ∑ e, p e ≤ 0 := Finset.sum_nonpos fun e _ => le_of_not_gt (h (Finset.mem_univ e))
    linarith
  obtain ⟨es, hes, hmax⟩ := Finset.exists_max_image _ F hne
  have hpes : 0 < p es := (Finset.mem_filter.mp hes).2
  have hfeF : fe rho (A ∘ E) ≤ F es := by
    rw [hfe]
    calc ∑ e, ∑ a, Complex.normSq (v a e) ≤ ∑ e, p e * F es := by
          apply Finset.sum_le_sum
          intro e _
          rcases (hp0 e).lt_or_eq with h | h
          · have := hmax e (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩)
            calc ∑ a, Complex.normSq (v a e) = p e * F e := by
                  simp only [F]; field_simp
              _ ≤ p e * F es := mul_le_mul_of_nonneg_left this (hp0 e)
          · have hz := hpz e h.symm
            have : ∀ a, v a e = 0 := by
              intro a; simp only [v]; rw [Matrix.mul_assoc, hz, Matrix.mul_zero, Matrix.trace_zero]
            simp [this, ← h]
      _ = F es := by rw [← Finset.sum_mul, hpsum, one_mul]
  -- reorder the Kraus family of E so that `es` comes first
  have hme : me - 1 + 1 = me := by have := es.pos; omega
  let σ : Fin me ≃ Fin me := Equiv.swap ⟨0, es.pos⟩ es
  let EK : Fin (me - 1 + 1) → Matrix J I ℂ := fun k => EK0 (σ (Fin.cast hme k))
  have hEK0 : EK 0 = EK0 es := by
    simp only [EK, σ]
    have : Fin.cast hme 0 = ⟨0, es.pos⟩ := rfl
    rw [this, Equiv.swap_apply_left]
  have hRepE : Represents EK E := by
    intro X
    rw [hEK']
    unfold krausApply
    exact (Fintype.sum_equiv ((finCongr hme).trans σ) _ _ (fun k => rfl)).symm
  -- concentrate the Kraus family of A on the selected branch
  obtain ⟨hcc, hcn⟩ := X7P29b_conc (fun a => v a es)
  set S : ℝ := ∑ a, Complex.normSq (v a es) with hS
  set c : Fin ma → ℂ := fun a => conj (v a es) / ((Real.sqrt S : ℝ) : ℂ) with hc
  refine ⟨ma, me - 1, Fin.cons (∑ a, c a • AK0 a) (fun j => AK0 j - conj (c j) • ∑ a, c a • AK0 a),
    EK, fun X => by rw [hAK, X7P29_rot AK0 c hcc X], hRepE, ?_, ?_⟩
  · rw [hEK0]; exact hpes
  · rw [hEK0, Fin.cons_zero]
    change fe rho (A ∘ E) ≤ operatorFe rho
      ((∑ a, c a • AK0 a) * (((Real.sqrt (p es))⁻¹ : ℝ) : ℂ) • EK0 es)
    unfold operatorFe
    have htr : ((∑ a, c a • AK0 a) * (((Real.sqrt (p es))⁻¹ : ℝ) : ℂ) • EK0 es * rho).trace =
        (((Real.sqrt (p es))⁻¹ : ℝ) : ℂ) * ∑ a, c a * v a es := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      congr 1
      simp [Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, v]
    rw [htr, Complex.normSq_mul, Complex.normSq_ofReal, hcn]
    have hF : F es = S / p es := rfl
    have hsq : (Real.sqrt (p es))⁻¹ * (Real.sqrt (p es))⁻¹ = (p es)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (hp0 es)]
    rw [hsq, ← div_eq_inv_mul, ← hF]
    exact hfeF

end QAlgorithms.Papers.Independent.Gap48.P29

end

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P29 in
theorem solution {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (A : Superop J I) (hA : IsChannel A) (E : Superop I J) (hE : FiniteCPMap E)
    (hnorm : (E rho).trace = 1) :
    ∃ a e : ℕ, ∃ AK : Fin (a + 1) → Matrix I J ℂ,
      ∃ EK : Fin (e + 1) → Matrix J I ℂ,
        Represents AK A ∧ Represents EK E ∧
        0 < (conjSuperop (EK 0) rho).trace.re ∧
        fe rho (A ∘ E) ≤ operatorFe rho
          (AK 0 * ((((Real.sqrt ((conjSuperop (EK 0) rho).trace.re))⁻¹ : ℝ) : ℂ) • EK 0)) :=
  QAlgorithms.Papers.Independent.Gap48.P29.X7P29b_main rho hrho A hA E hE hnorm
