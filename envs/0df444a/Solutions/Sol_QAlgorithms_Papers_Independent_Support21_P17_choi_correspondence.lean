-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.choi_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:23:09.158999+00:00
-- url     : https://prove2.me/submissions/7b967e3f-d9a7-40df-b359-7051b7dd61c0

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

lemma g66j_cpt (m n : ℕ)
    (A : M m) (B : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    (tracialV m n).conjTranspose * Matrix.kronecker A B * tracialV m n =
      (m : ℂ)⁻¹ • traceRight (Matrix.kronecker (1 : M n) A.transpose * B) := by
  ext ν ν'
  simp only [Matrix.mul_apply, tracialV, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    traceRight, Matrix.smul_apply, Matrix.of_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    Matrix.one_apply]
  simp only [apply_ite, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, one_mul]
  simp only [Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.one_apply, Matrix.transpose_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hc : star (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) = (m : ℂ)⁻¹ := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg m)]
    push_cast; ring
  rw [smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.sum_comm, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [← hc]; ring

lemma g66j_lin_expand {m n : ℕ} (T : Lin m n) (A : M m) :
    T A = ∑ b, ∑ h, A b h • T (Matrix.single b h 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun h _ => ?_))
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

lemma g66j_recon (m n : ℕ) (hm : 0 < m) (T : Lin m n) (A : M m) :
    T A = (tracialV m n).conjTranspose * Matrix.kronecker A (scaledChoi T) * tracialV m n := by
  rw [g66j_cpt]
  ext ν ν'
  rw [g66j_lin_expand T A]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Matrix.sum_apply, Matrix.smul_apply, traceRight, Matrix.of_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.transpose_apply, scaledChoi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  field_simp

lemma g66j_choi_comp (m n d : ℕ) (hn : 0 < n) (T1 : Lin m n) (T2 : Lin n d) :
    scaledChoi (T2.comp T1) = bellCompression (scaledChoi T2) (scaledChoi T1) := by
  ext x y
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [scaledChoi, bellCompression, LinearMap.comp_apply]
  rw [g66j_lin_expand T2 (T1 _)]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun h _ => ?_))
  field_simp

lemma g66j_psd_of_nonneg {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (hq : ∀ v : n → ℂ, 0 ≤ star v ⬝ᵥ (M *ᵥ v)) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ hq
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have h := hq (WithLp.ofLp v)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
  have him := (Complex.nonneg_iff.mp h).2
  have e : v.ofLp ⬝ᵥ star (M *ᵥ v.ofLp) = star (star v.ofLp ⬝ᵥ M *ᵥ v.ofLp) := by
    simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  rw [e]
  apply Complex.ext <;> simp; rw [← him]; simp

lemma g66j_qf {I K : Type*} [Fintype I] [Fintype K] (v : K → I → ℂ) (x : I → ℂ) :
    star x ⬝ᵥ ((∑ k, Matrix.vecMulVec (v k) (star (v k))) *ᵥ x) =
      ((∑ k, ‖∑ q, star (v k q) * x q‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  simp only [dotProduct, Matrix.mulVec, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  have e : ∀ k, ((‖∑ q, star (v k q) * x q‖ : ℝ) : ℂ) ^ 2 =
      ∑ p, ∑ q, star (x p) * (v k p * star (v k q) * x q) := by
    intro k
    rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
    ring
  simp only [e]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_comm]

lemma g66j_cs {m : ℕ} (w : Fin m → ℂ) : ‖∑ a, w a‖ ^ 2 ≤ m * ∑ a, ‖w a‖ ^ 2 := by
  calc ‖∑ a, w a‖ ^ 2 ≤ (∑ a, ‖w a‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ _ := by
        have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖w a‖)
        simpa using this

lemma g66j_key {n m : ℕ} (F : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) (hF : F.PosSemidef)
    (c : ℝ) (hG : ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - traceRight F).PosSemidef) :
    (((m * c : ℝ) : ℂ) • (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) - F).PosSemidef := by
  obtain ⟨r, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hF
  have hTr : traceRight F = ∑ kh : Fin r × Fin m,
      Matrix.vecMulVec (fun ν => v kh.1 (ν, kh.2)) (star (fun ν => v kh.1 (ν, kh.2))) := by
    ext ν ν'
    simp only [traceRight, Matrix.of_apply, hv, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Pi.star_apply, Fintype.sum_prod_type]
    exact Finset.sum_comm
  apply g66j_psd_of_nonneg
  intro x
  have hsplit : star x ⬝ᵥ ((((m * c : ℝ) : ℂ) • (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) - F) *ᵥ x)
      = (((m * c : ℝ) : ℂ)) * (star x ⬝ᵥ x) - star x ⬝ᵥ (F *ᵥ x) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
  -- per-slice inequalities
  have hslice : ∀ a : Fin m, ∑ kh : Fin r × Fin m,
      ‖∑ ν, star (v kh.1 (ν, kh.2)) * x (ν, a)‖ ^ 2 ≤ c * ∑ ν, ‖x (ν, a)‖ ^ 2 := by
    intro a
    have h := hG.dotProduct_mulVec_nonneg (fun ν => x (ν, a))
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul, hTr, g66j_qf] at h
    have e : star (fun ν => x (ν, a)) ⬝ᵥ (fun ν => x (ν, a)) = ((∑ ν, ‖x (ν, a)‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply]; push_cast
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      rw [← Complex.conj_mul']; rfl
    rw [e, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.zero_le_real] at h
    linarith
  have hx : star x ⬝ᵥ x = ((∑ a, ∑ ν, ‖x (ν, a)‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type]; push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun ν _ => ?_))
    rw [← Complex.conj_mul']; rfl
  rw [hsplit, hv, g66j_qf, hx, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.zero_le_real]
  -- main real inequality
  have hS : ∀ k, ∑ q, star (v k q) * x q = ∑ a, ∑ ν, star (v k (ν, a)) * x (ν, a) := by
    intro k; rw [Fintype.sum_prod_type, Finset.sum_comm]
  have step1 : ∀ k, ‖∑ q, star (v k q) * x q‖ ^ 2 ≤
      m * ∑ a, ∑ h, ‖∑ ν, star (v k (ν, h)) * x (ν, a)‖ ^ 2 := by
    intro k
    rw [hS k]
    refine (g66j_cs _).trans ?_
    gcongr with a
    exact Finset.single_le_sum (f := fun h => ‖∑ ν, star (v k (ν, h)) * x (ν, a)‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ a)
  have step2 : ∑ k, ‖∑ q, star (v k q) * x q‖ ^ 2 ≤
      m * ∑ a, ∑ kh : Fin r × Fin m, ‖∑ ν, star (v kh.1 (ν, kh.2)) * x (ν, a)‖ ^ 2 := by
    refine (Finset.sum_le_sum (fun k _ => step1 k)).trans (le_of_eq ?_)
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Fintype.sum_prod_type]
  have step3 : m * ∑ a, ∑ kh : Fin r × Fin m, ‖∑ ν, star (v kh.1 (ν, kh.2)) * x (ν, a)‖ ^ 2 ≤
      m * ∑ a, c * ∑ ν, ‖x (ν, a)‖ ^ 2 := by
    gcongr with a; exact hslice a
  rw [← Finset.mul_sum] at step3
  nlinarith [step2, step3]

def g66j_ofc {I O : Type*} (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Matrix (O × I) (O × I) ℂ :=
  Matrix.of fun p q => M (Matrix.single p.2 q.2 1) p.1 q.1

theorem g66j_sum_psd {I ι : Type*} [Fintype I] (s : Finset ι) (A : ι → Matrix I I ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem g66j_swap22 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem g66j_lin_expand' {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem g66j_cp_of_choi {I O : Type*} [Fintype I] [Fintype O]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hC : (g66j_ofc M).PosSemidef) :
    Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  obtain ⟨m2, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (o, i) * star (g l (o', j)) := by
    intro i j o o'
    have : M (Matrix.single i j 1) o o' = g66j_ofc M (o, i) (o', j) := rfl
    rw [this, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  let F : Fin m1 → Fin m2 → (Fin r × O → ℂ) := fun a l q => ∑ i, v a (q.1, i) * g l (q.2, i)
  have hY : idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [g66j_lin_expand']
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [g66j_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact g66j_sum_psd _ _ fun a => g66j_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _

theorem g66j_choi_of_cp {I O : Type*} [Fintype I] [Fintype O]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (h : Entanglement.IsCompletelyPositive M) :
    (g66j_ofc M).PosSemidef := by
  let e := Fintype.equivFin I
  let Ω : Fin (Fintype.card I) × I → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : g66j_ofc M = (idTensorSuperop M (Matrix.vecMulVec Ω (star Ω))).submatrix
      (fun q : O × I => (e q.2, q.1)) (fun q => (e q.2, q.1)) := by
    ext ⟨o, i⟩ ⟨o', i'⟩
    rw [Matrix.submatrix_apply]
    show M (Matrix.single i i' 1) o o' =
      M (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) o o'
    have hX : (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) =
        Matrix.single i i' 1 := by
      ext j j'
      by_cases h1 : i = j <;> by_cases h2 : i' = j' <;>
        simp [Matrix.single_apply, Matrix.vecMulVec_apply, Ω, h1, h2, Ne.symm, eq_comm]
    rw [hX]
  rw [hE]
  exact hY.submatrix _

lemma g66j_sc_eq {m n : ℕ} (T : Lin m n) : scaledChoi T = (m : ℂ) • g66j_ofc T := by
  ext p q; rw [Matrix.smul_apply, smul_eq_mul]; simp only [scaledChoi, g66j_ofc, Matrix.of_apply]; convert rfl

lemma g66j_psd_smul_iff {ι : Type*} [Fintype ι] (c : ℂ) (hc : 0 < c) (X : Matrix ι ι ℂ) :
    (c • X).PosSemidef ↔ X.PosSemidef := by
  constructor
  · intro h
    have hc' : c ≠ 0 := hc.ne'
    have : X = c⁻¹ • (c • X) := by rw [smul_smul, inv_mul_cancel₀ hc', one_smul]
    rw [this]; exact h.smul (inv_nonneg.mpr hc.le)
  · intro h; exact h.smul hc.le

lemma g66j_cp_iff {m n : ℕ} (hm : 0 < m) (T : Lin m n) :
    Entanglement.IsCompletelyPositive T ↔ (scaledChoi T).PosSemidef := by
  have hc : (0 : ℂ) < m := by exact_mod_cast hm
  rw [g66j_sc_eq, g66j_psd_smul_iff _ hc]
  exact ⟨g66j_choi_of_cp T, g66j_cp_of_choi T⟩

lemma g66j_coef_apply {dx dy : ℕ} (C : Fin dy → Fin dy → Fin dx → Fin dx → ℂ) (X : M dx) (y z : Fin dy) :
    coefficientMap C X y z = ∑ a, ∑ b, C y z a b * X a b := rfl

lemma g66j_from_sc {m n : ℕ} (hm : 0 < m) (T : Lin m n) : fromScaledChoi (scaledChoi T) = T := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  apply LinearMap.ext; intro A
  ext μ ν
  rw [fromScaledChoi, g66j_coef_apply, g66j_lin_expand' T A]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, scaledChoi]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  field_simp
  rw [mul_comm]; convert rfl

lemma g66j_sc_from {m n : ℕ} (hm : 0 < m) (F : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    scaledChoi (fromScaledChoi F) = F := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  ext p q
  rw [scaledChoi, fromScaledChoi, g66j_coef_apply]
  simp only [Matrix.single_apply, mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp

lemma g66j_trR {m n : ℕ} (T : Lin m n) : traceRight (scaledChoi T) = (m : ℂ) • T 1 := by
  ext ν ν'
  rw [g66j_lin_expand' T 1]
  simp only [traceRight, Matrix.of_apply, scaledChoi, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  convert rfl

lemma g66j_sc_sub {m n : ℕ} (a : ℂ) (S T : Lin m n) :
    scaledChoi (a • S - T) = a • scaledChoi S - scaledChoi T := by
  ext p q; simp [scaledChoi]; ring

lemma g66j_sc_prep {m n : ℕ} (hm : 0 < m) : scaledChoi (tracialPreparation m n) = 1 := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  ext p q
  rw [scaledChoi, tracialPreparation, g66j_coef_apply]
  simp only [Matrix.single_apply, mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, hm']

theorem solution (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∀ T : Lin m n,
      Entanglement.IsCompletelyPositive T ↔ (scaledChoi T).PosSemidef) ∧
    (∀ T : Lin m n, fromScaledChoi (scaledChoi T) = T) ∧
    (∀ F : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ,
      scaledChoi (fromScaledChoi F) = F ∧
      (F.PosSemidef → Entanglement.IsCompletelyPositive (fromScaledChoi F))) ∧
    (∀ (T : Lin m n), Entanglement.IsCompletelyPositive T →
      (∀ A, T A = (tracialV m n).conjTranspose * Matrix.kronecker A (scaledChoi T) * tracialV m n) ∧
      (∀ A, T A = (m : ℂ)⁻¹ • traceRight
        (Matrix.kronecker (1 : M n) A.transpose * scaledChoi T)) ∧
      ((1 - T 1).PosSemidef ↔ ((m : ℂ) • (1 : M n) - traceRight (scaledChoi T)).PosSemidef) ∧
      ((1 - T 1).PosSemidef →
        (((m : ℂ) ^ 2) • (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) - scaledChoi T).PosSemidef ∧
        Entanglement.IsCompletelyPositive (((m : ℂ) ^ 2) • tracialPreparation m n - T))) := by
  have hc : (0 : ℂ) < m := by exact_mod_cast hm
  have hunit : ∀ T : Lin m n, (m : ℂ) • (1 : M n) - traceRight (scaledChoi T) = (m : ℂ) • (1 - T 1) := by
    intro T; rw [g66j_trR, smul_sub]
  refine ⟨g66j_cp_iff hm, g66j_from_sc hm, fun F => ⟨g66j_sc_from hm F, fun hF => ?_⟩, fun T hT => ?_⟩
  · rw [g66j_cp_iff hm, g66j_sc_from hm]; exact hF
  refine ⟨g66j_recon m n hm T, fun A => by rw [← g66j_cpt]; exact g66j_recon m n hm T A, ?_, ?_⟩
  · rw [hunit, g66j_psd_smul_iff _ hc]
  · intro h1
    have hkey := g66j_key (scaledChoi T) ((g66j_cp_iff hm T).1 hT) (m : ℝ)
      (by rw [Complex.ofReal_natCast, hunit, g66j_psd_smul_iff _ hc]; exact h1)
    have e : (((m * m : ℝ)) : ℂ) = (m : ℂ) ^ 2 := by push_cast; ring
    rw [e] at hkey
    refine ⟨hkey, ?_⟩
    rw [g66j_cp_iff hm, g66j_sc_sub, g66j_sc_prep hm]
    exact hkey

end
