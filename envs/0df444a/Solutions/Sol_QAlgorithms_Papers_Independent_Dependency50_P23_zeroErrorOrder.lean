-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P23.zeroErrorOrder
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:27:46.56299+00:00
-- url     : https://prove2.me/submissions/6bb6d0c0-b86d-4880-bd72-bb3c955a517e

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

set_option linter.unusedSectionVars false

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def x8vec (X : Matrix B A ℂ) : A × B → ℂ := fun p => X p.2 p.1

def x8ip (u x : A × B → ℂ) : ℂ := ∑ p, conj (x p) * u p

def x8Q (J : Matrix (A × B) (A × B) ℂ) (x : A × B → ℂ) : ℂ :=
  ∑ p, ∑ q, conj (x p) * J p q * x q

lemma x8_choi_kraus {m : ℕ} (E : Fin m → Matrix B A ℂ) (N : Superop A B)
    (hN : ∀ ρ, N ρ = krausApply E ρ) :
    choi N = ∑ i, Matrix.vecMulVec (x8vec (E i)) (star (x8vec (E i))) := by
  ext p q
  simp only [choi, hN, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    x8vec, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Pi.star_apply, ite_and]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma x8_Q_rank1 (u x : A × B → ℂ) :
    x8Q (Matrix.vecMulVec u (star u)) x = ((‖x8ip u x‖ ^ 2 : ℝ) : ℂ) := by
  have : x8Q (Matrix.vecMulVec u (star u)) x = x8ip u x * conj (x8ip u x) := by
    unfold x8Q x8ip
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def, map_mul,
      Complex.conj_conj]
    ring
  rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma x8_Q_sum {m : ℕ} (J : Fin m → Matrix (A × B) (A × B) ℂ) (x : A × B → ℂ) :
    x8Q (∑ i, J i) x = ∑ i, x8Q (J i) x := by
  unfold x8Q
  simp only [Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_comm

lemma x8_Q_choi_re {m : ℕ} (E : Fin m → Matrix B A ℂ) (N : Superop A B)
    (hN : ∀ ρ, N ρ = krausApply E ρ) (x : A × B → ℂ) :
    (x8Q (choi N) x).re = ∑ i, ‖x8ip (x8vec (E i)) x‖ ^ 2 := by
  rw [x8_choi_kraus E N hN, x8_Q_sum, Complex.re_sum]
  simp only [x8_Q_rank1, Complex.ofReal_re]

lemma x8_Q_choi_nonneg (N : Superop A B) (hN : IsChannel N) (x : A × B → ℂ) :
    0 ≤ (x8Q (choi N) x).re := by
  obtain ⟨m, E, -, hE⟩ := hN
  rw [x8_Q_choi_re E N hE]; positivity

lemma x8_vec_add (X Y : Matrix B A ℂ) : x8vec (X + Y) = x8vec X + x8vec Y := rfl

lemma x8_ip_add (u v x : A × B → ℂ) : x8ip (u + v) x = x8ip u x + x8ip v x := by
  simp [x8ip, mul_add, Finset.sum_add_distrib]

lemma x8_ip_smul (c : ℂ) (u x : A × B → ℂ) : x8ip (c • u) x = c * x8ip u x := by
  simp [x8ip, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring

lemma x8_gen_bound (N : Superop A B) (X : Matrix B A ℂ) (hX : X ∈ bipartiteGraph N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖x8ip (x8vec X) x‖ ^ 2 ≤ C * (x8Q (choi N) x).re := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨k, F, -, hF, i, rfl⟩ := hX
    refine ⟨1, zero_le_one, fun x => ?_⟩
    rw [one_mul, x8_Q_choi_re F N hF]
    exact Finset.single_le_sum (f := fun j => ‖x8ip (x8vec (F j)) x‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  | zero =>
    refine ⟨0, le_rfl, fun x => ?_⟩
    simp [x8ip, x8vec]
  | add X Y _ _ hX hY =>
    obtain ⟨C1, hC1, h1⟩ := hX
    obtain ⟨C2, hC2, h2⟩ := hY
    refine ⟨2 * C1 + 2 * C2, by positivity, fun x => ?_⟩
    rw [x8_vec_add, x8_ip_add]
    have ht := norm_add_le (x8ip (x8vec X) x) (x8ip (x8vec Y) x)
    have hn1 := norm_nonneg (x8ip (x8vec X) x)
    have hn2 := norm_nonneg (x8ip (x8vec Y) x)
    have := h1 x
    have := h2 x
    nlinarith [sq_nonneg (‖x8ip (x8vec X) x‖ - ‖x8ip (x8vec Y) x‖),
      norm_nonneg (x8ip (x8vec X) x + x8ip (x8vec Y) x)]
  | smul c X _ hX =>
    obtain ⟨C1, hC1, h1⟩ := hX
    refine ⟨‖c‖ ^ 2 * C1, by positivity, fun x => ?_⟩
    have : x8vec (c • X) = c • x8vec X := rfl
    rw [this, x8_ip_smul, norm_mul, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 x) (by positivity)

lemma x8_dom (N G : Superop A B) (hG : IsChannel G)
    (hK : bipartiteGraph G ≤ bipartiteGraph N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (x8Q (choi G) x).re ≤ C * (x8Q (choi N) x).re := by
  obtain ⟨m, E, hE, hGE⟩ := hG
  have hmem : ∀ j, E j ∈ bipartiteGraph N := fun j =>
    hK (Submodule.subset_span ⟨m, E, hE, hGE, j, rfl⟩)
  choose C hC0 hC using fun j => x8_gen_bound N (E j) (hmem j)
  refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC0 j, fun x => ?_⟩
  rw [x8_Q_choi_re E G hGE, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => hC j x

lemma x8_tr_rank1 (J : Matrix (A × B) (A × B) ℂ) (v : A × B → ℂ) :
    (J * Matrix.vecMulVec v (star v)).trace = x8Q J v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, x8Q,
    Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma x8_tr_psd (N G : Superop A B) (hN : IsChannel N) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, (x8Q (choi G) x).re ≤ C * (x8Q (choi N) x).re)
    (P : Matrix (A × B) (A × B) ℂ) (hP : P.PosSemidef) :
    0 ≤ (choi N * P).trace.re ∧ (choi G * P).trace.re ≤ C * (choi N * P).trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hP
  simp only [Matrix.mul_sum, Matrix.trace_sum, x8_tr_rank1, Complex.re_sum, Finset.mul_sum]
  exact ⟨Finset.sum_nonneg fun k _ => x8_Q_choi_nonneg N hN (v k),
    Finset.sum_le_sum fun k _ => hC (v k)⟩

lemma x8_tr_one (N : Superop A B) (hN : IsChannel N) (ρ : Matrix A A ℂ) (hρ : ρ.trace = 1) :
    (choi N * Matrix.kronecker ρ (1 : Matrix B B ℂ)).trace = 1 := by
  obtain ⟨m, E, hE, hNE⟩ := hN
  rw [x8_choi_kraus E N hNE, Matrix.sum_mul, Matrix.trace_sum, ← hρ]
  have h1 : ∀ a a', ∑ i, ∑ b, conj (E i b a) * E i b a' = if a = a' then 1 else 0 := by
    intro a a'
    have := congrFun (congrFun hE a) a'
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      RCLike.star_def, Matrix.one_apply] at this
    exact this
  have h2 : ∀ i, (Matrix.vecMulVec (x8vec (E i)) (star (x8vec (E i))) *
      Matrix.kronecker ρ (1 : Matrix B B ℂ)).trace =
      ∑ a, ∑ a', ρ a' a * ∑ b, conj (E i b a') * E i b a := by
    intro i
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, x8vec, Pi.star_apply,
      RCLike.star_def, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [h2]
  calc ∑ i, ∑ a, ∑ a', ρ a' a * ∑ b, conj (E i b a') * E i b a
      = ∑ a, ∑ a', ρ a' a * ∑ i, ∑ b, conj (E i b a') * E i b a := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ρ.trace := by
        simp only [h1, mul_ite, mul_one, mul_zero]
        simp [Matrix.trace]

lemma x8_eff (N : Superop A B) (hN : IsChannel N) {ppt : Bool} {lam : ℝ} {ρ : Matrix A A ℂ}
    {F : Matrix (A × B) (A × B) ℂ} (hf : SuccessFeasible ppt lam⁻¹ ρ F) :
    (Matrix.kronecker ρ (1 : Matrix B B ℂ) - F).PosSemidef ∧
    effectProb (choi N) F = 1 - (choi N * (Matrix.kronecker ρ (1 : Matrix B B ℂ) - F)).trace.re := by
  obtain ⟨hρ, -, hle, -, -⟩ := hf
  refine ⟨hle, ?_⟩
  unfold effectProb
  rw [Matrix.mul_sub, Matrix.trace_sub, x8_tr_one N hN ρ hρ.2]
  simp

lemma x8_cs (u x : A × B → ℂ) :
    ‖x8ip u x‖ ^ 2 ≤ (∑ p, ‖x p‖ ^ 2) * ∑ p, ‖u p‖ ^ 2 := by
  have h1 : ‖x8ip u x‖ ≤ ∑ p, ‖x p‖ * ‖u p‖ := by
    unfold x8ip
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p => ‖x p‖) (fun p => ‖u p‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

lemma x8_Q_bound (N : Superop A B) (hN : IsChannel N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, (x8Q (choi N) x).re ≤ K * ∑ p, ‖x p‖ ^ 2 := by
  obtain ⟨m, E, -, hE⟩ := hN
  refine ⟨∑ i, ∑ p, ‖x8vec (E i) p‖ ^ 2, by positivity, fun x => ?_⟩
  rw [x8_Q_choi_re E N hE, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => (x8_cs _ x).trans (le_of_eq (mul_comm _ _))

lemma x8_tr_bound (N : Superop A B) (K : ℝ) (hK : ∀ x, (x8Q (choi N) x).re ≤ K * ∑ p, ‖x p‖ ^ 2)
    (F : Matrix (A × B) (A × B) ℂ) (hF : F.PosSemidef) :
    (choi N * F).trace.re ≤ K * F.trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hF
  simp only [Matrix.mul_sum, Matrix.trace_sum, x8_tr_rank1, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => (hK (v k)).trans (le_of_eq ?_)
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

lemma x8_trace_traceLeft (F : Matrix (A × B) (A × B) ℂ) : (traceLeft F).trace = F.trace := by
  simp only [Matrix.trace, Matrix.diag, traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma x8_succ_le (N : Superop A B) (K : ℝ) (hK : ∀ x, (x8Q (choi N) x).re ≤ K * ∑ p, ‖x p‖ ^ 2)
    {ppt : Bool} {lam : ℝ} {ρ : Matrix A A ℂ} {F : Matrix (A × B) (A × B) ℂ}
    (hf : SuccessFeasible ppt lam⁻¹ ρ F) :
    effectProb (choi N) F ≤ K * (lam⁻¹ * Fintype.card B) := by
  obtain ⟨-, hF, -, htl, -⟩ := hf
  have := x8_tr_bound N K hK F hF
  have htr : F.trace.re = lam⁻¹ * Fintype.card B := by
    rw [← x8_trace_traceLeft, htl, Matrix.trace_smul, Matrix.trace_one]; simp
  unfold effectProb; rw [← htr]; exact this

lemma x8_succ_le_one (N : Superop A B) (hN : IsChannel N) {ppt : Bool} {lam : ℝ}
    {ρ : Matrix A A ℂ} {F : Matrix (A × B) (A × B) ℂ} (hf : SuccessFeasible ppt lam⁻¹ ρ F) :
    effectProb (choi N) F ≤ 1 := by
  obtain ⟨hP, he⟩ := x8_eff N hN hf
  rw [he]
  have := (x8_tr_psd N N hN 1 zero_le_one (fun x => by simp) _ hP).1
  linarith

lemma x8_lam_bound (N : Superop A B) (hN : IsChannel N) (ppt : Bool) :
    ∃ L : ℝ, ∀ lam : ℝ, 1 ≤ lam → 1 ≤ realSuccess ppt N lam → lam ≤ L := by
  obtain ⟨K, hK0, hK⟩ := x8_Q_bound N hN
  refine ⟨K * Fintype.card B, fun lam hlam h => ?_⟩
  have hne : (successValues ppt N lam).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    unfold realSuccess at h
    rw [hc, Real.sSup_empty] at h
    linarith
  have hle : realSuccess ppt N lam ≤ K * (lam⁻¹ * Fintype.card B) := by
    refine csSup_le hne ?_
    rintro s ⟨ρ, F, hf, rfl⟩
    exact x8_succ_le N K hK hf
  have h1 : 1 ≤ K * (lam⁻¹ * Fintype.card B) := h.trans hle
  have hl : 0 < lam := by linarith
  rw [← mul_assoc, mul_comm K, mul_assoc, inv_mul_eq_div, le_div_iff₀ hl, one_mul] at h1
  linarith

lemma x8_T_bdd (N : Superop A B) (hN : IsChannel N) (ppt : Bool) :
    BddAbove {r | ∃ lam : ℝ, 1 ≤ lam ∧ 1 - 0 ≤ realSuccess ppt N lam ∧ r = log2 lam} := by
  obtain ⟨L, hL⟩ := x8_lam_bound N hN ppt
  refine ⟨log2 L, ?_⟩
  rintro r ⟨lam, h1, h2, rfl⟩
  rw [sub_zero] at h2
  have := hL lam h1 h2
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) this)
    (Real.log_nonneg (by norm_num))

lemma x8_S_bdd (N : Superop A B) (hN : IsChannel N) (ppt : Bool) (lam : ℝ) :
    BddAbove (successValues ppt N lam) := by
  refine ⟨1, ?_⟩
  rintro s ⟨ρ, F, hf, rfl⟩
  exact x8_succ_le_one N hN hf

lemma x8_choi_kron (N : Superop A B) (hN : IsChannel N) (X : Matrix A A ℂ) (Y : Matrix B B ℂ) :
    (choi N * Matrix.kronecker Xᵀ Y).trace = (Y * N X).trace := by
  obtain ⟨m, E, -, hE⟩ := hN
  rw [x8_choi_kraus E N hE, Matrix.sum_mul, Matrix.trace_sum, hE, krausApply, Matrix.mul_sum,
    Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_mul_comm, x8_tr_rank1]
  simp only [x8Q, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, x8vec, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  ring

lemma x8_code (N : Superop A B) (hN : IsChannel N) {m : ℕ} (hm : 0 < m) (K : UACode A B m)
    (hK : uaCodeSuccess N K = 1) : 1 ≤ realSuccess true N m := by
  set c : ℂ := (((m : ℝ)⁻¹ : ℝ) : ℂ) with hcdef
  have hc : 0 ≤ c := Complex.zero_le_real.2 (by positivity)
  have hmc : c * (m : ℂ) = 1 := by
    rw [hcdef]; push_cast; field_simp
  set ρ : Matrix A A ℂ := c • ∑ k, (K.state k)ᵀ with hρ
  set F : Matrix (A × B) (A × B) ℂ :=
    c • ∑ k, Matrix.kronecker (K.state k)ᵀ (K.measurement k) with hF
  have hst : ∀ k, ((K.state k)ᵀ).PosSemidef := fun k => (K.density k).1.transpose
  have hM : ∀ k, (K.measurement k).PosSemidef := fun k => K.povm.1 k
  have hMc : ∀ k, (1 - K.measurement k).PosSemidef := by
    intro k
    rw [← K.povm.2, ← Finset.sum_erase_eq_sub (Finset.mem_univ k)]
    exact Matrix.posSemidef_sum _ fun o _ => hM o
  have hkron : ∀ (X : Matrix A A ℂ) (Y : Matrix B B ℂ), X.PosSemidef → Y.PosSemidef →
      (Matrix.kronecker X Y).PosSemidef := fun X Y hX hY => hX.kronecker hY
  have hfeas : SuccessFeasible true ((m : ℝ))⁻¹ ρ F := by
    refine ⟨⟨(Matrix.posSemidef_sum _ fun k _ => hst k).smul hc, ?_⟩,
      (Matrix.posSemidef_sum _ fun k _ => hkron _ _ (hst k) (hM k)).smul hc, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩
    · rw [hρ, Matrix.trace_smul, Matrix.trace_sum]
      simp only [Matrix.trace_transpose, fun k => (K.density k).2]
      simp [hmc]
    · have : Matrix.kronecker ρ (1 : Matrix B B ℂ) - F =
          c • ∑ k, Matrix.kronecker (K.state k)ᵀ (1 - K.measurement k) := by
        ext p q
        simp only [hρ, hF, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.kronecker,
          Matrix.kroneckerMap_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      unfold LEop; rw [this]
      exact (Matrix.posSemidef_sum _ fun k _ => hkron _ _ (hst k) (hMc k)).smul hc
    · ext b b'
      have hP := congrFun (congrFun K.povm.2 b) b'
      simp only [Matrix.sum_apply] at hP
      have htr : ∀ k, ∑ a, K.state k a a = 1 := fun k => (K.density k).2
      simp only [traceLeft, hF, Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply, smul_eq_mul]
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [← Finset.sum_mul, htr, one_mul, hP]
      rfl
    · have : PT F = c • ∑ k, Matrix.kronecker (K.state k)ᵀ (K.measurement k)ᵀ := by
        ext p q
        simp [PT, QAlgorithms.Papers.Independent.Information100.P03.partialTransposeB,
          Entanglement.partialTransposeFirst, hF, Matrix.sum_apply, Matrix.kronecker,
          Matrix.kroneckerMap_apply]
      rw [this]
      exact (Matrix.posSemidef_sum _ fun k _ => hkron _ _ (hst k) (hM k).transpose).smul hc
    · have : Matrix.kronecker ρ (1 : Matrix B B ℂ) - PT F =
          c • ∑ k, Matrix.kronecker (K.state k)ᵀ (1 - (K.measurement k)ᵀ) := by
        ext p q
        simp only [PT, QAlgorithms.Papers.Independent.Information100.P03.partialTransposeB,
          Entanglement.partialTransposeFirst, hρ, hF, Matrix.of_apply, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.transpose_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      unfold LEop; rw [this]
      have h' : ∀ k, (1 - (K.measurement k)ᵀ).PosSemidef := fun k => by
        have := (hMc k).transpose
        rwa [Matrix.transpose_sub, Matrix.transpose_one] at this
      exact (Matrix.posSemidef_sum _ fun k _ => hkron _ _ (hst k) (h' k)).smul hc
  have hval : effectProb (choi N) F = 1 := by
    rw [← hK]
    unfold effectProb uaCodeSuccess
    rw [hF, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum]
    simp only [x8_choi_kron N hN, effectProb, hcdef, smul_eq_mul]
    rw [Complex.re_ofReal_mul, Complex.re_sum]
  have hmem : (1 : ℝ) ∈ successValues true N m := ⟨ρ, F, hfeas, hval.symm⟩
  exact le_csSup (x8_S_bdd N hN true m) hmem

lemma x8_rs_mono (N : Superop A B) (hN : IsChannel N) (lam : ℝ)
    (h : 1 ≤ realSuccess true N lam) : 1 ≤ realSuccess false N lam := by
  have hne : (successValues true N lam).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    unfold realSuccess at h
    rw [hc, Real.sSup_empty] at h
    linarith
  refine h.trans (csSup_le_csSup (x8_S_bdd N hN false lam) hne ?_)
  rintro s ⟨ρ, F, ⟨h1, h2, h3, h4, -⟩, rfl⟩
  exact ⟨ρ, F, ⟨h1, h2, h3, h4, fun h => absurd h (by simp)⟩, rfl⟩

theorem x8_main [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    uaZeroMessages N ≤ zeroMessages true N ∧ zeroMessages true N ≤ zeroMessages false N := by
  constructor
  · unfold uaZeroMessages
    by_cases hS : {r | ∃ m : ℕ, 0 < m ∧ (∃ K : UACode A B m, uaCodeSuccess N K = 1) ∧
        r = (m : ℝ)} = ∅
    · rw [hS, Real.sSup_empty]
      unfold zeroMessages
      exact Real.rpow_nonneg (by norm_num) _
    · refine csSup_le (Set.nonempty_iff_ne_empty.2 hS) ?_
      rintro r ⟨m, hm, ⟨K, hK⟩, rfl⟩
      have hmem : log2 m ∈ {r | ∃ lam : ℝ, 1 ≤ lam ∧ 1 - 0 ≤ realSuccess true N lam ∧
          r = log2 lam} := ⟨m, by exact_mod_cast hm, by rw [sub_zero]; exact x8_code N hN hm K hK, rfl⟩
      have h := le_csSup (x8_T_bdd N hN true) hmem
      unfold zeroMessages oneShot
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      calc (m : ℝ) = (2 : ℝ) ^ (Real.logb 2 m) := (Real.rpow_logb (by norm_num) (by norm_num) hm').symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  · unfold zeroMessages
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    unfold oneShot
    by_cases hT : {r | ∃ lam : ℝ, 1 ≤ lam ∧ 1 - 0 ≤ realSuccess true N lam ∧ r = log2 lam} = ∅
    · rw [hT, Real.sSup_empty]
      refine Real.sSup_nonneg ?_
      rintro r ⟨lam, h1, -, rfl⟩
      unfold log2
      exact div_nonneg (Real.log_nonneg h1) (Real.log_nonneg (by norm_num))
    · refine csSup_le_csSup (x8_T_bdd N hN false) (Set.nonempty_iff_ne_empty.2 hT) ?_
      rintro r ⟨lam, h1, h2, rfl⟩
      rw [sub_zero] at h2
      exact ⟨lam, h1, by rw [sub_zero]; exact x8_rs_mono N hN lam h2, rfl⟩

end QAlgorithms.Papers.Independent.Dependency50.P23

end

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P23

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

theorem solution {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : QAlgorithms.Superop A B) (hN : QAlgorithms.IsChannel N) :
    uaZeroMessages N ≤ zeroMessages true N ∧ zeroMessages true N ≤ zeroMessages false N :=
  x8_main N hN

end
