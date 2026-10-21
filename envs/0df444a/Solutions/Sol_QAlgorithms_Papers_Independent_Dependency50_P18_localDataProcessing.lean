-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.localDataProcessing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T06:48:03.870029+00:00
-- url     : https://prove2.me/submissions/87c13513-5573-438d-8219-b640aa7fc868

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

namespace G55L

open QAlgorithms

lemma kraus_single {ι κ K : Type} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (i j : ι) (a b : κ) :
    krausApply E (Matrix.single i j 1) a b = ∑ p, E p a i * conj (E p b j) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [ite_and, Finset.sum_ite_eq]

lemma tensor_kraus {A B C E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E]
    [DecidableEq A] [DecidableEq B] {m n : ℕ}
    (N : Superop A C) (M : Superop B E) (K : Fin m → Matrix C A ℂ) (L : Fin n → Matrix E B ℂ)
    (hN : ∀ ρ, N ρ = krausApply K ρ) (hM : ∀ ρ, M ρ = krausApply L ρ) (X : Matrix (A × B) (A × B) ℂ) :
    QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M X =
      krausApply (fun pq : Fin m × Fin n => Matrix.kronecker (K pq.1) (L pq.2)) X := by
  ext a b
  simp only [QAlgorithms.Papers.Independent.Information100.P62.tensorChannel, hN, hM, kraus_single]
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.of_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, star_mul', RCLike.star_def]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun x => (x.2.2.2.2.2, x.2.2.2.2.1, x.2.1, x.2.2.2.1, x.1, x.2.2.1)
      invFun := fun y => (y.2.2.2.2.1, y.2.2.1, y.2.2.2.2.2, y.2.2.2.1, y.2.1, y.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]
  ring


open QAlgorithms.Papers.Independent.Information100.P04 (gamma)

lemma kraus_psd {ι κ K : Type} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) {X : Matrix ι ι ℂ} (hX : X.PosSemidef) : (krausApply E X).PosSemidef := by
  unfold krausApply
  classical
  induction (Finset.univ : Finset K) using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (hX.mul_mul_conjTranspose_same _).add ih

lemma kraus_herm {ι κ K : Type} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) {X : Matrix ι ι ℂ} (hX : X.IsHermitian) : (krausApply E X).IsHermitian := by
  unfold krausApply Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX.eq,
    Matrix.mul_assoc]

lemma kraus_add {ι κ K : Type} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (X Y : Matrix ι ι ℂ) : krausApply E (X + Y) = krausApply E X + krausApply E Y := by
  simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma kraus_sub {ι κ K : Type} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (X Y : Matrix ι ι ℂ) : krausApply E (X - Y) = krausApply E X - krausApply E Y := by
  simp [krausApply, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

lemma kraus_trace {ι κ K : Type} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : IsKrausFamily E) (X : Matrix ι ι ℂ) :
    (krausApply E X).trace = X.trace := by
  unfold krausApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) X]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hE, Matrix.one_mul]

lemma kraus_kron {A B C E K L : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype K] [Fintype L]
    (P : K → Matrix C A ℂ) (Q : L → Matrix E B ℂ) (k : Matrix A A ℂ) (l : Matrix B B ℂ) :
    krausApply (fun pq : K × L => Matrix.kronecker (P pq.1) (Q pq.2)) (Matrix.kronecker k l) =
      Matrix.kronecker (krausApply P k) (krausApply Q l) := by
  unfold krausApply
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  rw [Fintype.sum_prod_type]
  ext a b
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul_sum]

lemma gamma_kraus {A B C E K L : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype K] [Fintype L]
    (P : K → Matrix C A ℂ) (Q : L → Matrix E B ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    gamma (krausApply (fun pq : K × L => Matrix.kronecker (P pq.1) (Q pq.2)) X) =
      krausApply (fun pq : K × L => Matrix.kronecker (P pq.1) ((Q pq.2).map conj)) (gamma X) := by
  ext a b
  simp only [gamma, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.map_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, star_mul', RCLike.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun x => (x.1, x.2.2.2, x.2.2.1, x.2.1)
      invFun := fun y => (y.1, y.2.2.2, y.2.2.1, y.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]
  ring


lemma sum_kron {A B C E K L : Type} [Fintype K] [Fintype L]
    (f : K → Matrix A C ℂ) (g : L → Matrix B E ℂ) :
    ∑ pq : K × L, Matrix.kronecker (f pq.1) (g pq.2) = Matrix.kronecker (∑ p, f p) (∑ q, g q) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]

lemma tensor_channel {A B C E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E]
    [DecidableEq A] [DecidableEq B]
    (N : Superop A C) (M : Superop B E) (hN : IsChannel N) (hM : IsChannel M) :
    IsChannel (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M) := by
  obtain ⟨m, K, hK, hNK⟩ := hN
  obtain ⟨n, L, hL, hML⟩ := hM
  let e := (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))
  refine ⟨m * n, fun j => Matrix.kronecker (K (e.symm j).1) (L (e.symm j).2), ?_, fun X => ?_⟩
  · unfold IsKrausFamily
    rw [Fintype.sum_equiv e.symm _ (fun pq : Fin m × Fin n =>
      (Matrix.kronecker (K pq.1) (L pq.2))ᴴ * Matrix.kronecker (K pq.1) (L pq.2)) (fun _ => rfl)]
    simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
    rw [show (∑ pq : Fin m × Fin n, Matrix.kroneckerMap (· * ·) ((K pq.1)ᴴ * K pq.1) ((L pq.2)ᴴ * L pq.2))
      = Matrix.kroneckerMap (· * ·) (∑ p, (K p)ᴴ * K p) (∑ q, (L q)ᴴ * L q) from
      sum_kron (fun p => (K p)ᴴ * K p) (fun q => (L q)ᴴ * L q)]
    unfold IsKrausFamily at hK hL
    rw [hK, hL, Matrix.one_kronecker_one]
  · rw [tensor_kraus N M K L hNK hML X]
    unfold krausApply
    exact (Fintype.sum_equiv e.symm (fun j => Matrix.kronecker (K (e.symm j).1) (L (e.symm j).2) * X *
      (Matrix.kronecker (K (e.symm j).1) (L (e.symm j).2))ᴴ) _ (fun _ => rfl)).symm


lemma feas_push {A B C E K L : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype K] [Fintype L]
    (P : K → Matrix C A ℂ) (Q : L → Matrix E B ℂ)
    (s : Matrix (A × B) (A × B) ℂ) (k : Matrix A A ℂ) (l : Matrix B B ℂ)
    (v : Matrix (A × B) (A × B) ℂ) (h : GammaFeasible s k l v) :
    GammaFeasible (krausApply (fun pq : K × L => Matrix.kronecker (P pq.1) (Q pq.2)) s)
      (krausApply P k) (krausApply Q l)
      (krausApply (fun pq : K × L => Matrix.kronecker (P pq.1) (Q pq.2)) v) := by
  obtain ⟨hk, hl, hv, h1, h2, h3, h4⟩ := h
  refine ⟨kraus_herm _ hk, kraus_herm _ hl, kraus_herm _ hv, ?_, ?_, ?_, ?_⟩
  · rw [← kraus_add, gamma_kraus]; exact kraus_psd _ h1
  · rw [← kraus_sub, gamma_kraus]; exact kraus_psd _ h2
  · rw [← kraus_kron, ← kraus_add]; exact kraus_psd _ h3
  · rw [← kraus_kron, ← kraus_sub]; exact kraus_psd _ h4

lemma gauge_le {A B C E K L : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype K] [Fintype L]
    [DecidableEq A] [DecidableEq B]
    (P : K → Matrix C A ℂ) (Q : L → Matrix E B ℂ) (hP : IsKrausFamily P) (hQ : IsKrausFamily Q)
    (s : Matrix (A × B) (A × B) ℂ) :
    correlationGauge (krausApply (fun pq : K × L => Matrix.kronecker (P pq.1) (Q pq.2)) s) ≤
      correlationGauge s := by
  apply sInf_le_sInf
  rintro r ⟨k, l, v, hf, rfl⟩
  refine ⟨krausApply P k, krausApply Q l, _, feas_push P Q s k l v hf, ?_⟩
  rw [show (k.kronecker l).trace = k.trace * l.trace from Matrix.trace_kronecker k l,
    show ((krausApply P k).kronecker (krausApply Q l)).trace = (krausApply P k).trace * (krausApply Q l).trace
      from Matrix.trace_kronecker _ _, kraus_trace P hP, kraus_trace Q hQ]

lemma gauge_nonneg {A B : Type} [Fintype A] [Fintype B] (s : Matrix (A × B) (A × B) ℂ) :
    0 ≤ correlationGauge s := by
  apply le_sInf
  rintro r ⟨k, l, v, hf, rfl⟩
  obtain ⟨-, -, -, -, -, h3, h4⟩ := hf
  have t3 := (Complex.nonneg_iff.mp h3.trace_nonneg).1
  have t4 := (Complex.nonneg_iff.mp h4.trace_nonneg).1
  rw [Matrix.trace_add, Complex.add_re] at t3
  rw [Matrix.trace_sub, Complex.sub_re] at t4
  have : (0 : ℝ) ≤ (Matrix.kronecker k l).trace.re := by linarith
  exact_mod_cast this

lemma logBits_mono {x y : EReal} (hx : 0 ≤ x) (hxy : x ≤ y) : logBits x ≤ logBits y := by
  unfold logBits
  by_cases h0 : x = 0
  · simp [h0]
  by_cases hyt : y = ⊤
  · simp [hyt]
  have hxt : x ≠ ⊤ := fun h => hyt (top_le_iff.mp (h ▸ hxy))
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
  have hy0 : y ≠ 0 := fun h => by rw [h] at hxy; exact absurd (lt_of_lt_of_le hpos hxy) (lt_irrefl 0)
  have hxb : x ≠ ⊥ := fun h => by rw [h] at hpos; exact absurd hpos (not_lt.mpr bot_le)
  have hyb : y ≠ ⊥ := fun h => by rw [h] at hxy; exact hxb (le_bot_iff.mp hxy)
  simp only [h0, hxt, hxb, hy0, hyt, hyb, if_false]
  have hx' : 0 < x.toReal := EReal.toReal_pos hpos hxt
  have hle : x.toReal ≤ y.toReal := EReal.toReal_le_toReal hxy hxb hyt
  exact_mod_cast Real.logb_le_logb_of_le (by norm_num) hx' hle

end G55L

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

open G55L in
theorem solution (D : Divergence) (hD : IsGeneralizedDivergence D)
    (N : QAlgorithms.Superop A C) (M : QAlgorithms.Superop B E)
    (hN : QAlgorithms.IsChannel N) (hM : QAlgorithms.IsChannel M) :
    (∀ sigma : Matrix (A × B) (A × B) ℂ, sigma.PosSemidef →
      cGamma (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M sigma) ≤ cGamma sigma) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M rho) ≤ capitalGamma D rho) := by
  have hch := tensor_channel N M hN hM
  obtain ⟨m, K, hK, hNK⟩ := hN
  obtain ⟨n, L, hL, hML⟩ := hM
  have ht := tensor_kraus N M K L hNK hML
  refine ⟨fun sigma _ => ?_, fun rho hrho => ?_⟩
  · unfold cGamma
    rw [ht]
    exact logBits_mono (gauge_nonneg _) (gauge_le K L hK hL sigma)
  · unfold capitalGamma
    apply le_sInf
    rintro r ⟨sigma, hs, hg, rfl⟩
    refine (sInf_le (show D (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M rho)
      (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M sigma) ∈
      {r | ∃ τ : Matrix (C × E) (C × E) ℂ, τ.PosSemidef ∧ correlationGauge τ ≤ 1 ∧
        r = D (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M rho) τ} from
      ⟨QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M sigma, ?_, ?_, rfl⟩)).trans ?_
    · rw [ht]; exact kraus_psd _ hs
    · rw [ht]; exact (gauge_le K L hK hL sigma).trans hg
    · exact hD.dataProcessing rho sigma _ hrho hs hch
