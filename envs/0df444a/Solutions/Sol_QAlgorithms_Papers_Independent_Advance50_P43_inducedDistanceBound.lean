-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P43.inducedDistanceBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:25:20.930995+00:00
-- url     : https://prove2.me/submissions/81ef9ab5-8e50-4154-81fa-cb4415438fb4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P43
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45
  (holevoCapacity resourceCapacity standardEbit)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer diamond)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst privateCapacity)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumCapacity)

open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

variable {A B C Q : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype Q]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Q]

end QAlgorithms.Papers.Independent.Advance50.P43

open QAlgorithms.Papers.Independent.Advance50.P43
open QAlgorithms.Papers.Independent.Information100.P32 (evolution)
open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

section s110f
open scoped MatrixOrder
lemma s110f_unitary_norm_le {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : U ∈ unitary (Matrix n n ℂ)) : ‖U‖ ≤ 1 := by
  rcases isEmpty_or_nonempty n with h | h
  · have : U = 0 := Subsingleton.elim _ _
    simp [this]
  · rw [CStarRing.norm_of_mem_unitary hU]

lemma s110f_diag_entry_le {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (j : n) :
    ‖M j j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j 1)
  have h2 : ‖((EuclideanSpace.equiv n ℂ).symm (M *ᵥ (EuclideanSpace.single j (1:ℂ)))) j‖ ≤
      ‖(EuclideanSpace.equiv n ℂ).symm (M *ᵥ (EuclideanSpace.single j (1:ℂ)))‖ :=
    PiLp.norm_apply_le _ j
  have h3 : ((EuclideanSpace.equiv n ℂ).symm (M *ᵥ (EuclideanSpace.single j (1:ℂ)))) j = M j j := by
    simp
  rw [h3] at h2
  simpa using h2.trans h

lemma s110f_trace_density_le {n : Type} [Fintype n] [DecidableEq n] (G τ : Matrix n n ℂ)
    (hτ : τ.PosSemidef) (htr : τ.trace = 1) : ‖(G * τ).trace‖ ≤ ‖G‖ := by
  have hH := hτ.1
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hUm : U ∈ unitary (Matrix n n ℂ) := hH.eigenvectorUnitary.2
  have hsU : U * star U = 1 := Unitary.mul_star_self_of_mem hUm
  have hUs : star U * U = 1 := Unitary.star_mul_self_of_mem hUm
  have key : (G * τ).trace = ∑ j, (star U * G * U) j j * (hH.eigenvalues j : ℂ) := by
    conv_lhs => rw [hs]
    rw [show G * (U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U)
        = (G * U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) * star U by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
    simp [Matrix.trace, Matrix.mul_diagonal]
  have hev : ∀ j, 0 ≤ hH.eigenvalues j := hτ.eigenvalues_nonneg
  have hsum : ∑ j, hH.eigenvalues j = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h' := this.symm
    exact_mod_cast congrArg Complex.re h'
  rw [key]
  calc ‖∑ j, (star U * G * U) j j * (hH.eigenvalues j : ℂ)‖
      ≤ ∑ j, ‖(star U * G * U) j j * (hH.eigenvalues j : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖G‖ * hH.eigenvalues j := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hev j)]
        apply mul_le_mul_of_nonneg_right _ (hev j)
        calc ‖(star U * G * U) j j‖ ≤ ‖star U * G * U‖ := s110f_diag_entry_le _ j
          _ ≤ ‖star U‖ * ‖G‖ * ‖U‖ := by
              refine (Matrix.l2_opNorm_mul _ _).trans ?_
              gcongr
              exact Matrix.l2_opNorm_mul _ _
          _ ≤ 1 * ‖G‖ * 1 := by
              gcongr
              · exact s110f_unitary_norm_le _ (Unitary.star_mem hUm)
              · exact s110f_unitary_norm_le _ hUm
          _ = ‖G‖ := by ring
    _ = ‖G‖ := by rw [← Finset.mul_sum, hsum, mul_one]

lemma s110f_traceNorm_dual {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ)
    (hW : W.IsHermitian) : ∃ S : Matrix n n ℂ, ‖S‖ ≤ 1 ∧
      QAlgorithms.traceNorm W = (S * W).trace.re := by
  set U : Matrix n n ℂ := (hW.eigenvectorUnitary : Matrix n n ℂ)
  have hUm : U ∈ unitary (Matrix n n ℂ) := hW.eigenvectorUnitary.2
  have hUs : star U * U = 1 := Unitary.star_mul_self_of_mem hUm
  have hsU : U * star U = 1 := Unitary.mul_star_self_of_mem hUm
  let sg : n → ℂ := fun i => if 0 ≤ hW.eigenvalues i then 1 else -1
  refine ⟨U * Matrix.diagonal sg * star U, ?_, ?_⟩
  · calc ‖U * Matrix.diagonal sg * star U‖ ≤ ‖U‖ * ‖Matrix.diagonal sg‖ * ‖star U‖ := by
          refine (Matrix.l2_opNorm_mul _ _).trans ?_
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 * 1 := by
          gcongr
          · exact s110f_unitary_norm_le _ hUm
          · rw [Matrix.l2_opNorm_diagonal]
            refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => ?_
            simp only [sg]; split_ifs <;> simp
          · exact s110f_unitary_norm_le _ (Unitary.star_mem hUm)
      _ = 1 := by ring
  · have hsa : IsSelfAdjoint W := hW.isSelfAdjoint
    have htn : QAlgorithms.traceNorm W = ∑ i, |hW.eigenvalues i| := by
      unfold QAlgorithms.traceNorm
      rw [hW.eq]
      have h1 : W * W = cfc (fun t : ℝ => t * t) W := by
        rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) W, cfc_id' ℝ W]
      rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) W]
      have h2 : cfc (Real.sqrt ∘ fun t : ℝ => t * t) W = cfc (fun t : ℝ => |t|) W := by
        apply cfc_congr
        intro t _
        simp only [Function.comp, ← sq, Real.sqrt_sq_eq_abs]
      rw [h2, hW.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
        Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem hW.eigenvectorUnitary.2, one_mul,
        Matrix.trace_diagonal]
      simp
    have hconj : star U * W * U = Matrix.diagonal (RCLike.ofReal ∘ hW.eigenvalues) := by
      have hs := hW.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at hs
      conv_lhs => rw [hs]
      simp only [U] at hUs ⊢
      rw [show star (hW.eigenvectorUnitary : Matrix n n ℂ) *
          ((hW.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (RCLike.ofReal ∘ hW.eigenvalues) *
            star (hW.eigenvectorUnitary : Matrix n n ℂ)) * (hW.eigenvectorUnitary : Matrix n n ℂ)
          = (star (hW.eigenvectorUnitary : Matrix n n ℂ) * (hW.eigenvectorUnitary : Matrix n n ℂ)) *
            Matrix.diagonal (RCLike.ofReal ∘ hW.eigenvalues) *
            (star (hW.eigenvectorUnitary : Matrix n n ℂ) * (hW.eigenvectorUnitary : Matrix n n ℂ)) by
          simp only [Matrix.mul_assoc], hUs, one_mul, mul_one]
    rw [htn]
    have : (U * Matrix.diagonal sg * star U * W).trace =
        (Matrix.diagonal sg * (star U * W * U)).trace := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [this, hconj, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [sg, Function.comp]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · push Not at h; simp [abs_of_neg h]

lemma s110f_kraus_norm_le {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [Nonempty ι]
    (G : K → Matrix ι ι ℂ) (h : ∑ j, (G j)ᴴ * G j = 1) (k : K) : ‖G k‖ ≤ 1 := by
  have h1 : (G k)ᴴ * G k ≤ 1 := by
    rw [← h]
    exact Finset.single_le_sum (f := fun j => (G j)ᴴ * G j)
      (fun j _ => star_mul_self_nonneg (G j)) (Finset.mem_univ k)
  have h2 : ‖(G k)ᴴ * G k‖ ≤ ‖(1 : Matrix ι ι ℂ)‖ :=
    CStarAlgebra.norm_le_norm_of_nonneg_of_le (star_mul_self_nonneg (G k)) h1
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, norm_one] at h2
  nlinarith [norm_nonneg (G k)]

end s110f


lemma s110f_trace_aux {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (S : Matrix B B ℂ)
    (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    ∑ b, ∑ b', S b b' * (∑ a, ∑ c, M (a, (b', c)) (a, (b, c))) =
      ((Matrix.kronecker (1 : Matrix A A ℂ) (Matrix.kronecker S (1 : Matrix C C ℂ))) * M).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.mul_sum]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, b, 2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

lemma s110f_mapFirst_aux {A R K : Type} [Fintype A] [Fintype R] [Fintype K]
    [DecidableEq A] [DecidableEq R] (F : K → Matrix A A ℂ)
    (τ : Matrix (A × R) (A × R) ℂ) (a a' : A) (r r' : R) :
    (∑ k, F k * (Matrix.of fun i j => τ (i, r) (j, r')) * (F k)ᴴ) a a' =
      (∑ k, Matrix.kronecker (F k) (1 : Matrix R R ℂ) * τ *
        (Matrix.kronecker (F k) (1 : Matrix R R ℂ))ᴴ) (a, r) (a', r') := by
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    apply_ite star, star_zero, star_one]

section s110g
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

lemma s110f_evo_ct {I : Type} [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (t : ℝ) : (evolution H t)ᴴ = evolution H (-t) := by
  unfold evolution
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq]
  congr 2
  simp [Complex.ext_iff]

lemma s110f_evo_mul {I : Type} [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) (t : ℝ) :
    evolution H t * evolution H (-t) = 1 := by
  unfold evolution
  rw [← Matrix.exp_add_of_commute]
  · rw [← add_smul]
    simp
  · exact ((Commute.refl H).smul_left _).smul_right _

lemma s110f_receive_apply (D : LRData A B C) (t : ℝ)
    (Z : Matrix (A × (B × C)) (A × (B × C)) ℂ) (b b' : B) :
    receive D t Z b b' = ∑ a, ∑ c, (evolution D.H t * Z * (evolution D.H t)ᴴ) (a, (b, c)) (a, (b', c)) :=
  rfl

lemma s110f_receive_trace (D : LRData A B C) (t : ℝ) (S : Matrix B B ℂ)
    (Z : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    (S * receive D t Z).trace =
      (onB (A := A) (C := C) S * (evolution D.H t * Z * (evolution D.H t)ᴴ)).trace := by
  rw [onB, ← s110f_trace_aux]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, s110f_receive_apply]

lemma s110f_receive_sub (D : LRData A B C) (t : ℝ)
    (Z1 Z2 : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    receive D t Z1 - receive D t Z2 = receive D t (Z1 - Z2) := by
  ext b b'
  rw [Matrix.sub_apply, s110f_receive_apply, s110f_receive_apply, s110f_receive_apply]
  simp [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

lemma s110f_receive_herm (D : LRData A B C) (t : ℝ)
    (Z : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hZ : Z.IsHermitian) :
    (receive D t Z).IsHermitian := by
  have hM : (evolution D.H t * Z * (evolution D.H t)ᴴ).IsHermitian := by
    show (evolution D.H t * Z * (evolution D.H t)ᴴ)ᴴ = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hZ.eq, Matrix.mul_assoc]
  show (receive D t Z)ᴴ = receive D t Z
  ext b b'
  rw [Matrix.conjTranspose_apply, s110f_receive_apply, s110f_receive_apply]
  generalize evolution D.H t * Z * (evolution D.H t)ᴴ = M at hM
  simp only [star_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro c _
  rw [← Matrix.conjTranspose_apply M, hM.eq]

lemma s110f_mapFirst_kraus {K : ℕ} (F : Fin K → Matrix A A ℂ)
    (τ : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    mapFirst (QAlgorithms.krausApply F) τ =
      ∑ k, onA (B := B) (C := C) (F k) * τ * (onA (B := B) (C := C) (F k))ᴴ := by
  ext ⟨a, r⟩ ⟨a', r'⟩
  exact s110f_mapFirst_aux F τ a a' r r'

lemma s110f_onA_kraus {K : ℕ} (F : Fin K → Matrix A A ℂ) (hF : QAlgorithms.IsKrausFamily F) :
    ∑ k, (onA (B := B) (C := C) (F k))ᴴ * onA (B := B) (C := C) (F k) = 1 := by
  have hk : ∀ k, (onA (B := B) (C := C) (F k))ᴴ * onA (B := B) (C := C) (F k) =
      Matrix.kronecker ((F k)ᴴ * F k) (1 : Matrix (B × C) (B × C) ℂ) := by
    intro k
    simp only [onA]
    unfold Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one]
  simp only [hk]
  have hs : ∑ k, Matrix.kronecker ((F k)ᴴ * F k) (1 : Matrix (B × C) (B × C) ℂ) =
      Matrix.kronecker (∑ k, (F k)ᴴ * F k) (1 : Matrix (B × C) (B × C) ℂ) := by
    ext x y
    simp [Matrix.sum_apply, Matrix.kronecker, Finset.sum_mul]
  rw [hs]
  unfold QAlgorithms.IsKrausFamily at hF
  rw [hF]; exact Matrix.one_kronecker_one

end s110g


section s110c
open scoped MatrixOrder

lemma s110c_kron_one_norm {A R : Type} [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R]
    (F : Matrix A A ℂ) : ‖Matrix.kronecker F (1 : Matrix R R ℂ)‖ ≤ ‖F‖ := by
  let φ : Matrix A A ℂ →⋆ₐ[ℂ] Matrix (A × R) (A × R) ℂ :=
    { toFun := fun X => Matrix.kronecker X 1
      map_one' := Matrix.one_kronecker_one
      map_mul' := fun X Y => by
        show Matrix.kronecker (X * Y) (1 : Matrix R R ℂ) =
          Matrix.kronecker X 1 * Matrix.kronecker Y 1
        unfold Matrix.kronecker
        rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      map_zero' := by
        show Matrix.kronecker (0 : Matrix A A ℂ) (1 : Matrix R R ℂ) = 0
        unfold Matrix.kronecker; exact Matrix.zero_kronecker _
      map_add' := fun X Y => by
        show Matrix.kronecker (X + Y) (1 : Matrix R R ℂ) = Matrix.kronecker X 1 + Matrix.kronecker Y 1
        unfold Matrix.kronecker; exact Matrix.add_kronecker _ _ _
      commutes' := fun c => by
        show Matrix.kronecker (algebraMap ℂ (Matrix A A ℂ) c) (1 : Matrix R R ℂ) = _
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        unfold Matrix.kronecker
        rw [Matrix.smul_kronecker, Matrix.one_kronecker_one]
      map_star' := fun X => by
        show Matrix.kronecker (star X) (1 : Matrix R R ℂ) = star (Matrix.kronecker X 1)
        unfold Matrix.kronecker
        rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one] }
  exact NonUnitalStarAlgHom.norm_apply_le φ F

lemma s110c_psd_norm_le_trace {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP : P.PosSemidef) : ‖P‖ ≤ P.trace.re := by
  have hH := hP.1
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  have hUm : U ∈ unitary (Matrix n n ℂ) := hH.eigenvectorUnitary.2
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hev : ∀ j, 0 ≤ hH.eigenvalues j := hP.eigenvalues_nonneg
  have htr : P.trace.re = ∑ j, hH.eigenvalues j := by
    have := hH.trace_eq_sum_eigenvalues
    rw [this]; simp
  rw [htr]
  calc ‖P‖ = ‖U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U‖ := congrArg _ hs
    _ ≤ ‖U‖ * ‖Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues : n → ℂ)‖ * ‖star U‖ := by
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        gcongr
        exact Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * (∑ j, hH.eigenvalues j) * 1 := by
        have hd : ‖Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues : n → ℂ)‖ ≤
            ∑ j, hH.eigenvalues j := by
          rw [Matrix.l2_opNorm_diagonal]
          refine pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => hev j) |>.mpr fun i => ?_
          simp only [Function.comp, RCLike.norm_ofReal, abs_of_nonneg (hev i)]
          exact Finset.single_le_sum (f := fun j => hH.eigenvalues j) (fun j _ => hev j)
            (Finset.mem_univ i)
        have h1 := s110f_unitary_norm_le _ hUm
        have h2 := s110f_unitary_norm_le _ (Unitary.star_mem hUm)
        have hs0 : 0 ≤ ∑ j, hH.eigenvalues j := Finset.sum_nonneg fun j _ => hev j
        exact mul_le_mul (mul_le_mul h1 hd (norm_nonneg _) zero_le_one) h2 (norm_nonneg _)
          (by positivity)
    _ = ∑ j, hH.eigenvalues j := by ring

lemma s110c_sum_sq_norm {A K : Type} [Fintype A] [DecidableEq A] [Fintype K]
    (F : K → Matrix A A ℂ) (hF : ∑ k, (F k)ᴴ * F k = 1) :
    ∑ k, ‖F k‖ * ‖F k‖ ≤ Fintype.card A := by
  calc ∑ k, ‖F k‖ * ‖F k‖ = ∑ k, ‖(F k)ᴴ * F k‖ := by
        simp [Matrix.l2_opNorm_conjTranspose_mul_self]
    _ ≤ ∑ k, ((F k)ᴴ * F k).trace.re := Finset.sum_le_sum fun k _ =>
        s110c_psd_norm_le_trace _ (Matrix.posSemidef_conjTranspose_mul_self _)
    _ = (∑ k, (F k)ᴴ * F k).trace.re := by rw [Matrix.trace_sum, Complex.re_sum]
    _ = Fintype.card A := by rw [hF]; simp

end s110c

lemma s110c_onA_kraus {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] {K : Type} [Fintype K]
    (F : K → Matrix A A ℂ) (hF : ∑ k, (F k)ᴴ * F k = 1) :
    ∑ k, (onA (B := B) (C := C) (F k))ᴴ * onA (B := B) (C := C) (F k) = 1 := by
  have hk : ∀ k, (onA (B := B) (C := C) (F k))ᴴ * onA (B := B) (C := C) (F k) =
      Matrix.kronecker ((F k)ᴴ * F k) (1 : Matrix (B × C) (B × C) ℂ) := by
    intro k
    simp only [onA]
    unfold Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one]
  simp only [hk]
  have hs : ∑ k, Matrix.kronecker ((F k)ᴴ * F k) (1 : Matrix (B × C) (B × C) ℂ) =
      Matrix.kronecker (∑ k, (F k)ᴴ * F k) (1 : Matrix (B × C) (B × C) ℂ) := by
    ext x y
    simp [Matrix.sum_apply, Matrix.kronecker, Finset.sum_mul]
  rw [hs, hF]; exact Matrix.one_kronecker_one

lemma s110c_main {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (D : LRData A B C) (τ : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (hτ : QAlgorithms.IsDensityMatrix τ) (t : ℝ) {K : Type} [Fintype K] (F : K → Matrix A A ℂ)
    (hF : ∑ k, (F k)ᴴ * F k = 1) :
    QAlgorithms.traceNorm (receive D t (∑ k, onA (B := B) (C := C) (F k) * τ * (onA (B := B) (C := C) (F k))ᴴ) - receive D t τ)
      ≤ Fintype.card A * D.epsilon t := by
  set U := evolution D.H t with hUdef
  have hU1 : U * Uᴴ = 1 := by
    rw [hUdef, s110f_evo_ct _ D.hermitian]; exact s110f_evo_mul _ t
  have hU2 : Uᴴ * U = 1 := by
    rw [hUdef, s110f_evo_ct _ D.hermitian]
    have := s110f_evo_mul D.H (-t)
    rwa [neg_neg] at this
  have hUmem : U ∈ unitary (Matrix (A × (B × C)) (A × (B × C)) ℂ) := ⟨hU2, hU1⟩
  have hUsmem : Uᴴ ∈ unitary (Matrix (A × (B × C)) (A × (B × C)) ℂ) := Unitary.star_mem hUmem
  set G : K → Matrix (A × (B × C)) (A × (B × C)) ℂ := fun k => onA (B := B) (C := C) (F k)
    with hGdef
  have hG : ∑ k, (G k)ᴴ * G k = 1 := s110c_onA_kraus F hF
  rw [s110f_receive_sub]
  set Z := ∑ k, onA (B := B) (C := C) (F k) * τ * (onA (B := B) (C := C) (F k))ᴴ with hZdef
  have hτH : τᴴ = τ := hτ.1.1
  have hZH : (Z - τ).IsHermitian := by
    show (Z - τ)ᴴ = Z - τ
    rw [Matrix.conjTranspose_sub, hτH, hZdef, Matrix.conjTranspose_sum]
    congr 1
    apply Finset.sum_congr rfl; intro k _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hτH, Matrix.mul_assoc]
  obtain ⟨S, hS, htn⟩ := s110f_traceNorm_dual _ (s110f_receive_herm D t _ hZH)
  rw [htn, s110f_receive_trace]
  set Y := Uᴴ * onB (A := A) (C := C) S * U with hYdef
  have e1 : (onB (A := A) (C := C) S * (U * (Z - τ) * Uᴴ)).trace = (Y * (Z - τ)).trace := by
    rw [show onB (A := A) (C := C) S * (U * (Z - τ) * Uᴴ) =
        (onB (A := A) (C := C) S * U * (Z - τ)) * Uᴴ by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [hYdef, Matrix.mul_assoc]
  have e2 : Z - τ = ∑ k, (G k * τ * (G k)ᴴ - τ * ((G k)ᴴ * G k)) := by
    rw [Finset.sum_sub_distrib, ← Matrix.mul_sum, hG, Matrix.mul_one]
  have e3 : ∀ k, (Y * (G k * τ * (G k)ᴴ - τ * ((G k)ᴴ * G k))).trace =
      ((G k)ᴴ * (Y * G k - G k * Y) * τ).trace := by
    intro k
    have a1 : (Y * (G k * τ * (G k)ᴴ)).trace = ((G k)ᴴ * (Y * G k) * τ).trace := by
      rw [show Y * (G k * τ * (G k)ᴴ) = (Y * G k * τ) * (G k)ᴴ by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    have a2 : (Y * (τ * ((G k)ᴴ * G k))).trace = ((G k)ᴴ * (G k * Y) * τ).trace := by
      rw [show Y * (τ * ((G k)ᴴ * G k)) = (Y * τ) * ((G k)ᴴ * G k) by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_sub, Matrix.trace_sub, a1, a2, ← Matrix.trace_sub, ← Matrix.sub_mul,
      ← Matrix.mul_sub]
  have hUU : ∀ X : Matrix (A × (B × C)) (A × (B × C)) ℂ, Uᴴ * (U * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hU2, Matrix.one_mul]
  have e4 : ∀ k, ‖Y * G k - G k * Y‖ ≤ D.epsilon t * ‖F k‖ := by
    intro k
    set G' := U * G k * Uᴴ with hG'
    have hc : Y * G k - G k * Y =
        Uᴴ * (onB (A := A) (C := C) S * G' - G' * onB (A := A) (C := C) S) * U := by
      simp only [hYdef, hG', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hUU]
      rw [hU2, Matrix.mul_one]
    have hb := D.bound (-t) (F k) S
    simp only at hb
    rw [s110f_evo_ct _ D.hermitian, neg_neg, ← hUdef, ← s110f_evo_ct _ D.hermitian, ← hUdef,
      D.even] at hb
    have hε := D.nonnegative t
    rw [hc]
    calc ‖Uᴴ * (onB (A := A) (C := C) S * G' - G' * onB (A := A) (C := C) S) * U‖
        ≤ ‖Uᴴ‖ * ‖onB (A := A) (C := C) S * G' - G' * onB (A := A) (C := C) S‖ * ‖U‖ := by
          refine (Matrix.l2_opNorm_mul _ _).trans ?_
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * (D.epsilon t * ‖F k‖ * ‖S‖) * 1 := by
          gcongr
          · exact s110f_unitary_norm_le _ hUsmem
          · rw [norm_sub_rev]; exact hb
          · exact s110f_unitary_norm_le _ hUmem
      _ ≤ 1 * (D.epsilon t * ‖F k‖ * 1) * 1 := by gcongr
      _ = D.epsilon t * ‖F k‖ := by ring
  rw [e1, e2, Matrix.mul_sum, Matrix.trace_sum]
  simp only [e3]
  calc (∑ k, ((G k)ᴴ * (Y * G k - G k * Y) * τ).trace).re
      ≤ ‖∑ k, ((G k)ᴴ * (Y * G k - G k * Y) * τ).trace‖ := Complex.re_le_norm _
    _ ≤ ∑ k, ‖((G k)ᴴ * (Y * G k - G k * Y) * τ).trace‖ := norm_sum_le _ _
    _ ≤ ∑ k, D.epsilon t * (‖F k‖ * ‖F k‖) := by
        apply Finset.sum_le_sum; intro k _
        refine (s110f_trace_density_le _ τ hτ.1 hτ.2).trans ?_
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        rw [Matrix.l2_opNorm_conjTranspose]
        have hGk : ‖G k‖ ≤ ‖F k‖ := s110c_kron_one_norm (F k)
        calc ‖G k‖ * ‖Y * G k - G k * Y‖ ≤ ‖F k‖ * (D.epsilon t * ‖F k‖) :=
              mul_le_mul hGk (e4 k) (norm_nonneg _) (norm_nonneg _)
          _ = D.epsilon t * (‖F k‖ * ‖F k‖) := by ring
    _ = D.epsilon t * ∑ k, ‖F k‖ * ‖F k‖ := by rw [Finset.mul_sum]
    _ ≤ D.epsilon t * Fintype.card A :=
        mul_le_mul_of_nonneg_left (s110c_sum_sq_norm F hF) (D.nonnegative t)
    _ = Fintype.card A * D.epsilon t := by ring


lemma s110c_pt {A Q : Type} [Fintype A] [Fintype Q] {K : Type} [Fintype K]
    (e e' : Q × A → ℂ) (Bm : Matrix K Q ℂ) (T : A → A → ℂ) :
    ∑ k, ∑ a, ∑ a', (∑ q', e (q', a) * star (Bm k q')) * T a a' *
        star (∑ q'', e' (q'', a') * star (Bm k q'')) =
      ∑ u : Q × A, ∑ v : Q × A, e u * ((Bmᴴ * Bm) u.1 v.1 * T u.2 v.2) * star (e' v) := by
  simp only [Fintype.sum_prod_type, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum,
    star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun x => (x.2.2.2.2, x.2.1, x.2.2.2.1, x.2.2.1, x.1)
      invFun := fun y => (y.2.2.2.2, y.2.1, y.2.2.2.1, y.2.2.1, y.1)
      left_inv := fun x => rfl
      right_inv := fun y => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]
  ring

def s110c_F {A Q : Type} [Fintype Q] {m : ℕ} (Ek : Fin m → Matrix (Q × A) (Q × A) ℂ)
    (Bm : Matrix Q Q ℂ) : Fin m × Q × Q → Matrix A A ℂ :=
  fun p a' a => ∑ q', Ek p.1 (p.2.1, a') (q', a) * star (Bm p.2.2 q')

lemma s110c_R {A R : Type} [Fintype A] [Fintype R] [DecidableEq R]
    (F : Matrix A A ℂ) (τ : Matrix (A × R) (A × R) ℂ) (x1 y1 : A) (x2 y2 : R) :
    (Matrix.kronecker F (1 : Matrix R R ℂ) * τ * (Matrix.kronecker F (1 : Matrix R R ℂ))ᴴ) (x1, x2) (y1, y2) =
      ∑ a, ∑ a', F x1 a * τ (a, x2) (a', y2) * star (F y1 a') := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, apply_ite star, star_one, star_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma s110c_L {A B C Q : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Q]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Q] {m : ℕ}
    (Ek : Fin m → Matrix (Q × A) (Q × A) ℂ) (ρ : Matrix Q Q ℂ)
    (τ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (x1 y1 : A) (x2 y2 : B × C) :
    encodedNetwork (Q := Q) τ (QAlgorithms.krausApply Ek) ρ (x1, x2) (y1, y2) =
      ∑ j, ∑ q, ∑ u : Q × A, ∑ v : Q × A,
        Ek j (q, x1) u * (ρ u.1 v.1 * τ (u.2, x2) (v.2, y2)) * star (Ek j (q, y1) v) := by
  simp only [encodedNetwork, QAlgorithms.krausApply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro q _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v _
  erw [Matrix.mul_apply]; rw [Finset.sum_mul]


lemma s110c_enc {A B C Q : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Q]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Q] {m : ℕ}
    (Ek : Fin m → Matrix (Q × A) (Q × A) ℂ) (Bm : Matrix Q Q ℂ)
    (τ : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    encodedNetwork (Q := Q) τ (QAlgorithms.krausApply Ek) (Bmᴴ * Bm) =
      ∑ p, onA (B := B) (C := C) (s110c_F Ek Bm p) * τ * (onA (B := B) (C := C) (s110c_F Ek Bm p))ᴴ := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  rw [s110c_L, Matrix.sum_apply]
  simp only [onA, s110c_R, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro q _
  have := s110c_pt (fun u => Ek j (q, x1) u) (fun v => Ek j (q, y1) v) Bm
    (fun a a' => τ (a, x2) (a', y2))
  simp only [Fintype.sum_prod_type] at this
  rw [← this]; rfl

lemma s110c_kraus {A Q : Type} [Fintype A] [Fintype Q] [DecidableEq A] [DecidableEq Q] {m : ℕ}
    (Ek : Fin m → Matrix (Q × A) (Q × A) ℂ) (hE : ∑ j, (Ek j)ᴴ * Ek j = 1) (Bm : Matrix Q Q ℂ)
    (htr : (Bmᴴ * Bm).trace = 1) :
    ∑ p, (s110c_F Ek Bm p)ᴴ * s110c_F Ek Bm p = 1 := by
  ext a b
  have h1 : ∀ u v : Q × A, ∑ j, ∑ q, ∑ a', star (Ek j (q, a') u) * Ek j (q, a') v =
      (1 : Matrix (Q × A) (Q × A) ℂ) u v := by
    intro u v
    rw [← hE]
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, s110c_F,
    Fintype.sum_prod_type, star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
  have h2 : ∀ q' q'' : Q, ∑ k, Bm k q' * star (Bm k q'') = (Bmᴴ * Bm) q'' q' := by
    intro q' q''
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
  have key : ∑ x : Fin m, ∑ x_1 : Q, ∑ x_2 : Q, ∑ x_3 : A, ∑ x_4 : Q, ∑ x_5 : Q,
      star (Ek x (x_1, x_3) (x_5, a)) * Bm x_2 x_5 * (Ek x (x_1, x_3) (x_4, b) * star (Bm x_2 x_4)) =
      ∑ q' : Q, ∑ q'' : Q, (∑ k, Bm k q' * star (Bm k q'')) *
        (∑ j, ∑ q, ∑ a', star (Ek j (q, a') (q', a)) * Ek j (q, a') (q'', b)) := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv
      { toFun := fun x => (x.2.2.2.2.2, x.2.2.2.2.1, (x.1, x.2.1, x.2.2.2.1), x.2.2.1)
        invFun := fun y => (y.2.2.1.1, y.2.2.1.2.1, y.2.2.2, y.2.2.1.2.2, y.2.1, y.1)
        left_inv := fun x => rfl
        right_inv := fun y => rfl } _ _ (fun x => ?_)
    simp only [Equiv.coe_fn_mk]
    ring
  rw [key]
  simp only [h1, h2, Matrix.one_apply, Prod.mk.injEq]
  by_cases hab : a = b
  · simp only [hab, and_true, if_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ]
    rw [← htr, Matrix.trace]; rfl
  · simp [hab]

section s110fin
open scoped MatrixOrder

theorem solution {A B C Q : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Q]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Q]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty Q]
    (D : LRData A B C)
    (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ) (htau : QAlgorithms.IsDensityMatrix tau)
    (E : QAlgorithms.Superop (Q × A) (Q × A)) (hE : QAlgorithms.IsChannel E) (t : ℝ) :
    stateDistance (snc D tau E t) (comparisonZero D tau t) ≤
      (Fintype.card A : ℝ) ^ 2 * D.epsilon t := by
  obtain ⟨m, Ek, hK, hEq⟩ := hE
  have hEfun : E = QAlgorithms.krausApply Ek := funext hEq
  subst hEfun
  have hbound : ∀ ρ : Matrix Q Q ℂ, QAlgorithms.IsDensityMatrix ρ →
      QAlgorithms.traceNorm (snc D tau (QAlgorithms.krausApply Ek) t ρ -
        comparisonZero D tau t ρ) ≤ (Fintype.card A : ℝ) * D.epsilon t := by
    intro ρ hρ
    obtain ⟨Bm, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      (Matrix.nonneg_iff_posSemidef.mpr hρ.1)
    have hB' : ρ = Bmᴴ * Bm := hB
    have htr : (Bmᴴ * Bm).trace = 1 := hB' ▸ hρ.2
    have hcz : comparisonZero D tau t ρ = receive D t tau := by
      show ρ.trace • receive D t tau = receive D t tau
      rw [hρ.2, one_smul]
    rw [hcz]
    show QAlgorithms.traceNorm (receive D t (encodedNetwork tau (QAlgorithms.krausApply Ek) ρ) -
      receive D t tau) ≤ _
    rw [hB', s110c_enc]
    exact s110c_main D tau htau t _ (s110c_kraus Ek hK Bm htr)
  have hA1 : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hε := D.nonnegative t
  apply csSup_le
  · obtain ⟨i0⟩ := (inferInstance : Nonempty Q)
    refine ⟨_, Matrix.diagonal (fun i => if i = i0 then (1 : ℂ) else 0), ⟨?_, ?_⟩, rfl⟩
    · rw [Matrix.posSemidef_diagonal_iff]
      intro i; split_ifs <;> simp
    · simp [Matrix.trace_diagonal]
  · rintro v ⟨ρ, hρ, rfl⟩
    calc _ ≤ (Fintype.card A : ℝ) * D.epsilon t := hbound ρ hρ
      _ ≤ (Fintype.card A : ℝ) ^ 2 * D.epsilon t := by
        apply mul_le_mul_of_nonneg_right _ hε
        nlinarith

end s110fin
