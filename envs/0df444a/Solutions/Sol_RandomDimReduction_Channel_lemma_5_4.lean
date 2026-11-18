-- Prove2me | solution 1 for RandomDimReduction.Channel.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T19:04:28.950795+00:00
-- url     : https://prove2.me/submissions/5832623f-df05-4b2a-bdc5-04768d743227

import Definitions.Def_RandomDimReduction_Channel_Tensor
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Matrix.Spectrum
import Theorems.Thm_KWSpectrum_Estimator_eq_2_4_projections
import Definitions.Def_RandomDimReduction_Channel_Schur
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Logic.Equiv.Fintype
import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Theorems.Thm_RandomDimReduction_Channel_spechtModel_properties
import Theorems.Thm_RandomDimReduction_Channel_lemma_B_1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

-- TensorAlgebra
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma tensor_mul {a b c : Type} [Fintype b] (n : ℕ)
    (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    tensor n (A * B) = tensor n A * tensor n B := by
  ext i j
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum fun t z => A (i t) z * B z (j t)

lemma tensor_conjTranspose {a b : Type} (n : ℕ) (A : Matrix a b ℂ) :
    tensor n Aᴴ = (tensor n A)ᴴ := by
  ext i j
  simp [tensor, Matrix.conjTranspose_apply]

lemma tensor_one {a : Type} [DecidableEq a] (n : ℕ) :
    tensor n (1 : Op a) = 1 := by
  ext i j
  simp only [tensor, Matrix.one_apply, Finset.prod_boole]
  simp [funext_iff]

lemma tensor_isometry {a b : Type} [Fintype a] [Fintype b] [DecidableEq b] (n : ℕ)
    (A : Matrix a b ℂ) (h : Aᴴ * A = 1) :
    (tensor n A)ᴴ * tensor n A = 1 := by
  rw [← tensor_conjTranspose, ← tensor_mul, h, tensor_one]

end RandomDimReduction.Channel

-- PolynomialUnitary
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma unitPhases_infinite : Set.Infinite {z : ℂ | star z * z = 1} := by
  have hi : (Set.Icc (0 : ℝ) Real.pi).Infinite := Set.Icc_infinite Real.pi_pos
  have he := hi.image (Circle.exp_injOn_Icc (by linarith [Real.pi_pos]))
  have hc := he.image Circle.coe_injective.injOn
  apply hc.mono
  rintro z ⟨u, ⟨r, hr, rfl⟩, rfl⟩
  change star (Circle.exp r : ℂ) * (Circle.exp r : ℂ) = 1
  simp [Complex.star_def, Complex.conj_mul', Circle.norm_coe]

lemma eval_substitute {σ τ : Type} (p : MvPolynomial σ ℂ)
    (f : σ → MvPolynomial τ ℂ) (z : τ → ℂ) :
    MvPolynomial.eval z (MvPolynomial.eval₂Hom MvPolynomial.C f p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval z (f i)) p :=
  (MvPolynomial.eval_assoc f z p).symm

def conjugateDiagonalPoly {d : ℕ} (V : Op (Fin d)) (ij : Fin d × Fin d) :
    MvPolynomial (Fin d) ℂ :=
  ∑ r, MvPolynomial.C (V ij.1 r * star (V ij.2 r)) * MvPolynomial.X r

lemma eval_conjugateDiagonalPoly {d : ℕ} (V : Op (Fin d)) (z : Fin d → ℂ)
    (ij : Fin d × Fin d) :
    MvPolynomial.eval z (conjugateDiagonalPoly V ij) =
      (V * Matrix.diagonal z * Vᴴ) ij.1 ij.2 := by
  simp [conjugateDiagonalPoly, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, mul_assoc, mul_comm, mul_left_comm]

lemma diagonal_unitary {d : ℕ} (z : Fin d → ℂ) (hz : ∀ i, star (z i) * z i = 1) :
    Matrix.diagonal z ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  have he : (fun i => star (z i) * z i) = fun _ => (1 : ℂ) := funext hz
  simpa only [Pi.star_apply, he, Matrix.diagonal_one]

lemma polynomial_zero_of_unitary_zero {d : ℕ} (p : MvPolynomial (Fin d × Fin d) ℂ)
    (hp : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      MvPolynomial.eval (fun ij => U ij.1 ij.2) p = 0) :
    ∀ A : Op (Fin d), MvPolynomial.eval (fun ij => A ij.1 ij.2) p = 0 := by
  have hHerm (A : Op (Fin d)) (hA : A.IsHermitian) :
      MvPolynomial.eval (fun ij => A ij.1 ij.2) p = 0 := by
    let V : Matrix.unitaryGroup (Fin d) ℂ := hA.eigenvectorUnitary
    let q : MvPolynomial (Fin d) ℂ :=
      MvPolynomial.eval₂Hom MvPolynomial.C (conjugateDiagonalPoly (V : Op (Fin d))) p
    have hq : q = 0 := by
      apply MvPolynomial.funext_set (fun _ => {z : ℂ | star z * z = 1})
        (fun _ => unitPhases_infinite)
      intro z hz
      have hu := diagonal_unitary z (fun i => hz i (Set.mem_univ i))
      let D : Matrix.unitaryGroup (Fin d) ℂ := ⟨Matrix.diagonal z, hu⟩
      have hh := hp (V * D * star V)
      simpa only [q, eval_substitute, MvPolynomial.eval_C,
        eval_conjugateDiagonalPoly, Submonoid.coe_mul,
        Unitary.coe_star, Matrix.star_eq_conjTranspose, map_zero, D] using hh
    have hs := congrArg (MvPolynomial.eval (fun i => (hA.eigenvalues i : ℂ))) hq
    simp only [q, eval_substitute, MvPolynomial.eval_C,
      eval_conjugateDiagonalPoly, map_zero] at hs
    apply Eq.trans _ hs
    apply congrArg (fun z => MvPolynomial.eval z p)
    funext ij
    have hspectral := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def, V] using
      congrArg (fun B : Op (Fin d) => B ij.1 ij.2) hspectral
  intro A
  let H : Op (Fin d) := (2 : ℂ)⁻¹ • (A + Aᴴ)
  let K : Op (Fin d) := (2 * Complex.I)⁻¹ • (A - Aᴴ)
  have hH : H.IsHermitian := by
    exact (Matrix.isHermitian_add_transpose_self A).smul (by simp)
  have hK : K.IsHermitian := by
    change Kᴴ = K
    simp only [K, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, star_inv₀, star_mul, Complex.star_def,
      map_ofNat, Complex.conj_I]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    field_simp
    ring
  let q : MvPolynomial Unit ℂ := MvPolynomial.eval₂Hom MvPolynomial.C
    (fun ij => MvPolynomial.C (H ij.1 ij.2) +
      MvPolynomial.X () * MvPolynomial.C (K ij.1 ij.2)) p
  have hq : q = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range (Complex.ofReal : ℝ → ℂ))
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro z hz
    obtain ⟨r, hr⟩ := hz () (Set.mem_univ ())
    have he := hHerm (H + (r : ℂ) • K) (hH.add (hK.smul (show star (r : ℂ) = (r : ℂ) from Complex.conj_ofReal r)))
    simpa only [q, eval_substitute, MvPolynomial.eval_C,
      map_add, map_mul, MvPolynomial.eval_X, ← hr, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, map_zero] using he
  have he := congrArg (MvPolynomial.eval (fun _ => Complex.I)) hq
  simp only [q, eval_substitute, MvPolynomial.eval_C,
    map_add, map_mul, MvPolynomial.eval_X, map_zero] at he
  apply Eq.trans _ he
  apply congrArg (fun z => MvPolynomial.eval z p)
  funext ij
  dsimp [H, K]
  field_simp
  ring

end RandomDimReduction.Channel

-- PermutationCharacters
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma perm_entry_reversed (d n : ℕ) (g : Equiv.Perm (Fin n)) (y x : Word n d) :
    QAlgorithms.Schur.tensorPermutation d n g y x = if x = y ∘ g then 1 else 0 := by
  simp only [QAlgorithms.Schur.tensorPermutation, Matrix.of_apply]
  have h : (y = x ∘ g.symm) ↔ (x = y ∘ g) := by
    constructor <;> rintro rfl <;> funext i <;> simp
  by_cases hx : x = y ∘ g
  · rw [if_pos (h.mpr hx), if_pos hx]
  · rw [if_neg (fun h' => hx (h.mp h')), if_neg hx]

lemma tensorPermutation_mul (d n : ℕ) (g h : Equiv.Perm (Fin n)) :
    QAlgorithms.Schur.tensorPermutation d n g * QAlgorithms.Schur.tensorPermutation d n h =
      QAlgorithms.Schur.tensorPermutation d n (g * h) := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single (y ∘ g)]
  · rw [perm_entry_reversed, perm_entry_reversed, perm_entry_reversed, if_pos rfl,
      one_mul, Equiv.Perm.coe_mul]
    rfl
  · intro b _ hb
    rw [perm_entry_reversed, if_neg (fun e => hb e), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma perm_entry_identity (n : ℕ) (g : Equiv.Perm (Fin n)) :
    QAlgorithms.Schur.tensorPermutation n n g id id = if g = 1 then 1 else 0 := by
  rw [perm_entry_reversed]
  have he : ((id : Fin n → Fin n) = id ∘ g) ↔ g = 1 := by
    constructor
    · intro h
      apply Equiv.ext
      intro i
      exact (congrFun h i).symm
    · rintro rfl
      rfl
  simp only [he]

lemma isotypic_identity_entry (n : ℕ) (lam : Shape n) :
    QAlgorithms.Schur.isotypicProjector lam id id =
      ((spechtDim lam : ℂ) / (n.factorial : ℂ)) * QAlgorithms.Schur.spechtCharacter lam 1 := by
  simp [QAlgorithms.Schur.isotypicProjector, Matrix.smul_apply, Matrix.sum_apply,
    perm_entry_identity, mul_ite, spechtDim]

lemma isotypic_product_identity_entry (n : ℕ) (lam mu : Shape n) :
    (QAlgorithms.Schur.isotypicProjector lam * QAlgorithms.Schur.isotypicProjector mu) id id =
      (((spechtDim lam : ℂ) / (n.factorial : ℂ)) * ((spechtDim mu : ℂ) / (n.factorial : ℂ))) *
        ∑ g : Equiv.Perm (Fin n),
          QAlgorithms.Schur.spechtCharacter lam g * QAlgorithms.Schur.spechtCharacter mu g⁻¹ := by
  simp only [QAlgorithms.Schur.isotypicProjector, smul_mul_smul_comm,
    Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    tensorPermutation_mul, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    perm_entry_identity]
  rw [Finset.sum_comm]
  simp_rw [mul_eq_one_iff_eq_inv, mul_ite, mul_zero, mul_one]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, inv_inv]
  simp only [← Finset.mul_sum, spechtDim]

end RandomDimReduction.Channel

-- SchurPermutations
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma tensorPermutation_one (n d : ℕ) : QAlgorithms.Schur.tensorPermutation d n 1 = 1 := by
  ext i j
  rfl

lemma tensorPermutation_adjoint (n d : ℕ) (π : Equiv.Perm (Fin n)) :
    (QAlgorithms.Schur.tensorPermutation d n π)ᴴ = QAlgorithms.Schur.tensorPermutation d n π⁻¹ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, perm_entry_reversed]
  have he : (i = j ∘ π) ↔ j = i ∘ (π⁻¹ : Equiv.Perm (Fin n)) := by
    constructor <;> rintro rfl <;> funext t <;> simp
  simp [he]

def tensorPermutation_rep (n d : ℕ) :
    Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Word n d) ℂ where
  toFun π := ⟨QAlgorithms.Schur.tensorPermutation d n π, by
    constructor
    · change (QAlgorithms.Schur.tensorPermutation d n π)ᴴ * QAlgorithms.Schur.tensorPermutation d n π = 1
      rw [tensorPermutation_adjoint, tensorPermutation_mul, inv_mul_cancel, tensorPermutation_one]
    · change QAlgorithms.Schur.tensorPermutation d n π * (QAlgorithms.Schur.tensorPermutation d n π)ᴴ = 1
      rw [tensorPermutation_adjoint, tensorPermutation_mul, mul_inv_cancel, tensorPermutation_one]⟩
  map_one' := by apply Subtype.ext; exact tensorPermutation_one n d
  map_mul' π σ := by apply Subtype.ext; exact (tensorPermutation_mul d n π σ).symm

lemma tensor_perm_natural (n k d : ℕ) (W : Matrix (Fin d) (Fin k) ℂ)
    (π : Equiv.Perm (Fin n)) :
    tensor n W * QAlgorithms.Schur.tensorPermutation k n π =
      QAlgorithms.Schur.tensorPermutation d n π * tensor n W := by
  have he (i j : Word n d) : i = j ∘ π.symm ↔ j = i ∘ π := by
    constructor <;> intro h <;> subst_vars <;> funext t <;> simp
  ext i j
  simp only [Matrix.mul_apply, QAlgorithms.Schur.tensorPermutation, Matrix.of_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [he]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [tensor, Function.comp_apply]
  simpa using (Equiv.prod_comp π (fun t => W (i t) (j (π.symm t)))).symm

lemma schur_nu_one {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (hsp : ∀ lam : Shape n, 0 < spechtDim lam) (lam : Shape n) : S.nu lam 1 = 1 := by
  haveI : NeZero (spechtDim lam) := ⟨Nat.ne_of_gt (hsp lam)⟩
  have h := S.intertwines 1 1
  rw [tensorPermutation_one, tensor_one, Matrix.mul_one, Matrix.mul_one, S.left_unitary] at h
  ext i j
  have he := congrArg (fun A : Op (SchurIndex n d) => A ⟨lam, (0,i)⟩ ⟨lam, (0,j)⟩) h
  simpa [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply] using he.symm

lemma schur_intertwines_permutation {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (hsp : ∀ lam : Shape n, 0 < spechtDim lam) (π : Equiv.Perm (Fin n)) :
    S.U * QAlgorithms.Schur.tensorPermutation d n π * S.Uᴴ =
      Matrix.blockDiagonal' (fun lam => Matrix.kronecker (κ.action lam π : Op (Fin (spechtDim lam)))
        (1 : Op (Fin (weylDim d lam)))) := by
  have h := S.intertwines π 1
  simpa only [tensor_one, Matrix.mul_one, schur_nu_one S hsp] using h

end RandomDimReduction.Channel

-- TensorSpan
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

def tensorEntryPolynomial {n d : ℕ} (x y : Word n d) : MvPolynomial (Fin d × Fin d) ℂ :=
  ∏ t, MvPolynomial.X (x t,y t)

def tensorFunctionalPolynomial {n d : ℕ} (f : Op (Word n d) →ₗ[ℂ] ℂ) :
    MvPolynomial (Fin d × Fin d) ℂ :=
  ∑ x, ∑ y, MvPolynomial.C (f (Matrix.single x y 1)) * tensorEntryPolynomial x y

lemma eval_tensorFunctionalPolynomial {n d : ℕ} (f : Op (Word n d) →ₗ[ℂ] ℂ)
    (A : Op (Fin d)) :
    MvPolynomial.eval (fun ij => A ij.1 ij.2) (tensorFunctionalPolynomial f) =
      f (tensor n A) := by
  have he := congrArg f (Matrix.matrix_eq_sum_single (tensor n A))
  rw [he]
  simp only [tensorFunctionalPolynomial, tensorEntryPolynomial, map_sum, map_mul,
    MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hs : Matrix.single x y (tensor n A x y) =
      (tensor n A x y) • Matrix.single x y (1 : ℂ) := by
    simpa using (Matrix.smul_single (tensor n A x y) x y (1 : ℂ)).symm
  rw [hs, map_smul]
  simp [tensor, mul_comm]

lemma tensor_mem_span_unitary (n d : ℕ) (A : Op (Fin d)) :
    tensor n A ∈ Submodule.span ℂ (Set.range
      (fun U : Matrix.unitaryGroup (Fin d) ℂ => tensor n (U : Op (Fin d)))) := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
  intro f hf
  have hf' := (Submodule.mem_dualAnnihilator f).mp hf
  have hp : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      MvPolynomial.eval (fun ij => U ij.1 ij.2) (tensorFunctionalPolynomial f) = 0 := by
    intro U
    rw [eval_tensorFunctionalPolynomial]
    exact hf' _ (Submodule.subset_span ⟨U,rfl⟩)
  have h := polynomial_zero_of_unitary_zero (tensorFunctionalPolynomial f) hp A
  rwa [eval_tensorFunctionalPolynomial] at h

def wordPairType {n d : ℕ} (x y : Word n d) : (Fin d × Fin d) →₀ ℕ :=
  ∑ t, Finsupp.single (x t,y t) 1

lemma tensorEntryPolynomial_monomial {n d : ℕ} (x y : Word n d) :
    tensorEntryPolynomial x y = MvPolynomial.monomial (wordPairType x y) 1 := by
  simp only [tensorEntryPolynomial, wordPairType, MvPolynomial.monomial_sum_one,
    MvPolynomial.X]

lemma wordPairType_apply {n d : ℕ} (x y : Word n d) (ij : Fin d × Fin d) :
    wordPairType x y ij = Fintype.card {t : Fin n // (x t,y t) = ij} := by
  simp [wordPairType, Finsupp.single_apply, Fintype.card_subtype, eq_comm]

lemma wordPairType_eq_perm {n d : ℕ} (x y z w : Word n d)
    (h : wordPairType x y = wordPairType z w) :
    ∃ π : Equiv.Perm (Fin n), (∀ t, x t = z (π t)) ∧ ∀ t, y t = w (π t) := by
  have hc (ij : Fin d × Fin d) :
      Fintype.card {t : Fin n // (x t,y t) = ij} =
      Fintype.card {t : Fin n // (z t,w t) = ij} := by
    simpa only [wordPairType_apply] using congrArg (fun m => m ij) h
  let e (ij : Fin d × Fin d) := Fintype.equivOfCardEq (hc ij)
  refine ⟨Equiv.ofFiberEquiv e, ?_, ?_⟩
  · intro t
    exact (congrArg Prod.fst (Equiv.ofFiberEquiv_map e t)).symm
  · intro t
    exact (congrArg Prod.snd (Equiv.ofFiberEquiv_map e t)).symm

end RandomDimReduction.Channel

-- PermutationCentralizerSpan
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma matrixFunctional_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : Op ι →ₗ[ℂ] ℂ) (Y : Op ι) :
    f Y = ∑ x, ∑ y, Y x y * f (Matrix.single x y 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hs : Matrix.single x y (Y x y) = (Y x y) • Matrix.single x y (1 : ℂ) := by
    simpa using (Matrix.smul_single (Y x y) x y (1 : ℂ)).symm
  rw [hs, map_smul, smul_eq_mul]

lemma permutation_commutant_entries {n d : ℕ} (Y : Op (Word n d))
    (hY : ∀ π, QAlgorithms.Schur.tensorPermutation d n π * Y =
      Y * QAlgorithms.Schur.tensorPermutation d n π)
    (π : Equiv.Perm (Fin n)) (x y : Word n d) :
    Y (x ∘ π) (y ∘ π) = Y x y := by
  have h := congrArg (fun B : Op (Word n d) => B x (y ∘ π)) (hY π)
  simp only [Matrix.mul_apply, perm_entry_reversed, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have he (z : Word n d) : (y ∘ π = z ∘ π) ↔ y = z := by
    constructor
    · intro hz
      funext t
      simpa using congrFun hz (π.symm t)
    · rintro rfl
      rfl
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] at h
  exact h

lemma permutation_commutant_type {n d : ℕ} (Y : Op (Word n d))
    (hY : ∀ π, QAlgorithms.Schur.tensorPermutation d n π * Y =
      Y * QAlgorithms.Schur.tensorPermutation d n π)
    (x y z w : Word n d) (h : wordPairType x y = wordPairType z w) :
    Y x y = Y z w := by
  obtain ⟨π, hx, hy⟩ := wordPairType_eq_perm x y z w h
  have hx' : x = z ∘ π := funext hx
  have hy' : y = w ∘ π := funext hy
  rw [hx', hy', permutation_commutant_entries Y hY]

def typeIndicator {n d : ℕ} (m : (Fin d × Fin d) →₀ ℕ) : Op (Word n d) :=
  fun x y => if wordPairType x y = m then 1 else 0

lemma functional_typeIndicator {n d : ℕ} (f : Op (Word n d) →ₗ[ℂ] ℂ)
    (m : (Fin d × Fin d) →₀ ℕ) :
    f (typeIndicator m) = MvPolynomial.coeff m (tensorFunctionalPolynomial f) := by
  rw [matrixFunctional_eq_sum]
  simp only [tensorFunctionalPolynomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul, tensorEntryPolynomial_monomial,
    MvPolynomial.coeff_monomial, typeIndicator]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

lemma permutation_commutant_mem_span_tensor {n d : ℕ} (Y : Op (Word n d))
    (hY : ∀ π, QAlgorithms.Schur.tensorPermutation d n π * Y =
      Y * QAlgorithms.Schur.tensorPermutation d n π) :
    Y ∈ Submodule.span ℂ (Set.range (tensor (a := Fin d) (b := Fin d) n)) := by
  let T := Set.range (fun xy : Word n d × Word n d => wordPairType xy.1 xy.2)
  letI : Fintype T := Fintype.ofFinite T
  let rep : T → Word n d × Word n d := fun m => Classical.choose m.property
  have hrep (m : T) : wordPairType (rep m).1 (rep m).2 = m.val :=
    Classical.choose_spec m.property
  have hdecomp : Y = ∑ m : T, Y (rep m).1 (rep m).2 • typeIndicator m.val := by
    ext x y
    let m : T := ⟨wordPairType x y, ⟨(x,y), rfl⟩⟩
    rw [Matrix.sum_apply, Finset.sum_eq_single m]
    · simp only [Matrix.smul_apply, typeIndicator, smul_eq_mul, m, if_pos rfl, ite_true, mul_one]
      exact permutation_commutant_type Y hY x y _ _ (hrep m).symm
    · intro v _ hvm
      have hne : wordPairType x y ≠ v.val := by
        intro he
        apply hvm
        exact Subtype.ext he.symm
      simp [Matrix.smul_apply, typeIndicator, hne]
    · simp
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
  intro f hf
  have hf' := (Submodule.mem_dualAnnihilator f).mp hf
  have hp : tensorFunctionalPolynomial f = 0 := by
    apply MvPolynomial.funext
    intro z
    let A : Op (Fin d) := fun i j => z (i,j)
    have hh := hf' (tensor n A) (Submodule.subset_span ⟨A,rfl⟩)
    simpa only [← eval_tensorFunctionalPolynomial, A, Prod.mk.eta, map_zero] using hh
  rw [hdecomp, map_sum]
  apply Finset.sum_eq_zero
  intro m _
  rw [map_smul, functional_typeIndicator, hp, MvPolynomial.coeff_zero, smul_zero]

lemma permutation_commutant_mem_span_unitary {n d : ℕ} (Y : Op (Word n d))
    (hY : ∀ π, QAlgorithms.Schur.tensorPermutation d n π * Y =
      Y * QAlgorithms.Schur.tensorPermutation d n π) :
    Y ∈ Submodule.span ℂ (Set.range
      (fun U : Matrix.unitaryGroup (Fin d) ℂ => tensor n (U : Op (Fin d)))) := by
  apply Submodule.span_le.mpr (fun B hB => ?_) (permutation_commutant_mem_span_tensor Y hY)
  obtain ⟨A,rfl⟩ := hB
  exact tensor_mem_span_unitary n d A

end RandomDimReduction.Channel

-- RawBlocks
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

def rawBlock {L : Type} {a b : L → Type}
    (D : Matrix (Sigma a) (Sigma b) ℂ) (l m : L) : Matrix (a l) (b m) ℂ :=
  fun i j => D ⟨l,i⟩ ⟨m,j⟩

lemma rawBlock_mul_right {L : Type} [Fintype L] [DecidableEq L]
    {a b c : L → Type} [∀ l, Fintype (b l)]
    (D : Matrix (Sigma a) (Sigma b) ℂ) (R : ∀ l, Matrix (b l) (c l) ℂ) (l m : L) :
    rawBlock (D * Matrix.blockDiagonal' R) l m = rawBlock D l m * R m := by
  ext i j
  simp only [rawBlock, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single m]
  · simp [Matrix.blockDiagonal'_apply_eq]
  · intro t _ htm
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ htm]
  · simp

lemma rawBlock_mul_left {L : Type} [Fintype L] [DecidableEq L]
    {a b c : L → Type} [∀ l, Fintype (b l)]
    (R : ∀ l, Matrix (a l) (b l) ℂ) (D : Matrix (Sigma b) (Sigma c) ℂ) (l m : L) :
    rawBlock (Matrix.blockDiagonal' R * D) l m = R l * rawBlock D l m := by
  ext i j
  simp only [rawBlock, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single l]
  · simp [Matrix.blockDiagonal'_apply_eq]
  · intro t _ htl
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ htl.symm]
  · simp

end RandomDimReduction.Channel

-- BlockCentralizer
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma mul_kron_single_right {a b : ℕ}
    (Y : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (u v : Fin b) (i j : Fin a × Fin b) :
    (Y * Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (Matrix.single u v 1)) i j =
      if j.2 = v then Y i (j.1,u) else 0 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.one_apply, Matrix.single, ite_and, eq_comm]

lemma mul_kron_single_left {a b : ℕ}
    (Y : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (u v : Fin b) (i j : Fin a × Fin b) :
    (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (Matrix.single u v 1) * Y) i j =
      if i.2 = u then Y (i.1,v) j else 0 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.one_apply, Matrix.single, ite_and, eq_comm]

lemma kron_commutant_formula {a b : ℕ}
    (Y : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hY : ∀ A : Matrix (Fin b) (Fin b) ℂ,
      Y * Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) A =
        Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) A * Y) :
    Y = Matrix.kronecker (WildeQIT.partialTraceRight Y)
      (((b : ℂ)⁻¹) • (1 : Matrix (Fin b) (Fin b) ℂ)) := by
  have he (i j : Fin a) (u v : Fin b) (huv : u ≠ v) : Y (i,u) (j,v) = 0 := by
    have h := congrArg (fun Z => Z (i,u) (j,v)) (hY (Matrix.single v v 1))
    simpa only [mul_kron_single_right, mul_kron_single_left, if_pos rfl, ite_true,
      if_neg huv] using h
  have hd (i j : Fin a) (u v : Fin b) : Y (i,u) (j,u) = Y (i,v) (j,v) := by
    have h := congrArg (fun Z => Z (i,u) (j,v)) (hY (Matrix.single u v 1))
    simpa only [mul_kron_single_right, mul_kron_single_left, if_pos rfl, ite_true] using h
  ext ⟨i,u⟩ ⟨j,v⟩
  by_cases huv : u = v
  · subst v
    have hb : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt u.isLt))
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, WildeQIT.partialTraceRight, Matrix.of_apply]
    simp_rw [← hd i j u]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring
  · simp [Matrix.kronecker, Matrix.one_apply, huv, he i j u v huv]

lemma fullBlock_commutant_formula {L : Type} [Fintype L] [DecidableEq L]
    (p q : L → ℕ) (Y : Matrix (Sigma fun l => Fin (p l) × Fin (q l))
      (Sigma fun l => Fin (p l) × Fin (q l)) ℂ)
    (hY : ∀ A : ∀ l, Matrix (Fin (q l)) (Fin (q l)) ℂ,
      Y * Matrix.blockDiagonal' (fun l => Matrix.kronecker
        (1 : Matrix (Fin (p l)) (Fin (p l)) ℂ) (A l)) =
      Matrix.blockDiagonal' (fun l => Matrix.kronecker
        (1 : Matrix (Fin (p l)) (Fin (p l)) ℂ) (A l)) * Y) :
    Y = Matrix.blockDiagonal' (fun l => Matrix.kronecker
      (WildeQIT.partialTraceRight (rawBlock Y l l))
      (((q l : ℂ)⁻¹) • (1 : Matrix (Fin (q l)) (Fin (q l)) ℂ))) := by
  have hb (l m : L) (A : ∀ l, Matrix (Fin (q l)) (Fin (q l)) ℂ) :
      rawBlock Y l m * Matrix.kronecker (1 : Matrix (Fin (p m)) (Fin (p m)) ℂ) (A m) =
      Matrix.kronecker (1 : Matrix (Fin (p l)) (Fin (p l)) ℂ) (A l) * rawBlock Y l m := by
    have h := congrArg (fun Z => rawBlock Z l m) (hY A)
    rwa [rawBlock_mul_right, rawBlock_mul_left] at h
  ext ⟨l,i⟩ ⟨m,j⟩
  by_cases hlm : l = m
  · subst m
    rw [Matrix.blockDiagonal'_apply_eq]
    have hlocal (A : Matrix (Fin (q l)) (Fin (q l)) ℂ) :
        rawBlock Y l l * Matrix.kronecker (1 : Matrix (Fin (p l)) (Fin (p l)) ℂ) A =
        Matrix.kronecker (1 : Matrix (Fin (p l)) (Fin (p l)) ℂ) A * rawBlock Y l l := by
      simpa only [Pi.single_eq_same] using hb l l (Pi.single l A)
    exact congrArg (fun Z => Z i j) (kron_commutant_formula (rawBlock Y l l) hlocal)
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hlm]
    have h := hb l m (fun s => if s = l then 1 else 0)
    simp only [if_pos rfl, ite_true, if_neg (Ne.symm hlm), Matrix.kronecker,
      Matrix.one_kronecker_one, Matrix.kroneckerMap_zero_right (· * ·) (fun a => mul_zero a),
      Matrix.mul_zero, Matrix.one_mul] at h
    exact congrArg (fun Z => Z i j) h.symm

end RandomDimReduction.Channel

-- TwirlInvariance
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma continuous_twirl_integrand (n d : ℕ) (X : Op (Word n d)) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      tensor n (U : Op (Fin d)) * X * (tensor n (U : Op (Fin d)))ᴴ) := by
  have hc : Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => tensor n (U : Op (Fin d))) :=
    by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      have hval : Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => (U : Op (Fin d))) :=
        continuous_subtype_val
      exact continuous_finsetProd _ fun t _ =>
        (continuous_apply (j t)).comp ((continuous_apply (i t)).comp hval)
  exact (hc.matrix_mul continuous_const).matrix_mul hc.matrix_conjTranspose

lemma twirl_unitary_invariant (n d : ℕ) (X : Op (Word n d))
    (V : Matrix.unitaryGroup (Fin d) ℂ) :
    tensor n (V : Op (Fin d)) * twirl n d X * (tensor n (V : Op (Fin d)))ᴴ = twirl n d X := by
  let f := fun U : Matrix.unitaryGroup (Fin d) ℂ =>
    tensor n (U : Op (Fin d)) * X * (tensor n (U : Op (Fin d)))ᴴ
  have hf := (continuous_twirl_integrand n d X).integrable_of_hasCompactSupport
    (μ := MixedCloning.Optimal.haar d) (HasCompactSupport.of_compactSpace f)
  let T := tensor n (V : Op (Fin d))
  haveI : (MixedCloning.Optimal.haar d).IsMulLeftInvariant := by
    dsimp [MixedCloning.Optimal.haar]
    infer_instance
  change T * (∫ U, f U ∂MixedCloning.Optimal.haar d) * Tᴴ = _
  calc
    _ = (∫ U, T * f U ∂MixedCloning.Optimal.haar d) * Tᴴ := by
      congr 1
      exact ((mulLeftLinearMap (Word n d) ℝ T).toContinuousLinearMap.integral_comp_comm hf).symm
    _ = ∫ U, T * f U * Tᴴ ∂MixedCloning.Optimal.haar d :=
      ((mulRightLinearMap (Word n d) ℝ Tᴴ).toContinuousLinearMap.integral_comp_comm
        (((continuous_const (y := T)).matrix_mul (continuous_twirl_integrand n d X)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))).symm
    _ = ∫ U, f (V * U) ∂MixedCloning.Optimal.haar d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun U => by
        dsimp [T, f]
        rw [tensor_mul]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := integral_mul_left_eq_self f V

lemma twirl_commutes_unitary (n d : ℕ) (X : Op (Word n d))
    (V : Matrix.unitaryGroup (Fin d) ℂ) :
    twirl n d X * tensor n (V : Op (Fin d)) = tensor n (V : Op (Fin d)) * twirl n d X := by
  have h := congrArg (fun Y : Op (Word n d) => Y * tensor n (V : Op (Fin d)))
    (twirl_unitary_invariant n d X V)
  have hiso := tensor_isometry n (V : Op (Fin d)) V.property.1
  simpa only [Matrix.mul_assoc, hiso, Matrix.mul_one] using h.symm

lemma twirl_commutes_permutation_commutant (n d : ℕ) (X Y : Op (Word n d))
    (hY : ∀ π, QAlgorithms.Schur.tensorPermutation d n π * Y =
      Y * QAlgorithms.Schur.tensorPermutation d n π) :
    twirl n d X * Y = Y * twirl n d X := by
  have hmem := permutation_commutant_mem_span_unitary Y hY
  let C : Submodule ℂ (Op (Word n d)) :=
    LinearMap.ker ((mulLeftLinearMap (Word n d) ℂ (twirl n d X)) -
      (mulRightLinearMap (Word n d) ℂ (twirl n d X)))
  have hle : Submodule.span ℂ (Set.range
      (fun U : Matrix.unitaryGroup (Fin d) ℂ => tensor n (U : Op (Fin d)))) ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨U,rfl⟩
    change twirl n d X * tensor n (U : Op (Fin d)) -
      tensor n (U : Op (Fin d)) * twirl n d X = 0
    exact sub_eq_zero.mpr (twirl_commutes_unitary n d X U)
  exact sub_eq_zero.mp (hle hmem)

end RandomDimReduction.Channel

-- SchurTwirl
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma schur_intertwines_tensor {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (A : Op (Fin d)) :
    S.U * tensor n A * S.Uᴴ = Matrix.blockDiagonal' (fun lam =>
      Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (S.nu lam A)) := by
  simpa only [tensorPermutation_one, Matrix.mul_one, map_one, Submonoid.coe_one] using S.intertwines 1 A

lemma schur_nu_isometry {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (hsp : ∀ lam : Shape n, 0 < spechtDim lam) (V : Matrix.unitaryGroup (Fin d) ℂ)
    (lam : Shape n) : (S.nu lam (V : Op (Fin d)))ᴴ * S.nu lam (V : Op (Fin d)) = 1 := by
  have hdiso : (S.U * tensor n (V : Op (Fin d)) * S.Uᴴ)ᴴ *
      (S.U * tensor n (V : Op (Fin d)) * S.Uᴴ) = 1 := by
    calc
      _ = S.U * (tensor n (V : Op (Fin d)))ᴴ * (S.Uᴴ * S.U) *
          tensor n (V : Op (Fin d)) * S.Uᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = S.U * ((tensor n (V : Op (Fin d)))ᴴ * tensor n (V : Op (Fin d))) * S.Uᴴ := by
        rw [S.right_unitary]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [tensor_isometry n _ V.property.1, Matrix.mul_one, S.left_unitary]
  rw [schur_intertwines_tensor, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul] at hdiso
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul] at hdiso
  haveI : NeZero (spechtDim lam) := ⟨Nat.ne_of_gt (hsp lam)⟩
  ext i j
  have he := congrArg (fun A : Op (SchurIndex n d) => A ⟨lam,(0,i)⟩ ⟨lam,(0,j)⟩) hdiso
  simpa [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply] using he

lemma schurBlock_conjugate_tensor {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (A : Op (Fin d)) (X : Op (Word n d)) (lam : Shape n) :
    schurBlock S (tensor n A * X * (tensor n A)ᴴ) lam lam =
      Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (S.nu lam A) *
        schurBlock S X lam lam *
        (Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (S.nu lam A))ᴴ := by
  have he : S.U * (tensor n A * X * (tensor n A)ᴴ) * S.Uᴴ =
      (S.U * tensor n A * S.Uᴴ) * (S.U * X * S.Uᴴ) * (S.U * tensor n A * S.Uᴴ)ᴴ := by
    symm
    calc
      _ = S.U * tensor n A * (S.Uᴴ * S.U) * X * (S.Uᴴ * S.U) * (tensor n A)ᴴ * S.Uᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [S.right_unitary]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  change rawBlock (S.U * (tensor n A * X * (tensor n A)ᴴ) * S.Uᴴ) lam lam = _
  rw [he, schur_intertwines_tensor, Matrix.blockDiagonal'_conjTranspose,
    rawBlock_mul_right, rawBlock_mul_left]
  rfl

def schurTraceLinearMap {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (lam : Shape n) : Op (Word n d) →ₗ[ℂ] Op (Fin (spechtDim lam)) where
  toFun X := WildeQIT.partialTraceRight (schurBlock S X lam lam)
  map_add' X Y := by
    ext i j
    simp [WildeQIT.partialTraceRight, schurBlock, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j
    simp [WildeQIT.partialTraceRight, schurBlock, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum]

lemma schurTrace_twirl {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (hsp : ∀ lam : Shape n, 0 < spechtDim lam) (X : Op (Word n d)) (lam : Shape n) :
    WildeQIT.partialTraceRight (schurBlock S (twirl n d X) lam lam) =
      WildeQIT.partialTraceRight (schurBlock S X lam lam) := by
  let L := schurTraceLinearMap S lam
  have hf := (continuous_twirl_integrand n d X).integrable_of_hasCompactSupport
    (μ := MixedCloning.Optimal.haar d) (HasCompactSupport.of_compactSpace _)
  change L (∫ V : Matrix.unitaryGroup (Fin d) ℂ,
    tensor n (V : Op (Fin d)) * X * (tensor n (V : Op (Fin d)))ᴴ
      ∂MixedCloning.Optimal.haar d) = L X
  calc
    _ = ∫ V : Matrix.unitaryGroup (Fin d) ℂ,
        L (tensor n (V : Op (Fin d)) * X * (tensor n (V : Op (Fin d)))ᴴ)
          ∂MixedCloning.Optimal.haar d :=
      (L.toContinuousLinearMap.integral_comp_comm hf).symm
    _ = ∫ _V : Matrix.unitaryGroup (Fin d) ℂ, L X ∂MixedCloning.Optimal.haar d := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro V
      change WildeQIT.partialTraceRight (schurBlock S (tensor n (V : Op (Fin d)) * X * (tensor n (V : Op (Fin d)))ᴴ) lam lam) =
        WildeQIT.partialTraceRight (schurBlock S X lam lam)
      rw [schurBlock_conjugate_tensor]
      simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
      have h := lemma_B_1 (schurBlock S X lam lam) (S.nu lam (V : Op (Fin d))) (S.nu lam (V : Op (Fin d)))
      simpa only [Matrix.kronecker, schur_nu_isometry S hsp, Matrix.one_kronecker_one, Matrix.one_mul] using h
    _ = L X := by simp

lemma schurFullBlock_commutes_permutation {n d : ℕ} {κ : SpechtModel n}
    (S : SchurTransform κ d) (hsp : ∀ lam : Shape n, 0 < spechtDim lam)
    (A : ∀ lam : Shape n, Op (Fin (weylDim d lam))) :
    ∀ π, QAlgorithms.Schur.tensorPermutation d n π *
        (S.Uᴴ * Matrix.blockDiagonal' (fun lam => Matrix.kronecker
          (1 : Op (Fin (spechtDim lam))) (A lam)) * S.U) =
      (S.Uᴴ * Matrix.blockDiagonal' (fun lam => Matrix.kronecker
          (1 : Op (Fin (spechtDim lam))) (A lam)) * S.U) *
        QAlgorithms.Schur.tensorPermutation d n π := by
  intro π
  let P := QAlgorithms.Schur.tensorPermutation d n π
  let D := Matrix.blockDiagonal' fun lam => Matrix.kronecker
    (1 : Op (Fin (spechtDim lam))) (A lam)
  let R := Matrix.blockDiagonal' fun lam => Matrix.kronecker
    (κ.action lam π : Op (Fin (spechtDim lam))) (1 : Op (Fin (weylDim d lam)))
  have hS : S.U * P * S.Uᴴ = R := schur_intertwines_permutation S hsp π
  have hleft : P * S.Uᴴ = S.Uᴴ * R := by
    rw [← hS]
    simp only [← Matrix.mul_assoc, S.right_unitary, Matrix.one_mul]
  have hright : S.U * P = R * S.U := by
    rw [← hS]
    simp only [Matrix.mul_assoc, S.right_unitary, Matrix.mul_one]
  have hDR : R * D = D * R := by
    dsimp [R,D]
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    congr 1
    funext lam
    simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  change P * (S.Uᴴ * D * S.U) = (S.Uᴴ * D * S.U) * P
  calc
    _ = S.Uᴴ * R * D * S.U := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hleft]
    _ = S.Uᴴ * D * R * S.U := by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc R D, hDR]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hright]; simp only [Matrix.mul_assoc]

lemma schurTwirl_commutes_fullBlock {n d : ℕ} {κ : SpechtModel n}
    (S : SchurTransform κ d) (hsp : ∀ lam : Shape n, 0 < spechtDim lam)
    (X : Op (Word n d)) (A : ∀ lam : Shape n, Op (Fin (weylDim d lam))) :
    (S.U * twirl n d X * S.Uᴴ) * Matrix.blockDiagonal' (fun lam =>
      Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (A lam)) =
    Matrix.blockDiagonal' (fun lam =>
      Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (A lam)) * (S.U * twirl n d X * S.Uᴴ) := by
  let D := Matrix.blockDiagonal' fun lam => Matrix.kronecker
    (1 : Op (Fin (spechtDim lam))) (A lam)
  have h := twirl_commutes_permutation_commutant n d X (S.Uᴴ * D * S.U)
    (schurFullBlock_commutes_permutation S hsp A)
  have he := congrArg (fun Y : Op (Word n d) => S.U * Y * S.Uᴴ) h
  have h1 : S.U * (twirl n d X * (S.Uᴴ * D * S.U)) * S.Uᴴ =
      (S.U * twirl n d X * S.Uᴴ) * D := by
    simp only [Matrix.mul_assoc, S.left_unitary, Matrix.mul_one]
  have h2 : S.U * ((S.Uᴴ * D * S.U) * twirl n d X) * S.Uᴴ =
      D * (S.U * twirl n d X * S.Uᴴ) := by
    simp only [← Matrix.mul_assoc, S.left_unitary, Matrix.one_mul]
  rwa [h1,h2] at he

end RandomDimReduction.Channel

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n d : ℕ) (hn : 0 < n) (hd : 1 ≤ d)
    (κ : SpechtModel n) (S : SchurTransform κ d) (X : Op (Word n d)) :
    S.U * twirl n d X * S.Uᴴ = twirlBlocks S X := by
  have hsp (lam : Shape n) : 0 < spechtDim lam :=
    ((RandomDimReduction.Channel.spechtModel_properties n hn κ).1 lam).1
  have h := fullBlock_commutant_formula (fun lam : Shape n => spechtDim lam)
    (fun lam : Shape n => weylDim d lam) (S.U * twirl n d X * S.Uᴴ)
    (schurTwirl_commutes_fullBlock S hsp X)
  change _ = Matrix.blockDiagonal' _
  rw [h]
  congr 1
  funext lam
  change Matrix.kronecker (WildeQIT.partialTraceRight (schurBlock S (twirl n d X) lam lam)) _ = _
  rw [schurTrace_twirl S hsp]
