-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.parallelDiscrimination
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:19:08.041256+00:00
-- url     : https://prove2.me/submissions/69ae45e6-7612-4866-a382-deeb6cd3c9da

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_widthSdpAnnihilator
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_finiteTensorWidths
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker

namespace X6P75T7

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P75

lemma psd_ctc {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ C : Matrix ι ι ℂ, A = Cᴴ * C := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  open scoped MatrixOrder in
  have hB : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  open scoped MatrixOrder in
  exact ⟨CFC.sqrt A, by rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self A h0]⟩

/-- product Kraus operator on `N` registers -/
def TP {N s d : ℕ}
    {r : ℕ} (A : Fin r → Matrix (Fin s) (Fin d) ℂ) (κ : Fin N → Fin r) :
    Matrix (Fin N → Fin s) (Fin N → Fin d) ℂ :=
  fun y x => ∏ i, A (κ i) (y i) (x i)

lemma kraus_single {ι κ K : Type*} [Fintype K] [Fintype ι] [DecidableEq ι]
    (A : K → Matrix κ ι ℂ) (u u' : ι) (v v' : κ) :
    krausApply A (Matrix.single u u' 1) v v' = ∑ k, A k v u * star (A k v' u') := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [ite_and, ite_mul]

lemma pi_kraus {N s d r : ℕ} (A : Fin r → Matrix (Fin s) (Fin d) ℂ)
    (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    piSuperop (fun _ : Fin N => krausApply A) X = krausApply (fun κ => TP (N := N) A κ) X := by
  ext y y'
  simp only [piSuperop, Matrix.of_apply, kraus_single]
  simp only [Fintype.prod_sum (fun (i : Fin N) (k : Fin r) =>
    A k (y i) _ * star (A k (y' i) _))]
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, TP,
    Finset.prod_mul_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [star_prod]
  ring

lemma id_kraus {a : ℕ} {ι κ K : Type*} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (E : K → Matrix κ ι ℂ) (X : Matrix (Fin a × ι) (Fin a × ι) ℂ) :
    idTensorSuperop (R := Fin a) (krausApply E) X =
      krausApply (fun j => Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (E j)) X := by
  ext p q
  simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.one_apply, apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_irrel, Finset.sum_ite_eq]


/-- the simple-tensor map as a multilinear map -/
def T (N : ℕ) (ι : Type*) [Fintype ι] :
    MultilinearMap ℂ (fun _ : Fin N => Matrix ι ι ℂ) (Matrix (Fin N → ι) (Fin N → ι) ℂ) :=
  MultilinearMap.pi fun x => MultilinearMap.pi fun y =>
    (MultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ).compLinearMap
      (fun i => Matrix.entryLinearMap ℂ ℂ (x i) (y i))

lemma T_apply {N : ℕ} {ι : Type*} [Fintype ι] (X : Fin N → Matrix ι ι ℂ) :
    T N ι X = fun x y => ∏ i, X i (x i) (y i) := by
  ext x y
  change (MultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ)
    (fun i => Matrix.entryLinearMap ℂ ℂ (x i) (y i) (X i)) = _
  simp

lemma zero_on_span {N : ℕ} {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (F : MultilinearMap ℂ (fun _ : Fin N => V) W) (G : Set V) (φ : W →ₗ[ℂ] ℂ)
    (h : ∀ X : Fin N → V, (∀ i, X i ∈ G) → φ (F X) = 0) :
    ∀ X : Fin N → V, (∀ i, X i ∈ Submodule.span ℂ G) → φ (F X) = 0 := by
  have key : ∀ k : ℕ, ∀ X : Fin N → V, (∀ i, X i ∈ Submodule.span ℂ G) →
      (∀ i : Fin N, k ≤ i.val → X i ∈ G) → φ (F X) = 0 := by
    intro k
    induction k with
    | zero => exact fun X _ hG => h X fun i => hG i (Nat.zero_le _)
    | succ k ih =>
      intro X hS hG
      by_cases hk : k < N
      · set i0 : Fin N := ⟨k, hk⟩
        let L : V →ₗ[ℂ] ℂ := φ.comp (F.toLinearMap X i0)
        have hL : Submodule.span ℂ G ≤ LinearMap.ker L := by
          rw [Submodule.span_le]
          intro g hg
          simp only [SetLike.mem_coe, LinearMap.mem_ker, L, LinearMap.comp_apply,
            MultilinearMap.toLinearMap_apply]
          apply ih
          · intro i
            by_cases hi : i = i0
            · subst hi; simpa using Submodule.subset_span hg
            · simp [Function.update_of_ne hi, hS i]
          · intro i hi
            by_cases hi' : i = i0
            · subst hi'; simpa using hg
            · rw [Function.update_of_ne hi']
              apply hG
              have : i.val ≠ k := fun h => hi' (Fin.ext h)
              omega
        have := hL (hS i0)
        simpa [L, LinearMap.mem_ker, MultilinearMap.toLinearMap_apply] using this
      · exact ih X hS fun i hi => absurd (lt_of_le_of_lt hi i.isLt) hk
  exact fun X hS => key N X hS fun i hi => absurd i.isLt (not_lt.2 hi)


section cross
variable {N d s r t : ℕ} (A : Fin r → Matrix (Fin s) (Fin d) ℂ) (B : Fin t → Matrix (Fin s) (Fin d) ℂ)

/-- the product cross operator `⊗_i B_{λ_i}† A_{κ_i}` -/
def Yp (κ : Fin N → Fin r) (l : Fin N → Fin t) : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  T N (Fin d) (fun i => (B (l i))ᴴ * A (κ i))

lemma TP_mul (κ : Fin N → Fin r) (l : Fin N → Fin t) :
    (TP B l)ᴴ * TP A κ = Yp A B κ l := by
  ext x x'
  rw [Yp, T_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, TP, star_prod]
  rw [Fintype.prod_sum (fun (i : Fin N) (j : Fin s) => star (B (l i) j (x i)) * A (κ i) j (x' i))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

lemma Yp_mem (κ : Fin N → Fin r) (l : Fin N → Fin t) :
    Yp A B κ l ∈ tensorPower (crossSpace A B) N := by
  rw [Yp, T_apply]
  exact Submodule.subset_span ⟨fun i => (B (l i))ᴴ * A (κ i),
    fun i => Submodule.subset_span ⟨κ i, l i, rfl⟩, rfl⟩

lemma ann_iff (σ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    (∀ X ∈ tensorPower (crossSpace A B) N, (σ * X).trace = 0) ↔
      ∀ (κ : Fin N → Fin r) (l : Fin N → Fin t), (σ * Yp A B κ l).trace = 0 := by
  constructor
  · exact fun h κ l => h _ (Yp_mem A B κ l)
  · intro h X hX
    let φ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ] ℂ :=
      (Matrix.traceLinearMap (Fin N → Fin d) ℂ ℂ).comp (LinearMap.mulLeft ℂ σ)
    have hφ : ∀ Z, φ Z = (σ * Z).trace := fun Z => rfl
    have hle : tensorPower (crossSpace A B) N ≤ LinearMap.ker φ := by
      unfold tensorPower
      rw [Submodule.span_le]
      rintro Z ⟨Xs, hXs, hZ⟩
      rw [← T_apply] at hZ
      subst hZ
      show φ (T N (Fin d) Xs) = 0
      refine zero_on_span (T N (Fin d)) {X | ∃ k l, X = (B l)ᴴ * A k} φ ?_ Xs hXs
      intro Xs hG
      choose κ l hkl using hG
      have : Xs = fun i => (B (l i))ᴴ * A (κ i) := funext hkl
      rw [this, hφ]
      exact h κ l
    have := hle hX
    rwa [LinearMap.mem_ker, hφ] at this


/-- Kraus operator of `id_a ⊗ Φ^{⊗N}` -/
def KK (a : ℕ) {u : ℕ} (E : Fin u → Matrix (Fin s) (Fin d) ℂ) (κ : Fin N → Fin u) :
    Matrix (Fin a × (Fin N → Fin s)) (Fin a × (Fin N → Fin d)) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (TP E κ)

lemma tot_eq (a : ℕ) {u : ℕ} (E : Fin u → Matrix (Fin s) (Fin d) ℂ)
    (R : Matrix (Fin a × (Fin N → Fin d)) (Fin a × (Fin N → Fin d)) ℂ) :
    idTensorSuperop (R := Fin a) (piSuperop (fun _ : Fin N => krausApply E)) R =
      ∑ κ : Fin N → Fin u, KK a E κ * R * (KK a E κ)ᴴ := by
  have : piSuperop (fun _ : Fin N => krausApply E) = krausApply (fun κ => TP (N := N) E κ) :=
    funext (pi_kraus E)
  rw [this, id_kraus]
  rfl

lemma G_eq (a : ℕ) (κ : Fin N → Fin r) (l : Fin N → Fin t) :
    (KK a B l)ᴴ * KK a A κ = Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (Yp A B κ l) := by
  simp only [KK, Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, TP_mul]

end cross

/-- partial trace over the reference -/
def ptr {a : ℕ} {D : Type*} (M : Matrix (Fin a × D) (Fin a × D) ℂ) : Matrix D D ℂ := fun x x' => ∑ b, M (b, x) (b, x')

lemma trace_ptr_mul {a : ℕ} {D : Type*} [Fintype D] [DecidableEq D] (M : Matrix (Fin a × D) (Fin a × D) ℂ)
    (Y : Matrix D D ℂ) : (ptr M * Y).trace = (M * Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ptr, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul,
    zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]

lemma trace_ptr {a : ℕ} {D : Type*} [Fintype D] (M : Matrix (Fin a × D) (Fin a × D) ℂ) :
    (ptr M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, ptr, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma ptr_psd {a : ℕ} {D : Type*} [Fintype D] {α : Type*} [Fintype α]
    (C : Matrix α (Fin a × D) ℂ) : (ptr (Cᴴ * C)).PosSemidef := by
  have : ptr (Cᴴ * C) = ∑ b, (Matrix.of fun q x => C q (b, x))ᴴ * Matrix.of fun q x => C q (b, x) := by
    ext x x'
    simp [ptr, Matrix.mul_apply, Matrix.sum_apply, Matrix.conjTranspose_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun b _ => Matrix.posSemidef_conjTranspose_mul_self _


section vec
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def qf (X : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ := star v ⬝ᵥ (X *ᵥ v)

lemma qf_conjTranspose (Z : Matrix ι ι ℂ) (v : ι → ℂ) : star v ⬝ᵥ (Zᴴ *ᵥ v) = star (qf Z v) := by
  simp only [qf, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply, star_sum,
    star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def nrm (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma nrm_nonneg (v : ι → ℂ) : 0 ≤ nrm v := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma nrm_pos {v : ι → ℂ} (hv : v ≠ 0) : 0 < nrm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

def dens (v : ι → ℂ) : Matrix ι ι ℂ := (((nrm v)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec v (star v)

lemma dens_psd (v : ι → ℂ) : (dens v).PosSemidef := by
  unfold dens
  refine (Matrix.posSemidef_vecMulVec_self_star v).smul ?_
  exact_mod_cast inv_nonneg.2 (nrm_nonneg v)

lemma dens_trace {v : ι → ℂ} (hv : v ≠ 0) : (dens v).trace = 1 := by
  unfold dens
  rw [Matrix.trace_smul]
  have : (Matrix.vecMulVec v (star v)).trace = ((nrm v : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply, nrm]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  rw [this, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ (nrm_pos hv).ne']
  simp

lemma dens_trace_mul (v : ι → ℂ) (X : Matrix ι ι ℂ) :
    (dens v * X).trace = (((nrm v)⁻¹ : ℝ) : ℂ) * qf X v := by
  unfold dens qf
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma dens_isDensity {v : ι → ℂ} (hv : v ≠ 0) : QAlgorithms.IsDensityMatrix (dens v) :=
  ⟨dens_psd v, dens_trace hv⟩


lemma vmv (u : ι → ℂ) (G : Matrix ι ι ℂ) :
    Matrix.vecMulVec u (star u) * G * Matrix.vecMulVec u (star u) =
      (star u ⬝ᵥ (G *ᵥ u)) • Matrix.vecMulVec u (star u) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end vec


section dirs
variable {N d s r t : ℕ} (A : Fin r → Matrix (Fin s) (Fin d) ℂ) (B : Fin t → Matrix (Fin s) (Fin d) ℂ)

lemma rot {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) (Y : Matrix n m ℂ) :
    (X * Y).trace = (Y * X).trace := Matrix.trace_mul_comm X Y

lemma term_eq {a : ℕ} (R C : Matrix (Fin a × (Fin N → Fin d)) (Fin a × (Fin N → Fin d)) ℂ) (hC : R = Cᴴ * C)
    (κ : Fin N → Fin r) (l : Fin N → Fin t) :
    (KK a A κ * R * (KK a A κ)ᴴ * (KK a B l * R * (KK a B l)ᴴ)).trace =
      ((C * ((KK a B l)ᴴ * KK a A κ) * Cᴴ)ᴴ * (C * ((KK a B l)ᴴ * KK a A κ) * Cᴴ)).trace := by
  subst hC
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [rot (KK a A κ)]
  simp only [Matrix.mul_assoc]
  rw [rot Cᴴ]
  simp only [Matrix.mul_assoc]

lemma pp_to_dens {a : ℕ} (R : Matrix (Fin a × (Fin N → Fin d)) (Fin a × (Fin N → Fin d)) ℂ) (hR : IsDensityMatrix R)
    (h : idTensorSuperop (R := Fin a) (piSuperop (fun _ : Fin N => krausApply A)) R *
      idTensorSuperop (R := Fin a) (piSuperop (fun _ : Fin N => krausApply B)) R = 0) :
    ∃ σ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ, IsDensityMatrix σ ∧ ∀ (κ : Fin N → Fin r) (l : Fin N → Fin t), (σ * Yp A B κ l).trace = 0 := by
  rw [tot_eq, tot_eq, Finset.sum_mul_sum] at h
  have htr := congrArg Matrix.trace h
  rw [Matrix.trace_zero, Matrix.trace_sum] at htr
  simp only [Matrix.trace_sum] at htr
  obtain ⟨C, hC⟩ := psd_ctc R hR.1
  simp only [term_eq A B R C hC] at htr
  have hnn : ∀ (κ : Fin N → Fin r) (l : Fin N → Fin t), (0 : ℂ) ≤ ((C * ((KK a B l)ᴴ * KK a A κ) * Cᴴ)ᴴ *
      (C * ((KK a B l)ᴴ * KK a A κ) * Cᴴ)).trace :=
    fun κ l => (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have htr' := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun κ _ => Finset.sum_nonneg fun l _ => hnn κ l)).1 htr
  have hW : ∀ (κ : Fin N → Fin r) (l : Fin N → Fin t), C * ((KK a B l)ᴴ * KK a A κ) * Cᴴ = 0 := by
    intro κ l
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hnn κ l)).1 (htr' κ (Finset.mem_univ _)) l
      (Finset.mem_univ _)
    exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 this
  have hRGR : ∀ (κ : Fin N → Fin r) (l : Fin N → Fin t), R * ((KK a B l)ᴴ * KK a A κ) * R = 0 := by
    intro κ l
    calc R * ((KK a B l)ᴴ * KK a A κ) * R
        = Cᴴ * (C * ((KK a B l)ᴴ * KK a A κ) * Cᴴ) * C := by rw [hC]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hW, Matrix.mul_zero, Matrix.zero_mul]
  have hRh : Rᴴ = R := hR.1.isHermitian.eq
  set σ' := ptr (R * R) with hσ'
  have hσ'psd : σ'.PosSemidef := by
    have := ptr_psd (a := a) R
    rwa [hRh] at this
  have hσ'ann : ∀ (κ : Fin N → Fin r) (l : Fin N → Fin t), (σ' * Yp A B κ l).trace = 0 := by
    intro κ l
    rw [hσ', trace_ptr_mul, ← G_eq]
    calc (R * R * ((KK a B l)ᴴ * KK a A κ)).trace
        = (R * ((KK a B l)ᴴ * KK a A κ) * R).trace := by
          rw [Matrix.mul_assoc, rot, Matrix.mul_assoc]
      _ = 0 := by rw [hRGR, Matrix.trace_zero]
  -- normalize
  have hR0 : R ≠ 0 := by
    intro h0; have := hR.2; rw [h0, Matrix.trace_zero] at this; exact zero_ne_one this
  have htrσ : σ'.trace = (Rᴴ * R).trace := by rw [hσ', trace_ptr, hRh]
  have hne : σ'.trace ≠ 0 := by
    rw [htrσ]; exact fun h0 => hR0 (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0)
  have hnn' := hσ'psd.trace_nonneg
  set τ := σ'.trace with hτ
  have hτre : τ = ((τ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [(Complex.le_def.1 hnn').2.symm]
  have hpos : 0 < τ.re := by
    rcases (Complex.le_def.1 hnn').1.lt_or_eq with h | h
    · simpa using h
    · exfalso; apply hne; rw [hτre, ← h]; simp
  refine ⟨((τ.re⁻¹ : ℝ) : ℂ) • σ', ⟨hσ'psd.smul ?_, ?_⟩, ?_⟩
  · exact_mod_cast (inv_pos.2 hpos).le
  · rw [Matrix.trace_smul, ← hτ, smul_eq_mul]
    have e : ((τ.re⁻¹ : ℝ) : ℂ) * τ = ((τ.re⁻¹ * τ.re : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, ← hτre]
    rw [e, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
  · intro κ l
    rw [Matrix.smul_mul, Matrix.trace_smul, hσ'ann, smul_zero]

/-- purification vector of `Cᴴ C` -/
def psi {D : Type*} {a : ℕ} (e : D ≃ Fin a) (C : Matrix D D ℂ) : Fin a × D → ℂ :=
  fun p => star (C (e.symm p.1) p.2)

lemma kron_mulVec {D : Type*} [Fintype D] [DecidableEq D] {a : ℕ} (Y : Matrix D D ℂ)
    (v : Fin a × D → ℂ) (b : Fin a) (x : D) :
    (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) Y *ᵥ v) (b, x) = ∑ x', Y x x' * v (b, x') := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker, Matrix.one_apply,
    ite_mul]

lemma scal {D : Type*} [Fintype D] [DecidableEq D] {a : ℕ} (e : D ≃ Fin a) (C Y : Matrix D D ℂ) :
    star (psi e C) ⬝ᵥ (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) Y *ᵥ psi e C) =
      (Y * (Cᴴ * C)).trace := by
  rw [dotProduct, Fintype.sum_prod_type]
  simp only [kron_mulVec, psi, Pi.star_apply, star_star]
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

lemma dens_to_pp [Nonempty (Fin N → Fin d)] (σ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hσ : IsDensityMatrix σ)
    (hann : ∀ (κ : Fin N → Fin r) (l : Fin N → Fin t), (σ * Yp A B κ l).trace = 0) :
    ∃ a : ℕ, 0 < a ∧ ∃ R : Matrix (Fin a × (Fin N → Fin d)) (Fin a × (Fin N → Fin d)) ℂ,
      IsDensityMatrix R ∧
      idTensorSuperop (R := Fin a) (piSuperop (fun _ : Fin N => krausApply A)) R *
        idTensorSuperop (R := Fin a) (piSuperop (fun _ : Fin N => krausApply B)) R = 0 := by
  obtain ⟨C, hC⟩ := psd_ctc σ hσ.1
  set e := Fintype.equivFin (Fin N → Fin d)
  set a := Fintype.card (Fin N → Fin d)
  have hψ : psi e C ≠ 0 := by
    intro h
    have hC0 : C = 0 := by
      ext z x
      have := congrFun h (e z, x)
      simpa [psi] using this
    have := hσ.2
    rw [hC, hC0, Matrix.mul_zero, Matrix.trace_zero] at this
    exact zero_ne_one this
  refine ⟨_, Fintype.card_pos, dens (psi e C), dens_isDensity hψ, ?_⟩
  have hsc : ∀ (κ : Fin N → Fin r) (l : Fin N → Fin t),
      star (psi e C) ⬝ᵥ (((KK a A κ)ᴴ * KK a B l) *ᵥ psi e C) = 0 := by
    intro κ l
    have : (KK a A κ)ᴴ * KK a B l = ((KK a B l)ᴴ * KK a A κ)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [this, qf_conjTranspose, qf, G_eq, scal, ← hC, rot, hann, star_zero]
  have hRGR : ∀ (κ : Fin N → Fin r) (l : Fin N → Fin t),
      dens (psi e C) * ((KK a A κ)ᴴ * KK a B l) * dens (psi e C) = 0 := by
    intro κ l
    unfold dens
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, vmv, hsc, zero_smul, smul_zero,
      smul_zero]
  rw [tot_eq, tot_eq, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun κ _ => Finset.sum_eq_zero fun l _ => ?_
  calc KK a A κ * dens (psi e C) * (KK a A κ)ᴴ * (KK a B l * dens (psi e C) * (KK a B l)ᴴ)
      = KK a A κ * (dens (psi e C) * ((KK a A κ)ᴴ * KK a B l) * dens (psi e C)) * (KK a B l)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hRGR, Matrix.mul_zero, Matrix.zero_mul]

end dirs

lemma phase_zero : phase 0 = 1 := by simp [phase]

lemma mem_omega_zero {ι : Type*} [Fintype ι] (R : Matrix ι ι ℂ) :
    R ∈ omega (ι := ι) 0 ↔ IsDensityMatrix R := by
  constructor
  · rintro ⟨-, -, P, Q, hP, hQ, htr, rfl⟩
    simp only [blend, zero_div, neg_zero, phase_zero, one_smul]
    exact ⟨hP.add hQ, by rw [Matrix.trace_add]; exact htr⟩
  · rintro ⟨hR, htr⟩
    refine ⟨le_rfl, Real.pi_pos, R, 0, hR, Matrix.PosSemidef.zero, by simpa using htr, ?_⟩
    simp [blend, phase_zero]

section final
variable {N d s r t : ℕ} (A : Fin r → Matrix (Fin s) (Fin d) ℂ) (B : Fin t → Matrix (Fin s) (Fin d) ℂ)

lemma pp_iff (hd : 0 < d) (hN : 1 ≤ N) :
    ParallelPerfect (krausApply A) (krausApply B) N ↔
      Real.pi ≤ N * infWidth (crossSpace A B) := by
  haveI : Nonempty (Fin N → Fin d) := ⟨fun _ => ⟨0, hd⟩⟩
  set M := tensorPower (crossSpace A B) N
  have hM : M = listTensorSpace (fun _ : Fin N => d) (fun _ => crossSpace A B) := rfl
  have hw : infWidth M = min (N * infWidth (crossSpace A B)) Real.pi := by
    rw [hM, (finiteTensorWidths hN (fun _ : Fin N => d) (fun _ => hd)).1]
    simp
  have h2 := (widthSdpAnnihilator M 0 le_rfl Real.pi_pos).1.trans
    (widthSdpAnnihilator M 0 le_rfl Real.pi_pos).2
  rw [add_zero, hw, le_min_iff, and_iff_left le_rfl] at h2
  rw [h2]
  constructor
  · rintro ⟨a, -, R, hR, h⟩
    obtain ⟨σ, hσ, hann⟩ := pp_to_dens A B R hR h
    exact ⟨σ, (mem_omega_zero σ).2 hσ, (ann_iff A B σ).2 hann⟩
  · rintro ⟨σ, hσ, hann⟩
    exact dens_to_pp A B σ ((mem_omega_zero σ).1 hσ) ((ann_iff A B σ).1 hann)

theorem main (hd : 0 < d) (hs : 0 < s) (hA : IsKrausFamily A) (hB : IsKrausFamily B) :
    ((∃ N : ℕ, 1 ≤ N ∧ ParallelPerfect (krausApply A) (krausApply B) N) ↔
      0 < infWidth (crossSpace A B)) ∧
    (0 < infWidth (crossSpace A B) →
      let N0 := minimumCopies (krausApply A) (krausApply B)
      N0 = ⌈Real.pi / infWidth (crossSpace A B)⌉₊ ∧ 1 ≤ N0 ∧
        ParallelPerfect (krausApply A) (krausApply B) N0 ∧
        ∀ N : ℕ, 1 ≤ N → N < N0 → ¬ ParallelPerfect (krausApply A) (krausApply B) N) := by
  set w := infWidth (crossSpace A B)
  have key : ∀ N : ℕ, 0 < w → ((1 ≤ N ∧ ParallelPerfect (krausApply A) (krausApply B) N) ↔
      ⌈Real.pi / w⌉₊ ≤ N) := by
    intro N hw
    have hc : 1 ≤ ⌈Real.pi / w⌉₊ := Nat.one_le_iff_ne_zero.2
      (Nat.ceil_pos.2 (div_pos Real.pi_pos hw)).ne'
    constructor
    · rintro ⟨hN, hpp⟩
      rw [Nat.ceil_le, div_le_iff₀ hw]
      rw [pp_iff A B hd hN] at hpp
      linarith
    · intro hle
      have hN : 1 ≤ N := hc.trans hle
      refine ⟨hN, (pp_iff A B hd hN).2 ?_⟩
      rw [Nat.ceil_le, div_le_iff₀ hw] at hle
      linarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨N, hN, hpp⟩
    rw [pp_iff A B hd hN] at hpp
    by_contra hw
    push Not at hw
    have : (N : ℝ) * w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hw
    linarith [Real.pi_pos]
  · intro hw
    exact ⟨_, ((key _ hw).2 le_rfl).1, ((key _ hw).2 le_rfl).2⟩
  · intro hw
    simp only
    have hS : {N | 1 ≤ N ∧ ParallelPerfect (krausApply A) (krausApply B) N} =
        {N | ⌈Real.pi / w⌉₊ ≤ N} := Set.ext fun N => key N hw
    have hN0 : minimumCopies (krausApply A) (krausApply B) = ⌈Real.pi / w⌉₊ := by
      unfold minimumCopies
      rw [hS]
      have hmem : ⌈Real.pi / w⌉₊ ∈ {N : ℕ | ⌈Real.pi / w⌉₊ ≤ N} := by simp [Nat.le_ceil]
      exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨_, hmem⟩)
    rw [hN0]
    refine ⟨rfl, ((key _ hw).2 le_rfl).1, ((key _ hw).2 le_rfl).2, ?_⟩
    intro N hN hlt hpp
    exact absurd ((key N hw).1 ⟨hN, hpp⟩) (not_le.2 hlt)

end final

end X6P75T7

open Classical QAlgorithms QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution {d s r t : ℕ} (hd : 0 < d) (hs : 0 < s)
    (A : Fin r → Matrix (Fin s) (Fin d) ℂ) (B : Fin t → Matrix (Fin s) (Fin d) ℂ)
    (hA : IsKrausFamily A) (hB : IsKrausFamily B) :
    ((∃ N : ℕ, 1 ≤ N ∧ ParallelPerfect (krausApply A) (krausApply B) N) ↔
      0 < infWidth (crossSpace A B)) ∧
    (0 < infWidth (crossSpace A B) →
      let N0 := minimumCopies (krausApply A) (krausApply B)
      N0 = ⌈Real.pi / infWidth (crossSpace A B)⌉₊ ∧ 1 ≤ N0 ∧
        ParallelPerfect (krausApply A) (krausApply B) N0 ∧
        ∀ N : ℕ, 1 ≤ N → N < N0 → ¬ ParallelPerfect (krausApply A) (krausApply B) N) :=
  X6P75T7.main A B hd hs hA hB
