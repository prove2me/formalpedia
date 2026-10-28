-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P31.krausOperatorNormFormula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:30:38.285541+00:00
-- url     : https://prove2.me/submissions/a3b94a1d-acf7-4eb3-a0a3-2561c6c7c8cf

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31


/-! X6: operator-norm toolkit for Kraus maps (plain vectors, l2 operator norm). -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

namespace X6KN

open QAlgorithms

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- squared Euclidean norm of a plain vector -/
def nsq (v : n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma nsq_nonneg (v : n → ℂ) : 0 ≤ nsq v := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma norm_toLp (v : n → ℂ) : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ = √(nsq v) := by
  rw [EuclideanSpace.norm_eq]; rfl

lemma N1 (M : Matrix m n ℂ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x : n → ℂ, nsq (M *ᵥ x) ≤ c * nsq x) :
    ‖M‖ ≤ √c := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg c) fun x => ?_
  have hx : x = WithLp.toLp 2 x.ofLp := rfl
  show ‖(WithLp.toLp 2 (M *ᵥ x.ofLp) : EuclideanSpace ℂ m)‖ ≤ √c * ‖x‖
  rw [hx, norm_toLp, norm_toLp, ← Real.sqrt_mul hc]
  exact Real.sqrt_le_sqrt (h _)

lemma N3 (M : Matrix m n ℂ) (x : n → ℂ) : nsq (M *ᵥ x) ≤ ‖M‖ ^ 2 * nsq x := by
  have := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 x)
  have e : ‖(EuclideanSpace.equiv m ℂ).symm (M *ᵥ (WithLp.toLp 2 x : EuclideanSpace ℂ n))‖ =
      √(nsq (M *ᵥ x)) := norm_toLp _
  rw [e, norm_toLp] at this
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
  rw [mul_pow, Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _)] at h2
  exact h2

lemma N2 (M : Matrix m n ℂ) (w : m → ℂ) (v : n → ℂ) :
    ‖star w ⬝ᵥ (M *ᵥ v)‖ ≤ ‖M‖ * √(nsq w) * √(nsq v) := by
  have hi := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 w : EuclideanSpace ℂ m)
    (WithLp.toLp 2 (M *ᵥ v) : EuclideanSpace ℂ m)
  rw [EuclideanSpace.inner_eq_star_dotProduct, norm_toLp, norm_toLp] at hi
  have e : (M *ᵥ v) ⬝ᵥ star w = star w ⬝ᵥ (M *ᵥ v) := dotProduct_comm _ _
  simp only [e] at hi
  have h3 := N3 M v
  have h4 : √(nsq (M *ᵥ v)) ≤ ‖M‖ * √(nsq v) := by
    calc √(nsq (M *ᵥ v)) ≤ √(‖M‖ ^ 2 * nsq v) := Real.sqrt_le_sqrt h3
      _ = ‖M‖ * √(nsq v) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  calc ‖star w ⬝ᵥ (M *ᵥ v)‖ ≤ √(nsq w) * √(nsq (M *ᵥ v)) := hi
    _ ≤ √(nsq w) * (‖M‖ * √(nsq v)) := mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
    _ = _ := by ring

lemma nsq_eq_re (v : n → ℂ) : nsq v = (star v ⬝ᵥ v).re := by
  simp only [nsq, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.mul_re]

lemma nsq_smul (t : ℂ) (v : n → ℂ) : nsq (t • v) = ‖t‖ ^ 2 * nsq v := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

/-- complex Cauchy–Schwarz for finite sums -/
lemma cs (z a : n → ℂ) : ‖∑ k, z k * a k‖ ≤ √(nsq z) * √(nsq a) := by
  have h1 : ‖∑ k, z k * a k‖ ≤ ∑ k, ‖z k‖ * ‖a k‖ := by
    refine (norm_sum_le _ _).trans ?_
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖z k‖) (fun k => ‖a k‖)
  have h3 : ∑ k, ‖z k‖ * ‖a k‖ ≤ √(nsq z) * √(nsq a) := by
    rw [← Real.sqrt_mul (nsq_nonneg _)]
    apply Real.le_sqrt_of_sq_le
    exact h2
  linarith

end X6KN


/-! X6: the operator-norm formula for the maximal output norm of a Kraus channel. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

namespace X6KN

open QAlgorithms Matrix

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

lemma spec {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix I I ℂ) := by
  have hs := hX.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  exact hs

lemma spec_sum {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    X = ∑ i, ((hX.eigenvalues i : ℝ) : ℂ) •
      vecMulVec (⇑(hX.eigenvectorBasis i)) (star ⇑(hX.eigenvectorBasis i)) := by
  conv_lhs => rw [spec hX]
  ext a b
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, Matrix.star_apply, Pi.star_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma eig_bounds {σ : Matrix I I ℂ} (hσ : IsDensityMatrix σ) :
    (∀ i, 0 ≤ hσ.1.1.eigenvalues i) ∧ ∑ i, hσ.1.1.eigenvalues i = 1 := by
  have h0 : ∀ i, 0 ≤ hσ.1.1.eigenvalues i := hσ.1.eigenvalues_nonneg
  refine ⟨h0, ?_⟩
  have key : (σ.trace).re = 1 := by rw [hσ.2]; simp
  rw [hσ.1.1.trace_eq_sum_eigenvalues, Complex.re_sum] at key
  simpa using key

lemma nsq_basis {X : Matrix I I ℂ} (hX : X.IsHermitian) (i : I) :
    nsq (⇑(hX.eigenvectorBasis i)) = 1 := by
  have h := hX.eigenvectorBasis.orthonormal.1 i
  have : (WithLp.toLp 2 (⇑(hX.eigenvectorBasis i)) : EuclideanSpace ℂ I) =
      hX.eigenvectorBasis i := rfl
  rw [← this, norm_toLp] at h
  have h2 := congrArg (· ^ 2) h
  simp only [one_pow] at h2
  rwa [Real.sq_sqrt (nsq_nonneg _)] at h2

variable (A : K → Matrix I I ℂ)

/-- the factor `W` with `Φ(u u*) = W W*` -/
def W (u : I → ℂ) : Matrix I K ℂ := Matrix.of fun a k => (A k *ᵥ u) a

lemma kraus_smul (c : ℂ) (X : Matrix I I ℂ) : krausApply A (c • X) = c • krausApply A X := by
  simp [krausApply, Finset.smul_sum]

lemma kraus_sum {ι : Type} [Fintype ι] (c : ι → ℂ) (X : ι → Matrix I I ℂ) :
    krausApply A (∑ i, c i • X i) = ∑ i, c i • krausApply A (X i) := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]
  rw [Finset.sum_comm]

lemma hW (u : I → ℂ) : krausApply A (vecMulVec u (star u)) = W A u * (W A u)ᴴ := by
  ext a b
  simp only [krausApply, W, Matrix.sum_apply, Matrix.mul_apply, vecMulVec_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, mulVec, dotProduct, Pi.star_apply, star_sum,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

lemma hWx (u x : I → ℂ) : (W A u)ᴴ *ᵥ x = fun k => star (star x ⬝ᵥ (A k *ᵥ u)) := by
  funext k
  simp only [W, mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum,
    star_mul', Pi.star_apply, star_star]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma nsq_Wx (u x : I → ℂ) : nsq ((W A u)ᴴ *ᵥ x) = nsq (fun k => star x ⬝ᵥ (A k *ᵥ u)) := by
  rw [hWx]; simp [nsq]

lemma normPhi (u : I → ℂ) : ‖krausApply A (vecMulVec u (star u))‖ = ‖(W A u)ᴴ‖ ^ 2 := by
  rw [hW]
  have := Matrix.l2_opNorm_conjTranspose_mul_self (W A u)ᴴ
  rw [Matrix.conjTranspose_conjTranspose] at this
  rw [this]; ring

lemma Mz_bound (z : K → ℂ) (hz : nsq z = 1) (u : I → ℂ) :
    nsq ((∑ k, z k • A k) *ᵥ u) ≤ ‖krausApply A (vecMulVec u (star u))‖ := by
  set y := (∑ k, z k • A k) *ᵥ u
  set N := ‖(W A u)ᴴ‖
  rw [normPhi]
  have h1' : ∀ v : I → ℂ, star v ⬝ᵥ ((∑ k, z k • A k) *ᵥ u) =
      ∑ k, z k * (star v ⬝ᵥ (A k *ᵥ u)) := by
    intro v
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have h1 : star y ⬝ᵥ y = ∑ k, z k * (star y ⬝ᵥ (A k *ᵥ u)) := h1' y
  have h2 : nsq y ≤ √(nsq (fun k => star y ⬝ᵥ (A k *ᵥ u))) := by
    rw [nsq_eq_re]
    calc (star y ⬝ᵥ y).re ≤ ‖star y ⬝ᵥ y‖ := Complex.re_le_norm _
      _ = ‖∑ k, z k * (star y ⬝ᵥ (A k *ᵥ u))‖ := by rw [h1]
      _ ≤ √(nsq z) * √(nsq (fun k => star y ⬝ᵥ (A k *ᵥ u))) := cs _ _
      _ = _ := by rw [hz, Real.sqrt_one, one_mul]
  have h3 : √(nsq (fun k => star y ⬝ᵥ (A k *ᵥ u))) ≤ N * √(nsq y) := by
    rw [← nsq_Wx]
    calc √(nsq ((W A u)ᴴ *ᵥ y)) ≤ √(N ^ 2 * nsq y) := Real.sqrt_le_sqrt (N3 _ _)
      _ = N * √(nsq y) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  set t := √(nsq y)
  have ht : nsq y = t ^ 2 := (Real.sq_sqrt (nsq_nonneg _)).symm
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hN : 0 ≤ N := norm_nonneg _
  rw [ht] at h2 ⊢
  have : t ^ 2 ≤ N * t := h2.trans h3
  nlinarith

lemma pure_dens (u : I → ℂ) (hu : nsq u = 1) : IsDensityMatrix (vecMulVec u (star u)) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star u, ?_⟩
  rw [Matrix.trace]
  simp only [Matrix.diag, vecMulVec_apply, Pi.star_apply]
  have : ∀ a, u a * star (u a) = ((‖u a‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [this]
  rw [← Complex.ofReal_sum]
  have h : ∑ a, ‖u a‖ ^ 2 = 1 := hu
  rw [h]; simp

lemma vmv_smul (t : ℂ) (u : I → ℂ) :
    vecMulVec (t • u) (star (t • u)) = ((‖t‖ ^ 2 : ℝ) : ℂ) • vecMulVec u (star u) := by
  ext a b
  simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, Matrix.smul_apply,
    star_mul']
  have : t * star t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← this]; ring

end X6KN


/-! X6: assembling the operator-norm formula `ν_∞(Φ) = sup_{‖z‖=1} ‖Σ z_k A_k‖²`. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

namespace X6KN

open QAlgorithms Matrix

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

lemma norm_density_le {σ : Matrix I I ℂ} (hσ : IsDensityMatrix σ) : ‖σ‖ ≤ 1 := by
  obtain ⟨h0, hs⟩ := eig_bounds hσ
  conv_lhs => rw [spec_sum hσ.1.1]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖((hσ.1.1.eigenvalues i : ℝ) : ℂ) • vecMulVec (⇑(hσ.1.1.eigenvectorBasis i))
        (star ⇑(hσ.1.1.eigenvectorBasis i))‖
      ≤ ∑ i, hσ.1.1.eigenvalues i * 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 i)]
        refine mul_le_mul_of_nonneg_left ?_ (h0 i)
        -- ‖u u*‖ = nsq u = 1
        have hu := nsq_basis hσ.1.1 i
        set u := ⇑(hσ.1.1.eigenvectorBasis i)
        have e : vecMulVec u (star u) = (Matrix.replicateCol Unit u) * (Matrix.replicateCol Unit u)ᴴ := by
          ext a b; simp [vecMulVec_apply, Matrix.mul_apply]
        rw [e]
        have := Matrix.l2_opNorm_conjTranspose_mul_self (Matrix.replicateCol Unit u)ᴴ
        rw [Matrix.conjTranspose_conjTranspose] at this
        rw [this]
        have hc : ‖(Matrix.replicateCol Unit u)ᴴ‖ ≤ 1 := by
          have := N1 (Matrix.replicateCol Unit u)ᴴ zero_le_one (fun x => ?_)
          · simpa using this
          simp only [nsq, Fintype.univ_unit, Finset.sum_singleton, one_mul]
          have e2 : ((Matrix.replicateCol Unit u)ᴴ *ᵥ x) () = star u ⬝ᵥ x := by
            simp [mulVec, dotProduct, Matrix.conjTranspose_apply]
          rw [e2]
          have h1 : ‖star u ⬝ᵥ x‖ ≤ √(nsq u) * √(nsq x) := by
            have := cs (star u) x
            have e3 : star u ⬝ᵥ x = ∑ k, (star u) k * x k := rfl
            have e4 : nsq (star u) = nsq u := by simp [nsq, norm_star]
            rw [e3]; rw [e4] at this; exact this
          rw [hu, Real.sqrt_one, one_mul] at h1
          have := pow_le_pow_left₀ (norm_nonneg _) h1 2
          rwa [Real.sq_sqrt (nsq_nonneg _)] at this
        nlinarith [norm_nonneg (Matrix.replicateCol Unit u)ᴴ]
    _ = 1 := by simp only [mul_one]; exact hs

variable (A : K → Matrix I I ℂ)

lemma kraus_dens (hA : IsKrausFamily A) {ρ : Matrix I I ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (krausApply A ρ) := by
  refine ⟨Matrix.posSemidef_sum _ fun k _ => hρ.1.mul_mul_conjTranspose_same (A k), ?_⟩
  show Matrix.trace (∑ k, A k * ρ * (A k)ᴴ) = 1
  rw [Matrix.trace_sum]
  have : ∀ k, Matrix.trace (A k * ρ * (A k)ᴴ) = Matrix.trace ((A k)ᴴ * A k * ρ) := by
    intro k; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [this, ← Matrix.trace_sum, ← Matrix.sum_mul]
  rw [show ∑ k, (A k)ᴴ * A k = 1 from hA, Matrix.one_mul, hρ.2]

theorem main [Nonempty I] (hA : IsKrausFamily A) :
    Papers.Independent.Support50.P31.nuP ⊤ (krausApply A) = sSup (Set.range fun z :
      {z : EuclideanSpace ℂ K // ‖z‖ = 1} => specNorm (∑ k, z.val k • A k) ^ 2) := by
  unfold Papers.Independent.Support50.P31.nuP
  rw [if_pos rfl]
  set S := Set.range fun X : {X : Matrix I I ℂ // IsDensityMatrix X} =>
    specNorm (krausApply A X.val) with hSdef
  set T := Set.range fun z : {z : EuclideanSpace ℂ K // ‖z‖ = 1} =>
    specNorm (∑ k, z.val k • A k) ^ 2 with hTdef
  obtain ⟨i0⟩ := (inferInstance : Nonempty I)
  have hSb : BddAbove S := ⟨1, by
    rintro _ ⟨X, rfl⟩; exact norm_density_le (kraus_dens A hA X.2)⟩
  set e0 : I → ℂ := Pi.single i0 1
  have he0 : nsq e0 = 1 := by
    simp only [nsq, e0]
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hSne : S.Nonempty := ⟨_, ⟨vecMulVec e0 (star e0), pure_dens e0 he0⟩, rfl⟩
  have hS0 : 0 ≤ sSup S := (norm_nonneg _).trans (le_csSup hSb ⟨⟨_, pure_dens e0 he0⟩, rfl⟩)
  -- Step A
  have stepA : ∀ z : K → ℂ, nsq z = 1 → ‖∑ k, z k • A k‖ ^ 2 ≤ sSup S := by
    intro z hz
    have hb : ‖∑ k, z k • A k‖ ≤ √(sSup S) := by
      refine N1 _ hS0 fun x => ?_
      refine (Mz_bound A z hz x).trans ?_
      rcases (nsq_nonneg x).eq_or_lt with h0 | hpos
      · have hx : x = 0 := by
          funext a
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i‖)).1 h0.symm a
            (Finset.mem_univ a)
          simpa using this
        subst hx; simpa [krausApply] using mul_nonneg hS0 (nsq_nonneg (0 : I → ℂ))
      · set t := √(nsq x)
        have ht : 0 < t := Real.sqrt_pos.2 hpos
        set u := ((t⁻¹ : ℝ) : ℂ) • x
        have hu : nsq u = 1 := by
          rw [nsq_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht), inv_pow,
            Real.sq_sqrt (nsq_nonneg _)]
          exact inv_mul_cancel₀ hpos.ne'
        have hxu : x = ((t : ℝ) : ℂ) • u := by
          simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one,
            one_smul]
        conv_lhs => rw [hxu]
        rw [vmv_smul, kraus_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
          Real.sq_sqrt (nsq_nonneg _), mul_comm]
        exact mul_le_mul_of_nonneg_right (le_csSup hSb ⟨⟨_, pure_dens u hu⟩, rfl⟩) hpos.le
    have := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rwa [Real.sq_sqrt hS0] at this
  have hzn : ∀ z : {z : EuclideanSpace ℂ K // ‖z‖ = 1}, nsq z.val.ofLp = 1 := by
    intro z
    have h := z.2
    have e : (WithLp.toLp 2 z.val.ofLp : EuclideanSpace ℂ K) = z.val := rfl
    rw [← e, norm_toLp] at h
    have h2 := congrArg (· ^ 2) h
    simp only [one_pow] at h2
    rwa [Real.sq_sqrt (nsq_nonneg _)] at h2
  have hTb : BddAbove T := ⟨sSup S, by rintro _ ⟨z, rfl⟩; exact stepA _ (hzn z)⟩
  have hK : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have h := congrFun (congrFun hA i0) i0
    simp [Finset.univ_eq_empty] at h
  obtain ⟨k0⟩ := hK
  have hTne : T.Nonempty := by
    refine ⟨_, ⟨⟨WithLp.toLp 2 (Pi.single k0 1), ?_⟩, rfl⟩⟩
    rw [norm_toLp]
    simp only [nsq]
    rw [Finset.sum_eq_single k0]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hT0 : 0 ≤ sSup T := (sq_nonneg _).trans (le_csSup hTb ⟨⟨WithLp.toLp 2 (Pi.single k0 1),
    by rw [norm_toLp]; simp only [nsq]; rw [Finset.sum_eq_single k0] <;> simp_all [Pi.single_apply]⟩,
      rfl⟩)
  -- Step B, pure inputs
  have stepBp : ∀ u : I → ℂ, nsq u = 1 → ‖krausApply A (vecMulVec u (star u))‖ ≤ sSup T := by
    intro u hu
    rw [normPhi]
    have hb : ‖(W A u)ᴴ‖ ≤ √(sSup T) := by
      refine N1 _ hT0 fun x => ?_
      rw [nsq_Wx]
      set a : K → ℂ := fun k => star x ⬝ᵥ (A k *ᵥ u)
      rcases (nsq_nonneg a).eq_or_lt with h0 | hpos
      · rw [← h0]; exact mul_nonneg hT0 (nsq_nonneg _)
      · set s := nsq a
        set z : K → ℂ := fun k => star (a k) / ((√s : ℝ) : ℂ)
        have hs : 0 < √s := Real.sqrt_pos.2 hpos
        have hz : nsq z = 1 := by
          simp only [nsq, z, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hs, div_pow, Real.sq_sqrt hpos.le, ← Finset.sum_div]
          exact div_self hpos.ne'
        have hsum : ∑ k, z k * a k = ((√s : ℝ) : ℂ) := by
          have : ∀ k, z k * a k = ((‖a k‖ ^ 2 : ℝ) : ℂ) / ((√s : ℝ) : ℂ) := by
            intro k
            simp only [z]
            rw [div_mul_eq_mul_div, mul_comm, Complex.star_def, Complex.mul_conj,
              Complex.normSq_eq_norm_sq]
          simp only [this, ← Finset.sum_div, ← Complex.ofReal_sum]
          have : ∑ k, ‖a k‖ ^ 2 = s := rfl
          rw [this]
          have hs' : ((√s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
          field_simp
          rw [← Complex.ofReal_pow, Real.sq_sqrt hpos.le]
        have hdot : star x ⬝ᵥ ((∑ k, z k • A k) *ᵥ u) = ∑ k, z k * a k := by
          rw [Matrix.sum_mulVec, dotProduct_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        have hN := N2 (∑ k, z k • A k) x u
        rw [hdot, hsum, hu, Real.sqrt_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hs] at hN
        have hzT : ‖∑ k, z k • A k‖ ^ 2 ≤ sSup T :=
          le_csSup hTb ⟨⟨WithLp.toLp 2 z, by rw [norm_toLp, hz, Real.sqrt_one]⟩, rfl⟩
        have := pow_le_pow_left₀ hs.le hN 2
        rw [mul_pow, Real.sq_sqrt hpos.le, Real.sq_sqrt (nsq_nonneg _)] at this
        calc s ≤ ‖∑ k, z k • A k‖ ^ 2 * nsq x := this
          _ ≤ sSup T * nsq x := mul_le_mul_of_nonneg_right hzT (nsq_nonneg _)
    have := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rwa [Real.sq_sqrt hT0] at this
  -- Step B, general densities
  have stepB : ∀ ρ : Matrix I I ℂ, IsDensityMatrix ρ → ‖krausApply A ρ‖ ≤ sSup T := by
    intro ρ hρ
    obtain ⟨h0, hs⟩ := eig_bounds hρ
    rw [spec_sum hρ.1.1, kraus_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖((hρ.1.1.eigenvalues i : ℝ) : ℂ) • krausApply A (vecMulVec
          (⇑(hρ.1.1.eigenvectorBasis i)) (star ⇑(hρ.1.1.eigenvectorBasis i)))‖
        ≤ ∑ i, hρ.1.1.eigenvalues i * sSup T := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 i)]
          exact mul_le_mul_of_nonneg_left (stepBp _ (nsq_basis _ i)) (h0 i)
      _ = sSup T := by rw [← Finset.sum_mul, hs, one_mul]
  apply le_antisymm
  · exact csSup_le hSne (by rintro _ ⟨X, rfl⟩; exact stepB X.1 X.2)
  · exact csSup_le hTne (by rintro _ ⟨z, rfl⟩; exact stepA _ (hzn z))

end X6KN


open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P31

theorem solution {I K : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype K] [DecidableEq K] (A : K → Matrix I I ℂ) (hA : IsKrausFamily A) :
    nuP ⊤ (krausApply A) = sSup (Set.range fun z :
      {z : EuclideanSpace ℂ K // ‖z‖ = 1} => specNorm (∑ k, z.val k • A k) ^ 2) :=
  X6KN.main A hA
