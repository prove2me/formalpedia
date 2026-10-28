-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P31.productInputBounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:56:30.114531+00:00
-- url     : https://prove2.me/submissions/5381dcfe-2967-4d0f-9a8c-eb2866d38127

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


/-! X6: spectra of Kronecker products of Hermitian matrices. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Kronecker Matrix.Norms.L2Operator

namespace X6PI

open QAlgorithms Matrix X6KN

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- eigenvalues as a multiset are determined by any unitary diagonalisation -/
lemma eig_ms {X : Matrix n n ℂ} (hX : X.IsHermitian) (W : Matrix n n ℂ) (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (d : n → ℝ) (h : X = W * diagonal (fun p => (d p : ℂ)) * Wᴴ) :
    Multiset.map hX.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
  let U : (Matrix n n ℂ)ˣ := ⟨W, Wᴴ, hW2, hW1⟩
  have hc : X.charpoly = (diagonal (fun p => (d p : ℂ))).charpoly := by
    have key := Matrix.charpoly_units_conj U (diagonal (fun p => (d p : ℂ)))
    have hv : (U : Matrix n n ℂ) = W := rfl
    rw [hv, Matrix.inv_eq_left_inv hW1] at key
    rw [h]; exact key
  rw [hX.charpoly_eq, Matrix.charpoly_diagonal] at hc
  have h1 := congrArg Polynomial.roots hc
  have e : ∀ (f : n → ℂ), (∏ i, (Polynomial.X - Polynomial.C (f i))) =
      (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Multiset.map f Finset.univ.val)).prod := by
    intro f; rw [Multiset.map_map]; rfl
  rw [e, e, Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at h1
  have h2 : Multiset.map Complex.ofReal (Multiset.map hX.eigenvalues Finset.univ.val) =
      Multiset.map Complex.ofReal (Multiset.map d Finset.univ.val) := by
    rw [Multiset.map_map, Multiset.map_map]; exact h1
  exact Multiset.map_injective Complex.ofReal_injective h2

lemma sum_eig {X : Matrix n n ℂ} (hX : X.IsHermitian) (W : Matrix n n ℂ) (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (d : n → ℝ) (h : X = W * diagonal (fun p => (d p : ℂ)) * Wᴴ)
    (g : ℝ → ℝ) : ∑ i, g (hX.eigenvalues i) = ∑ p, g (d p) := by
  have e1 : ∑ i, g (hX.eigenvalues i) =
      (Multiset.map g (Multiset.map hX.eigenvalues Finset.univ.val)).sum := by
    rw [Multiset.map_map]; rfl
  have e2 : ∑ p, g (d p) = (Multiset.map g (Multiset.map d Finset.univ.val)).sum := by
    rw [Multiset.map_map]; rfl
  rw [e1, e2, eig_ms hX W hW1 hW2 d h]

lemma spec' {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix n n ℂ)ᴴ := spec hX

/-- `Σ g(eig(A ⊗ B)) = Σ_{i,j} g(λ_i μ_j)` -/
lemma sum_eig_kron {A : Matrix n n ℂ} {B : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (A ⊗ₖ B).IsHermitian) (g : ℝ → ℝ) :
    ∑ p, g (hAB.eigenvalues p) = ∑ i, ∑ j, g (hA.eigenvalues i * hB.eigenvalues j) := by
  set U := (hA.eigenvectorUnitary : Matrix n n ℂ)
  set V := (hB.eigenvectorUnitary : Matrix m m ℂ)
  have hU1 : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hV1 : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  have hV2 : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  set W := U ⊗ₖ V
  have hW1 : Wᴴ * W = 1 := by
    simp only [W, conjTranspose_kronecker, ← mul_kronecker_mul, hU1, hV1, one_kronecker_one]
  have hW2 : W * Wᴴ = 1 := by
    simp only [W, conjTranspose_kronecker, ← mul_kronecker_mul, hU2, hV2, one_kronecker_one]
  have h : A ⊗ₖ B = W * diagonal (fun p : n × m =>
      ((hA.eigenvalues p.1 * hB.eigenvalues p.2 : ℝ) : ℂ)) * Wᴴ := by
    conv_lhs => rw [spec' hA, spec' hB]
    rw [mul_kronecker_mul, mul_kronecker_mul, diagonal_kronecker_diagonal]
    simp only [W, conjTranspose_kronecker]
    push_cast
    rfl
  rw [sum_eig hAB W hW1 hW2 _ h g, Fintype.sum_prod_type]

end X6PI


/-! X6: Schatten norms, entropy and operator norm of Kronecker products of densities. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Kronecker Matrix.Norms.L2Operator

namespace X6PI

open QAlgorithms Matrix X6KN
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P63 (schatten eigen)

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma sum_eigen {X : Matrix n n ℂ} (hX : X.IsHermitian) (g : ℝ → ℝ) :
    ∑ j, g (eigen X j) = ∑ i, g (hX.eigenvalues i) := by
  have e : ∀ j, eigen X j = hX.eigenvalues₀ j := by
    intro j
    simp only [eigen, ascEigenvalues, dif_pos hX, Fin.rev_rev]
  simp only [e, Matrix.IsHermitian.eigenvalues]
  exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun j => g (hX.eigenvalues₀ j))).symm

lemma schatten_eq {X : Matrix n n ℂ} (hX : X.IsHermitian) (q : ℝ) :
    schatten q X = (∑ i, hX.eigenvalues i ^ q) ^ (1 / q) := by
  unfold schatten
  rw [sum_eigen hX (fun x => x ^ q)]

lemma kron_dens {A : Matrix n n ℂ} {B : Matrix m m ℂ} (hA : IsDensityMatrix A)
    (hB : IsDensityMatrix B) : IsDensityMatrix (A ⊗ₖ B) :=
  ⟨hA.1.kronecker hB.1, by rw [Matrix.trace_kronecker, hA.2, hB.2, one_mul]⟩

lemma schatten_kron {A : Matrix n n ℂ} {B : Matrix m m ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {q : ℝ} (hq : 0 < q) : schatten q (A ⊗ₖ B) = schatten q A * schatten q B := by
  have hAB : (A ⊗ₖ B).PosSemidef := hA.kronecker hB
  rw [schatten_eq hAB.1, schatten_eq hA.1, schatten_eq hB.1,
    sum_eig_kron hA.1 hB.1 hAB.1 (fun x => x ^ q)]
  have h0 := hA.eigenvalues_nonneg
  have h1 := hB.eigenvalues_nonneg
  simp only [Real.mul_rpow (h0 _) (h1 _), ← Finset.mul_sum, ← Finset.sum_mul]
  rw [Real.mul_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (h0 i) _)
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (h1 i) _)]

lemma ent_eig {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    entropy ρ = ∑ i, Real.negMulLog (hρ.eigenvalues i) := by
  unfold entropy
  have hU := Unitary.star_mul_self_of_mem hρ.eigenvectorUnitary.2
  have hc : cfc (fun x : ℝ => x * Real.log x) ρ = (hρ.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => (((hρ.eigenvalues i) * Real.log (hρ.eigenvalues i) : ℝ) : ℂ)) *
      star (hρ.eigenvectorUnitary : Matrix n n ℂ) := by
    rw [hρ.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  rw [hc, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.negMulLog]

lemma eig_sum1 {ρ : Matrix n n ℂ} (hρ : IsDensityMatrix ρ) : ∑ i, hρ.1.1.eigenvalues i = 1 :=
  (eig_bounds hρ).2

lemma ent_kron {A : Matrix n n ℂ} {B : Matrix m m ℂ} (hA : IsDensityMatrix A)
    (hB : IsDensityMatrix B) : entropy (A ⊗ₖ B) = entropy A + entropy B := by
  have hAB := kron_dens hA hB
  rw [ent_eig hAB.1.1, ent_eig hA.1.1, ent_eig hB.1.1,
    sum_eig_kron hA.1.1 hB.1.1 hAB.1.1 Real.negMulLog]
  simp only [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [eig_sum1 hA, eig_sum1 hB]; ring

/-- `‖A‖ ‖B‖ ≤ ‖A ⊗ B‖` for the l2 operator norm -/
lemma norm_kron_ge (A : Matrix n n ℂ) (B : Matrix m m ℂ) : ‖A‖ * ‖B‖ ≤ ‖A ⊗ₖ B‖ := by
  have key : ∀ x : n → ℂ, ∀ y : m → ℂ, √(nsq (A *ᵥ x)) * √(nsq (B *ᵥ y)) ≤
      ‖A ⊗ₖ B‖ * (√(nsq x) * √(nsq y)) := by
    intro x y
    set xy : n × m → ℂ := fun p => x p.1 * y p.2
    have h1 : (A ⊗ₖ B) *ᵥ xy = fun p => (A *ᵥ x) p.1 * (B *ᵥ y) p.2 := by
      funext p
      simp only [mulVec, dotProduct, kroneckerMap_apply, xy, Fintype.sum_prod_type,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (f := fun x_1 i => A p.1 i * x i * (B p.2 x_1 * y x_1))]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have hn : ∀ (u : n → ℂ) (v : m → ℂ), nsq (fun p : n × m => u p.1 * v p.2) = nsq u * nsq v := by
      intro u v
      simp only [nsq, norm_mul, mul_pow, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    have h3 := N3 (A ⊗ₖ B) xy
    rw [h1, hn, hn] at h3
    have := Real.sqrt_le_sqrt h3
    rwa [Real.sqrt_mul (nsq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_mul (nsq_nonneg _)] at this
  -- approximate the operator norms
  rcases (norm_nonneg A).eq_or_lt with hA0 | hApos
  · rw [← hA0, zero_mul]; exact norm_nonneg _
  rcases (norm_nonneg B).eq_or_lt with hB0 | hBpos
  · rw [← hB0, mul_zero]; exact norm_nonneg _
  have approx : ∀ {k : Type} [Fintype k] [DecidableEq k] (M : Matrix k k ℂ) (r : ℝ), r < ‖M‖ →
      ∃ x : k → ℂ, √(nsq x) < 1 ∧ r < √(nsq (M *ᵥ x)) := by
    intro k _ _ M r hr
    rw [Matrix.l2_opNorm_def] at hr
    obtain ⟨x, hx1, hx2⟩ := ContinuousLinearMap.exists_lt_apply_of_lt_opNorm _ hr
    refine ⟨x.ofLp, ?_, ?_⟩
    · have e : (WithLp.toLp 2 x.ofLp : EuclideanSpace ℂ k) = x := rfl
      rw [← e, norm_toLp] at hx1; exact hx1
    · have e : ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := k) (n := k)).trans
          LinearMap.toContinuousLinearMap M) x = WithLp.toLp 2 (M *ᵥ x.ofLp) := rfl
      rw [e, norm_toLp] at hx2; exact hx2
  by_contra hlt
  push Not at hlt
  -- choose r < ‖A‖, s < ‖B‖ with r * s > ‖A ⊗ B‖
  obtain ⟨t, ht1, ht2, ht0⟩ : ∃ t : ℝ, t < 1 ∧ ‖A ⊗ₖ B‖ < (t * ‖A‖) * (t * ‖B‖) ∧ 0 < t := by
    have hc : Filter.Tendsto (fun t : ℝ => (t * ‖A‖) * (t * ‖B‖)) (nhds 1)
        (nhds ((1 * ‖A‖) * (1 * ‖B‖))) := by
      exact ((continuous_id.mul continuous_const).mul (continuous_id.mul continuous_const)).tendsto 1
    simp only [one_mul] at hc
    have hev := hc.eventually (lt_mem_nhds hlt)
    have hl : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio 1), ‖A ⊗ₖ B‖ < t * ‖A‖ * (t * ‖B‖) :=
      nhdsWithin_le_nhds hev
    have hp : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio 1), (0 : ℝ) < t :=
      nhdsWithin_le_nhds (lt_mem_nhds one_pos)
    obtain ⟨t, ⟨ht, ht'⟩, ht0⟩ := ((hl.and self_mem_nhdsWithin).and hp).exists
    exact ⟨t, ht', ht, ht0⟩
  have htA : t * ‖A‖ < ‖A‖ := by nlinarith
  have htB : t * ‖B‖ < ‖B‖ := by nlinarith
  obtain ⟨x, hx1, hx2⟩ := approx A _ htA
  obtain ⟨y, hy1, hy2⟩ := approx B _ htB
  have hk := key x y
  have hxy : √(nsq x) * √(nsq y) ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (nsq x), Real.sqrt_nonneg (nsq y)]
  have : (t * ‖A‖) * (t * ‖B‖) < √(nsq (A *ᵥ x)) * √(nsq (B *ᵥ y)) :=
    mul_lt_mul'' hx2 hy2 (by positivity) (by positivity)
  nlinarith [norm_nonneg (A ⊗ₖ B)]

end X6PI


/-! X6: tensor products of Kraus channels. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Kronecker

namespace X6PI

open QAlgorithms Matrix
open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

variable {A B K L : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

lemma kraus_single (E : K → Matrix A A ℂ) (c d a b : A) :
    krausApply E (Matrix.single c d 1) a b = ∑ k, E k a c * star (E k b d) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma ts_kraus (E : K → Matrix A A ℂ) (F : L → Matrix B B ℂ) :
    tensorSuperop (krausApply E) (krausApply F) =
      krausApply (fun kl : K × L => E kl.1 ⊗ₖ F kl.2) := by
  funext X
  ext a b
  simp only [tensorSuperop, kraus_single]
  have hterm : ∀ i j : A × B, X i j * (∑ k, E k a.1 i.1 * star (E k b.1 j.1)) *
      (∑ l, F l a.2 i.2 * star (F l b.2 j.2)) = ∑ kl : K × L,
        (E kl.1 a.1 i.1 * F kl.2 a.2 i.2) * X i j * star (E kl.1 b.1 j.1 * F kl.2 b.2 j.2) := by
    intro i j
    rw [Fintype.sum_prod_type, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_mul']; ring
  simp only [hterm]
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    kroneckerMap_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun kl _ => Finset.sum_comm

lemma sum_kron {ι κ : Type} [Fintype ι] [Fintype κ] (X : ι → Matrix A A ℂ) (Y : κ → Matrix B B ℂ) :
    (∑ i, X i) ⊗ₖ (∑ j, Y j) = ∑ ij : ι × κ, X ij.1 ⊗ₖ Y ij.2 := by
  ext a b
  simp only [kroneckerMap_apply, Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]

lemma kron_family (E : K → Matrix A A ℂ) (F : L → Matrix B B ℂ) (hE : IsKrausFamily E)
    (hF : IsKrausFamily F) : IsKrausFamily (fun kl : K × L => E kl.1 ⊗ₖ F kl.2) := by
  unfold IsKrausFamily at *
  simp only [conjTranspose_kronecker, ← mul_kronecker_mul]
  rw [← sum_kron (fun k => (E k)ᴴ * E k) (fun l => (F l)ᴴ * F l), hE, hF, one_kronecker_one]

lemma kraus_kron (E : K → Matrix A A ℂ) (F : L → Matrix B B ℂ) (ρ : Matrix A A ℂ)
    (σ : Matrix B B ℂ) : krausApply (fun kl : K × L => E kl.1 ⊗ₖ F kl.2) (ρ ⊗ₖ σ) =
      krausApply E ρ ⊗ₖ krausApply F σ := by
  simp only [krausApply, conjTranspose_kronecker, ← mul_kronecker_mul]
  rw [sum_kron]

end X6PI


/-! X6: product inputs give `ν_p(Φ)ν_p(Ψ) ≤ ν_p(Φ⊗Ψ)` and `ν_H(Φ⊗Ψ) ≤ ν_H(Φ)+ν_H(Ψ)`. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Kronecker ENNReal Matrix.Norms.L2Operator

namespace X6PI

open QAlgorithms Matrix X6KN
open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P63 (schatten)
open QAlgorithms.Papers.Independent.Support50.P31

lemma prod_sup (S T U : Set ℝ) (hS : S.Nonempty) (hT : T.Nonempty)
    (hS0 : ∀ s ∈ S, 0 ≤ s) (hT0 : ∀ t ∈ T, 0 ≤ t) (hSb : BddAbove S) (hTb : BddAbove T)
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t ≤ sSup U) : sSup S * sSup T ≤ sSup U := by
  obtain ⟨s0, hs0⟩ := hS
  obtain ⟨t0, ht0⟩ := hT
  have hU0 : 0 ≤ sSup U := (mul_nonneg (hS0 s0 hs0) (hT0 t0 ht0)).trans (h s0 hs0 t0 ht0)
  have hT0' : 0 ≤ sSup T := (hT0 t0 ht0).trans (le_csSup hTb ht0)
  rcases hT0'.eq_or_lt with hz | hpos
  · rw [← hz, mul_zero]; exact hU0
  have key : ∀ s ∈ S, s * sSup T ≤ sSup U := by
    intro s hs
    rcases (hS0 s hs).eq_or_lt with hz | hspos
    · rw [← hz, zero_mul]; exact hU0
    have : sSup T ≤ sSup U / s := csSup_le ⟨t0, ht0⟩ fun t ht => by
      rw [le_div_iff₀ hspos, mul_comm]; exact h s hs t ht
    rwa [le_div_iff₀ hspos, mul_comm] at this
  have : sSup S ≤ sSup U / sSup T := csSup_le ⟨s0, hs0⟩ fun s hs => by
    rw [le_div_iff₀ hpos]; exact key s hs
  rwa [le_div_iff₀ hpos] at this

variable {n : Type} [Fintype n] [DecidableEq n]

lemma schatten_nonneg (q : ℝ) {X : Matrix n n ℂ} (hX : X.PosSemidef) : 0 ≤ schatten q X := by
  rw [schatten_eq hX.1]
  exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hX.eigenvalues_nonneg i) _) _

lemma schatten_le_one {ρ : Matrix n n ℂ} (hρ : IsDensityMatrix ρ) {q : ℝ} (hq : 1 ≤ q) :
    schatten q ρ ≤ 1 := by
  rw [schatten_eq hρ.1.1]
  obtain ⟨h0, hs⟩ := eig_bounds hρ
  have h1 : ∀ i, hρ.1.1.eigenvalues i ≤ 1 := fun i => by
    rw [← hs]; exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  apply Real.rpow_le_one
  · exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (h0 i) _
  · rw [← hs]
    refine Finset.sum_le_sum fun i _ => ?_
    rcases (h0 i).eq_or_lt with h | h
    · rw [← h, Real.zero_rpow (by linarith)]
    · calc hρ.1.1.eigenvalues i ^ q ≤ hρ.1.1.eigenvalues i ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge h (h1 i) hq
        _ = _ := Real.rpow_one _
  · exact one_div_nonneg.mpr (by linarith)

lemma ent_nonneg {ρ : Matrix n n ℂ} (hρ : IsDensityMatrix ρ) : 0 ≤ entropy ρ := by
  rw [ent_eig hρ.1.1]
  obtain ⟨h0, hs⟩ := eig_bounds hρ
  refine Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (h0 i) ?_
  rw [← hs]; exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem main [Nonempty I] [Nonempty J] {K L : Type} [Fintype K] [DecidableEq K] [Fintype L]
    [DecidableEq L] (E : K → Matrix I I ℂ) (F : L → Matrix J J ℂ) (hE : IsKrausFamily E)
    (hF : IsKrausFamily F) :
    (∀ p : ℝ≥0∞, 1 ≤ p → nuP p (krausApply E) * nuP p (krausApply F) ≤
      nuP p (tensorSuperop (krausApply E) (krausApply F))) ∧
    nuH (tensorSuperop (krausApply E) (krausApply F)) ≤ nuH (krausApply E) + nuH (krausApply F) := by
  rw [ts_kraus]
  set G := fun kl : K × L => E kl.1 ⊗ₖ F kl.2
  have hG : IsKrausFamily G := kron_family E F hE hF
  obtain ⟨i0⟩ := (inferInstance : Nonempty I)
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  have he : ∀ {m : Type} [Fintype m] [DecidableEq m] (x : m), IsDensityMatrix
      (vecMulVec (Pi.single x (1 : ℂ)) (star (Pi.single x (1 : ℂ)))) := by
    intro m _ _ x
    refine pure_dens _ ?_
    simp only [nsq]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have dI : ∃ ρ : Matrix I I ℂ, IsDensityMatrix ρ := ⟨_, he i0⟩
  have dJ : ∃ ρ : Matrix J J ℂ, IsDensityMatrix ρ := ⟨_, he j0⟩
  have dIJ : ∃ ρ : Matrix (I × J) (I × J) ℂ, IsDensityMatrix ρ := ⟨_, he (i0, j0)⟩
  refine ⟨fun p hp => ?_, ?_⟩
  · unfold nuP
    by_cases htop : p = ⊤
    · simp only [if_pos htop]
      have bdd : ∀ {m : Type} [Fintype m] [DecidableEq m] {R : Type} [Fintype R] [DecidableEq R]
          (H : R → Matrix m m ℂ), IsKrausFamily H → BddAbove (Set.range fun X :
            {X : Matrix m m ℂ // IsDensityMatrix X} => specNorm (krausApply H X.val)) := by
        intro m _ _ R _ _ H hH
        exact ⟨1, by rintro _ ⟨X, rfl⟩; exact norm_density_le (kraus_dens H hH X.2)⟩
      refine prod_sup _ _ _ ?_ ?_ ?_ ?_ (bdd E hE) (bdd F hF) ?_
      · obtain ⟨ρ, hρ⟩ := dI; exact ⟨_, ⟨ρ, hρ⟩, rfl⟩
      · obtain ⟨ρ, hρ⟩ := dJ; exact ⟨_, ⟨ρ, hρ⟩, rfl⟩
      · rintro _ ⟨X, rfl⟩; exact norm_nonneg _
      · rintro _ ⟨X, rfl⟩; exact norm_nonneg _
      · rintro _ ⟨ρ, rfl⟩ _ ⟨σ, rfl⟩
        calc specNorm (krausApply E ρ.val) * specNorm (krausApply F σ.val)
            ≤ specNorm (krausApply E ρ.val ⊗ₖ krausApply F σ.val) := norm_kron_ge _ _
          _ = specNorm (krausApply G (ρ.val ⊗ₖ σ.val)) := by rw [kraus_kron]
          _ ≤ _ := le_csSup (bdd G hG) ⟨⟨_, kron_dens ρ.2 σ.2⟩, rfl⟩
    · simp only [if_neg htop]
      unfold Papers.Independent.Gap48.P03.maximumOutputPNorm
      have hq : 1 ≤ p.toReal := by
        have := ENNReal.toReal_mono htop hp
        simpa using this
      have bdd : ∀ {m : Type} [Fintype m] [DecidableEq m] {R : Type} [Fintype R] [DecidableEq R]
          (H : R → Matrix m m ℂ), IsKrausFamily H → BddAbove {s | ∃ rho : Matrix m m ℂ,
            IsDensityMatrix rho ∧ s = schatten p.toReal (krausApply H rho)} := by
        intro m _ _ R _ _ H hH
        exact ⟨1, by rintro _ ⟨X, hX, rfl⟩; exact schatten_le_one (kraus_dens H hH hX) hq⟩
      refine prod_sup _ _ _ ?_ ?_ ?_ ?_ (bdd E hE) (bdd F hF) ?_
      · obtain ⟨ρ, hρ⟩ := dI; exact ⟨_, ρ, hρ, rfl⟩
      · obtain ⟨ρ, hρ⟩ := dJ; exact ⟨_, ρ, hρ, rfl⟩
      · rintro _ ⟨X, hX, rfl⟩; exact schatten_nonneg _ (kraus_dens E hE hX).1
      · rintro _ ⟨X, hX, rfl⟩; exact schatten_nonneg _ (kraus_dens F hF hX).1
      · rintro _ ⟨ρ, hρ, rfl⟩ _ ⟨σ, hσ, rfl⟩
        rw [← schatten_kron (kraus_dens E hE hρ).1 (kraus_dens F hF hσ).1 (by linarith),
          ← kraus_kron]
        exact le_csSup (bdd G hG) ⟨_, kron_dens hρ hσ, rfl⟩
  · unfold nuH
    have bddb : ∀ {m : Type} [Fintype m] [DecidableEq m] {R : Type} [Fintype R] [DecidableEq R]
        (H : R → Matrix m m ℂ), IsKrausFamily H → BddBelow (Set.range fun X :
          {X : Matrix m m ℂ // IsDensityMatrix X} => entropy (krausApply H X.val)) := by
      intro m _ _ R _ _ H hH
      exact ⟨0, by rintro _ ⟨X, rfl⟩; exact ent_nonneg (kraus_dens H hH X.2)⟩
    set c := sInf (Set.range fun X : {X : Matrix (I × J) (I × J) ℂ // IsDensityMatrix X} =>
      entropy (krausApply G X.val))
    have step : ∀ ρ : Matrix I I ℂ, IsDensityMatrix ρ → ∀ σ : Matrix J J ℂ, IsDensityMatrix σ →
        c ≤ entropy (krausApply E ρ) + entropy (krausApply F σ) := by
      intro ρ hρ σ hσ
      rw [← ent_kron (kraus_dens E hE hρ) (kraus_dens F hF hσ), ← kraus_kron]
      exact csInf_le (bddb G hG) ⟨⟨_, kron_dens hρ hσ⟩, rfl⟩
    obtain ⟨ρ0, hρ0⟩ := dI
    obtain ⟨σ0, hσ0⟩ := dJ
    have h1 : ∀ σ : Matrix J J ℂ, IsDensityMatrix σ →
        c - entropy (krausApply F σ) ≤ sInf (Set.range fun X : {X : Matrix I I ℂ //
          IsDensityMatrix X} => entropy (krausApply E X.val)) := by
      intro σ hσ
      refine le_csInf ⟨_, ⟨ρ0, hρ0⟩, rfl⟩ ?_
      rintro _ ⟨ρ, rfl⟩
      have := step ρ.val ρ.2 σ hσ
      linarith
    have h2 : c - sInf (Set.range fun X : {X : Matrix I I ℂ //
          IsDensityMatrix X} => entropy (krausApply E X.val)) ≤
        sInf (Set.range fun X : {X : Matrix J J ℂ // IsDensityMatrix X} =>
          entropy (krausApply F X.val)) := by
      refine le_csInf ⟨_, ⟨σ0, hσ0⟩, rfl⟩ ?_
      rintro _ ⟨σ, rfl⟩
      have := h1 σ.val σ.2
      linarith
    linarith

end X6PI


open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P31
open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)
open scoped ENNReal

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (Phi : Superop I I) (Psi : Superop J J) (hPhi : IsChannel Phi) (hPsi : IsChannel Psi) :
    (∀ p : ℝ≥0∞, 1 ≤ p → nuP p Phi * nuP p Psi ≤ nuP p (tensorSuperop Phi Psi)) ∧
      nuH (tensorSuperop Phi Psi) ≤ nuH Phi + nuH Psi := by
  obtain ⟨m, E, hE, hP⟩ := hPhi
  obtain ⟨m', F, hF, hQ⟩ := hPsi
  obtain rfl : Phi = krausApply E := funext hP
  obtain rfl : Psi = krausApply F := funext hQ
  exact X6PI.main E F hE hF
