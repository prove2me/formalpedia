-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P31.idealChannelNormEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:46:30.736509+00:00
-- url     : https://prove2.me/submissions/8debfc33-beb0-403f-b110-3b37ecf380d7

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


/-! X6: pointwise spectral bounds for near-pure densities. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

namespace X6NP

open QAlgorithms Matrix X6KN X6PI Real
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

variable {I : Type} [Fintype I] [DecidableEq I]

lemma norm_unitary_le (U : Matrix I I ℂ) (hU : Uᴴ * U = 1) : ‖U‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [hU] at h
  have h1 : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
    have := N1 (1 : Matrix I I ℂ) zero_le_one (fun x => by simp)
    simpa using this
  nlinarith [norm_nonneg U]

/-- the operator norm of a density is its largest eigenvalue -/
lemma spec_max [Nonempty I] {σ : Matrix I I ℂ} (hσ : IsDensityMatrix σ) :
    ∃ i, ‖σ‖ = hσ.1.1.eigenvalues i ∧ ∀ j, hσ.1.1.eigenvalues j ≤ hσ.1.1.eigenvalues i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ hσ.1.1.eigenvalues Finset.univ_nonempty
  refine ⟨i, le_antisymm ?_ ?_, fun j => hi j (Finset.mem_univ j)⟩
  · set M := hσ.1.1.eigenvalues i
    have h0 := hσ.1.eigenvalues_nonneg
    set U := (hσ.1.1.eigenvectorUnitary : Matrix I I ℂ)
    have hU1 : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hσ.1.1.eigenvectorUnitary.2
    have hU2 : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hσ.1.1.eigenvectorUnitary.2
    have hUn := norm_unitary_le U hU1
    have hUs : ‖Uᴴ‖ ≤ 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]; exact hUn
    have hD : ‖diagonal (fun k => ((hσ.1.1.eigenvalues k : ℝ) : ℂ))‖ ≤ M := by
      have hM0 : 0 ≤ M := h0 i
      have := N1 (diagonal (fun k => ((hσ.1.1.eigenvalues k : ℝ) : ℂ))) (sq_nonneg M) (fun x => by
        simp only [nsq, mulVec_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
          Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        rw [sq_abs]
        exact pow_le_pow_left₀ (h0 k) (hi k (Finset.mem_univ k)) 2)
      rwa [Real.sqrt_sq hM0] at this
    calc ‖σ‖ = ‖U * diagonal (fun k => ((hσ.1.1.eigenvalues k : ℝ) : ℂ)) * Uᴴ‖ := by
          rw [← X6PI.spec' hσ.1.1]
      _ ≤ ‖U‖ * ‖diagonal (fun k => ((hσ.1.1.eigenvalues k : ℝ) : ℂ))‖ * ‖Uᴴ‖ :=
          (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
            (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ 1 * M * 1 := by gcongr; linarith [h0 i]
      _ = M := by ring
  · set u := ⇑(hσ.1.1.eigenvectorBasis i)
    have hu := nsq_basis hσ.1.1 i
    have h3 := N3 σ u
    rw [hσ.1.1.mulVec_eigenvectorBasis i, hu, mul_one] at h3
    have : nsq ((hσ.1.1.eigenvalues i : ℂ) • u) = hσ.1.1.eigenvalues i ^ 2 := by
      have e : (hσ.1.1.eigenvalues i • u : I → ℂ) = ((hσ.1.1.eigenvalues i : ℝ) : ℂ) • u := by
        funext a; simp [Complex.real_smul]
      rw [nsq_smul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h4 : nsq (hσ.1.1.eigenvalues i • u) = hσ.1.1.eigenvalues i ^ 2 := by
      have e : (hσ.1.1.eigenvalues i • u : I → ℂ) = ((hσ.1.1.eigenvalues i : ℝ) : ℂ) • u := by
        funext a; simp [Complex.real_smul]
      rw [e]; exact this
    rw [h4] at h3
    exact le_of_sq_le_sq (by simpa using h3) (norm_nonneg _) |> fun h => h

lemma rest_sum {σ : Matrix I I ℂ} (hσ : IsDensityMatrix σ) (i : I) :
    ∑ j ∈ Finset.univ.erase i, hσ.1.1.eigenvalues j = 1 - hσ.1.1.eigenvalues i := by
  have h := Finset.add_sum_erase Finset.univ hσ.1.1.eigenvalues (Finset.mem_univ i)
  rw [(eig_bounds hσ).2] at h
  linarith

lemma rest_le {σ : Matrix I I ℂ} (hσ : IsDensityMatrix σ) (i j : I) (hj : j ∈ Finset.univ.erase i) :
    hσ.1.1.eigenvalues j ≤ 1 - hσ.1.1.eigenvalues i := by
  rw [← rest_sum hσ i]
  exact Finset.single_le_sum (fun k _ => hσ.1.eigenvalues_nonneg k) hj

/-- `m ≤ ‖σ‖_p ≤ m + m (r/m)^p` -/
lemma schatten_bounds {σ : Matrix I I ℂ} (hσ : IsDensityMatrix σ) (i : I)
    (hmax : ∀ j, hσ.1.1.eigenvalues j ≤ hσ.1.1.eigenvalues i) (hm : 0 < hσ.1.1.eigenvalues i)
    {p : ℝ} (hp : 1 < p) :
    hσ.1.1.eigenvalues i ≤ schatten p σ ∧
      schatten p σ ≤ hσ.1.1.eigenvalues i + hσ.1.1.eigenvalues i *
        ((1 - hσ.1.1.eigenvalues i) / hσ.1.1.eigenvalues i) ^ p := by
  set m := hσ.1.1.eigenvalues i
  set r := 1 - m
  have h0 := hσ.1.eigenvalues_nonneg
  have hr0 : 0 ≤ r := by
    have := rest_sum hσ i
    show 0 ≤ 1 - hσ.1.1.eigenvalues i
    rw [← this]; exact Finset.sum_nonneg fun j _ => h0 j
  have hp0 : 0 < p := by linarith
  rw [schatten_eq hσ.1.1]
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => hσ.1.1.eigenvalues j ^ p)
    (Finset.mem_univ i)
  have hrest0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, hσ.1.1.eigenvalues j ^ p :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg (h0 j) _
  have hrest : ∑ j ∈ Finset.univ.erase i, hσ.1.1.eigenvalues j ^ p ≤ r ^ p := by
    calc ∑ j ∈ Finset.univ.erase i, hσ.1.1.eigenvalues j ^ p
        ≤ ∑ j ∈ Finset.univ.erase i, hσ.1.1.eigenvalues j * r ^ (p - 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hl := rest_le hσ i j hj
          rcases (h0 j).eq_or_lt with hz | hpos
          · rw [← hz, Real.zero_rpow hp0.ne']; simp
          · rw [show p = 1 + (p - 1) by ring, Real.rpow_add hpos, Real.rpow_one,
              show 1 + (p - 1) - 1 = p - 1 by ring]
            exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hpos.le hl (by linarith)) hpos.le
      _ = r * r ^ (p - 1) := by rw [← Finset.sum_mul, rest_sum hσ i]
      _ = r ^ p := by
          rcases hr0.eq_or_lt with hz | hpos
          · rw [← hz, zero_mul, Real.zero_rpow hp0.ne']
          · rw [← Real.rpow_one_add' hpos.le (by linarith)]; ring_nf
  constructor
  · have : m ^ p ≤ ∑ j, hσ.1.1.eigenvalues j ^ p := by
      rw [← hsplit]; linarith
    calc m = (m ^ p) ^ (1 / p) := by
          rw [← Real.rpow_mul hm.le, mul_one_div_cancel hp0.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hm.le _) this (by positivity)
  · have hs : ∑ j, hσ.1.1.eigenvalues j ^ p ≤ m ^ p * (1 + (r / m) ^ p) := by
      rw [← hsplit, mul_add, mul_one, Real.div_rpow hr0 hm.le,
        mul_div_cancel₀ _ (Real.rpow_pos_of_pos hm p).ne']
      linarith
    have hx : 0 ≤ (r / m) ^ p := Real.rpow_nonneg (div_nonneg hr0 hm.le) _
    calc (∑ j, hσ.1.1.eigenvalues j ^ p) ^ (1 / p)
        ≤ (m ^ p * (1 + (r / m) ^ p)) ^ (1 / p) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (h0 j) _) hs
            (by positivity)
      _ = m * (1 + (r / m) ^ p) ^ (1 / p) := by
          rw [Real.mul_rpow (Real.rpow_nonneg hm.le _) (by linarith), ← Real.rpow_mul hm.le,
            mul_one_div_cancel hp0.ne', Real.rpow_one]
      _ ≤ m * (1 + 1 / p * (r / m) ^ p) := by
          refine mul_le_mul_of_nonneg_left ?_ hm.le
          exact rpow_one_add_le_one_add_mul_self (by linarith) (by positivity)
            (by rw [div_le_one hp0]; linarith)
      _ ≤ m + m * (r / m) ^ p := by
          have : 1 / p * (r / m) ^ p ≤ (r / m) ^ p := by
            rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hp0]; nlinarith
          nlinarith

/-- `η(r) ≤ S(σ) ≤ η(r) + r (1 + log d)` -/
lemma ent_bounds {σ : Matrix I I ℂ} (hσ : IsDensityMatrix σ) (i : I)
    (hmax : ∀ j, hσ.1.1.eigenvalues j ≤ hσ.1.1.eigenvalues i) (hm : 0 < hσ.1.1.eigenvalues i) :
    negMulLog (1 - hσ.1.1.eigenvalues i) ≤ entropy σ ∧
      entropy σ ≤ negMulLog (1 - hσ.1.1.eigenvalues i) +
        (1 - hσ.1.1.eigenvalues i) * (1 + Real.log (Fintype.card I)) := by
  set m := hσ.1.1.eigenvalues i
  set r := 1 - m
  have h0 := hσ.1.eigenvalues_nonneg
  have hr0 : 0 ≤ r := by
    have := rest_sum hσ i
    show 0 ≤ 1 - hσ.1.1.eigenvalues i
    rw [← this]; exact Finset.sum_nonneg fun j _ => h0 j
  have hm1 : m ≤ 1 := by linarith
  rw [ent_eig hσ.1.1]
  rw [← Finset.add_sum_erase Finset.univ (fun j => negMulLog (hσ.1.1.eigenvalues j))
    (Finset.mem_univ i)]
  have hηm0 : 0 ≤ negMulLog m := Real.negMulLog_nonneg hm.le hm1
  have hηm1 : negMulLog m ≤ r := by
    have := Real.one_sub_inv_le_log_of_pos hm
    rw [negMulLog]
    have : m * (1 - m⁻¹) ≤ m * Real.log m := mul_le_mul_of_nonneg_left this hm.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hm.ne'] at this
    simp only [r]; linarith
  constructor
  · have : negMulLog r ≤ ∑ j ∈ Finset.univ.erase i, negMulLog (hσ.1.1.eigenvalues j) := by
      calc negMulLog r = ∑ j ∈ Finset.univ.erase i, -(hσ.1.1.eigenvalues j * Real.log r) := by
            rw [negMulLog, Finset.sum_neg_distrib, ← Finset.sum_mul, rest_sum hσ i]; ring
        _ ≤ _ := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [negMulLog]
            rcases (h0 j).eq_or_lt with hz | hpos
            · rw [← hz]; simp
            · have := Real.log_le_log hpos (rest_le hσ i j hj)
              nlinarith
    linarith
  · rcases hr0.eq_or_lt with hz | hrpos
    · have : ∀ j ∈ Finset.univ.erase i, hσ.1.1.eigenvalues j = 0 := by
        intro j hj
        exact le_antisymm (by have := rest_le hσ i j hj; simp only [r] at hz; linarith) (h0 j)
      rw [Finset.sum_congr rfl fun j hj => by rw [this j hj]]
      simp only [negMulLog_zero, Finset.sum_const_zero, add_zero]
      rw [← hz]; simp only [negMulLog_zero, zero_mul, add_zero]
      linarith
    · set d : ℝ := (Fintype.card I : ℝ)
      have hd : 1 ≤ d := by
        have : Nonempty I := ⟨i⟩
        simp only [d]; exact_mod_cast Fintype.card_pos
      set c := r / d
      have hc : 0 < c := div_pos hrpos (by linarith)
      have tang : ∀ x : ℝ, 0 ≤ x → negMulLog x ≤ -x * Real.log c - x + c := by
        intro x hx
        rcases hx.eq_or_lt with hz | hpos
        · rw [← hz]; simp [hc.le]
        · have := Real.one_sub_inv_le_log_of_pos (div_pos hpos hc)
          rw [Real.log_div hpos.ne' hc.ne', inv_div] at this
          have h2 := mul_le_mul_of_nonneg_left this hpos.le
          rw [mul_sub, mul_one, mul_div_cancel₀ _ hpos.ne'] at h2
          rw [negMulLog]; nlinarith
      have hcard : ((Finset.univ.erase i).card : ℝ) ≤ d := by
        simp only [d]; exact_mod_cast Finset.card_le_univ _
      have hsum : ∑ j ∈ Finset.univ.erase i, negMulLog (hσ.1.1.eigenvalues j) ≤
          negMulLog r + r * Real.log d := by
        calc ∑ j ∈ Finset.univ.erase i, negMulLog (hσ.1.1.eigenvalues j)
            ≤ ∑ j ∈ Finset.univ.erase i, (-hσ.1.1.eigenvalues j * Real.log c -
                hσ.1.1.eigenvalues j + c) := Finset.sum_le_sum fun j _ => tang _ (h0 j)
          _ = -r * Real.log c - r + (Finset.univ.erase i).card * c := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
                ← Finset.sum_mul, Finset.sum_neg_distrib, rest_sum hσ i]
          _ ≤ -r * Real.log c - r + d * c := by gcongr
          _ = negMulLog r + r * Real.log d := by
              have hd0 : d ≠ 0 := by linarith
              simp only [c, negMulLog]
              rw [Real.log_div hrpos.ne' hd0, mul_div_cancel₀ _ hd0]; ring
      nlinarith

end X6NP


/-! X6: abstract pure-input attainment for convex objectives over a compact parameter set. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

namespace X6PE

open QAlgorithms Matrix X6KN

variable {I : Type} [Fintype I] [DecidableEq I]

lemma pure_eq (v : EuclideanSpace ℂ I) : pureDensity v = vecMulVec (⇑v) (star ⇑v) := by
  ext a b; simp [pureDensity, vecMulVec_apply]

lemma nsq_of_norm {v : EuclideanSpace ℂ I} (hv : ‖v‖ = 1) : nsq (⇑v) = 1 := by
  have h := norm_toLp (⇑v)
  have e : (WithLp.toLp 2 (⇑v) : EuclideanSpace ℂ I) = v := rfl
  rw [e, hv] at h
  have h0 := nsq_nonneg (⇑v)
  have := congrArg (· ^ 2) h
  simp only [one_pow] at this
  rw [Real.sq_sqrt h0] at this
  exact this.symm

lemma pure_dens' {v : EuclideanSpace ℂ I} (hv : ‖v‖ = 1) : IsDensityMatrix (pureDensity v) := by
  rw [pure_eq]; exact pure_dens _ (nsq_of_norm hv)

lemma basis_norm {X : Matrix I I ℂ} (hX : X.IsHermitian) (i : I) : ‖hX.eigenvectorBasis i‖ = 1 :=
  hX.eigenvectorBasis.orthonormal.1 i

lemma continuous_pure : Continuous fun v : EuclideanSpace ℂ I => pureDensity v := by
  have hc : ∀ a : I, Continuous fun v : EuclideanSpace ℂ I => v a := fun a =>
    (EuclideanSpace.proj (𝕜 := ℂ) a).continuous
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [pureDensity, Matrix.of_apply]
  exact (hc a).mul (Complex.continuous_conj.comp (hc b))

lemma continuous_kraus {K : Type} [Fintype K] (A : K → Matrix I I ℂ) :
    Continuous fun X : Matrix I I ℂ => krausApply A X := by
  unfold krausApply
  refine continuous_finset_sum _ fun k _ => ?_
  exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

/-- Abstract attainment: a convex objective `g t` (for each parameter `t ∈ S`, `S` compact)
whose pointwise supremum is `F`, has a pure maximizer of `F ∘ Φ` over densities. -/
lemma attain_max [Nonempty I] {T : Type} [TopologicalSpace T] {S : Set T} (hS : IsCompact S)
    (hSne : S.Nonempty) (Φ : Matrix I I ℂ → Matrix I I ℂ)
    (g : T → Matrix I I ℂ → ℝ) (F : Matrix I I ℂ → ℝ)
    (hcont : Continuous fun p : EuclideanSpace ℂ I × T => g p.2 (Φ (pureDensity p.1)))
    (hle : ∀ t ∈ S, ∀ ρ, IsDensityMatrix ρ → g t (Φ ρ) ≤ F (Φ ρ))
    (heq : ∀ ρ, IsDensityMatrix ρ → ∃ t ∈ S, g t (Φ ρ) = F (Φ ρ))
    (hconv : ∀ t ∈ S, ∀ (w : I → ℝ) (u : I → EuclideanSpace ℂ I), (∀ i, 0 ≤ w i) →
      ∑ i, w i = 1 → (∀ i, ‖u i‖ = 1) →
      g t (Φ (∑ i, ((w i : ℝ) : ℂ) • pureDensity (u i))) ≤ ∑ i, w i * g t (Φ (pureDensity (u i)))) :
    ∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧
      ∀ ρ, IsDensityMatrix ρ → F (Φ ρ) ≤ F (Φ (pureDensity v)) := by
  obtain ⟨i0⟩ := (inferInstance : Nonempty I)
  obtain ⟨t1, ht1⟩ := hSne
  have hK := (isCompact_sphere (0 : EuclideanSpace ℂ I) 1).prod hS
  have hKne : (Metric.sphere (0 : EuclideanSpace ℂ I) 1 ×ˢ S).Nonempty :=
    ⟨(EuclideanSpace.single i0 1, t1), by simp, ht1⟩
  obtain ⟨⟨v0, t0⟩, ⟨hv0, ht0⟩, hmax⟩ := hK.exists_isMaxOn hKne hcont.continuousOn
  have hv0' : ‖v0‖ = 1 := by simpa using hv0
  refine ⟨v0, hv0', fun ρ hρ => ?_⟩
  obtain ⟨t, ht, hgt⟩ := heq ρ hρ
  have hspec : ρ = ∑ i, ((hρ.1.1.eigenvalues i : ℝ) : ℂ) • pureDensity (hρ.1.1.eigenvectorBasis i) := by
    conv_lhs => rw [spec_sum hρ.1.1]
    simp only [pure_eq]
  obtain ⟨h0, hs⟩ := eig_bounds hρ
  have hM : ∀ i, g t (Φ (pureDensity (hρ.1.1.eigenvectorBasis i))) ≤ g t0 (Φ (pureDensity v0)) :=
    fun i => hmax (a := (hρ.1.1.eigenvectorBasis i, t)) ⟨by simp [basis_norm], ht⟩
  calc F (Φ ρ) = g t (Φ ρ) := hgt.symm
    _ ≤ ∑ i, hρ.1.1.eigenvalues i * g t (Φ (pureDensity (hρ.1.1.eigenvectorBasis i))) := by
        conv_lhs => rw [hspec]
        exact hconv t ht _ _ h0 hs (basis_norm hρ.1.1)
    _ ≤ ∑ i, hρ.1.1.eigenvalues i * g t0 (Φ (pureDensity v0)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (h0 i)
    _ = g t0 (Φ (pureDensity v0)) := by rw [← Finset.sum_mul, hs, one_mul]
    _ ≤ F (Φ (pureDensity v0)) := hle t0 ht0 _ (pure_dens' hv0')

end X6PE


/-! X6: Peierls-type variational formula for convex trace functions and pure attainment. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

namespace X6PE

open QAlgorithms Matrix X6KN
open QAlgorithms.Papers.Independent.Information100.P63 (eigen)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- real quadratic form -/
def q (X : Matrix I I ℂ) (x : I → ℂ) : ℝ := (star x ⬝ᵥ X *ᵥ x).re

lemma q_sum (w : I → ℝ) (X : I → Matrix I I ℂ) (x : I → ℂ) :
    q (∑ i, ((w i : ℝ) : ℂ) • X i) x = ∑ i, w i * q (X i) x := by
  simp [q, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
    Complex.re_sum]

lemma q_nonneg {X : Matrix I I ℂ} (hX : X.PosSemidef) (x : I → ℂ) : 0 ≤ q X x :=
  (Complex.nonneg_iff.1 (hX.dotProduct_mulVec_nonneg x)).1

lemma q_spec {X : Matrix I I ℂ} (hX : X.IsHermitian) (x : I → ℂ) :
    q X x = ∑ k, hX.eigenvalues k *
      Complex.normSq ((star (hX.eigenvectorUnitary : Matrix I I ℂ) *ᵥ x) k) := by
  set U := (hX.eigenvectorUnitary : Matrix I I ℂ)
  set v := star U *ᵥ x
  have hUU : (star U)ᴴ = U := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hspec : X = U * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star U :=
    spec hX
  have : star x ⬝ᵥ X *ᵥ x =
      star v ⬝ᵥ Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) *ᵥ v := by
    conv_lhs => rw [hspec]
    simp only [v, Matrix.star_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hUU]
  rw [q, this]
  simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_apply]; simp [Complex.mul_re, Complex.mul_im]; ring

lemma q_eig {X : Matrix I I ℂ} (hX : X.IsHermitian) (j : I) :
    q X (hX.eigenvectorBasis j) = hX.eigenvalues j := by
  have hn : (star (⇑(hX.eigenvectorBasis j)) ⬝ᵥ ⇑(hX.eigenvectorBasis j)) = 1 := by
    have := hX.eigenvectorBasis.orthonormal.1 j
    have h2 : inner ℂ (hX.eigenvectorBasis j) (hX.eigenvectorBasis j) = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, this]; simp
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
    rw [← h2, dotProduct_comm]
  rw [q, hX.mulVec_eigenvectorBasis j, dotProduct_smul, hn]
  simp

lemma normSq_col (W : Matrix I I ℂ) (j : I) :
    ∑ k, Complex.normSq (W k j) = ((Wᴴ * W) j j).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_apply]; simp [Complex.mul_re]

lemma normSq_row (W : Matrix I I ℂ) (k : I) :
    ∑ j, Complex.normSq (W k j) = ((W * Wᴴ) k k).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_apply]; simp [Complex.mul_re]

/-- Peierls inequality: diagonal of a PSD matrix in any orthonormal basis vs its spectrum. -/
lemma peierls {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f) {X : Matrix I I ℂ} (hX : X.PosSemidef)
    {E : Matrix I I ℂ} (hE : Eᴴ * E = 1) :
    ∑ j, f (q X (Eᵀ j)) ≤ ∑ k, f (hX.1.eigenvalues k) := by
  set U := (hX.1.eigenvectorUnitary : Matrix I I ℂ)
  have hU2 : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hX.1.eigenvectorUnitary.2
  set W := star U * E
  have hW1 : Wᴴ * W = 1 := by
    simp only [W, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, hU2, Matrix.one_mul, hE]
  have hW2 : W * Wᴴ = 1 := mul_eq_one_comm.1 hW1
  have hcol : ∀ j k, (star U *ᵥ (Eᵀ j)) k = W k j := by
    intro j k; rfl
  have h0 := hX.eigenvalues_nonneg
  have step : ∀ j, f (q X (Eᵀ j)) ≤
      ∑ k, Complex.normSq (W k j) * f (hX.1.eigenvalues k) := by
    intro j
    have e : q X (Eᵀ j) = ∑ k, hX.1.eigenvalues k * Complex.normSq (W k j) := by
      rw [q_spec hX.1]; rfl
    rw [e]
    have := hf.map_sum_le (t := Finset.univ) (w := fun k => Complex.normSq (W k j))
      (p := fun k => hX.1.eigenvalues k) (fun k _ => Complex.normSq_nonneg _)
      (by rw [normSq_col, hW1]; simp) (fun k _ => h0 k)
    have e2 : ∑ k, hX.1.eigenvalues k * Complex.normSq (W k j) =
        ∑ k, Complex.normSq (W k j) • hX.1.eigenvalues k :=
      Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul, mul_comm]
    rw [e2]
    exact this.trans (le_of_eq (Finset.sum_congr rfl fun k _ => smul_eq_mul _ _))
  calc ∑ j, f (q X (Eᵀ j))
      ≤ ∑ j, ∑ k, Complex.normSq (W k j) * f (hX.1.eigenvalues k) :=
        Finset.sum_le_sum fun j _ => step j
    _ = ∑ k, (∑ j, Complex.normSq (W k j)) * f (hX.1.eigenvalues k) := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ = ∑ k, f (hX.1.eigenvalues k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [normSq_row, hW2]; simp

lemma sum_eigen' {X : Matrix I I ℂ} (hX : X.IsHermitian) (g : ℝ → ℝ) :
    ∑ j, g (eigen X j) = ∑ i, g (hX.eigenvalues i) := X6PI.sum_eigen hX g

/-- the unitary set is compact -/
lemma compact_unitary : IsCompact {E : Matrix I I ℂ | Eᴴ * E = 1} := by
  have hcl : IsClosed {E : Matrix I I ℂ | Eᴴ * E = 1} :=
    isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hsub : {E : Matrix I I ℂ | Eᴴ * E = 1} ⊆
      Set.pi Set.univ (fun _ : I => Set.pi Set.univ (fun _ : I => Metric.closedBall (0 : ℂ) 1)) := by
    intro E hE i _ j _
    simp only [Metric.mem_closedBall, dist_zero_right]
    have h1 := normSq_col E j
    rw [show Eᴴ * E = 1 from hE] at h1
    simp only [Matrix.one_apply_eq, Complex.one_re] at h1
    have h2 : Complex.normSq (E i j) ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun k => Complex.normSq (E k j))
        (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    rw [Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg (E i j)]
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hcl hsub

lemma continuous_coe : Continuous fun x : EuclideanSpace ℂ I => (⇑x : I → ℂ) :=
  continuous_pi fun a => (EuclideanSpace.proj (𝕜 := ℂ) a).continuous

lemma continuous_q {T : Type} [TopologicalSpace T] {X : T → Matrix I I ℂ} {x : T → I → ℂ}
    (hX : Continuous X) (hx : Continuous x) : Continuous fun t => q (X t) (x t) :=
  Complex.continuous_re.comp ((continuous_star.comp hx).dotProduct (hX.matrix_mulVec hx))

/-- pure attainment of the maximum of a convex trace function of the output -/
theorem trace_max [Nonempty I] {K : Type} [Fintype K] [DecidableEq K] (A : K → Matrix I I ℂ)
    (hA : IsKrausFamily A) {f : ℝ → ℝ} (hfc : Continuous f) (hf : ConvexOn ℝ (Set.Ici 0) f) :
    ∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧ ∀ ρ, IsDensityMatrix ρ →
      ∑ j, f (eigen (krausApply A ρ) j) ≤ ∑ j, f (eigen (krausApply A (pureDensity v)) j) := by
  refine attain_max compact_unitary ⟨1, by simp⟩ (krausApply A)
    (fun E X => ∑ j, f (q X (Eᵀ j))) (fun X => ∑ j, f (eigen X j)) ?_ ?_ ?_ ?_
  · refine continuous_finsetSum _ fun j _ => hfc.comp (continuous_q
      ((continuous_kraus A).comp (continuous_pure.comp continuous_fst)) ?_)
    exact continuous_pi fun i => (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
  · intro E hE ρ hρ
    have hσ := (kraus_dens A hA hρ).1
    rw [sum_eigen' hσ.1]
    exact peierls hf hσ hE
  · intro ρ hρ
    have hσ := (kraus_dens A hA hρ).1
    refine ⟨hσ.1.eigenvectorUnitary, Unitary.star_mul_self_of_mem hσ.1.eigenvectorUnitary.2, ?_⟩
    rw [sum_eigen' hσ.1]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact congrArg f (q_eig hσ.1 j)
  · intro E _ w u hw hs hu
    show ∑ j, f (q (krausApply A (∑ i, ((w i : ℝ) : ℂ) • pureDensity (u i))) (Eᵀ j)) ≤ _
    rw [kraus_sum]
    have hP : ∀ i, (krausApply A (pureDensity (u i))).PosSemidef := fun i =>
      (kraus_dens A hA (pure_dens' (hu i))).1
    calc ∑ j, f (q (∑ i, ((w i : ℝ) : ℂ) • krausApply A (pureDensity (u i))) (Eᵀ j))
        = ∑ j, f (∑ i, w i • q (krausApply A (pureDensity (u i))) (Eᵀ j)) := by
          simp only [q_sum, smul_eq_mul]
      _ ≤ ∑ j, ∑ i, w i • f (q (krausApply A (pureDensity (u i))) (Eᵀ j)) :=
          Finset.sum_le_sum fun j _ => hf.map_sum_le (fun i _ => hw i) hs
            (fun i _ => q_nonneg (hP i) _)
      _ = ∑ i, w i * ∑ j, f (q (krausApply A (pureDensity (u i))) (Eᵀ j)) := by
          rw [Finset.sum_comm]; simp only [smul_eq_mul, Finset.mul_sum]

end X6PE


/-! X6: pure-input attainment of the output-purity extrema (Amosov–Holevo–Werner §2). -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

namespace X6PE

open QAlgorithms Matrix X6KN
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P63 (schatten eigen)
open QAlgorithms.Papers.Independent.Support50.P31

variable {I : Type} [Fintype I] [DecidableEq I]

lemma nsq_sum (x : I → ℂ) (U : Matrix I I ℂ) (hU : U * Uᴴ = 1) :
    ∑ k, Complex.normSq ((star U *ᵥ x) k) = nsq x := by
  rw [nsq_eq_re]
  have hUU : (star U)ᴴ = U := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have : star x ⬝ᵥ x = star (star U *ᵥ x) ⬝ᵥ (star U *ᵥ x) := by
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hUU]
    rw [show U * star U = 1 from hU, Matrix.vecMul_one]
  rw [this]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_apply]; simp [Complex.mul_re]

lemma minEig_le {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (j : I) :
    minEigenvalue σ ≤ hσ.eigenvalues j := by
  unfold minEigenvalue ascEigenvalues
  have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨j⟩
  rw [dif_pos hpos, dif_pos hσ]
  show hσ.eigenvalues₀ (Fin.rev ⟨0, hpos⟩) ≤ hσ.eigenvalues₀ _
  apply hσ.eigenvalues₀_antitone
  rw [Fin.le_def]; simp only [Fin.val_rev]
  have := ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).isLt
  omega

lemma minEig_eq [Nonempty I] {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) :
    ∃ j, minEigenvalue σ = hσ.eigenvalues j := by
  have hpos : 0 < Fintype.card I := Fintype.card_pos
  refine ⟨Fintype.equivOfCardEq (Fintype.card_fin _) (Fin.rev ⟨0, hpos⟩), ?_⟩
  unfold minEigenvalue ascEigenvalues
  rw [dif_pos hpos, dif_pos hσ]
  simp [Matrix.IsHermitian.eigenvalues]

lemma q_lower {X : Matrix I I ℂ} (hX : X.IsHermitian) (x : I → ℂ) (hx : nsq x = 1) :
    minEigenvalue X ≤ q X x := by
  have hU : (hX.eigenvectorUnitary : Matrix I I ℂ) * (hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  have hs := nsq_sum x _ hU
  rw [hx] at hs
  rw [q_spec hX, ← mul_one (minEigenvalue X), ← hs, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (minEig_le hX k) (Complex.normSq_nonneg _)

lemma mem_sphere_iff {x : EuclideanSpace ℂ I} : x ∈ Metric.sphere (0 : EuclideanSpace ℂ I) 1 ↔
    ‖x‖ = 1 := by simp

variable {K : Type} [Fintype K] [DecidableEq K]

lemma lin_eq (A : K → Matrix I I ℂ) (x : EuclideanSpace ℂ I) (w : I → ℝ)
    (u : I → EuclideanSpace ℂ I) :
    q (krausApply A (∑ i, ((w i : ℝ) : ℂ) • pureDensity (u i))) ⇑x =
      ∑ i, w i * q (krausApply A (pureDensity (u i))) ⇑x := by
  rw [kraus_sum, q_sum]

theorem norm_max [Nonempty I] (A : K → Matrix I I ℂ) (hA : IsKrausFamily A) :
    ∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧ ∀ ρ, IsDensityMatrix ρ →
      ‖krausApply A ρ‖ ≤ ‖krausApply A (pureDensity v)‖ := by
  refine attain_max (isCompact_sphere (0 : EuclideanSpace ℂ I) 1)
    ⟨EuclideanSpace.single (Classical.arbitrary I) 1, by simp⟩ (krausApply A)
    (fun x X => q X ⇑x) (fun X => ‖X‖) ?_ ?_ ?_ ?_
  · exact continuous_q ((continuous_kraus A).comp (continuous_pure.comp continuous_fst))
      (continuous_coe.comp continuous_snd)
  · intro x hx ρ _
    have hx' := nsq_of_norm (mem_sphere_iff.1 hx)
    refine (Complex.re_le_norm _).trans ?_
    have := N2 (krausApply A ρ) ⇑x ⇑x
    rw [hx', Real.sqrt_one, mul_one, mul_one] at this
    exact this
  · intro ρ hρ
    have hσ := kraus_dens A hA hρ
    obtain ⟨i, hi, -⟩ := X6NP.spec_max hσ
    exact ⟨hσ.1.1.eigenvectorBasis i, mem_sphere_iff.2 (basis_norm _ i),
      by rw [q_eig hσ.1.1 i, hi]⟩
  · intro x _ w u _ _ _
    exact le_of_eq (lin_eq A x w u)

theorem minEig_min [Nonempty I] (A : K → Matrix I I ℂ) (hA : IsKrausFamily A) :
    ∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧ ∀ ρ, IsDensityMatrix ρ →
      minEigenvalue (krausApply A (pureDensity v)) ≤ minEigenvalue (krausApply A ρ) := by
  have := attain_max (isCompact_sphere (0 : EuclideanSpace ℂ I) 1)
    ⟨EuclideanSpace.single (Classical.arbitrary I) 1, by simp⟩ (krausApply A)
    (fun x X => -q X ⇑x) (fun X => -minEigenvalue X) ?_ ?_ ?_ ?_
  · obtain ⟨v, hv, h⟩ := this
    exact ⟨v, hv, fun ρ hρ => neg_le_neg_iff.1 (h ρ hρ)⟩
  · exact (continuous_q ((continuous_kraus A).comp (continuous_pure.comp continuous_fst))
      (continuous_coe.comp continuous_snd)).neg
  · intro x hx ρ hρ
    exact neg_le_neg (q_lower (kraus_dens A hA hρ).1.1 _ (nsq_of_norm (mem_sphere_iff.1 hx)))
  · intro ρ hρ
    have hσ := kraus_dens A hA hρ
    obtain ⟨i, hi⟩ := minEig_eq hσ.1.1
    exact ⟨hσ.1.1.eigenvectorBasis i, mem_sphere_iff.2 (basis_norm _ i),
      by rw [q_eig hσ.1.1 i, hi]⟩
  · intro x _ w u _ _ _
    refine le_of_eq ?_
    show -q _ _ = _
    rw [lin_eq A x w u, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring

lemma ent_eigen {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    entropy X = -∑ j, eigen X j * Real.log (eigen X j) := by
  rw [X6PI.ent_eig hX, sum_eigen' hX (fun t => t * Real.log t), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.negMulLog]

theorem main [Nonempty I] (Phi : Superop I I) (hPhi : IsChannel Phi) :
    (∀ p : ℝ≥0∞, 1 ≤ p → ∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧
      pPurity p (Phi (pureDensity v)) = nuP p Phi) ∧
    (∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧ entropy (Phi (pureDensity v)) = nuH Phi) ∧
    (∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧
      minEigenvalue (Phi (pureDensity v)) = nuMinus Phi) := by
  obtain ⟨m, A, hA, hΦ⟩ := hPhi
  have hP : Phi = krausApply A := funext hΦ
  subst hP
  refine ⟨fun p hp => ?_, ?_, ?_⟩
  · by_cases hpt : p = ⊤
    · subst hpt
      obtain ⟨v, hv, h⟩ := norm_max A hA
      refine ⟨v, hv, ?_⟩
      unfold pPurity nuP
      rw [if_pos rfl, if_pos rfl]
      refine (IsGreatest.csSup_eq ?_).symm
      refine ⟨⟨⟨_, pure_dens' hv⟩, rfl⟩, ?_⟩
      rintro _ ⟨X, rfl⟩
      exact h X.1 X.2
    · have hr : 1 ≤ p.toReal := by
        have := ENNReal.toReal_mono hpt hp
        simpa using this
      set r := p.toReal
      obtain ⟨v, hv, h⟩ := trace_max A hA (Real.continuous_rpow_const (by linarith))
        (convexOn_rpow hr)
      refine ⟨v, hv, ?_⟩
      unfold pPurity nuP
      rw [if_neg hpt, if_neg hpt]
      unfold QAlgorithms.Papers.Independent.Gap48.P03.maximumOutputPNorm
      refine (IsGreatest.csSup_eq ?_).symm
      refine ⟨⟨_, pure_dens' hv, rfl⟩, ?_⟩
      rintro _ ⟨ρ, hρ, rfl⟩
      unfold schatten
      have hσ := (kraus_dens A hA hρ).1
      have h0 : 0 ≤ ∑ j, eigen (krausApply A ρ) j ^ r := by
        rw [sum_eigen' hσ.1 (fun t => t ^ r)]
        exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hσ.eigenvalues_nonneg i) _
      exact Real.rpow_le_rpow h0 (h ρ hρ) (by positivity)
  · obtain ⟨v, hv, h⟩ := trace_max A hA Real.continuous_mul_log Real.convexOn_mul_log
    refine ⟨v, hv, ?_⟩
    unfold nuH
    refine (IsLeast.csInf_eq ?_).symm
    refine ⟨⟨⟨_, pure_dens' hv⟩, rfl⟩, ?_⟩
    rintro _ ⟨X, rfl⟩
    show _ ≤ entropy (krausApply A X.1)
    rw [ent_eigen (kraus_dens A hA X.2).1.1, ent_eigen (kraus_dens A hA (pure_dens' hv)).1.1]
    exact neg_le_neg (h X.1 X.2)
  · obtain ⟨v, hv, h⟩ := minEig_min A hA
    refine ⟨v, hv, ?_⟩
    unfold nuMinus
    refine (IsLeast.csInf_eq ?_).symm
    refine ⟨⟨⟨_, pure_dens' hv⟩, rfl⟩, ?_⟩
    rintro _ ⟨X, rfl⟩
    exact h X.1 X.2

end X6PE


/-! X6: spectral identities for `M Mᴴ` versus `Mᴴ M` and Gram matrices of Kraus outputs. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

namespace X6IC

open QAlgorithms Matrix X6KN X6PE

/-- trace functions vanishing at zero agree on `M Mᴴ` and `Mᴴ M` -/
lemma tf_comm {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) (h1 : (M * Mᴴ).IsHermitian)
    (h2 : (Mᴴ * M).IsHermitian) :
    ∑ i, f (h1.eigenvalues i) = ∑ k, f (h2.eigenvalues k) := by
  have key := Matrix.charpoly_mul_comm' M Mᴴ
  have h := congrArg Polynomial.roots key
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow, h1.roots_charpoly_eq_eigenvalues,
    h2.roots_charpoly_eq_eigenvalues] at h
  have h' := congrArg (fun s : Multiset ℂ => (s.map fun z => f z.re).sum) h
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton, Complex.zero_re, hf, smul_zero, zero_add,
    Multiset.map_map] at h'
  have e1 : ∀ {k : Type} (g : k → ℝ), ((fun z : ℂ => f z.re) ∘ RCLike.ofReal ∘ g) =
      fun i => f (g i) := by
    intro k g; funext i; simp
  rw [e1, e1] at h'
  exact h'

end X6IC


/-! X6: survival-probability formulas for Kraus maps and their ideal extensions. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate

namespace X6SF

open QAlgorithms Matrix X6KN

variable {n : Type} [Fintype n] [DecidableEq n]

lemma mul_vmv {m : Type} [Fintype m] (B : Matrix m n ℂ) (a b : n → ℂ) :
    B * vecMulVec a b = vecMulVec (B *ᵥ a) b := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma vmv_mul {m : Type} [Fintype m] (a : m → ℂ) (b : n → ℂ) (B : Matrix n n ℂ) :
    vecMulVec a b * B = vecMulVec a (b ᵥ* B) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma vmv_vmv (a b c d : n → ℂ) :
    vecMulVec a b * vecMulVec c d = (b ⬝ᵥ c) • vecMulVec a d := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, dotProduct, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma tr_vmv (a b : n → ℂ) : (vecMulVec a b).trace = b ⬝ᵥ a := by
  simp only [Matrix.trace, Matrix.diag, vecMulVec_apply, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma tr_pure (B : Matrix n n ℂ) (ψ : n → ℂ) :
    (vecMulVec ψ (star ψ) * (B * vecMulVec ψ (star ψ) * Bᴴ)).trace.re =
      ‖star ψ ⬝ᵥ (B *ᵥ ψ)‖ ^ 2 := by
  have e : ‖star ψ ⬝ᵥ (B *ᵥ ψ)‖ ^ 2 =
      ((star ψ ⬝ᵥ (B *ᵥ ψ)) * star (star ψ ⬝ᵥ (B *ᵥ ψ))).re := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [e]
  congr 1
  rw [mul_vmv B ψ (star ψ), vmv_mul (B *ᵥ ψ) (star ψ) Bᴴ, vmv_vmv, Matrix.trace_smul,
    tr_vmv, ← Matrix.star_mulVec, smul_eq_mul]
  congr 1
  rw [← star_dotProduct_star, star_star, dotProduct_comm]

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- `1 ⊗ A_k` -/
def Bk (A : K → Matrix I I ℂ) (k : K) : Matrix (J × I) (J × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then A k p.2 q.2 else 0

lemma ext_eq (A : K → Matrix I I ℂ) (X : Matrix (J × I) (J × I) ℂ) :
    idTensorSuperop (R := J) (krausApply A) X = ∑ k, Bk A k * X * (Bk A k)ᴴ := by
  ext p q
  simp only [idTensorSuperop, krausApply, Bk, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, ite_mul, zero_mul,
    apply_ite star, star_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma pd_eq {n : Type} (ψ : EuclideanSpace ℂ n) : pureDensity ψ = vecMulVec ψ.ofLp (star ψ.ofLp) := by
  ext a b; simp [pureDensity, vecMulVec_apply]

lemma flat_sum {n : Type} [Fintype n] [DecidableEq n] (B : K → Matrix n n ℂ)
    (ψ : EuclideanSpace ℂ n) :
    effectProb (pureDensity ψ) (∑ k, B k * pureDensity ψ * (B k)ᴴ) =
      ∑ k, ‖star ψ.ofLp ⬝ᵥ (B k *ᵥ ψ.ofLp)‖ ^ 2 := by
  unfold effectProb
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pd_eq, tr_pure]

lemma flat_kraus (A : K → Matrix I I ℂ) (v : EuclideanSpace ℂ I) :
    effectProb (pureDensity v) (krausApply A (pureDensity v)) =
      ∑ k, ‖star v.ofLp ⬝ᵥ (A k *ᵥ v.ofLp)‖ ^ 2 := flat_sum A v

lemma flat_ext (A : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ (J × I)) :
    effectProb (pureDensity ψ) (idTensorSuperop (R := J) (krausApply A) (pureDensity ψ)) =
      ∑ k, ‖star ψ.ofLp ⬝ᵥ (Bk A k *ᵥ ψ.ofLp)‖ ^ 2 := by
  rw [ext_eq]; exact flat_sum _ ψ

lemma Bk_dot (A : K → Matrix I I ℂ) (k : K) (ψ : J × I → ℂ) :
    star ψ ⬝ᵥ (Bk A k *ᵥ ψ) = ∑ j, star (fun a => ψ (j, a)) ⬝ᵥ (A k *ᵥ fun a => ψ (j, a)) := by
  simp only [dotProduct, mulVec, Bk, Matrix.of_apply, Fintype.sum_prod_type, Pi.star_apply,
    ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end X6SF


/-! X6: Gram-matrix comparison of `id ⊗ Φ` with `Φ` on pure inputs. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

namespace X6IC

open QAlgorithms Matrix X6KN X6PE

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

lemma tf_congr {n : Type} [Fintype n] [DecidableEq n] (f : ℝ → ℝ) {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (e : X = Y) :
    ∑ k, f (hX.eigenvalues k) = ∑ k, f (hY.eigenvalues k) := by
  subst e; rfl

lemma q_sum' {n : Type} [Fintype n] (w : J → ℝ) (X : J → Matrix n n ℂ) (x : n → ℂ) :
    q (∑ i, ((w i : ℝ) : ℂ) • X i) x = ∑ i, w i * q (X i) x := by
  simp [q, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
    Complex.re_sum]

/-- Peierls convexity of trace functions on PSD matrices -/
lemma tf_convex {n : Type} [Fintype n] [DecidableEq n] {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Set.Ici 0) f) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (G : J → Matrix n n ℂ) (hG : ∀ j, (G j).PosSemidef)
    (hS : (∑ j, ((w j : ℝ) : ℂ) • G j).PosSemidef) :
    ∑ k, f (hS.1.eigenvalues k) ≤ ∑ j, w j * ∑ k, f ((hG j).1.eigenvalues k) := by
  set E := (hS.1.eigenvectorUnitary : Matrix n n ℂ)
  have hE : Eᴴ * E = 1 := Unitary.star_mul_self_of_mem hS.1.eigenvectorUnitary.2
  calc ∑ k, f (hS.1.eigenvalues k)
      = ∑ k, f (∑ j, w j • q (G j) (Eᵀ k)) := by
        refine Finset.sum_congr rfl fun k _ => congrArg f ?_
        rw [← q_eig hS.1 k]
        show q _ (Eᵀ k) = _
        rw [q_sum']; rfl
    _ ≤ ∑ k, ∑ j, w j • f (q (G j) (Eᵀ k)) :=
        Finset.sum_le_sum fun k _ => hf.map_sum_le (fun j _ => hw j) hs
          (fun j _ => q_nonneg (hG j) _)
    _ = ∑ j, w j * ∑ k, f (q (G j) (Eᵀ k)) := by
        rw [Finset.sum_comm]; simp only [smul_eq_mul, Finset.mul_sum]
    _ ≤ ∑ j, w j * ∑ k, f ((hG j).1.eigenvalues k) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (peierls hf (hG j) hE) (hw j)

variable (A : K → Matrix I I ℂ)

lemma kraus_vmv (a b : I → ℂ) : krausApply A (vecMulVec a (star b)) = W A a * (W A b)ᴴ := by
  ext x y
  simp only [krausApply, W, Matrix.sum_apply, Matrix.mul_apply, vecMulVec_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, mulVec, dotProduct, Pi.star_apply, star_sum,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

def row (ψ : J × I → ℂ) (j : J) : I → ℂ := fun i => ψ (j, i)

def Mx (ψ : J × I → ℂ) : Matrix (J × I) K ℂ := Matrix.of fun p k => W A (row ψ p.1) p.2 k

lemma out_eq (ψ : EuclideanSpace ℂ (J × I)) :
    idTensorSuperop (R := J) (krausApply A) (pureDensity ψ) = Mx A ⇑ψ * (Mx A ⇑ψ)ᴴ := by
  ext p r
  have e : (Matrix.of fun i i' => pureDensity ψ (p.1, i) (r.1, i')) =
      vecMulVec (row (⇑ψ) p.1) (star (row (⇑ψ) r.1)) := by
    ext i i'; simp [pureDensity, vecMulVec_apply, row]
  simp only [idTensorSuperop, Matrix.of_apply]
  rw [e, kraus_vmv]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Mx, Matrix.of_apply]

lemma gram_eq (ψ : J × I → ℂ) :
    (Mx A ψ)ᴴ * Mx A ψ = ∑ j, (W A (row ψ j))ᴴ * W A (row ψ j) := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Mx, Matrix.of_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]

lemma W_smul (c : ℂ) (u : I → ℂ) : W A (c • u) = c • W A u := by
  ext a k; simp [W, Matrix.mulVec_smul]

lemma G_smul (c : ℝ) (u : I → ℂ) :
    (W A ((c : ℂ) • u))ᴴ * W A ((c : ℂ) • u) = ((c ^ 2 : ℝ) : ℂ) • ((W A u)ᴴ * W A u) := by
  rw [W_smul, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  simp [pow_two]

lemma W_zero : W A (0 : I → ℂ) = 0 := by ext a k; simp [W]

lemma pure_out (u : I → ℂ) : krausApply A (vecMulVec u (star u)) = W A u * (W A u)ᴴ :=
  kraus_vmv A u u

/-- normalisation of a row -/
def unitOf [Nonempty I] (r : I → ℂ) : I → ℂ :=
  if nsq r = 0 then Pi.single (Classical.arbitrary I) 1 else ((√(nsq r))⁻¹ : ℝ) • r

lemma nsq_single [Nonempty I] : nsq (Pi.single (Classical.arbitrary I) (1 : ℂ) : I → ℂ) = 1 := by
  simp only [nsq]
  rw [Finset.sum_eq_single (Classical.arbitrary I)]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

lemma nsq_zero_iff (r : I → ℂ) (h : nsq r = 0) : r = 0 := by
  funext a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖r i‖)).1 h a
    (Finset.mem_univ a)
  simpa using this

lemma unitOf_nsq [Nonempty I] (r : I → ℂ) : nsq (unitOf r) = 1 := by
  unfold unitOf
  split_ifs with h
  · exact nsq_single
  · have hp : 0 < nsq r := lt_of_le_of_ne (nsq_nonneg r) (Ne.symm h)
    have e : ((((√(nsq r))⁻¹ : ℝ)) • r : I → ℂ) = (((√(nsq r))⁻¹ : ℝ) : ℂ) • r := by
      funext a; simp [Complex.real_smul]
    rw [e, nsq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']

lemma G_row [Nonempty I] (r : I → ℂ) :
    (W A r)ᴴ * W A r = ((nsq r : ℝ) : ℂ) • ((W A (unitOf r))ᴴ * W A (unitOf r)) := by
  by_cases h : nsq r = 0
  · rw [nsq_zero_iff r h, W_zero]; simp [nsq]
  · have hp : 0 < nsq r := lt_of_le_of_ne (nsq_nonneg r) (Ne.symm h)
    have hr : r = ((√(nsq r) : ℝ) : ℂ) • unitOf r := by
      unfold unitOf; rw [if_neg h]
      funext a
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 hp).ne']
      simp
    conv_lhs => rw [hr]
    rw [G_smul, Real.sq_sqrt hp.le]

lemma sum_rows (ψ : J × I → ℂ) : ∑ j, nsq (row ψ j) = nsq ψ := by
  simp only [nsq, row, Fintype.sum_prod_type]

/-- trace-function comparison: `id ⊗ Φ` on a pure input is dominated by `Φ` on pure inputs -/
lemma tf_upper [Nonempty I] {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (C : ℝ) (hC : ∀ u : I → ℂ, nsq u = 1 → ∀ h : (krausApply A (vecMulVec u (star u))).IsHermitian,
      ∑ k, f (h.eigenvalues k) ≤ C)
    (ψ : EuclideanSpace ℂ (J × I)) (hψ : ‖ψ‖ = 1)
    (h : (idTensorSuperop (R := J) (krausApply A) (pureDensity ψ)).IsHermitian) :
    ∑ k, f (h.eigenvalues k) ≤ C := by
  set M := Mx A ⇑ψ
  have h1 : (M * Mᴴ).IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose M).1
  have h2 : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  rw [tf_congr f h h1 (out_eq A ψ), tf_comm M f hf0 h1 h2.1]
  set w : J → ℝ := fun j => nsq (row (⇑ψ) j)
  set G : J → Matrix K K ℂ := fun j => (W A (unitOf (row (⇑ψ) j)))ᴴ * W A (unitOf (row (⇑ψ) j))
  have hG : ∀ j, (G j).PosSemidef := fun j => Matrix.posSemidef_conjTranspose_mul_self _
  have hMG : Mᴴ * M = ∑ j, ((w j : ℝ) : ℂ) • G j := by
    rw [gram_eq]; exact Finset.sum_congr rfl fun j _ => G_row A _
  have hS : (∑ j, ((w j : ℝ) : ℂ) • G j).PosSemidef := hMG ▸ h2
  have hw : ∀ j, 0 ≤ w j := fun j => nsq_nonneg _
  have hs : ∑ j, w j = 1 := by rw [sum_rows]; exact nsq_of_norm hψ
  rw [tf_congr f h2.1 hS.1 hMG]
  refine (tf_convex hf w hw hs G hG hS).trans ?_
  have hj : ∀ j, ∑ k, f ((hG j).1.eigenvalues k) ≤ C := by
    intro j
    set u := unitOf (row (⇑ψ) j)
    have hu : (W A u * (W A u)ᴴ).IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose _).1
    rw [← tf_comm (W A u) f hf0 hu (hG j).1]
    have hu' : (krausApply A (vecMulVec u (star u))).IsHermitian := (pure_out A u).symm ▸ hu
    rw [← tf_congr f hu' hu (pure_out A u)]
    exact hC u (unitOf_nsq _) hu'
  calc ∑ j, w j * ∑ k, f ((hG j).1.eigenvalues k) ≤ ∑ j, w j * C :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj j) (hw j)
    _ = C := by rw [← Finset.sum_mul, hs, one_mul]

/-- the product input `e_{j₀} ⊗ v` -/
def lift [Nonempty J] (v : EuclideanSpace ℂ I) : EuclideanSpace ℂ (J × I) :=
  WithLp.toLp 2 (fun p => if p.1 = Classical.arbitrary J then v p.2 else 0)

lemma lift_row [Nonempty J] (v : EuclideanSpace ℂ I) (j : J) :
    row (⇑(lift v)) j = if j = Classical.arbitrary J then ⇑v else 0 := by
  funext i; by_cases hj : j = Classical.arbitrary J <;> simp [row, lift, hj]

lemma lift_norm [Nonempty J] {v : EuclideanSpace ℂ I} (hv : ‖v‖ = 1) : ‖lift (J := J) v‖ = 1 := by
  have h := norm_toLp (⇑(lift (J := J) v))
  have e : (WithLp.toLp 2 (⇑(lift (J := J) v)) : EuclideanSpace ℂ (J × I)) = lift v := rfl
  rw [e] at h
  rw [h, ← sum_rows, Finset.sum_eq_single (Classical.arbitrary J)]
  · rw [lift_row, if_pos rfl, nsq_of_norm hv, Real.sqrt_one]
  · intro b _ hb; rw [lift_row, if_neg hb]; simp [nsq]
  · simp

lemma gram_lift [Nonempty J] (v : EuclideanSpace ℂ I) :
    (Mx A ⇑(lift (J := J) v))ᴴ * Mx A ⇑(lift (J := J) v) = (W A ⇑v)ᴴ * W A ⇑v := by
  rw [gram_eq, Finset.sum_eq_single (Classical.arbitrary J)]
  · rw [lift_row, if_pos rfl]
  · intro b _ hb; rw [lift_row, if_neg hb, W_zero]; simp
  · simp

lemma tf_lift [Nonempty J] {f : ℝ → ℝ} (hf0 : f 0 = 0) (v : EuclideanSpace ℂ I)
    (h : (idTensorSuperop (R := J) (krausApply A) (pureDensity (lift (J := J) v))).IsHermitian)
    (h' : (krausApply A (pureDensity v)).IsHermitian) :
    ∑ k, f (h.eigenvalues k) = ∑ k, f (h'.eigenvalues k) := by
  set M := Mx A ⇑(lift (J := J) v)
  have h1 : (M * Mᴴ).IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose M).1
  have h2 : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hu : (W A ⇑v * (W A ⇑v)ᴴ).IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose _).1
  have hG : ((W A ⇑v)ᴴ * W A ⇑v).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self _).1
  rw [tf_congr f h h1 (out_eq A _), tf_comm M f hf0 h1 h2.1, tf_congr f h2.1 hG (gram_lift A v),
    ← tf_comm (W A ⇑v) f hf0 hu hG]
  exact tf_congr f hu h' (by rw [pure_eq, pure_out])

/-- operator norm versions -/
lemma norm_upper [Nonempty I] (C : ℝ)
    (hC : ∀ u : I → ℂ, nsq u = 1 → ‖krausApply A (vecMulVec u (star u))‖ ≤ C)
    (ψ : EuclideanSpace ℂ (J × I)) (hψ : ‖ψ‖ = 1) :
    ‖idTensorSuperop (R := J) (krausApply A) (pureDensity ψ)‖ ≤ C := by
  set M := Mx A ⇑ψ
  have e1 : ‖M * Mᴴ‖ = ‖Mᴴ * M‖ := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self Mᴴ
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at this
    rw [this, Matrix.l2_opNorm_conjTranspose_mul_self]
  have eW : ∀ u : I → ℂ, ‖(W A u)ᴴ * W A u‖ = ‖krausApply A (vecMulVec u (star u))‖ := by
    intro u
    rw [pure_out, Matrix.l2_opNorm_conjTranspose_mul_self]
    have := Matrix.l2_opNorm_conjTranspose_mul_self (W A u)ᴴ
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at this
    rw [this]
  have hw : ∀ j, 0 ≤ nsq (row (⇑ψ) j) := fun j => nsq_nonneg _
  have hs : ∑ j, nsq (row (⇑ψ) j) = 1 := by rw [sum_rows]; exact nsq_of_norm hψ
  rw [out_eq, e1, gram_eq]
  calc ‖∑ j, (W A (row (⇑ψ) j))ᴴ * W A (row (⇑ψ) j)‖
      ≤ ∑ j, ‖(W A (row (⇑ψ) j))ᴴ * W A (row (⇑ψ) j)‖ := norm_sum_le _ _
    _ = ∑ j, nsq (row (⇑ψ) j) *
          ‖(W A (unitOf (row (⇑ψ) j)))ᴴ * W A (unitOf (row (⇑ψ) j))‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [G_row, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j)]
    _ ≤ ∑ j, nsq (row (⇑ψ) j) * C := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hw j)
        rw [eW]; exact hC _ (unitOf_nsq _)
    _ = C := by rw [← Finset.sum_mul, hs, one_mul]

lemma norm_lift [Nonempty J] (v : EuclideanSpace ℂ I) :
    ‖idTensorSuperop (R := J) (krausApply A) (pureDensity (lift (J := J) v))‖ =
      ‖krausApply A (pureDensity v)‖ := by
  set M := Mx A ⇑(lift (J := J) v)
  have e1 : ‖M * Mᴴ‖ = ‖Mᴴ * M‖ := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self Mᴴ
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at this
    rw [this, Matrix.l2_opNorm_conjTranspose_mul_self]
  rw [out_eq, e1, gram_lift, pure_eq, pure_out, Matrix.l2_opNorm_conjTranspose_mul_self]
  have := Matrix.l2_opNorm_conjTranspose_mul_self (W A ⇑v)ᴴ
  rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at this
  rw [this]

end X6IC


/-! X6: `ν_p(id ⊗ Φ) = ν_p(Φ)` and `ν_H(id ⊗ Φ) = ν_H(Φ)` (Amosov–Holevo–Werner, Lemma (9)). -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal Kronecker

namespace X6IC

open QAlgorithms Matrix X6KN X6PE
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P63 (schatten eigen)
open QAlgorithms.Papers.Independent.Support50.P31

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

lemma Bk_kron (A : K → Matrix I I ℂ) (k : K) :
    X6SF.Bk (J := J) A k = (1 : Matrix J J ℂ) ⊗ₖ A k := by
  ext p q
  by_cases h : p.1 = q.1 <;> simp [X6SF.Bk, Matrix.kroneckerMap_apply, Matrix.one_apply, h]

lemma Bk_kraus (A : K → Matrix I I ℂ) (hA : IsKrausFamily A) :
    IsKrausFamily (X6SF.Bk (J := J) A) := by
  unfold IsKrausFamily
  simp only [Bk_kron, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have e : ∑ x, (1 : Matrix J J ℂ) ⊗ₖ ((A x)ᴴ * A x) = (1 : Matrix J J ℂ) ⊗ₖ ∑ x, (A x)ᴴ * A x := by
    ext p q; simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
  rw [e, show ∑ k, (A k)ᴴ * A k = 1 from hA, Matrix.one_kronecker_one]

lemma ext_kraus (A : K → Matrix I I ℂ) :
    idTensorSuperop (R := J) (krausApply A) = krausApply (X6SF.Bk (J := J) A) :=
  funext fun X => X6SF.ext_eq A X

/-! generic identification of the optimal values -/

variable {n : Type} [Fintype n] [DecidableEq n]

lemma nuP_fin (Φ : Superop n n) (hΦ : ∀ ρ, IsDensityMatrix ρ → IsDensityMatrix (Φ ρ))
    {p : ℝ≥0∞} (hpt : p ≠ ⊤) (hr : 1 ≤ p.toReal) {v : EuclideanSpace ℂ n} (hv : ‖v‖ = 1)
    (hmax : ∀ ρ, IsDensityMatrix ρ →
      ∑ j, eigen (Φ ρ) j ^ p.toReal ≤ ∑ j, eigen (Φ (pureDensity v)) j ^ p.toReal) :
    nuP p Φ = schatten p.toReal (Φ (pureDensity v)) := by
  unfold nuP
  rw [if_neg hpt]
  unfold QAlgorithms.Papers.Independent.Gap48.P03.maximumOutputPNorm
  refine IsGreatest.csSup_eq ?_
  refine ⟨⟨_, pure_dens' hv, rfl⟩, ?_⟩
  rintro _ ⟨ρ, hρ, rfl⟩
  unfold schatten
  have hσ := (hΦ ρ hρ).1
  have h0 : 0 ≤ ∑ j, eigen (Φ ρ) j ^ p.toReal := by
    rw [sum_eigen' hσ.1 (fun t => t ^ p.toReal)]
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hσ.eigenvalues_nonneg i) _
  exact Real.rpow_le_rpow h0 (hmax ρ hρ) (one_div_nonneg.2 (by linarith))

lemma nuP_top (Φ : Superop n n) {v : EuclideanSpace ℂ n} (hv : ‖v‖ = 1)
    (hmax : ∀ ρ, IsDensityMatrix ρ → ‖Φ ρ‖ ≤ ‖Φ (pureDensity v)‖) :
    nuP ⊤ Φ = ‖Φ (pureDensity v)‖ := by
  unfold nuP
  rw [if_pos rfl]
  refine IsGreatest.csSup_eq ?_
  refine ⟨⟨⟨_, pure_dens' hv⟩, rfl⟩, ?_⟩
  rintro _ ⟨X, rfl⟩
  exact hmax X.1 X.2

lemma nuH_eq (Φ : Superop n n) (hΦ : ∀ ρ, IsDensityMatrix ρ → IsDensityMatrix (Φ ρ))
    {v : EuclideanSpace ℂ n} (hv : ‖v‖ = 1)
    (hmax : ∀ ρ, IsDensityMatrix ρ → ∑ j, eigen (Φ ρ) j * Real.log (eigen (Φ ρ) j) ≤
      ∑ j, eigen (Φ (pureDensity v)) j * Real.log (eigen (Φ (pureDensity v)) j)) :
    nuH Φ = entropy (Φ (pureDensity v)) := by
  unfold nuH
  refine IsLeast.csInf_eq ?_
  refine ⟨⟨⟨_, pure_dens' hv⟩, rfl⟩, ?_⟩
  rintro _ ⟨X, rfl⟩
  show _ ≤ entropy (Φ X.1)
  rw [ent_eigen (hΦ _ X.2).1.1, ent_eigen (hΦ _ (pure_dens' hv)).1.1]
  exact neg_le_neg (hmax X.1 X.2)

/-! comparison of the two channels -/

lemma tf_main [Nonempty I] [Nonempty J] (A : K → Matrix I I ℂ) (hA : IsKrausFamily A)
    {f : ℝ → ℝ} (hfc : Continuous f) (hf : ConvexOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0) :
    ∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧ ∃ ψ : EuclideanSpace ℂ (J × I), ‖ψ‖ = 1 ∧
      (∀ ρ, IsDensityMatrix ρ →
        ∑ j, f (eigen (krausApply A ρ) j) ≤ ∑ j, f (eigen (krausApply A (pureDensity v)) j)) ∧
      (∀ ρ, IsDensityMatrix ρ →
        ∑ j, f (eigen (idTensorSuperop (R := J) (krausApply A) ρ) j) ≤
          ∑ j, f (eigen (idTensorSuperop (R := J) (krausApply A) (pureDensity ψ)) j)) ∧
      ∑ j, f (eigen (idTensorSuperop (R := J) (krausApply A) (pureDensity ψ)) j) =
        ∑ j, f (eigen (krausApply A (pureDensity v)) j) := by
  obtain ⟨v, hv, hvmax⟩ := trace_max A hA hfc hf
  obtain ⟨ψ, hψ, hψmax⟩ := trace_max (X6SF.Bk (J := J) A) (Bk_kraus A hA) hfc hf
  rw [← ext_kraus] at hψmax
  refine ⟨v, hv, ψ, hψ, hvmax, hψmax, le_antisymm ?_ ?_⟩
  · have hσ := (kraus_dens _ (Bk_kraus (J := J) A hA) (pure_dens' hψ)).1
    rw [← ext_kraus] at hσ
    have hτ := (kraus_dens A hA (pure_dens' hv)).1
    rw [sum_eigen' hσ.1, sum_eigen' hτ.1]
    refine tf_upper A hf hf0 _ ?_ ψ hψ hσ.1
    intro u hu h
    have hu' : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ I)‖ = 1 := by
      rw [norm_toLp, hu, Real.sqrt_one]
    have e : vecMulVec u (star u) = pureDensity (WithLp.toLp 2 u : EuclideanSpace ℂ I) := by
      rw [pure_eq]
    have := hvmax _ (pure_dens' hu')
    rw [← e] at this
    rw [sum_eigen' h, sum_eigen' hτ.1] at this
    exact this
  · have hσ := (kraus_dens _ (Bk_kraus (J := J) A hA) (pure_dens' (lift_norm (J := J) hv))).1
    rw [← ext_kraus] at hσ
    have hτ := (kraus_dens A hA (pure_dens' hv)).1
    have h1 := hψmax _ (pure_dens' (lift_norm (J := J) hv))
    rw [sum_eigen' hσ.1, tf_lift A hf0 v hσ.1 hτ.1, ← sum_eigen' hτ.1] at h1
    exact h1

theorem main [Nonempty I] [Nonempty J] (Phi : Superop I I) (hPhi : IsChannel Phi) :
    (∀ p : ℝ≥0∞, 1 ≤ p → nuP p (idTensorSuperop (R := J) Phi) = nuP p Phi) ∧
      nuH (idTensorSuperop (R := J) Phi) = nuH Phi := by
  obtain ⟨m, A, hA, hΦ⟩ := hPhi
  have hP : Phi = krausApply A := funext hΦ
  subst hP
  have hd1 : ∀ ρ, IsDensityMatrix ρ → IsDensityMatrix (krausApply A ρ) :=
    fun ρ hρ => kraus_dens A hA hρ
  have hd2 : ∀ ρ, IsDensityMatrix ρ →
      IsDensityMatrix (idTensorSuperop (R := J) (krausApply A) ρ) := by
    intro ρ hρ; rw [ext_kraus]; exact kraus_dens _ (Bk_kraus A hA) hρ
  refine ⟨fun p hp => ?_, ?_⟩
  · by_cases hpt : p = ⊤
    · subst hpt
      obtain ⟨v, hv, hvmax⟩ := norm_max A hA
      obtain ⟨ψ, hψ, hψmax⟩ := norm_max (X6SF.Bk (J := J) A) (Bk_kraus A hA)
      rw [← ext_kraus] at hψmax
      rw [nuP_top _ hv hvmax, nuP_top _ hψ hψmax]
      refine le_antisymm ?_ ?_
      · refine norm_upper A _ (fun u hu => ?_) ψ hψ
        have hu' : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ I)‖ = 1 := by
          rw [norm_toLp, hu, Real.sqrt_one]
        have e : vecMulVec u (star u) = pureDensity (WithLp.toLp 2 u : EuclideanSpace ℂ I) := by
          rw [pure_eq]
        rw [e]; exact hvmax _ (pure_dens' hu')
      · rw [← norm_lift (J := J) A v]
        exact hψmax _ (pure_dens' (lift_norm hv))
    · have hr : 1 ≤ p.toReal := by
        have := ENNReal.toReal_mono hpt hp
        simpa using this
      have hr0 : (0 : ℝ) ^ p.toReal = 0 := Real.zero_rpow (by linarith)
      obtain ⟨v, hv, ψ, hψ, hvmax, hψmax, heq⟩ := tf_main (J := J) A hA
        (Real.continuous_rpow_const (by linarith)) (convexOn_rpow hr) hr0
      rw [nuP_fin _ hd1 hpt hr hv hvmax, nuP_fin _ hd2 hpt hr hψ hψmax]
      unfold schatten
      rw [heq]
  · obtain ⟨v, hv, ψ, hψ, hvmax, hψmax, heq⟩ := tf_main (J := J) A hA
      Real.continuous_mul_log Real.convexOn_mul_log (by simp)
    rw [nuH_eq _ hd1 hv hvmax, nuH_eq _ hd2 hψ hψmax, ent_eigen (hd1 _ (pure_dens' hv)).1.1,
      ent_eigen (hd2 _ (pure_dens' hψ)).1.1, heq]

end X6IC


open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P31
open scoped ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J] (Phi : Superop I I) (hPhi : IsChannel Phi) :
    (∀ p : ℝ≥0∞, 1 ≤ p → nuP p (idTensorSuperop (R := J) Phi) = nuP p Phi) ∧
      nuH (idTensorSuperop (R := J) Phi) = nuH Phi := by
  convert X6IC.main (J := J) Phi hPhi
