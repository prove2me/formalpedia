-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P31.selfFidelityIdealChannel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:39:42.1104+00:00
-- url     : https://prove2.me/submissions/e0f4a87d-f32f-4b4d-acf7-3d6d1e4326f5

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


/-! X6: maximal survival probability is stable under an ideal (identity) extension. -/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ComplexConjugate

namespace X6SF

open QAlgorithms Matrix X6KN

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- `f(u) = Σ_k |⟨u, A_k u⟩|²` -/
def f (A : K → Matrix I I ℂ) (u : I → ℂ) : ℝ := ∑ k, ‖star u ⬝ᵥ (A k *ᵥ u)‖ ^ 2

lemma f_smul (A : K → Matrix I I ℂ) (t : ℂ) (u : I → ℂ) : f A (t • u) = ‖t‖ ^ 4 * f A u := by
  unfold f
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    norm_mul, norm_mul, norm_star]
  ring

lemma nsq_star (u : I → ℂ) : nsq (star u) = nsq u := by simp [nsq, norm_star]

lemma f_le (A : K → Matrix I I ℂ) (hA : IsKrausFamily A) (u : I → ℂ) : f A u ≤ nsq u ^ 2 := by
  have h1 : ∀ k, ‖star u ⬝ᵥ (A k *ᵥ u)‖ ^ 2 ≤ nsq u * nsq (A k *ᵥ u) := by
    intro k
    have := cs (star u) (A k *ᵥ u)
    rw [nsq_star] at this
    have h2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    rwa [mul_pow, Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _)] at h2
  have h3 : ∑ k, nsq (A k *ᵥ u) = nsq u := by
    simp only [nsq_eq_re, ← Complex.re_sum]
    congr 1
    have : ∀ k, star (A k *ᵥ u) ⬝ᵥ (A k *ᵥ u) = star u ⬝ᵥ (((A k)ᴴ * A k) *ᵥ u) := by
      intro k
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    simp only [this, ← dotProduct_sum, ← Matrix.sum_mulVec]
    rw [show ∑ k, (A k)ᴴ * A k = 1 from hA, Matrix.one_mulVec]
  unfold f
  calc ∑ k, ‖star u ⬝ᵥ (A k *ᵥ u)‖ ^ 2 ≤ ∑ k, nsq u * nsq (A k *ᵥ u) :=
        Finset.sum_le_sum fun k _ => h1 k
    _ = nsq u ^ 2 := by rw [← Finset.mul_sum, h3]; ring

lemma unit_nsq {n : Type} [Fintype n] [DecidableEq n] (v : {v : EuclideanSpace ℂ n // ‖v‖ = 1}) :
    nsq v.val.ofLp = 1 := by
  have h := v.2
  have e : (WithLp.toLp 2 v.val.ofLp : EuclideanSpace ℂ n) = v.val := rfl
  rw [← e, norm_toLp] at h
  have h2 := congrArg (· ^ 2) h
  simp only [one_pow] at h2
  rwa [Real.sq_sqrt (nsq_nonneg _)] at h2

theorem main (A : K → Matrix I I ℂ) (hA : IsKrausFamily A) [Nonempty I] [Nonempty J] :
    Papers.Independent.Support50.P31.nuFlat (idTensorSuperop (R := J) (krausApply A)) =
      Papers.Independent.Support50.P31.nuFlat (krausApply A) := by
  unfold Papers.Independent.Support50.P31.nuFlat
  simp only [flat_ext, flat_kraus]
  set S1 := Set.range fun ψ : {v : EuclideanSpace ℂ (J × I) // ‖v‖ = 1} =>
    ∑ k, ‖star ψ.val.ofLp ⬝ᵥ (Bk A k *ᵥ ψ.val.ofLp)‖ ^ 2
  set S0 := Set.range fun v : {v : EuclideanSpace ℂ I // ‖v‖ = 1} =>
    ∑ k, ‖star v.val.ofLp ⬝ᵥ (A k *ᵥ v.val.ofLp)‖ ^ 2
  obtain ⟨i0⟩ := (inferInstance : Nonempty I)
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  have hS0b : BddAbove S0 := ⟨1, by
    rintro _ ⟨v, rfl⟩
    have := f_le A hA v.val.ofLp
    rw [unit_nsq] at this; simpa [f] using this⟩
  have unitv : ∀ {n : Type} [Fintype n] [DecidableEq n] (w : n → ℂ), nsq w = 1 →
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖ = 1 := by
    intro n _ _ w hw; rw [norm_toLp, hw, Real.sqrt_one]
  have he0 : nsq (Pi.single i0 (1 : ℂ) : I → ℂ) = 1 := by
    simp only [nsq]
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hS0ne : S0.Nonempty := ⟨_, ⟨⟨_, unitv _ he0⟩, rfl⟩⟩
  set c := sSup S0
  have hc0 : 0 ≤ c := (Finset.sum_nonneg fun k _ => sq_nonneg _).trans
    (le_csSup hS0b ⟨⟨_, unitv _ he0⟩, rfl⟩)
  -- scaling bound
  have fb : ∀ u : I → ℂ, f A u ≤ c * nsq u ^ 2 := by
    intro u
    rcases (nsq_nonneg u).eq_or_lt with h0 | hpos
    · have hu : u = 0 := by
        funext a
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖u i‖)).1 h0.symm a
          (Finset.mem_univ a)
        simpa using this
      subst hu; simp [f, nsq]
    · set t := √(nsq u)
      have ht : 0 < t := Real.sqrt_pos.2 hpos
      set w := ((t⁻¹ : ℝ) : ℂ) • u
      have hw : nsq w = 1 := by
        rw [nsq_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht), inv_pow,
          Real.sq_sqrt (nsq_nonneg _)]
        exact inv_mul_cancel₀ hpos.ne'
      have huw : u = ((t : ℝ) : ℂ) • w := by
        simp only [w, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one,
          one_smul]
      have hfw : f A w ≤ c := le_csSup hS0b ⟨⟨_, unitv _ hw⟩, rfl⟩
      have e1 : nsq u ^ 2 = t ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (nsq_nonneg _)]
      conv_lhs => rw [huw]
      rw [f_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, e1, mul_comm]
      exact mul_le_mul_of_nonneg_right hfw (by positivity)
  -- upper bound on extended values
  have up : ∀ ψ : J × I → ℂ, nsq ψ = 1 →
      ∑ k, ‖star ψ ⬝ᵥ (Bk A k *ᵥ ψ)‖ ^ 2 ≤ c := by
    intro ψ hψ
    simp only [Bk_dot]
    set g : J → I → ℂ := fun j a => ψ (j, a)
    set T : J → EuclideanSpace ℂ K := fun j =>
      WithLp.toLp 2 (fun k => star (g j) ⬝ᵥ (A k *ᵥ g j))
    have hT : ∀ j, ‖T j‖ ≤ √c * nsq (g j) := by
      intro j
      rw [norm_toLp]
      calc √(nsq (fun k => star (g j) ⬝ᵥ (A k *ᵥ g j))) = √(f A (g j)) := rfl
        _ ≤ √(c * nsq (g j) ^ 2) := Real.sqrt_le_sqrt (fb _)
        _ = √c * nsq (g j) := by
          rw [Real.sqrt_mul hc0, Real.sqrt_sq (nsq_nonneg _)]
    have hsum : ∑ j, nsq (g j) = 1 := by
      rw [← hψ]; simp only [nsq, g, Fintype.sum_prod_type]
    have hnorm : ‖∑ j, T j‖ ≤ √c := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j, ‖T j‖ ≤ ∑ j, √c * nsq (g j) := Finset.sum_le_sum fun j _ => hT j
        _ = √c := by rw [← Finset.mul_sum, hsum, mul_one]
    have hT' : ∑ j, T j = WithLp.toLp 2 (fun k => ∑ j, star (g j) ⬝ᵥ (A k *ᵥ g j)) := by
      rw [← WithLp.toLp_sum]; congr 1; funext k; simp [Finset.sum_apply]
    rw [hT', norm_toLp] at hnorm
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
    rw [Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt hc0] at this
    exact this
  have hS1b : BddAbove S1 := ⟨c, by rintro _ ⟨ψ, rfl⟩; exact up _ (unit_nsq ψ)⟩
  -- lower bound
  have low : ∀ v : I → ℂ, nsq v = 1 → ∑ k, ‖star v ⬝ᵥ (A k *ᵥ v)‖ ^ 2 ≤ sSup S1 := by
    intro v hv
    set ψ : J × I → ℂ := fun p => if p.1 = j0 then v p.2 else 0
    have hψ : nsq ψ = 1 := by
      rw [← hv]
      simp only [nsq, ψ, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single j0]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    have hval : ∑ k, ‖star ψ ⬝ᵥ (Bk A k *ᵥ ψ)‖ ^ 2 = ∑ k, ‖star v ⬝ᵥ (A k *ᵥ v)‖ ^ 2 := by
      simp only [Bk_dot]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      rw [Finset.sum_eq_single j0]
      · simp [ψ]
      · intro b _ hb
        have : (fun a => ψ (b, a)) = 0 := by funext a; simp [ψ, hb]
        rw [this]; simp
      · simp
    rw [← hval]
    exact le_csSup hS1b ⟨⟨_, unitv _ hψ⟩, rfl⟩
  have hS1ne : S1.Nonempty := ⟨_, ⟨⟨_, unitv _ (show nsq (fun p : J × I =>
    if p.1 = j0 then (Pi.single i0 (1 : ℂ) : I → ℂ) p.2 else 0) = 1 by
      rw [← he0]
      simp only [nsq, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single j0]
      · simp
      · intro b _ hb; simp [hb]
      · simp)⟩, rfl⟩⟩
  apply le_antisymm
  · exact csSup_le hS1ne (by rintro _ ⟨ψ, rfl⟩; exact up _ (unit_nsq ψ))
  · exact csSup_le hS0ne (by rintro _ ⟨v, rfl⟩; exact low _ (unit_nsq v))

end X6SF


open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P31

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J] (Phi : Superop I I) (hPhi : IsChannel Phi) :
    nuFlat (idTensorSuperop (R := J) Phi) = nuFlat Phi := by
  obtain ⟨m, E, hE, hP⟩ := hPhi
  obtain rfl : Phi = krausApply E := funext hP
  exact X6SF.main E hE
