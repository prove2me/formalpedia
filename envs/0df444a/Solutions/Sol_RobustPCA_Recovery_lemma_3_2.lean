-- Prove2me | solution 1 for RobustPCA.Recovery.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T12:26:14.526555+00:00
-- url     : https://prove2.me/submissions/cd6e3b68-78a9-4a7f-9003-1600315c4128

import Mathlib
import Definitions.Def_RobustPCA_Recovery_Setup
import Theorems.Thm_IntroMatrixConc_Sampling_corollary_6_1_2

set_option autoImplicit false

open MatrixCompletion

namespace RPCA32

open RobustPCA.Recovery
open scoped BigOperators Classical


lemma entrySup_nonneg {n : ℕ} (A : RealMatrix n n) : 0 ≤ entrySupNorm A := by
  unfold entrySupNorm
  exact Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))

lemma le_entrySup {n : ℕ} (A : RealMatrix n n) (i j : Fin n) : |A i j| ≤ entrySupNorm A := by
  unfold entrySupNorm
  exact le_ciSup_of_le (Finite.bddAbove_range _) i
    (le_ciSup (f := fun j => |A i j|) (Finite.bddAbove_range _) j)

lemma entrySup_add {n : ℕ} (A B : RealMatrix n n) :
    entrySupNorm (A + B) ≤ entrySupNorm A + entrySupNorm B := by
  have h0 : 0 ≤ entrySupNorm A + entrySupNorm B :=
    add_nonneg (entrySup_nonneg A) (entrySup_nonneg B)
  unfold entrySupNorm
  refine Real.iSup_le (fun i => Real.iSup_le (fun j => ?_) h0) h0
  calc |(A + B) i j| = |A i j + B i j| := rfl
    _ ≤ |A i j| + |B i j| := abs_add_le _ _
    _ ≤ entrySupNorm A + entrySupNorm B := add_le_add (le_entrySup A i j) (le_entrySup B i j)

lemma entrySup_le {n : ℕ} (A : RealMatrix n n) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i j, |A i j| ≤ b) : entrySupNorm A ≤ b := by
  unfold entrySupNorm
  exact Real.iSup_le (fun i => Real.iSup_le (fun j => h i j) hb) hb

/-! ## Bernoulli sums -/

lemma bw_sum_one {N : ℕ} (p : ℝ) :
    ∑ A : Finset (Fin N × Fin N), bernoulliObservationWeight p A = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ : Finset (Fin N × Fin N))
  rw [Finset.powerset_univ, Finset.card_univ, show p + (1 - p) = 1 by ring, one_pow] at h
  exact h

lemma bw_nonneg {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset (Fin N × Fin N)) :
    0 ≤ bernoulliObservationWeight p A := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

lemma bep_not {N : ℕ} (p : ℝ) (P : Finset (Fin N × Fin N) → Prop) :
    bernoulliEventProb p (fun B => ¬ P B) = 1 - bernoulliEventProb p P := by
  unfold bernoulliEventProb
  rw [← bw_sum_one (N := N) p, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  by_cases h : P B
  · rw [if_neg (not_not.mpr h), if_pos h]; ring
  · rw [if_pos h, if_neg h]; ring

lemma entrySup_zero {n : ℕ} : entrySupNorm (0 : RealMatrix n n) = 0 :=
  le_antisymm (entrySup_le _ 0 le_rfl (fun i j => by simp)) (entrySup_nonneg _)

lemma prod_ite_univ {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) (a b : ℝ) :
    ∏ x, (if x ∈ B then a else b) = a ^ B.card * b ^ (Fintype.card α - B.card) := by
  rw [← Finset.prod_mul_prod_compl B]
  have h1 : ∏ x ∈ B, (if x ∈ B then a else b) = ∏ x ∈ B, a :=
    Finset.prod_congr rfl (fun x hx => by simp [hx])
  have h2 : ∏ x ∈ Bᶜ, (if x ∈ B then a else b) = ∏ x ∈ Bᶜ, b :=
    Finset.prod_congr rfl (fun x hx => by rw [Finset.mem_compl] at hx; simp [hx])
  rw [h1, h2, Finset.prod_const, Finset.prod_const, Finset.card_compl]

lemma bw_eq_prod {N : ℕ} (p : ℝ) (A : Finset (Fin N × Fin N)) :
    bernoulliObservationWeight p A = ∏ x, (if x ∈ A then p else 1 - p) := by
  unfold bernoulliObservationWeight
  rw [prod_ite_univ]

def eqv (n : ℕ) : Fin (n * n) ≃ Fin n × Fin n := finProdFinEquiv.symm

/-! ## Real matrices inside complex matrices with the `L²` operator norm -/

def cmap {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  B.map (fun t : ℝ => (t : ℂ))

lemma cmulVec_re {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℂ) (i : Fin N) :
    (Matrix.mulVec (cmap B) x i).re = Matrix.mulVec B (fun j => (x j).re) i := by
  simp only [cmap, Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.re_sum,
    Complex.re_ofReal_mul]

lemma cmulVec_im {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℂ) (i : Fin N) :
    (Matrix.mulVec (cmap B) x i).im = Matrix.mulVec B (fun j => (x j).im) i := by
  simp only [cmap, Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.im_sum,
    Complex.im_ofReal_mul]

section CBridge
open scoped Matrix.Norms.L2Operator

lemma cnorm_le {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ v : Fin N → ℝ, ∑ m, (Matrix.mulVec B v m) ^ 2 ≤ K ^ 2 * ∑ m, v m ^ 2) :
    ‖cmap B‖ ≤ K := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK (fun x => ?_)
  change ‖(WithLp.toLp 2 (Matrix.mulVec (cmap B) (WithLp.ofLp x)) : EuclideanSpace ℂ (Fin N))‖
    ≤ K * ‖x‖
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hK,
    ← Real.sqrt_mul (sq_nonneg K)]
  apply Real.sqrt_le_sqrt
  have hn : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hx : ∀ i, x i = WithLp.ofLp x i := fun i => rfl
  simp only [hn, PiLp.toLp_apply, cmulVec_re, cmulVec_im, Finset.sum_add_distrib, hx]
  have h1 := h (fun j => (WithLp.ofLp x j).re)
  have h2 := h (fun j => (WithLp.ofLp x j).im)
  rw [mul_add]
  exact add_le_add h1 h2

lemma real_le_cnorm {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) :
    ∑ m, (Matrix.mulVec B v m) ^ 2 ≤ ‖cmap B‖ ^ 2 * ∑ m, v m ^ 2 := by
  have h := ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin N) (n := Fin N)).trans
    LinearMap.toContinuousLinearMap (cmap B)).le_opNorm (WithLp.toLp 2 (fun j => (v j : ℂ)))
  rw [← Matrix.l2_opNorm_def] at h
  change ‖(WithLp.toLp 2 (Matrix.mulVec (cmap B) (fun j => (v j : ℂ))) :
      EuclideanSpace ℂ (Fin N))‖ ≤
    ‖cmap B‖ * ‖(WithLp.toLp 2 (fun j => (v j : ℂ)) : EuclideanSpace ℂ (Fin N))‖ at h
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
  have e1 : ∀ i, Matrix.mulVec (cmap B) (fun j => (v j : ℂ)) i =
      ((Matrix.mulVec B v i : ℝ) : ℂ) := by
    intro i
    simp only [cmap, Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.ofReal_sum,
      Complex.ofReal_mul]
  simp only [PiLp.toLp_apply, e1, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  have h0 : 0 ≤ ∑ m, (Matrix.mulVec B v m) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h0' : 0 ≤ ∑ m, v m ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [mul_pow, Real.sq_sqrt h0, Real.sq_sqrt h0'] at h2
  exact h2

end CBridge


/-! ## Part B: the Bernoulli product space -/

open MeasureTheory ProbabilityTheory

noncomputable def bern (ρ : ℝ) : Measure Bool :=
  ENNReal.ofReal ρ • Measure.dirac true + ENNReal.ofReal (1 - ρ) • Measure.dirac false

lemma bern_prob (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : IsProbabilityMeasure (bern ρ) := by
  constructor
  simp only [bern, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

lemma bern_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (g : Bool → E) :
    ∫ b, g b ∂(bern ρ) = ρ • g true + (1 - ρ) • g false := by
  unfold bern
  rw [integral_add_measure (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)
      (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (by linarith)]

lemma pi_integral_eval {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (k : Fin N) (g : Bool → E) :
    ∫ ω, g (ω k) ∂(Measure.pi (fun _ : Fin N => bern ρ)) = ρ • g true + (1 - ρ) • g false := by
  have := bern_prob ρ h0 h1
  have hmp := measurePreserving_eval (fun _ : Fin N => bern ρ) k
  have h := integral_map (μ := Measure.pi (fun _ : Fin N => bern ρ)) (φ := Function.eval k)
    (f := g) (measurable_pi_apply k).aemeasurable Integrable.of_finite.aestronglyMeasurable
  rw [hmp.map_eq] at h
  rw [← bern_integral ρ h0 h1 g]
  exact h.symm

lemma pi_singleton {N : ℕ} (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (ω : Fin N → Bool) :
    (Measure.pi (fun _ : Fin N => bern ρ) {ω}).toReal = ∏ k, (if ω k then ρ else 1 - ρ) := by
  have := bern_prob ρ h0 h1
  rw [← Set.univ_pi_singleton ω, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rcases Bool.eq_false_or_eq_true (ω k) with h | h <;>
    simp [h, bern, Measure.dirac_apply, ENNReal.toReal_ofReal h0,
      ENNReal.toReal_ofReal (sub_nonneg.mpr h1)]

lemma pi_toReal_eq_sum {N : ℕ} (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (S : Set (Fin N → Bool)) :
    (Measure.pi (fun _ : Fin N => bern ρ) S).toReal =
      ∑ ω, if ω ∈ S then ∏ k, (if ω k then ρ else 1 - ρ) else 0 := by
  have := bern_prob ρ h0 h1
  have hS : S = ↑(Finset.univ.filter (· ∈ S)) := by ext; simp
  conv_lhs => rw [hS]
  rw [← sum_measure_singleton, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  split_ifs
  · exact pi_singleton ρ h0 h1 ω
  · rfl

def setOf' {n : ℕ} (ω : Fin (n * n) → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => ω ((eqv n).symm p) = true)

def boolEquiv (n : ℕ) : (Fin (n * n) → Bool) ≃ Finset (Fin n × Fin n) where
  toFun ω := setOf' ω
  invFun Ω := fun k => decide (eqv n k ∈ Ω)
  left_inv ω := by funext k; simp [setOf']
  right_inv Ω := by ext p; simp [setOf']

lemma bep_eq_sum {n : ℕ} (ρ : ℝ) (F : Finset (Fin n × Fin n) → Prop) :
    bernoulliEventProb ρ F = ∑ ω : Fin (n * n) → Bool,
      if F (setOf' ω) then ∏ k, (if ω k then ρ else 1 - ρ) else 0 := by
  unfold bernoulliEventProb
  refine (Fintype.sum_equiv (boolEquiv n) _ _ (fun ω => ?_)).symm
  change _ = if F (setOf' ω) then bernoulliObservationWeight ρ (setOf' ω) else 0
  split_ifs
  · rw [bw_eq_prod, ← Equiv.prod_comp (eqv n)]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    simp [setOf']
  · rfl

noncomputable def tco (ρ : ℝ) (b : Bool) : ℝ := if b then ρ⁻¹ else 0

lemma cmap_apply {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    cmap B i j = (B i j : ℂ) := rfl

lemma cmap_smul {N : ℕ} (t : ℝ) (B : Matrix (Fin N) (Fin N) ℝ) :
    t • cmap B = cmap (t • B) := by
  ext i j
  simp [cmap_apply, Matrix.smul_apply, Complex.real_smul]

lemma cmap_add {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) : cmap A + cmap B = cmap (A + B) := by
  ext i j; simp [cmap_apply]

lemma cmap_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) : cmap A - cmap B = cmap (A - B) := by
  ext i j; simp [cmap_apply]

lemma cmap_sum {N : ℕ} {ι : Type*} [Fintype ι] (F : ι → Matrix (Fin N) (Fin N) ℝ) :
    ∑ k, cmap (F k) = cmap (∑ k, F k) := by
  ext i j; simp [cmap_apply, Matrix.sum_apply]

/-! ## Part C: the summands of `Z - ρ⁻¹ P_Ω Z` -/

def Ek {n : ℕ} (Z : RealMatrix n n) (k : Fin (n * n)) : RealMatrix n n :=
  fun a b => if (a, b) = eqv n k then Z a b else 0

noncomputable def Dg {n : ℕ} (i : Fin n) : RealMatrix n n :=
  Matrix.diagonal (fun a => if a = i then 1 else 0)

noncomputable def Sk {n : ℕ} (Z : RealMatrix n n) (ρ : ℝ) (k : Fin (n * n))
    (ω : Fin (n * n) → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  cmap ((1 - tco ρ (ω k)) • Ek Z k)

lemma Ek_sq {n : ℕ} (Z : RealMatrix n n) (k : Fin (n * n)) (t : ℝ) :
    cmap (t • Ek Z k) * (cmap (t • Ek Z k)).conjTranspose =
      cmap ((t ^ 2 * Z (eqv n k).1 (eqv n k).2 ^ 2) • Dg (eqv n k).1) ∧
    (cmap (t • Ek Z k)).conjTranspose * cmap (t • Ek Z k) =
      cmap ((t ^ 2 * Z (eqv n k).1 (eqv n k).2 ^ 2) • Dg (eqv n k).2) := by
  rcases hp : eqv n k with ⟨i, j⟩
  constructor
  · ext a c
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cmap_apply, Matrix.smul_apply,
      Ek, hp, Dg, Matrix.diagonal_apply, smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
      Prod.mk.injEq]
    rw [Finset.sum_eq_single j (fun m _ hm => by simp [hm]) (fun h => absurd (Finset.mem_univ j) h)]
    by_cases ha : a = i <;> by_cases hc : c = i <;> subst_vars <;> simp [*] <;> (try push_cast) <;> (try ring) <;> simp [Ne.symm hc]
  · ext a c
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cmap_apply, Matrix.smul_apply,
      Ek, hp, Dg, Matrix.diagonal_apply, smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
      Prod.mk.injEq]
    rw [Finset.sum_eq_single i (fun m _ hm => by simp [hm]) (fun h => absurd (Finset.mem_univ i) h)]
    by_cases ha : a = j <;> by_cases hc : c = j <;> subst_vars <;> simp [*] <;> (try push_cast) <;> (try ring) <;> simp [Ne.symm hc]

lemma sum_Ek {n : ℕ} (Z : RealMatrix n n) (ρ : ℝ) (ω : Fin (n * n) → Bool) :
    ∑ k, (1 - tco ρ (ω k)) • Ek Z k = Z - ρ⁻¹ • samplingProjection (setOf' ω) Z := by
  ext a b
  rw [Matrix.sum_apply, ← Equiv.sum_comp (eqv n).symm]
  simp only [Matrix.smul_apply, Ek, Equiv.apply_symm_apply, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.sub_apply, samplingProjection, setOf',
    Finset.mem_filter, true_and]
  unfold tco
  split_ifs <;> ring

lemma diag_bound {n : ℕ} (d : Fin n → ℝ) (K : ℝ) (hd : ∀ m, |d m| ≤ K) (v : Fin n → ℝ) :
    ∑ m, (Matrix.mulVec (Matrix.diagonal d) v m) ^ 2 ≤ K ^ 2 * ∑ m, v m ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun m _ => ?_)
  rw [Matrix.mulVec_diagonal, mul_pow]
  have h := pow_le_pow_left₀ (abs_nonneg _) (hd m) 2
  rw [sq_abs] at h
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

lemma sum_Dg {n : ℕ} (c : Fin (n * n) → ℝ) (f : Fin (n * n) → Fin n) :
    ∑ k, c k • Dg (f k) = Matrix.diagonal (fun m => ∑ k, if f k = m then c k else 0) := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Dg, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h
  · subst h
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h2 : f k = a
    · simp [h2]
    · simp [h2, Ne.symm h2]
  · exact Finset.sum_eq_zero (fun k _ => by simp)

lemma Ek_bound {n : ℕ} (Z : RealMatrix n n) (k : Fin (n * n)) (c K : ℝ) (hK : 0 ≤ K)
    (hc : |c| * entrySupNorm Z ≤ K) (v : Fin n → ℝ) :
    ∑ m, (Matrix.mulVec (c • Ek Z k) v m) ^ 2 ≤ K ^ 2 * ∑ m, v m ^ 2 := by
  rcases hp : eqv n k with ⟨i, j⟩
  have e : ∀ m, Matrix.mulVec (c • Ek Z k) v m = if m = i then c * Z i j * v j else 0 := by
    intro m
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Ek, hp, Prod.mk.injEq,
      smul_eq_mul]
    by_cases hm : m = i
    · subst hm
      simp only [true_and, mul_ite, mul_zero, ite_mul, zero_mul, if_true]
      rw [Finset.sum_ite_eq']
      simp
    · simp [hm]
  simp_rw [e]
  rw [Finset.sum_eq_single i (fun m _ hm => by simp [hm]) (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
  have hz := le_entrySup Z i j
  have h1 : |c * Z i j| ≤ K :=
    (by rw [abs_mul]; exact le_trans (mul_le_mul_of_nonneg_left hz (abs_nonneg _)) hc)
  have h2 : (c * Z i j) ^ 2 ≤ K ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs] at this
  have h3 : v j ^ 2 ≤ ∑ m, v m ^ 2 :=
    Finset.single_le_sum (f := fun m => v m ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  rw [mul_pow]
  exact mul_le_mul h2 h3 (sq_nonneg _) (sq_nonneg _)

section CBridge2
open scoped Matrix.Norms.L2Operator

lemma spec_le_cnorm {n : ℕ} (X : RealMatrix n n) :
    MatrixCompletion.spectralNorm X ≤ ‖cmap X‖ := by
  unfold MatrixCompletion.spectralNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  change ‖(WithLp.toLp 2 (Matrix.mulVec X (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin n))‖
    ≤ ‖cmap X‖ * ‖x‖
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (cmap X)),
    ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  have hx : ∀ i, x i = WithLp.ofLp x i := fun i => rfl
  simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, hx]
  exact real_le_cnorm X (WithLp.ofLp x)

end CBridge2

section Main
open scoped Matrix.Norms.L2Operator

variable {n : ℕ} (Z : RealMatrix n n) (ρ : ℝ)

lemma Sk_meas (k : Fin (n * n)) : Measurable (Sk Z ρ k) := measurable_of_countable _

lemma Sk_int (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (k : Fin (n * n)) :
    Integrable (Sk Z ρ k) (Measure.pi (fun _ : Fin (n * n) => bern ρ)) := by
  have := bern_prob ρ h0 h1
  exact Integrable.of_finite

lemma Sk_integral (h0 : 0 < ρ) (h1 : ρ ≤ 1) (k : Fin (n * n)) :
    ∫ ω, Sk Z ρ k ω ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)) = 0 := by
  have h := pi_integral_eval ρ h0.le h1 k (fun b => cmap ((1 - tco ρ b) • Ek Z k))
  simp only [Sk]
  rw [h, cmap_smul, cmap_smul, cmap_add, smul_smul, smul_smul, ← add_smul]
  simp only [tco, if_true, Bool.false_eq_true, if_false]
  have e : ρ * (1 - ρ⁻¹) + (1 - ρ) * (1 - 0) = 0 := by field_simp; ring
  rw [e, zero_smul]
  ext i j; simp [cmap_apply]

lemma Sk_indep (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    iIndepFun (Sk Z ρ) (Measure.pi (fun _ : Fin (n * n) => bern ρ)) := by
  have := bern_prob ρ h0 h1
  exact iIndepFun_pi (X := fun k (b : Bool) => cmap ((1 - tco ρ b) • Ek Z k))
    (fun k => (measurable_of_countable _).aemeasurable)

lemma Sk_dev (h0 : 0 < ρ) (h1 : ρ ≤ 1) (k : Fin (n * n)) (ω : Fin (n * n) → Bool) :
    Sk Z ρ k ω - ∫ η, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)) =
      cmap ((1 - tco ρ (ω k)) • Ek Z k) := by
  rw [Sk_integral Z ρ h0 h1, sub_zero, Sk]

lemma Z_dev (h0 : 0 < ρ) (h1 : ρ ≤ 1) (ω : Fin (n * n) → Bool) :
    (∑ k, Sk Z ρ k ω) - ∫ η, ∑ k, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)) =
      cmap (Z - ρ⁻¹ • samplingProjection (setOf' ω) Z) := by
  rw [integral_finsetSum _ (fun k _ => Sk_int Z ρ h0.le h1 k)]
  simp only [Sk_integral Z ρ h0 h1, Finset.sum_const_zero, sub_zero]
  simp only [Sk]
  rw [cmap_sum, sum_Ek]

lemma tco_dev (h0 : 0 < ρ) (h1 : ρ ≤ 1) (b : Bool) : |1 - tco ρ b| ≤ ρ⁻¹ := by
  have hi : 1 ≤ ρ⁻¹ := (one_le_inv₀ h0).mpr h1
  unfold tco
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma Sk_bound (h0 : 0 < ρ) (h1 : ρ ≤ 1) (k : Fin (n * n)) (ω : Fin (n * n) → Bool) :
    TroppMatrixConcentration.spectralNorm (Sk Z ρ k ω -
      ∫ η, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) ≤ ρ⁻¹ * entrySupNorm Z := by
  rw [Sk_dev Z ρ h0 h1]
  unfold TroppMatrixConcentration.spectralNorm
  have hZ := entrySup_nonneg Z
  have hK : 0 ≤ ρ⁻¹ * entrySupNorm Z := mul_nonneg (inv_nonneg.mpr h0.le) hZ
  exact cnorm_le _ _ hK (Ek_bound Z k _ _ hK
    (mul_le_mul_of_nonneg_right (tco_dev ρ h0 h1 _) hZ))

lemma dev_sq_integral (h0 : 0 < ρ) (h1 : ρ ≤ 1) (k : Fin (n * n)) :
    (∫ ω, (Sk Z ρ k ω - ∫ η, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) *
        (Sk Z ρ k ω - ∫ η, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))).conjTranspose
        ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) =
      cmap (((1 - ρ) / ρ * Z (eqv n k).1 (eqv n k).2 ^ 2) • Dg (eqv n k).1) ∧
    (∫ ω, (Sk Z ρ k ω - ∫ η, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))).conjTranspose *
        (Sk Z ρ k ω - ∫ η, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)))
        ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) =
      cmap (((1 - ρ) / ρ * Z (eqv n k).1 (eqv n k).2 ^ 2) • Dg (eqv n k).2) := by
  have hg : ∀ D : RealMatrix n n,
      ∫ ω, cmap (((1 - tco ρ (ω k)) ^ 2 * Z (eqv n k).1 (eqv n k).2 ^ 2) • D)
        ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)) =
      cmap (((1 - ρ) / ρ * Z (eqv n k).1 (eqv n k).2 ^ 2) • D) := by
    intro D
    rw [pi_integral_eval ρ h0.le h1 k
      (fun b => cmap (((1 - tco ρ b) ^ 2 * Z (eqv n k).1 (eqv n k).2 ^ 2) • D))]
    rw [cmap_smul, cmap_smul, cmap_add, smul_smul, smul_smul, ← add_smul]
    congr 2
    simp only [tco, if_true, Bool.false_eq_true, if_false]
    field_simp
    ring
  simp only [Sk_dev Z ρ h0 h1, (Ek_sq Z _ _).1, (Ek_sq Z _ _).2]
  exact ⟨hg _, hg _⟩

lemma diag_entry_le (h0 : 0 < ρ) (h1 : ρ ≤ 1) (f : Fin n × Fin n → Fin n)
    (hf : ∀ m, (Finset.univ.filter (fun p : Fin n × Fin n => f p = m)).card ≤ n) (m : Fin n) :
    |∑ k : Fin (n * n), if f (eqv n k) = m then (1 - ρ) / ρ * Z (eqv n k).1 (eqv n k).2 ^ 2 else 0|
      ≤ ρ⁻¹ * (n * entrySupNorm Z ^ 2) := by
  have ha : 0 ≤ (1 - ρ) / ρ := div_nonneg (by linarith) h0.le
  have hb : (1 - ρ) / ρ ≤ ρ⁻¹ := by
    rw [div_le_iff₀ h0, inv_mul_cancel₀ h0.ne']; linarith
  have hz : ∀ p : Fin n × Fin n, Z p.1 p.2 ^ 2 ≤ entrySupNorm Z ^ 2 := fun p => by
    have := pow_le_pow_left₀ (abs_nonneg _) (le_entrySup Z p.1 p.2) 2
    rwa [sq_abs] at this
  rw [Equiv.sum_comp (eqv n) (fun p => if f p = m then (1 - ρ) / ρ * Z p.1 p.2 ^ 2 else 0)]
  rw [abs_of_nonneg (Finset.sum_nonneg (fun p _ => by split_ifs <;> positivity))]
  rw [← Finset.sum_filter]
  calc ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => f p = m), (1 - ρ) / ρ * Z p.1 p.2 ^ 2
      ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => f p = m), ρ⁻¹ * entrySupNorm Z ^ 2 :=
        Finset.sum_le_sum (fun p _ => mul_le_mul hb (hz p) (sq_nonneg _) (inv_nonneg.mpr h0.le))
    _ = (Finset.univ.filter (fun p : Fin n × Fin n => f p = m)).card * (ρ⁻¹ * entrySupNorm Z ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * (ρ⁻¹ * entrySupNorm Z ^ 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hf m) (by positivity)
    _ = ρ⁻¹ * (n * entrySupNorm Z ^ 2) := by ring

lemma card_fst (m : Fin n) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 = m)).card ≤ n := by
  have : Finset.univ.filter (fun p : Fin n × Fin n => p.1 = m) =
      Finset.univ.image (fun j : Fin n => (m, j)) := by
    ext p; simp [Prod.ext_iff, eq_comm]
  rw [this]
  exact Finset.card_image_le.trans (by simp)

lemma card_snd (m : Fin n) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.2 = m)).card ≤ n := by
  have : Finset.univ.filter (fun p : Fin n × Fin n => p.2 = m) =
      Finset.univ.image (fun i : Fin n => (i, m)) := by
    ext p; simp [Prod.ext_iff, eq_comm]
  rw [this]
  exact Finset.card_image_le.trans (by simp)

lemma V_bound (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    TroppMatrixConcentration.spectralNorm (∑ k, ∫ ω,
        (Sk Z ρ k ω - ∫ η, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) *
        (Sk Z ρ k ω - ∫ η, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))).conjTranspose
        ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) ≤ ρ⁻¹ * (n * entrySupNorm Z ^ 2) ∧
    TroppMatrixConcentration.spectralNorm (∑ k, ∫ ω,
        (Sk Z ρ k ω - ∫ η, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))).conjTranspose *
        (Sk Z ρ k ω - ∫ η, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)))
        ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) ≤ ρ⁻¹ * (n * entrySupNorm Z ^ 2) := by
  have hK : 0 ≤ ρ⁻¹ * (n * entrySupNorm Z ^ 2) := by
    have := h0.le; positivity
  simp only [(dev_sq_integral Z ρ h0 h1 _).1, (dev_sq_integral Z ρ h0 h1 _).2]
  unfold TroppMatrixConcentration.spectralNorm
  rw [cmap_sum, cmap_sum, sum_Dg, sum_Dg]
  exact ⟨cnorm_le _ _ hK (diag_bound _ _ (diag_entry_le Z ρ h0 h1 Prod.fst card_fst)),
    cnorm_le _ _ hK (diag_bound _ _ (diag_entry_le Z ρ h0 h1 Prod.snd card_snd))⟩

lemma tail_main (h0 : 0 < ρ) (h1 : ρ ≤ 1) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (hZ : 0 < entrySupNorm Z) :
    bernoulliEventProb ρ (fun Ω => ¬ MatrixCompletion.spectralNorm
        (Z - ρ⁻¹ • samplingProjection Ω Z) ≤ t) ≤
      ((n + n : ℕ) : ℝ) * Real.exp (-(t ^ 2 / 2) /
        (ρ⁻¹ * (n * entrySupNorm Z ^ 2) + ρ⁻¹ * entrySupNorm Z * t / 3)) := by
  have := bern_prob ρ h0.le h1
  haveI : NeZero n := ⟨hn.ne'⟩
  have hL : 0 ≤ ρ⁻¹ * entrySupNorm Z := mul_nonneg (inv_nonneg.mpr h0.le) hZ.le
  have H := IntroMatrixConc.Sampling.corollary_6_1_2 (Measure.pi (fun _ : Fin (n * n) => bern ρ))
    (Sk Z ρ) (ρ⁻¹ * entrySupNorm Z) hL
    (Sk_meas Z ρ) (Sk_int Z ρ h0.le h1) (Sk_indep Z ρ h0.le h1)
    (fun k => Filter.Eventually.of_forall (fun ω => Sk_bound Z ρ h0 h1 k ω))
  dsimp only at H
  obtain ⟨hV, -, htail⟩ := H
  have hT := htail t ht.le
  have hVb := V_bound Z ρ h0 h1
  have hVle : TroppMatrixConcentration.rectSecondMoment (Measure.pi (fun _ : Fin (n * n) => bern ρ))
      (fun ω => ∑ k, Sk Z ρ k ω - ∫ η, ∑ k, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)))
      ≤ ρ⁻¹ * (n * entrySupNorm Z ^ 2) := by
    rw [hV]; exact max_le hVb.1 hVb.2
  have hV0 : 0 ≤ TroppMatrixConcentration.rectSecondMoment (Measure.pi (fun _ : Fin (n * n) => bern ρ))
      (fun ω => ∑ k, Sk Z ρ k ω - ∫ η, ∑ k, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) := by
    unfold TroppMatrixConcentration.rectSecondMoment TroppMatrixConcentration.spectralNorm
    exact le_max_of_le_left (norm_nonneg _)
  rw [bep_eq_sum]
  have hw : ∀ ω : Fin (n * n) → Bool, 0 ≤ ∏ k, (if ω k then ρ else 1 - ρ) := fun ω =>
    Finset.prod_nonneg (fun k _ => by split_ifs <;> linarith)
  calc _ ≤ ∑ ω : Fin (n * n) → Bool, (if ω ∈ {ω | t ≤ TroppMatrixConcentration.spectralNorm
          (∑ k, Sk Z ρ k ω - ∫ η, ∑ k, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)))} then
          ∏ k, (if ω k then ρ else 1 - ρ) else 0) := by
        refine Finset.sum_le_sum (fun ω _ => ?_)
        by_cases hg : MatrixCompletion.spectralNorm
            (Z - ρ⁻¹ • samplingProjection (setOf' ω) Z) ≤ t
        · rw [if_neg (not_not.mpr hg)]
          split_ifs
          · exact hw ω
          · exact le_rfl
        · rw [if_pos hg, if_pos]
          rw [Set.mem_ofPred_eq, Z_dev Z ρ h0 h1 ω]
          unfold TroppMatrixConcentration.spectralNorm
          push Not at hg
          exact hg.le.trans (spec_le_cnorm _)
    _ = ((Measure.pi (fun _ : Fin (n * n) => bern ρ)) {ω | t ≤ TroppMatrixConcentration.spectralNorm
          (∑ k, Sk Z ρ k ω - ∫ η, ∑ k, Sk Z ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)))}).toReal :=
        (pi_toReal_eq_sum ρ h0.le h1 _).symm
    _ ≤ _ := hT
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        rw [neg_div, neg_div, neg_le_neg_iff]
        have hLt : 0 < ρ⁻¹ * entrySupNorm Z * t / 3 := by
          have := inv_pos.mpr h0; positivity
        apply div_le_div_of_nonneg_left (by positivity) (by linarith)
        linarith

end Main

lemma arith32 (n : ℕ) (hn : 2 ≤ n) (ρ Zs : ℝ) (h0 : 0 < ρ) (hZ : 0 < Zs)
    (hlog : Real.log n ≤ ρ * n) :
    ((n + n : ℕ) : ℝ) * Real.exp (-((12 * Real.sqrt (n * Real.log n / ρ) * Zs) ^ 2 / 2) /
        (ρ⁻¹ * (n * Zs ^ 2) + ρ⁻¹ * Zs * (12 * Real.sqrt (n * Real.log n / ρ) * Zs) / 3)) ≤
      2 * (n : ℝ) ^ (-10 : ℤ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (n * Real.log n / ρ) := ⟨_, rfl⟩
  rw [← hsdef]
  have hs0 : 0 ≤ s := hsdef ▸ Real.sqrt_nonneg _
  have hs2 : s ^ 2 = n * Real.log n / ρ := by
    rw [hsdef, Real.sq_sqrt (by positivity)]
  have hsn : s ≤ n := by
    have h1 : s ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [hs2, div_le_iff₀ h0]; nlinarith
    by_contra hc
    push Not at hc
    nlinarith
  set A := ρ⁻¹ * Zs ^ 2 with hA
  have hA0 : 0 < A := by positivity
  have hD : 0 < ρ⁻¹ * (n * Zs ^ 2) + ρ⁻¹ * Zs * (12 * s * Zs) / 3 := by
    have := inv_pos.mpr h0; positivity
  have hkey : 11 * Real.log n ≤ (12 * s * Zs) ^ 2 / 2 /
      (ρ⁻¹ * (n * Zs ^ 2) + ρ⁻¹ * Zs * (12 * s * Zs) / 3) := by
    rw [le_div_iff₀ hD]
    have e1 : ρ⁻¹ * (n * Zs ^ 2) + ρ⁻¹ * Zs * (12 * s * Zs) / 3 = A * n + 4 * (A * s) := by
      rw [hA]; ring
    have e2 : (12 * s * Zs) ^ 2 / 2 = 72 * (s ^ 2 * Zs ^ 2) := by ring
    have e3 : s ^ 2 * Zs ^ 2 = Real.log n * (A * n) := by
      rw [hs2, hA]; field_simp
    rw [e1, e2, e3]
    have h1 : Real.log n * (A * s) ≤ Real.log n * (A * n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsn hA0.le) hL.le
    nlinarith
  have hexp : Real.exp (-((12 * s * Zs) ^ 2 / 2) /
      (ρ⁻¹ * (n * Zs ^ 2) + ρ⁻¹ * Zs * (12 * s * Zs) / 3)) ≤
      Real.exp (-((11 : ℕ) * Real.log n)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    push_cast
    linarith
  have hq : Real.exp (-((11 : ℕ) * Real.log n)) = ((n : ℝ) ^ 11)⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0]
  have hz : (n : ℝ) ^ (-10 : ℤ) = ((n : ℝ) ^ 10)⁻¹ := by
    simp [zpow_neg]
  rw [hz]
  calc _ ≤ ((n + n : ℕ) : ℝ) * ((n : ℝ) ^ 11)⁻¹ := by
        rw [← hq]; exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 2 * ((n : ℝ) ^ 10)⁻¹ := by
        push_cast
        field_simp
        ring

lemma bep_zero_of {N : ℕ} (p : ℝ) (P : Finset (Fin N × Fin N) → Prop) (h : ∀ B, ¬ P B) :
    bernoulliEventProb p P = 0 := by
  unfold bernoulliEventProb
  exact Finset.sum_eq_zero (fun B _ => if_neg (h B))

lemma bep_nonneg' {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : Finset (Fin N × Fin N) → Prop) :
    0 ≤ bernoulliEventProb p P := by
  unfold bernoulliEventProb
  exact Finset.sum_nonneg (fun B _ => by split_ifs; exact bw_nonneg hp0 hp1 B; exact le_rfl)

theorem main32 : ∃ C0 C0' c : ℝ, 0 < C0 ∧ 0 < C0' ∧ 0 < c ∧
      ∀ (n : ℕ) (Z : RealMatrix n n) (μ ρ0 : ℝ),
        0 < n → 1 ≤ μ → 0 < ρ0 → ρ0 ≤ 1 → ρ0 ≥ C0 * μ * Real.log n / n →
        bernoulliEventProb ρ0 (fun Ω =>
            MatrixCompletion.spectralNorm (Z - ρ0⁻¹ • samplingProjection Ω Z) ≤
              C0' * Real.sqrt (n * Real.log n / ρ0) * entrySupNorm Z) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  refine ⟨1, 12, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n Z μ ρ0 hn hμ hρ0 hρ1 hρ
  have hnot := bep_not (N := n) ρ0 (fun Ω =>
      MatrixCompletion.spectralNorm (Z - ρ0⁻¹ • samplingProjection Ω Z) ≤
        12 * Real.sqrt (n * Real.log n / ρ0) * entrySupNorm Z)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · have h1 : (n : ℝ) = 1 := by exact_mod_cast (by omega : n = 1)
    have hp := bep_nonneg' (N := n) hρ0.le hρ1 (fun Ω =>
      MatrixCompletion.spectralNorm (Z - ρ0⁻¹ • samplingProjection Ω Z) ≤
        12 * Real.sqrt (n * Real.log n / ρ0) * entrySupNorm Z)
    have hz1 : (n : ℝ) ^ (-10 : ℤ) = 1 := by rw [h1, one_zpow]
    rw [hz1, ge_iff_le]
    linarith
  suffices hs : bernoulliEventProb ρ0 (fun Ω => ¬
      MatrixCompletion.spectralNorm (Z - ρ0⁻¹ • samplingProjection Ω Z) ≤
        12 * Real.sqrt (n * Real.log n / ρ0) * entrySupNorm Z) ≤ 2 * (n : ℝ) ^ (-10 : ℤ) by
    rw [ge_iff_le]; linarith
  have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  rcases (entrySup_nonneg Z).eq_or_lt with hz | hz
  · have hZ0 : Z = 0 := by
      ext i j
      have := le_entrySup Z i j
      rw [← hz] at this
      exact abs_nonpos_iff.mp this
    rw [bep_zero_of]
    · positivity
    intro Ω hΩ
    apply hΩ
    have hS : samplingProjection Ω Z = 0 := by
      rw [hZ0]; ext i j; simp [samplingProjection]
    rw [hS, smul_zero, sub_zero, hZ0, entrySup_zero, mul_zero]
    unfold MatrixCompletion.spectralNorm
    simp
  · have hlog : Real.log n ≤ ρ0 * n := by
      have h2 := hρ
      rw [ge_iff_le, div_le_iff₀ (by linarith)] at h2
      nlinarith
    have ht : 0 < 12 * Real.sqrt (n * Real.log n / ρ0) * entrySupNorm Z := by
      have : 0 < Real.sqrt (n * Real.log n / ρ0) := Real.sqrt_pos.mpr (by positivity)
      positivity
    exact (tail_main Z ρ0 hρ0 hρ1 hn _ ht hz).trans (arith32 n hn2 ρ0 _ hρ0 hz hlog)

end RPCA32

open RPCA32

open RobustPCA.Recovery MatrixCompletion in
theorem solution :
    ∃ C0 C0' c : ℝ, 0 < C0 ∧ 0 < C0' ∧ 0 < c ∧
      ∀ (n : ℕ) (Z : RealMatrix n n) (μ ρ0 : ℝ),
        0 < n → 1 ≤ μ → 0 < ρ0 → ρ0 ≤ 1 → ρ0 ≥ C0 * μ * Real.log n / n →
        bernoulliEventProb ρ0 (fun Ω =>
            spectralNorm (Z - ρ0⁻¹ • samplingProjection Ω Z) ≤
              C0' * Real.sqrt (n * Real.log n / ρ0) * entrySupNorm Z) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  exact main32
