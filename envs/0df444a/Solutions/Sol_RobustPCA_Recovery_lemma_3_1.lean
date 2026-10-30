-- Prove2me | solution 1 for RobustPCA.Recovery.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T12:12:43.638488+00:00
-- url     : https://prove2.me/submissions/c261ea4a-b51d-493f-927f-98d692e515e2

import Mathlib
import Definitions.Def_RobustPCA_Recovery_Setup

set_option autoImplicit false

open MatrixCompletion



namespace RPCA28

open RobustPCA.Recovery
open scoped BigOperators Classical

/-! ## Projection algebra (copied from scratch/decomp/429b6866 and 0363db4b) -/

noncomputable def projM {n r : ℕ} (u : Fin r → Fin n → ℝ) : RealMatrix n n :=
  fun i a => ∑ k, u k i * u k a

noncomputable def PU {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.u

noncomputable def PV {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.v

lemma orth_idem {n r : ℕ} (u : Fin r → Fin n → ℝ)
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) :
    projM u * projM u = projM u := by
  ext i c
  simp only [Matrix.mul_apply, projM]
  have h1 : ∀ a, (∑ k, u k i * u k a) * (∑ l, u l a * u l c) =
      ∑ k, ∑ l, u k i * u l c * (u k a * u l a) := by
    intro a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  have h2 : ∀ l, ∑ a, u k i * u l c * (u k a * u l a) =
      u k i * u l c * (if k = l then 1 else 0) := by
    intro l
    rw [← Finset.mul_sum, hu]
  simp_rw [h2]
  simp

lemma PU_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : PU SV * PU SV = PU SV :=
  orth_idem SV.u SV.u_orthonormal

lemma PV_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : PV SV * PV SV = PV SV :=
  orth_idem SV.v SV.v_orthonormal

lemma projM_transpose {n r : ℕ} (u : Fin r → Fin n → ℝ) :
    Matrix.transpose (projM u) = projM u := by
  ext i a
  simp only [Matrix.transpose_apply, projM]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

lemma tangent_eq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV X = PU SV * X + X * PV SV - PU SV * X * PV SV := by
  ext i j
  simp only [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, PU, PV, projM]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]

lemma tangent_add {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    tangentProjection SV (X + Y) = tangentProjection SV X + tangentProjection SV Y := by
  simp only [tangent_eq, Matrix.mul_add, Matrix.add_mul]
  abel

lemma tangent_sub {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    tangentProjection SV (X - Y) = tangentProjection SV X - tangentProjection SV Y := by
  simp only [tangent_eq, Matrix.mul_sub, Matrix.sub_mul]
  abel

lemma tangent_smul {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (c : ℝ) (X : RealMatrix n n) :
    tangentProjection SV (c • X) = c • tangentProjection SV X := by
  simp only [tangent_eq, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add]

lemma tangent_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV (tangentProjection SV X) = tangentProjection SV X := by
  have hA := PU_idem SV
  have hB := PV_idem SV
  have hB' : ∀ Y : RealMatrix n n, Y * PV SV * PV SV = Y * PV SV := by
    intro Y; rw [Matrix.mul_assoc, hB]
  simp only [tangent_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    ← Matrix.mul_assoc, hA, hB']
  abel

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

/-! ## Frobenius inner product and the coordinate form of `P_T` -/

lemma inner_eq_trace {n : ℕ} (X Y : RealMatrix n n) :
    matrixInner X Y = (Matrix.transpose X * Y).trace := by
  simp only [matrixInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma inner_tangent {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    matrixInner (tangentProjection SV X) Y = matrixInner X (tangentProjection SV Y) := by
  rw [inner_eq_trace, inner_eq_trace, tangent_eq, tangent_eq]
  have hU : Matrix.transpose (PU SV) = PU SV := projM_transpose _
  have hV : Matrix.transpose (PV SV) = PV SV := projM_transpose _
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, hU, hV,
    Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub,
    Matrix.trace_add, Matrix.mul_assoc]
  have e1 : (PV SV * (Matrix.transpose X * Y)).trace =
      (Matrix.transpose X * (Y * PV SV)).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have e2 : (PV SV * (Matrix.transpose X * (PU SV * Y))).trace =
      (Matrix.transpose X * (PU SV * (Y * PV SV))).trace := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e1, e2]

lemma inner_coord {n : ℕ} (a b : Fin n) (M : RealMatrix n n) :
    matrixInner (coordinateMatrix a b) M = M a b := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero; intro j _; simp [hi]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma inner_coord' {n : ℕ} (a b : Fin n) (M : RealMatrix n n) :
    ∑ i, ∑ j, M i j * coordinateMatrix a b i j = M a b := by
  rw [← inner_coord a b M]
  unfold matrixInner
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => mul_comm _ _))

/-- `P_T e_ab`, the coefficient matrix of the entry `(a, b)` of `P_T`. -/
noncomputable def Ecoef {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b : Fin n) :
    RealMatrix n n :=
  tangentProjection SV (coordinateMatrix a b)

lemma tangent_entry {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Y : RealMatrix n n)
    (a b : Fin n) : tangentProjection SV Y a b = ∑ i, ∑ j, Ecoef SV a b i j * Y i j := by
  rw [← inner_coord a b (tangentProjection SV Y), ← inner_tangent]
  rfl

lemma Ecoef_sq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b : Fin n) :
    ∑ i, ∑ j, Ecoef SV a b i j ^ 2 = Ecoef SV a b a b := by
  have h := tangent_entry SV (Ecoef SV a b) a b
  rw [Ecoef, tangent_idem] at h
  rw [Ecoef, h]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma Ecoef_self {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b i j : Fin n) :
    Ecoef SV a b i j = ∑ x, ∑ y, Ecoef SV i j x y * Ecoef SV a b x y := by
  have h := tangent_entry SV (Ecoef SV a b) i j
  rw [Ecoef, tangent_idem] at h
  rw [Ecoef, h]

lemma Ecoef_diag {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b : Fin n) :
    Ecoef SV a b a b = PU SV a a + PV SV b b - PU SV a a * PV SV b b := by
  rw [Ecoef, tangent_eq]
  simp [Matrix.mul_apply, coordinateMatrix, Matrix.sub_apply, Matrix.add_apply, ite_and]

lemma PU_diag {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a : Fin n) :
    PU SV a a = ∑ k, SV.u k a ^ 2 := by
  unfold PU projM
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma PV_diag {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (b : Fin n) :
    PV SV b b = ∑ k, SV.v k b ^ 2 := by
  unfold PV projM
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma Ecoef_sq_le {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ)
    (hinc : Incoherent SV μ) (a b : Fin n) :
    ∑ i, ∑ j, Ecoef SV a b i j ^ 2 ≤ 2 * μ * r / n := by
  rw [Ecoef_sq, Ecoef_diag, PU_diag, PV_diag]
  have h1 := hinc.1 a
  have h2 := hinc.2.1 b
  have h3 : 0 ≤ ∑ k, SV.u k a ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h4 : 0 ≤ ∑ k, SV.v k b ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h5 := mul_nonneg h3 h4
  have e : 2 * μ * r / n = μ * r / n + μ * r / n := by ring
  rw [e]
  linarith

lemma Ecoef_abs_le {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ)
    (hinc : Incoherent SV μ) (a b i j : Fin n) :
    |Ecoef SV a b i j| ≤ 2 * μ * r / n := by
  have hK : 0 ≤ 2 * μ * r / n :=
    le_trans (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
      (Ecoef_sq_le SV μ hinc a b)
  rw [Ecoef_self]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun y => Ecoef SV i j y.1 y.2) (fun y => Ecoef SV a b y.1 y.2)
  simp only [Fintype.sum_prod_type] at hcs
  have hA := Ecoef_sq_le SV μ hinc i j
  have hB := Ecoef_sq_le SV μ hinc a b
  have hsq : (∑ x, ∑ y, Ecoef SV i j x y * Ecoef SV a b x y) ^ 2 ≤
      (2 * μ * r / n) ^ 2 := by
    refine le_trans hcs ?_
    rw [sq]
    exact mul_le_mul hA hB (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => sq_nonneg _))) hK
  rw [← sq_abs] at hsq
  exact (sq_le_sq₀ (abs_nonneg _) hK).mp hsq

/-- The deviation `Z - q⁻¹ P_T P_Ω Z` for `Z ∈ T`, entrywise, as a Bernoulli sum. -/
lemma dev_entry {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Z : RealMatrix n n)
    (hZ : tangentProjection SV Z = Z) (q : ℝ) (Ω : Finset (Fin n × Fin n)) (a b : Fin n) :
    (Z - q⁻¹ • tangentProjection SV (samplingProjection Ω Z)) a b =
      ∑ y : Fin n × Fin n, Ecoef SV a b y.1 y.2 * Z y.1 y.2 *
        (1 - (if y ∈ Ω then 1 else 0) / q) := by
  have h1 : Z a b = ∑ i, ∑ j, Ecoef SV a b i j * Z i j := by
    have := tangent_entry SV Z a b
    rwa [hZ] at this
  have h2 := tangent_entry SV (samplingProjection Ω Z) a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [h2]
  rw [h1, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [samplingProjection]
  split_ifs <;> ring

/-! ## Bernstein-type tail for weighted centred Bernoulli sums -/

lemma prod_split {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) (F G : α → ℝ) :
    ∏ x, (if x ∈ t then F x else G x) = (∏ x ∈ t, F x) * ∏ x ∈ Finset.univ \ t, G x := by
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext x; simp
  · congr 1; ext x; simp

lemma sum_prod_ite {N : ℕ} (F G : Fin N × Fin N → ℝ) :
    ∑ Ω : Finset (Fin N × Fin N), ∏ x, (if x ∈ Ω then F x else G x) = ∏ x, (F x + G x) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  exact Finset.sum_congr rfl (fun t _ => prod_split t F G)

lemma mgf_eq {N : ℕ} (q θ : ℝ) (c : Fin N × Fin N → ℝ) :
    ∑ Ω : Finset (Fin N × Fin N), bernoulliObservationWeight q Ω *
        Real.exp (θ * ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) =
      ∏ x, (q * Real.exp (θ * (c x * (1 - 1 / q))) + (1 - q) * Real.exp (θ * c x)) := by
  rw [← sum_prod_ite]
  refine Finset.sum_congr rfl (fun Ω _ => ?_)
  rw [bw_eq_prod, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  split_ifs <;> simp

lemma factor_le (q θ c : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hθ : 0 ≤ θ) (hM : θ * |c| ≤ q) :
    q * Real.exp (θ * (c * (1 - 1 / q))) + (1 - q) * Real.exp (θ * c) ≤
      Real.exp (θ ^ 2 * c ^ 2 / q) := by
  have hy2 : |θ * c| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hθ]; linarith
  have hq' : 1 ≤ 1 / q := by rw [le_div_iff₀ hq0]; linarith
  have h1q : |1 - 1 / q| ≤ 1 / q := by
    rw [abs_le]; constructor <;> linarith
  have hy1 : |θ * (c * (1 - 1 / q))| ≤ 1 := by
    rw [show θ * (c * (1 - 1 / q)) = (θ * c) * (1 - 1 / q) by ring, abs_mul]
    calc |θ * c| * |1 - 1 / q| ≤ |θ * c| * (1 / q) :=
          mul_le_mul_of_nonneg_left h1q (abs_nonneg _)
      _ = (θ * |c|) / q := by rw [abs_mul, abs_of_nonneg hθ]; ring
      _ ≤ 1 := by rw [div_le_one hq0]; exact hM
  have e1 := Real.abs_exp_sub_one_sub_id_le hy1
  have e2 := Real.abs_exp_sub_one_sub_id_le hy2
  have f1 := (abs_le.mp e1).2
  have f2 := (abs_le.mp e2).2
  have key : q * (1 + θ * (c * (1 - 1 / q)) + (θ * (c * (1 - 1 / q))) ^ 2) +
      (1 - q) * (1 + θ * c + (θ * c) ^ 2) = 1 + θ ^ 2 * c ^ 2 * (1 - q) / q := by
    field_simp; ring
  have g1 := mul_le_mul_of_nonneg_left (show Real.exp (θ * (c * (1 - 1 / q))) ≤
    1 + θ * (c * (1 - 1 / q)) + (θ * (c * (1 - 1 / q))) ^ 2 by linarith) hq0.le
  have g2 := mul_le_mul_of_nonneg_left (show Real.exp (θ * c) ≤
    1 + θ * c + (θ * c) ^ 2 by linarith) (show (0 : ℝ) ≤ 1 - q by linarith)
  have g3 : θ ^ 2 * c ^ 2 * (1 - q) / q ≤ θ ^ 2 * c ^ 2 / q := by
    apply div_le_div_of_nonneg_right _ hq0.le
    have : 0 ≤ θ ^ 2 * c ^ 2 := by positivity
    nlinarith
  have g4 := Real.add_one_le_exp (θ ^ 2 * c ^ 2 / q)
  linarith

lemma tail_one {N : ℕ} (q θ t : ℝ) (c : Fin N × Fin N → ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hθ : 0 ≤ θ) (hM : ∀ x, θ * |c x| ≤ q) :
    bernoulliEventProb q (fun Ω => t ≤ ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) ≤
      Real.exp (-θ * t + θ ^ 2 * (∑ x, c x ^ 2) / q) := by
  have step1 : bernoulliEventProb q
      (fun Ω => t ≤ ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) ≤
      Real.exp (-θ * t) * ∑ Ω : Finset (Fin N × Fin N), bernoulliObservationWeight q Ω *
        Real.exp (θ * ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) := by
    unfold bernoulliEventProb
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Ω _ => ?_)
    have hw := bw_nonneg hq0.le hq1 Ω
    split_ifs with h
    · have h1 : 1 ≤ Real.exp (-θ * t) *
          Real.exp (θ * ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      nlinarith
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hw (Real.exp_pos _).le)
  rw [mgf_eq] at step1
  refine le_trans step1 ?_
  have hprod : ∏ x, (q * Real.exp (θ * (c x * (1 - 1 / q))) + (1 - q) * Real.exp (θ * c x)) ≤
      ∏ x, Real.exp (θ ^ 2 * c x ^ 2 / q) := by
    apply Finset.prod_le_prod
    · intro x _
      exact add_nonneg (mul_nonneg hq0.le (Real.exp_pos _).le)
        (mul_nonneg (by linarith) (Real.exp_pos _).le)
    · intro x _
      exact factor_le q θ (c x) hq0 hq1 hθ (hM x)
  calc _ ≤ Real.exp (-θ * t) * ∏ x, Real.exp (θ ^ 2 * c x ^ 2 / q) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-θ * t + θ ^ 2 * (∑ x, c x ^ 2) / q) := by
        rw [← Real.exp_sum, ← Real.exp_add]
        congr 1
        rw [Finset.mul_sum, Finset.sum_div]

lemma bep_union {N : ℕ} {ι : Type*} [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : Finset (Fin N × Fin N) → Prop) (G : ι → Finset (Fin N × Fin N) → Prop)
    (h : ∀ Ω, F Ω → ∃ i, G i Ω) :
    bernoulliEventProb p F ≤ ∑ i, bernoulliEventProb p (G i) := by
  unfold bernoulliEventProb
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun Ω _ => ?_)
  have hw := bw_nonneg hp0 hp1 Ω
  have hnn : ∀ i ∈ (Finset.univ : Finset ι),
      0 ≤ (if G i Ω then bernoulliObservationWeight p Ω else 0) := by
    intro i _; split_ifs <;> first | exact hw | exact le_refl _
  split_ifs with hF
  · obtain ⟨i, hi⟩ := h Ω hF
    calc bernoulliObservationWeight p Ω =
          (if G i Ω then bernoulliObservationWeight p Ω else 0) := by rw [if_pos hi]
      _ ≤ _ := Finset.single_le_sum hnn (Finset.mem_univ i)
  · exact Finset.sum_nonneg hnn

lemma bep_false {N : ℕ} (p : ℝ) (F : Finset (Fin N × Fin N) → Prop) (h : ∀ Ω, ¬ F Ω) :
    bernoulliEventProb p F = 0 := by
  unfold bernoulliEventProb
  exact Finset.sum_eq_zero (fun Ω _ => if_neg (h Ω))


/-! ## G31: entrywise concentration on `T` (CLMW Lemma 3.1, failure `2 n^-11`) -/

def G31 : Prop :=
  ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
    ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ : ℝ) (Z : RealMatrix n n)
      (ε ρ0 : ℝ),
      0 < n → Incoherent SV μ → tangentProjection SV Z = Z → 0 < ε → ε ≤ 1 →
      0 < ρ0 → ρ0 ≤ 1 → ρ0 ≥ C0 * ε⁻¹ ^ 2 * μ * r * Real.log n / n →
      bernoulliEventProb ρ0 (fun Ω =>
          entrySupNorm (Z - ρ0⁻¹ • tangentProjection SV (samplingProjection Ω Z)) ≤
            ε * entrySupNorm Z) ≥
        1 - c * (n : ℝ) ^ (-11 : ℤ)

lemma g31_exp (ε q K Zs S2 : ℝ) (hK : 0 < K) (hZs : 0 < Zs) (hq : 0 < q)
    (hS : S2 ≤ Zs ^ 2 * K) :
    -(ε * q / (2 * K * Zs)) * (ε * Zs) + (ε * q / (2 * K * Zs)) ^ 2 * S2 / q ≤
      -(ε ^ 2 * q / (4 * K)) := by
  have h1 : (ε * q / (2 * K * Zs)) ^ 2 * S2 / q ≤
      (ε * q / (2 * K * Zs)) ^ 2 * (Zs ^ 2 * K) / q := by
    apply div_le_div_of_nonneg_right _ hq.le
    exact mul_le_mul_of_nonneg_left hS (sq_nonneg _)
  have h2 : -(ε * q / (2 * K * Zs)) * (ε * Zs) +
      (ε * q / (2 * K * Zs)) ^ 2 * (Zs ^ 2 * K) / q = -(ε ^ 2 * q / (4 * K)) := by
    field_simp
    ring
  linarith

lemma g31_log (ε q μ r n : ℝ) (hn : 0 < n) (hμr : 0 < μ * r) (hε : 0 < ε)
    (hq : q ≥ 104 * ε⁻¹ ^ 2 * μ * r * Real.log n / n) :
    -(ε ^ 2 * q / (4 * (2 * μ * r / n))) ≤ -13 * Real.log n := by
  have e : ε ^ 2 * q / (4 * (2 * μ * r / n)) = ε ^ 2 * q * n / (8 * (μ * r)) := by
    field_simp
    ring
  rw [e]
  have hεn : (0 : ℝ) ≤ ε ^ 2 * n := by positivity
  have h0 := mul_le_mul_of_nonneg_left hq hεn
  have e2 : ε ^ 2 * n * (104 * ε⁻¹ ^ 2 * μ * r * Real.log n / n) =
      104 * (μ * r) * Real.log n := by
    field_simp
  have h1 : 104 * (μ * r) * Real.log n ≤ ε ^ 2 * q * n := by
    rw [← e2]; linarith
  have h2 : 13 * Real.log n ≤ ε ^ 2 * q * n / (8 * (μ * r)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

lemma count_pow (x : ℝ) (hx : 0 < x) :
    x * x * 2 * Real.exp (-13 * Real.log x) = 2 * x ^ (-11 : ℤ) := by
  rw [show (-13 : ℝ) * Real.log x = ((-13 : ℤ) : ℝ) * Real.log x by norm_num,
    ← Real.log_zpow, Real.exp_log (zpow_pos hx _)]
  have h : x ^ (2 : ℤ) * x ^ (-13 : ℤ) = x ^ (-11 : ℤ) := by
    rw [← zpow_add₀ hx.ne']; norm_num
  rw [← h, zpow_two]
  ring

lemma g31_core {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ ε q : ℝ)
    (Z : RealMatrix n n) (hn : 0 < n) (hinc : Incoherent SV μ)
    (hZ : tangentProjection SV Z = Z) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hcond : q ≥ 104 * ε⁻¹ ^ 2 * μ * r * Real.log n / n) :
    bernoulliEventProb q (fun Ω => ¬ entrySupNorm
        (Z - q⁻¹ • tangentProjection SV (samplingProjection Ω Z)) ≤ ε * entrySupNorm Z) ≤
      2 * (n : ℝ) ^ (-11 : ℤ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * μ * r / n := ⟨_, rfl⟩
  obtain ⟨Zs, hZsdef⟩ : ∃ Zs : ℝ, Zs = entrySupNorm Z := ⟨_, rfl⟩
  have hZs0 : 0 ≤ Zs := hZsdef ▸ entrySup_nonneg Z
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact le_trans (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
      (Ecoef_sq_le SV μ hinc ⟨0, hn⟩ ⟨0, hn⟩)
  have hEabs : ∀ a b i j, |Ecoef SV a b i j| ≤ K := by
    intro a b i j; rw [hKdef]; exact Ecoef_abs_le SV μ hinc a b i j
  have hEsq : ∀ a b, ∑ i, ∑ j, Ecoef SV a b i j ^ 2 ≤ K := by
    intro a b; rw [hKdef]; exact Ecoef_sq_le SV μ hinc a b
  have hZle : ∀ i j, |Z i j| ≤ Zs := by
    intro i j; rw [hZsdef]; exact le_entrySup Z i j
  have hcabs : ∀ (ab y : Fin n × Fin n),
      |Ecoef SV ab.1 ab.2 y.1 y.2 * Z y.1 y.2| ≤ K * Zs := by
    intro ab y
    rw [abs_mul]
    exact mul_le_mul (hEabs _ _ _ _) (hZle _ _) (abs_nonneg _) hK0
  have hcsq : ∀ ab : Fin n × Fin n,
      ∑ y : Fin n × Fin n, (Ecoef SV ab.1 ab.2 y.1 y.2 * Z y.1 y.2) ^ 2 ≤ Zs ^ 2 * K := by
    intro ab
    have h1 : ∀ y : Fin n × Fin n, (Ecoef SV ab.1 ab.2 y.1 y.2 * Z y.1 y.2) ^ 2 ≤
        Zs ^ 2 * Ecoef SV ab.1 ab.2 y.1 y.2 ^ 2 := by
      intro y
      rw [mul_pow, mul_comm (Zs ^ 2)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [← sq_abs (Z _ _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hZle _ _) 2
    calc ∑ y : Fin n × Fin n, (Ecoef SV ab.1 ab.2 y.1 y.2 * Z y.1 y.2) ^ 2
        ≤ ∑ y : Fin n × Fin n, Zs ^ 2 * Ecoef SV ab.1 ab.2 y.1 y.2 ^ 2 :=
          Finset.sum_le_sum (fun y _ => h1 y)
      _ = Zs ^ 2 * ∑ i, ∑ j, Ecoef SV ab.1 ab.2 i j ^ 2 := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type]
      _ ≤ Zs ^ 2 * K := mul_le_mul_of_nonneg_left (hEsq _ _) (sq_nonneg _)
  rcases (mul_nonneg hK0 hZs0).eq_or_lt with h0 | hpos
  · -- degenerate case: every coefficient vanishes
    rw [bep_false]
    · positivity
    intro Ω hΩ
    apply hΩ
    have hmul : 0 ≤ ε * entrySupNorm Z := mul_nonneg hε0.le (entrySup_nonneg Z)
    refine entrySup_le _ _ hmul (fun a b => ?_)
    rw [dev_entry SV Z hZ q Ω a b]
    have hz : ∀ y : Fin n × Fin n, Ecoef SV a b y.1 y.2 * Z y.1 y.2 = 0 := by
      intro y
      have := hcabs (a, b) y
      rw [← h0] at this
      exact abs_nonpos_iff.mp this
    simp only [hz, zero_mul, Finset.sum_const_zero, abs_zero]
    exact hmul
  · have hK : 0 < K := by
      rcases hK0.eq_or_lt with h | h
      · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have hZs : 0 < Zs := by
      rcases hZs0.eq_or_lt with h | h
      · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have hμr : 0 < μ * r := by
      have h := mul_pos hK hnR
      rw [hKdef, div_mul_cancel₀ _ hnR.ne'] at h
      linarith
    obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = ε * q / (2 * K * Zs) := ⟨_, rfl⟩
    have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
    have himp : ∀ Ω : Finset (Fin n × Fin n), ¬ entrySupNorm
        (Z - q⁻¹ • tangentProjection SV (samplingProjection Ω Z)) ≤ ε * entrySupNorm Z →
        ∃ i : (Fin n × Fin n) × Bool, ε * Zs ≤ ∑ y : Fin n × Fin n,
          ((if i.2 then 1 else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)) *
            (1 - (if y ∈ Ω then 1 else 0) / q) := by
      intro Ω hΩ
      by_contra hno
      push Not at hno
      apply hΩ
      rw [← hZsdef]
      refine entrySup_le _ _ (by positivity) (fun a b => ?_)
      rw [dev_entry SV Z hZ q Ω a b, abs_le]
      have h1 := hno ((a, b), true)
      have h2 := hno ((a, b), false)
      simp only [if_true, one_mul, Bool.false_eq_true, if_false, neg_one_mul, neg_mul,
        Finset.sum_neg_distrib] at h1 h2
      constructor <;> linarith
    have htail : ∀ i : (Fin n × Fin n) × Bool, bernoulliEventProb q (fun Ω =>
        ε * Zs ≤ ∑ y : Fin n × Fin n,
          ((if i.2 then 1 else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)) *
            (1 - (if y ∈ Ω then 1 else 0) / q)) ≤ Real.exp (-13 * Real.log n) := by
      intro i
      have hM : ∀ y : Fin n × Fin n,
          θ * |(if i.2 then 1 else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)| ≤ q := by
        intro y
        have hs : |(if i.2 then (1 : ℝ) else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)| =
            |Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2| := by
          split_ifs <;> simp
        rw [hs]
        calc θ * |Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2| ≤ θ * (K * Zs) :=
              mul_le_mul_of_nonneg_left (hcabs _ _) hθ0
          _ = ε * q / 2 := by rw [hθdef]; field_simp
          _ ≤ q := by nlinarith
      refine le_trans (tail_one q θ (ε * Zs) _ hq0 hq1 hθ0 hM) ?_
      apply Real.exp_le_exp.mpr
      have hsq : ∑ y : Fin n × Fin n,
          ((if i.2 then (1 : ℝ) else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)) ^ 2 =
          ∑ y : Fin n × Fin n, (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2) ^ 2 := by
        refine Finset.sum_congr rfl (fun y _ => ?_); split_ifs <;> ring
      rw [hsq]
      have e1 := g31_exp ε q K Zs _ hK hZs hq0 (hcsq i.1)
      have e2 := g31_log ε q μ r n hnR hμr hε0 hcond
      rw [← hKdef] at e2
      rw [hθdef]
      linarith
    calc _ ≤ ∑ i : (Fin n × Fin n) × Bool, bernoulliEventProb q (fun Ω =>
          ε * Zs ≤ ∑ y : Fin n × Fin n,
            ((if i.2 then 1 else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)) *
              (1 - (if y ∈ Ω then 1 else 0) / q)) := bep_union hq0.le hq1 _ _ himp
      _ ≤ ∑ _i : (Fin n × Fin n) × Bool, Real.exp (-13 * Real.log n) :=
          Finset.sum_le_sum (fun i _ => htail i)
      _ = 2 * (n : ℝ) ^ (-11 : ℤ) := by
          rw [Finset.sum_const, Finset.card_univ]
          simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
          push_cast
          exact count_pow _ hnR

theorem g31 : G31 := by
  refine ⟨104, 2, by norm_num, by norm_num, ?_⟩
  intro n r L0 SV μ Z ε ρ0 hn hinc hZ hε0 hε1 hρ0 hρ1 hcond
  have h := g31_core SV μ ε ρ0 Z hn hinc hZ hε0 hε1 hρ0 hρ1 hcond
  rw [bep_not] at h
  linarith


/-! ## G32 in the dense regime: spectral norm of `Z - q⁻¹ P_Ω Z` via a net + Hoeffding -/

lemma n10_le {n : ℕ} (hn : 0 < n) : (n : ℝ) ^ (-11 : ℤ) ≤ (n : ℝ) ^ (-10 : ℤ) := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact zpow_le_zpow_right₀ h1 (by norm_num)

end RPCA28

open RPCA28 in
theorem lemma31_aux :
    ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ : ℝ) (Z : RealMatrix n n)
        (ε ρ0 : ℝ),
        0 < n → RobustPCA.Recovery.Incoherent SV μ → tangentProjection SV Z = Z → 0 < ε → ε ≤ 1 →
        0 < ρ0 → ρ0 ≤ 1 → ρ0 ≥ C0 * ε⁻¹ ^ 2 * μ * r * Real.log n / n →
        bernoulliEventProb ρ0 (fun Ω =>
            entrySupNorm (Z - ρ0⁻¹ • tangentProjection SV (samplingProjection Ω Z)) ≤
              ε * entrySupNorm Z) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  obtain ⟨C0, c, hC0, hc, h⟩ := g31
  refine ⟨C0, c, hC0, hc, ?_⟩
  intro n r L0 SV μ Z ε ρ0 hn hinc hZ hε0 hε1 hρ0 hρ1 hcond
  have h1 := h n r L0 SV μ Z ε ρ0 hn hinc hZ hε0 hε1 hρ0 hρ1 hcond
  have h2 := n10_le hn
  have h3 : c * (n : ℝ) ^ (-11 : ℤ) ≤ c * (n : ℝ) ^ (-10 : ℤ) :=
    mul_le_mul_of_nonneg_left h2 hc.le
  linarith

open MatrixCompletion RobustPCA.Recovery in
theorem solution :
    ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ : ℝ) (Z : RealMatrix n n)
        (ε ρ0 : ℝ),
        0 < n → Incoherent SV μ → tangentProjection SV Z = Z → 0 < ε → ε ≤ 1 →
        0 < ρ0 → ρ0 ≤ 1 → ρ0 ≥ C0 * ε⁻¹ ^ 2 * μ * r * Real.log n / n →
        bernoulliEventProb ρ0 (fun Ω =>
            entrySupNorm (Z - ρ0⁻¹ • tangentProjection SV (samplingProjection Ω Z)) ≤
              ε * entrySupNorm Z) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  exact lemma31_aux
