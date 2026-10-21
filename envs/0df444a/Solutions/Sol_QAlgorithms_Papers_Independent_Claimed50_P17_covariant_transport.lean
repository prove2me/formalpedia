-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.covariant_transport
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:52:08.490403+00:00
-- url     : https://prove2.me/submissions/37fc424e-538f-453f-9278-0e072e943c2e

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

theorem g58d_term {d : ℕ} (R : ReplicationChoiArray d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) (i j : Fin d) :
    Matrix.trace (replica R U i j *
      Matrix.kronecker (measurementEffect U i) (measurementEffect U j)) =
    ∑ k, ((representation U)ᴴ * diagonalBlocks R i j k * representation U) ((i,j),k) ((i,j),k) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, replica, Matrix.kronecker, Matrix.kroneckerMap_apply,
    measurementEffect, representation, diagonalBlocks, Matrix.conjTranspose_apply, Matrix.map_apply,
    Finset.sum_mul, Fintype.sum_prod_type, star_mul', RCLike.star_def, Complex.conj_conj]
  simp only [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv
    { toFun := fun p : Fin d × Fin d × Fin d × Fin d × Fin d × Fin d × Fin d =>
        (p.2.2.2.2.1, p.1, p.2.1, p.2.2.2.2.2.2, p.2.2.1, p.2.2.2.1, p.2.2.2.2.2.1)
      invFun := fun q : Fin d × Fin d × Fin d × Fin d × Fin d × Fin d × Fin d =>
        (q.2.1, q.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1, q.1, q.2.2.2.2.2.2, q.2.2.2.1)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  intro x
  simp only [Equiv.coe_fn_mk]; ring

theorem g58d_rep_unitary {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    (representation U)ᴴ * representation U = 1 := by
  have h1 : (U : Op (Fin d))ᴴ * (U : Op (Fin d)) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have h2 : ((U : Op (Fin d)).map conj)ᴴ * (U : Op (Fin d)).map conj = 1 := by
    ext a b
    have := congrFun (congrFun h1 a) b
    have h3 := congrArg conj this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul, RCLike.star_def,
      Complex.conj_conj, Matrix.one_apply] at h3
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, RCLike.star_def,
      Complex.conj_conj, Matrix.one_apply, h3]
    split_ifs <;> simp
  have m1 : (U : Op (Fin d)).map conj ∈ unitary (Matrix (Fin d) (Fin d) ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mpr h2
  have m2 : (U : Op (Fin d)) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := U.2
  have m3 := Matrix.kronecker_mem_unitary (Matrix.kronecker_mem_unitary m1 m1) m2
  exact Unitary.star_mul_self_of_mem m3

theorem g58d_rep_unitary' {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    representation U * (representation U)ᴴ = 1 :=
  mul_eq_one_comm.mp (g58d_rep_unitary U)

theorem g58d_si_cov {d : ℕ} (R : ReplicationChoiArray d) (hCov : BlocksCommuteWithRotations (diagonalBlocks R))
    (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    scoreIntegrand R U = (1 / (d : ℝ)^2) * ∑ i, ∑ j, ∑ k,
      (diagonalBlocks R i j k ((i,j),k) ((i,j),k)).re := by
  unfold scoreIntegrand
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [g58d_term, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_assoc, hCov U i j k, ← Matrix.mul_assoc, g58d_rep_unitary, Matrix.one_mul]

theorem g58d_score_cov {d : ℕ} (R : ReplicationChoiArray d) (hCov : BlocksCommuteWithRotations (diagonalBlocks R)) :
    haarReplicationScore R = (1 / (d : ℝ)^2) * ∑ i, ∑ j, ∑ k,
      (diagonalBlocks R i j k ((i,j),k) ((i,j),k)).re := by
  unfold haarReplicationScore
  simp only [g58d_si_cov R hCov]
  rw [integral_const]
  have hu : QAlgorithms.Schur.unitaryHaar d Set.univ = 1 := Measure.haarMeasure_self
  simp [Measure.real, hu]

theorem g58d_perm_mem {d : ℕ} (τ : Equiv.Perm (Fin d)) :
    permutationMatrix τ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, permutationMatrix, Matrix.star_apply, Matrix.one_apply]
  have hh : ∀ x, (b = τ x) ↔ (x = τ.symm b) := by
    intro x; constructor <;> intro h <;> subst h <;> simp
  simp only [hh, Finset.sum_ite_eq', Finset.mem_univ, if_true, Equiv.apply_symm_apply]
  split_ifs <;> simp_all

theorem g58d_perm_cov {d : ℕ} (M : Op (ABC d)) (τ : Equiv.Perm (Fin d))
    (h : M * representation ⟨_, g58d_perm_mem τ⟩ = representation ⟨_, g58d_perm_mem τ⟩ * M)
    (a b : ABC d) : M ((τ a.1.1, τ a.1.2), τ a.2) ((τ b.1.1, τ b.1.2), τ b.2) = M a b := by
  have := congrFun (congrFun h ((τ a.1.1, τ a.1.2), τ a.2)) b
  simp only [Matrix.mul_apply, representation, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.map_apply, permutationMatrix, Fintype.sum_prod_type] at this
  simp [apply_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] at this
  exact this

abbrev g58d_G (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

instance g58d_prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

instance g58d_haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

theorem g58d_int_cont {d : ℕ} {f : g58d_G d → ℂ} (hf : Continuous f) :
    Integrable f (QAlgorithms.Schur.unitaryHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem g58d_coe_cont {d : ℕ} (i j : Fin d) : Continuous (fun U : g58d_G d => (U : Op (Fin d)) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem g58d_right_inv (d : ℕ) (g : g58d_G d) :
    Measure.map (· * g) (QAlgorithms.Schur.unitaryHaar d) = QAlgorithms.Schur.unitaryHaar d := by
  haveI : IsProbabilityMeasure (Measure.map (· * g) (QAlgorithms.Schur.unitaryHaar d)) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

instance g58d_rinv (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsMulRightInvariant :=
  ⟨fun g => g58d_right_inv d g⟩

instance g58d_invinv (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsInvInvariant := by
  constructor
  haveI : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d).inv := by
    rw [Measure.inv]; exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  haveI : (QAlgorithms.Schur.unitaryHaar d).inv.IsHaarMeasure := ⟨⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem g58d_ent {d : ℕ} {n : Type} [Fintype n] (F : g58d_G d → Matrix n n ℂ)
    (hF : ∀ x y, Integrable (fun U => F U x y) (QAlgorithms.Schur.unitaryHaar d)) (x y : n) :
    (∫ U, F U ∂QAlgorithms.Schur.unitaryHaar d) x y = ∫ U, F U x y ∂QAlgorithms.Schur.unitaryHaar d := by
  have h1 : ∀ x : n, Integrable (fun U => F U x) (QAlgorithms.Schur.unitaryHaar d) :=
    fun x => Integrable.of_eval (hF x)
  exact (congrFun (eval_integral h1 x) y).trans (eval_integral (hF x) y)

theorem g58d_int_contR {d : ℕ} {f : g58d_G d → ℝ} (hf : Continuous f) :
    Integrable f (QAlgorithms.Schur.unitaryHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem g58d_rep_cont {d : ℕ} (x a : ABC d) : Continuous (fun U : g58d_G d => representation U x a) := by
  simp only [representation, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.map_apply]
  exact ((Complex.continuous_conj.comp (g58d_coe_cont _ _)).mul
    (Complex.continuous_conj.comp (g58d_coe_cont _ _))).mul (g58d_coe_cont _ _)

theorem g58d_A_cont {d : ℕ} {n : Type} [Fintype n] (A : g58d_G d → Matrix n n ℂ)
    (hA : ∀ x a, Continuous (fun U => A U x a)) (M : Matrix n n ℂ) (x y : n) :
    Continuous (fun U : g58d_G d => (A U * M * (A U)ᴴ) x y) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  exact continuous_finset_sum _ (fun b _ => (continuous_finset_sum _ (fun a _ =>
    (hA x a).mul continuous_const)).mul (Complex.continuous_conj.comp (hA y b)))

theorem g58d_A_cont' {d : ℕ} {n : Type} [Fintype n] (A : g58d_G d → Matrix n n ℂ)
    (hA : ∀ x a, Continuous (fun U => A U x a)) (M : Matrix n n ℂ) (x y : n) :
    Continuous (fun U : g58d_G d => ((A U)ᴴ * M * A U) x y) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  exact continuous_finset_sum _ (fun b _ => (continuous_finset_sum _ (fun a _ =>
    (Complex.continuous_conj.comp (hA a x)).mul continuous_const)).mul (hA b y))

theorem g58d_F_cont {d : ℕ} (M : Op (ABC d)) (x y : ABC d) :
    Continuous (fun U : g58d_G d => (representation U * M * (representation U)ᴴ) x y) :=
  g58d_A_cont _ g58d_rep_cont M x y

theorem g58d_int_psd {d : ℕ} {n : Type} [Fintype n] [DecidableEq n] (F : g58d_G d → Matrix n n ℂ) (hc : ∀ x y, Continuous (fun U => F U x y))
    (hpsd : ∀ U, (F U).PosSemidef) : (∫ U, F U ∂QAlgorithms.Schur.unitaryHaar d).PosSemidef := by
  have hI : ∀ x y, Integrable (fun U => F U x y) (QAlgorithms.Schur.unitaryHaar d) :=
    fun x y => g58d_int_cont (hc x y)
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext x y
    rw [Matrix.conjTranspose_apply, g58d_ent F hI, g58d_ent F hI, RCLike.star_def, ← integral_conj]
    congr 1; funext U
    have := congrFun (congrFun (hpsd U).1.eq x) y
    rw [Matrix.conjTranspose_apply, RCLike.star_def] at this
    exact this
  · have hJ : ∀ a b, Integrable (fun U => star v a * (F U a b * v b)) (QAlgorithms.Schur.unitaryHaar d) :=
      fun a b => ((hI a b).mul_const _).const_mul _
    have e : star v ⬝ᵥ (∫ U, F U ∂QAlgorithms.Schur.unitaryHaar d) *ᵥ v =
        ∫ U, star v ⬝ᵥ (F U) *ᵥ v ∂QAlgorithms.Schur.unitaryHaar d := by
      calc star v ⬝ᵥ (∫ U, F U ∂QAlgorithms.Schur.unitaryHaar d) *ᵥ v
          = ∑ a, ∑ b, star v a * ((∫ U, F U a b ∂QAlgorithms.Schur.unitaryHaar d) * v b) := by
            simp only [dotProduct, Matrix.mulVec, g58d_ent F hI, Finset.mul_sum]
        _ = ∑ a, ∑ b, ∫ U, star v a * (F U a b * v b) ∂QAlgorithms.Schur.unitaryHaar d := by
            refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
            rw [integral_const_mul, integral_mul_const]
        _ = ∫ U, ∑ a, ∑ b, star v a * (F U a b * v b) ∂QAlgorithms.Schur.unitaryHaar d := by
            rw [integral_finset_sum _ (fun a _ => integrable_finsetSum _ (fun b _ => hJ a b))]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [integral_finset_sum _ (fun b _ => hJ a b)]
        _ = _ := by
            congr 1; funext U
            simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [e]
    have hq : (fun U => star v ⬝ᵥ (F U) *ᵥ v) = fun U => (((star v ⬝ᵥ (F U) *ᵥ v).re : ℝ) : ℂ) := by
      funext U
      have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hpsd U)).2 v
      exact Complex.ext (by simp) (by simp [(Complex.nonneg_iff.mp this).2])
    rw [hq, integral_complex_ofReal]
    refine Complex.zero_le_real.mpr (integral_nonneg (fun U => ?_))
    exact (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (hpsd U)).2 v)).1

theorem g58d_rep_mul {d : ℕ} (V U : g58d_G d) :
    representation (V * U) = representation V * representation U := by
  simp only [representation, Matrix.kronecker]
  rw [show ((V * U : g58d_G d) : Op (Fin d)) = (V : Op (Fin d)) * (U : Op (Fin d)) from rfl,
    Matrix.map_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

theorem g58d_rep_inv {d : ℕ} (U : g58d_G d) : representation U⁻¹ = (representation U)ᴴ := by
  have hc : ((U⁻¹ : g58d_G d) : Op (Fin d)) = (U : Op (Fin d))ᴴ := rfl
  ext x y
  simp only [representation, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.map_apply,
    Matrix.conjTranspose_apply, hc, RCLike.star_def, map_mul, Complex.conj_conj]

theorem g58d_W_unitary {d : ℕ} (U : g58d_G d) :
    Matrix.kronecker ((U : Op (Fin d)).map conj) ((U : Op (Fin d)).map conj) *
      (Matrix.kronecker ((U : Op (Fin d)).map conj) ((U : Op (Fin d)).map conj))ᴴ = 1 := by
  have h1 : (U : Op (Fin d))ᴴ * (U : Op (Fin d)) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have h2 : ((U : Op (Fin d)).map conj)ᴴ * (U : Op (Fin d)).map conj = 1 := by
    ext a b
    have := congrFun (congrFun h1 a) b
    have h3 := congrArg conj this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul, RCLike.star_def,
      Complex.conj_conj, Matrix.one_apply] at h3
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, RCLike.star_def,
      Complex.conj_conj, Matrix.one_apply, h3]
    split_ifs <;> simp
  have m1 : (U : Op (Fin d)).map conj ∈ unitary (Matrix (Fin d) (Fin d) ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mpr h2
  exact Unitary.mul_star_self_of_mem (Matrix.kronecker_mem_unitary m1 m1)

theorem g58d_hcol {d : ℕ} (U : g58d_G d) (X : Fin d → Fin d → ℂ) :
    ∑ c, ∑ q, ∑ p, (U : Op (Fin d)) c p * X p q * conj ((U : Op (Fin d)) c q) = ∑ p, X p p := by
  have h1 : ∀ p q : Fin d, ∑ c, (U : Op (Fin d)) c p * conj ((U : Op (Fin d)) c q) =
      if p = q then 1 else 0 := by
    intro p q
    have hUU : (U : Op (Fin d))ᴴ * (U : Op (Fin d)) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
    have := congrArg conj (congrFun (congrFun hUU p) q)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, map_sum, map_mul,
      Complex.conj_conj, Matrix.one_apply] at this
    rw [this]; split_ifs <;> simp
  rw [Finset.sum_comm]
  have : ∀ q, ∑ c, ∑ p, (U : Op (Fin d)) c p * X p q * conj ((U : Op (Fin d)) c q) = X q q := by
    intro q
    rw [Finset.sum_comm]
    have e : ∀ p, ∑ c, (U : Op (Fin d)) c p * X p q * conj ((U : Op (Fin d)) c q) =
        X p q * (if p = q then 1 else 0) := by
      intro p; rw [← h1, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl (fun q _ => this q)

theorem g58d_trB {d : ℕ} (U : g58d_G d) (S : Op (ABC d)) :
    QAlgorithms.traceRight (Matrix.kronecker (1 : Op (AB d)) (U : Op (Fin d)) * S *
      (Matrix.kronecker (1 : Op (AB d)) (U : Op (Fin d)))ᴴ) = QAlgorithms.traceRight S := by
  ext a b
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  rw [show QAlgorithms.traceRight S (a1, a2) (b1, b2) = ∑ p, S ((a1, a2), p) ((b1, b2), p) from rfl,
    ← g58d_hcol U (fun p q => S ((a1, a2), p) ((b1, b2), q))]
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Prod.mk.injEq]
  simp only [ite_and, ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one, map_mul,
    apply_ite (starRingEnd ℂ), map_one, map_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_mul, Finset.sum_const_zero, Finset.sum_ite_irrel]

theorem g58d_trA {d : ℕ} (W : Op (AB d)) (X : Op (ABC d)) :
    QAlgorithms.traceRight (Matrix.kronecker W (1 : Op (Fin d)) * X * (Matrix.kronecker W (1 : Op (Fin d)))ᴴ) =
      W * QAlgorithms.traceRight X * Wᴴ := by
  ext a b
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one, map_mul,
    apply_ite (starRingEnd ℂ), map_one, map_zero, Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum, Finset.sum_const_zero, Finset.sum_ite_irrel]
  simp only [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv
    { toFun := fun x : Fin d × Fin d × Fin d × Fin d × Fin d => (x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.1)
      invFun := fun y : Fin d × Fin d × Fin d × Fin d × Fin d => (y.2.2.2.2, y.1, y.2.1, y.2.2.1, y.2.2.2.1)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  intro x; rfl

theorem g58d_trRep {d : ℕ} (U : g58d_G d) (S : Op (ABC d)) (hS : QAlgorithms.traceRight S = 1) :
    QAlgorithms.traceRight (representation U * S * (representation U)ᴴ) = 1 := by
  set W := Matrix.kronecker ((U : Op (Fin d)).map conj) ((U : Op (Fin d)).map conj) with hW
  have hrep : representation U = Matrix.kronecker W (1 : Op (Fin d)) *
      Matrix.kronecker (1 : Op (AB d)) (U : Op (Fin d)) := by
    rw [hW, representation]
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hrep, Matrix.conjTranspose_mul]
  rw [show Matrix.kronecker W (1 : Op (Fin d)) * Matrix.kronecker (1 : Op (AB d)) (U : Op (Fin d)) * S *
      ((Matrix.kronecker (1 : Op (AB d)) (U : Op (Fin d)))ᴴ * (Matrix.kronecker W (1 : Op (Fin d)))ᴴ) =
      Matrix.kronecker W (1 : Op (Fin d)) * (Matrix.kronecker (1 : Op (AB d)) (U : Op (Fin d)) * S *
      (Matrix.kronecker (1 : Op (AB d)) (U : Op (Fin d)))ᴴ) * (Matrix.kronecker W (1 : Op (Fin d)))ᴴ by
      simp only [Matrix.mul_assoc]]
  rw [g58d_trA, g58d_trB, hS, Matrix.mul_one, hW, g58d_W_unitary]

theorem g58d_mulR {d : ℕ} (F : g58d_G d → Op (ABC d))
    (hI : ∀ x y, Integrable (fun U => F U x y) (QAlgorithms.Schur.unitaryHaar d)) (M : Op (ABC d))
    (x y : ABC d) :
    ((∫ U, F U ∂QAlgorithms.Schur.unitaryHaar d) * M) x y =
      ∫ U, (F U * M) x y ∂QAlgorithms.Schur.unitaryHaar d := by
  simp only [Matrix.mul_apply, g58d_ent F hI]
  rw [integral_finset_sum _ (fun a _ => (hI x a).mul_const _)]
  exact Finset.sum_congr rfl (fun a _ => (integral_mul_const _ _).symm)

theorem g58d_mulL {d : ℕ} (F : g58d_G d → Op (ABC d))
    (hI : ∀ x y, Integrable (fun U => F U x y) (QAlgorithms.Schur.unitaryHaar d)) (M : Op (ABC d))
    (x y : ABC d) :
    (M * (∫ U, F U ∂QAlgorithms.Schur.unitaryHaar d)) x y =
      ∫ U, (M * F U) x y ∂QAlgorithms.Schur.unitaryHaar d := by
  simp only [Matrix.mul_apply, g58d_ent F hI]
  rw [integral_finset_sum _ (fun a _ => (hI a y).const_mul _)]
  exact Finset.sum_congr rfl (fun a _ => (integral_const_mul _ _).symm)

theorem g58d_lift_psd {d : ℕ} (C : Fin d → Op (ABC d)) (h : ∀ k, (C k).PosSemidef) :
    Matrix.PosSemidef (fun x y : ABCD d => if x.2 = y.2 then C x.2 x.1 y.1 else 0 : Op (ABCD d)) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun v => ?_⟩
  · refine Matrix.IsHermitian.ext (fun z w => ?_)
    show star (if w.2 = z.2 then C w.2 w.1 z.1 else 0) = if z.2 = w.2 then C z.2 z.1 w.1 else 0
    rw [RCLike.star_def]
    by_cases hzw : z.2 = w.2
    · rw [if_pos hzw.symm, if_pos hzw, hzw]
      have := congrFun (congrFun (h w.2).1.eq z.1) w.1
      simpa [Matrix.conjTranspose_apply] using this
    · rw [if_neg (Ne.symm hzw), if_neg hzw, map_zero]
  · have e : star v ⬝ᵥ (fun x y : ABCD d => if x.2 = y.2 then C x.2 x.1 y.1 else 0 : Op (ABCD d)) *ᵥ v =
        ∑ k, star (fun a => v (a, k)) ⬝ᵥ C k *ᵥ (fun a => v (a, k)) := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Pi.star_apply]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [← Fintype.sum_prod_type']
      apply Fintype.sum_equiv
        { toFun := fun x : Fin d × Fin d × Fin d × Fin d => (x.2.2.2, x.1, x.2.1, x.2.2.1)
          invFun := fun y : Fin d × Fin d × Fin d × Fin d => (y.2.1, y.2.2.1, y.2.2.2, y.1)
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }
      intro x; rfl
    rw [e]
    exact Finset.sum_nonneg (fun k _ => (Matrix.posSemidef_iff_dotProduct_mulVec.mp (h k)).2 _)

theorem g58d_learn_conj {d : ℕ} (U : g58d_G d) (rho : Op (Fin d)) :
    representation U * Matrix.kronecker (1 : Op (AB d)) rho * (representation U)ᴴ =
      Matrix.kronecker (1 : Op (AB d)) ((U : Op (Fin d)) * rho * (U : Op (Fin d))ᴴ) := by
  have hW := g58d_W_unitary U
  simp only [representation, Matrix.kronecker] at hW ⊢
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, hW]

set_option maxHeartbeats 800000 in
theorem solution (d : ℕ) (hd : 2 ≤ d) (timing : Timing) (R : ReplicationChoiArray d)
    (hR : IsReplicationStrategy timing R) :
    (∀ i j k, ∀ x y : ABC d,
      Integrable (fun U : (Matrix.unitaryGroup (Fin d) ℂ) =>
        (representation U * diagonalBlocks R i j k * (representation U).conjTranspose) x y)
        (QAlgorithms.Schur.unitaryHaar d)) ∧
    Integrable (scoreIntegrand R) (QAlgorithms.Schur.unitaryHaar d) ∧
    IsReplicationStrategy timing (twirl R) ∧ BlocksCommuteWithRotations (diagonalBlocks (twirl R)) ∧
    twirl R = dephaseClassicalOutput (twirl R) ∧ haarReplicationScore (twirl R) = haarReplicationScore R := by
  set B := diagonalBlocks R with hBdef
  have hFI : ∀ (M : Op (ABC d)) (x y : ABC d), Integrable (fun U : g58d_G d =>
      (representation U * M * (representation U)ᴴ) x y) (QAlgorithms.Schur.unitaryHaar d) :=
    fun M x y => g58d_int_cont (g58d_F_cont M x y)
  have hTent : ∀ i j k (x y : ABC d), twirlBlocks B i j k x y =
      ∫ U, (representation U * B i j k * (representation U)ᴴ) x y ∂QAlgorithms.Schur.unitaryHaar d :=
    fun i j k x y => g58d_ent (fun U => representation U * B i j k * (representation U)ᴴ)
      (fun x y => hFI _ x y) x y
  have hdb : diagonalBlocks (twirl R) = twirlBlocks B := by
    funext i j k; ext x y
    show (if k = k then twirlBlocks B i j k x y else 0) = _
    rw [if_pos rfl]
  have hpsdB : ∀ i j k, (B i j k).PosSemidef := fun i j k =>
    (hR.1 i j).submatrix (fun x : ABC d => (x, k))
  have hTpsd : ∀ i j k, (twirlBlocks B i j k).PosSemidef := fun i j k =>
    g58d_int_psd _ (g58d_F_cont _) (fun U => (hpsdB i j k).mul_mul_conjTranspose_same _)
  -- commutation
  have hcov : BlocksCommuteWithRotations (twirlBlocks B) := by
    intro V i j k
    ext x y
    have e1 := g58d_mulR (fun U => representation U * B i j k * (representation U)ᴴ)
      (fun x y => hFI _ x y) (representation V) x y
    have e2 := g58d_mulL (fun U => representation U * B i j k * (representation U)ᴴ)
      (fun x y => hFI _ x y) (representation V) x y
    simp only [twirlBlocks]
    rw [e1, e2]
    have key : ∀ U : g58d_G d, representation V * (representation U * B i j k * (representation U)ᴴ) =
        representation (V * U) * B i j k * (representation (V * U))ᴴ * representation V := by
      intro U
      rw [g58d_rep_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc, g58d_rep_unitary, Matrix.mul_one]
    simp only [key]
    exact (integral_mul_left_eq_self (fun W : g58d_G d =>
      (representation W * B i j k * (representation W)ᴴ * representation V) x y) V).symm
  -- sums of twirled blocks
  have hsumT : ∀ k (x y : ABC d), ∑ i, ∑ j, twirlBlocks B i j k x y =
      ∫ U, (representation U * (∑ i, ∑ j, B i j k) * (representation U)ᴴ) x y
        ∂QAlgorithms.Schur.unitaryHaar d := by
    intro k x y
    simp only [hTent]
    calc ∑ i, ∑ j, ∫ U, (representation U * B i j k * (representation U)ᴴ) x y ∂QAlgorithms.Schur.unitaryHaar d
        = ∑ i, ∫ U, ∑ j, (representation U * B i j k * (representation U)ᴴ) x y
            ∂QAlgorithms.Schur.unitaryHaar d :=
          Finset.sum_congr rfl (fun i _ => (integral_finset_sum _ (fun j _ => hFI _ x y)).symm)
      _ = ∫ U, ∑ i, ∑ j, (representation U * B i j k * (representation U)ᴴ) x y
            ∂QAlgorithms.Schur.unitaryHaar d :=
          (integral_finset_sum _ (fun i _ => integrable_finsetSum _ (fun j _ => hFI _ x y))).symm
      _ = _ := by
          congr 1; funext U
          simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  have hlift : ∀ i j, twirl R i j = (fun x y : ABCD d => if x.2 = y.2 then twirlBlocks B i j x.2 x.1 y.1
      else 0 : Op (ABCD d)) := fun i j => rfl
  refine ⟨fun i j k x y => hFI _ x y, ?_, ⟨fun i j => ?_, ?_⟩, hdb ▸ hcov, ?_, ?_⟩
  · -- integrability of score integrand
    have e : scoreIntegrand R = fun U => (1 / (d : ℝ)^2) * ∑ i, ∑ j, ∑ k,
        (((representation U)ᴴ * B i j k * representation U) ((i, j), k) ((i, j), k)).re := by
      funext U; unfold scoreIntegrand; congr 1
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [g58d_term, Complex.re_sum]
    rw [e]
    refine g58d_int_contR (continuous_const.mul (continuous_finset_sum _ (fun i _ =>
      continuous_finset_sum _ (fun j _ => continuous_finset_sum _ (fun k _ =>
        Complex.continuous_re.comp (g58d_A_cont' _ g58d_rep_cont _ _ _))))))
  · rw [hlift]; exact g58d_lift_psd _ (fun k => hTpsd i j k)
  · cases timing with
    | cloning =>
      obtain ⟨S, hS, hS1, hS2⟩ := hR.2
      have hblock : ∀ k, (∑ i, ∑ j, B i j k) = S := by
        intro k; ext x y
        have := congrFun (congrFun hS2 (x, k)) (y, k)
        simp only [Matrix.sum_apply, cloningTotal, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.one_apply, if_true, mul_one] at this
        simpa [hBdef, diagonalBlocks, Matrix.sum_apply] using this
      refine ⟨∫ U, representation U * S * (representation U)ᴴ ∂QAlgorithms.Schur.unitaryHaar d,
        g58d_int_psd _ (g58d_F_cont S) (fun U => hS.mul_mul_conjTranspose_same _), ?_, ?_⟩
      · ext a b
        show ∑ h, (∫ U, representation U * S * (representation U)ᴴ ∂QAlgorithms.Schur.unitaryHaar d) (a, h) (b, h)
          = (1 : Op (AB d)) a b
        simp only [g58d_ent _ (hFI S)]
        rw [← integral_finset_sum _ (fun c _ => hFI S _ _)]
        have : ∀ U : g58d_G d, ∑ c, (representation U * S * (representation U)ᴴ) (a, c) (b, c) =
            (1 : Op (AB d)) a b := fun U => congrFun (congrFun (g58d_trRep U S hS1) a) b
        simp only [this, integral_const]
        simp [Measure.real]
      · ext z w
        simp only [Matrix.sum_apply]
        simp only [hlift, cloningTotal, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
        by_cases h : z.2 = w.2
        · simp only [h, if_true, mul_one]
          rw [hsumT, hblock, g58d_ent _ (hFI S)]
        · simp only [h, if_false, mul_zero, Finset.sum_const_zero]
    | learning =>
      obtain ⟨rho, hr, hr1, hr2⟩ := hR.2
      have hblock : ∀ k, (∑ i, ∑ j, B i j k) = Matrix.kronecker (1 : Op (AB d)) rho := by
        intro k; ext x y
        have := congrFun (congrFun hr2 (x, k)) (y, k)
        simp only [Matrix.sum_apply, learningTotal, and_true] at this
        simp only [hBdef, diagonalBlocks, Matrix.sum_apply, this, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.one_apply]
        split_ifs <;> simp
      have hUI : ∀ a b, Integrable (fun U : g58d_G d => ((U : Op (Fin d)) * rho * (U : Op (Fin d))ᴴ) a b)
          (QAlgorithms.Schur.unitaryHaar d) := fun a b =>
        g58d_int_cont (g58d_A_cont _ g58d_coe_cont rho a b)
      refine ⟨∫ U, (U : Op (Fin d)) * rho * (U : Op (Fin d))ᴴ ∂QAlgorithms.Schur.unitaryHaar d,
        g58d_int_psd _ (g58d_A_cont _ g58d_coe_cont rho) (fun U => hr.mul_mul_conjTranspose_same _), ?_, ?_⟩
      · show ∑ a, (∫ U, (U : Op (Fin d)) * rho * (U : Op (Fin d))ᴴ ∂QAlgorithms.Schur.unitaryHaar d) a a = 1
        simp only [g58d_ent _ hUI]
        rw [← integral_finset_sum _ (fun a _ => hUI a a)]
        have : ∀ U : g58d_G d, ∑ a, ((U : Op (Fin d)) * rho * (U : Op (Fin d))ᴴ) a a = 1 := by
          intro U
          have h1 : (U : Op (Fin d))ᴴ * (U : Op (Fin d)) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
          show Matrix.trace ((U : Op (Fin d)) * rho * (U : Op (Fin d))ᴴ) = 1
          rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]; exact hr1
        simp only [this, integral_const]
        simp [Measure.real]
      · ext z w
        simp only [Matrix.sum_apply]
        simp only [hlift, learningTotal]
        by_cases h : z.2 = w.2
        · simp only [h, if_true, and_true]
          rw [hsumT, hblock]
          simp only [g58d_learn_conj]
          simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
          rw [integral_const_mul, g58d_ent _ hUI]
          split_ifs <;> simp
        · simp only [h, if_false, and_false, Finset.sum_const_zero]
  · funext i j; ext x y
    simp only [dephaseClassicalOutput, QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput, hlift]
    split_ifs <;> simp_all
  · -- score
    rw [g58d_score_cov _ (hdb ▸ hcov), hdb]
    unfold haarReplicationScore
    set g : g58d_G d → ℝ := fun U => (1 / (d : ℝ)^2) * ∑ i, ∑ j, ∑ k,
      ((representation U * B i j k * (representation U)ᴴ) ((i, j), k) ((i, j), k)).re with hg
    have hsi : ∀ U, scoreIntegrand R U = g U⁻¹ := by
      intro U; unfold scoreIntegrand; rw [hg]; simp only [g58d_rep_inv, Matrix.conjTranspose_conjTranspose]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [g58d_term, Complex.re_sum]
    simp only [hsi]
    rw [integral_inv_eq_self g]
    rw [hg, integral_const_mul]
    congr 1
    have hre : ∀ i j k, (twirlBlocks B i j k ((i, j), k) ((i, j), k)).re =
        ∫ U, ((representation U * B i j k * (representation U)ᴴ) ((i, j), k) ((i, j), k)).re
          ∂QAlgorithms.Schur.unitaryHaar d := by
      intro i j k
      rw [hTent]
      exact (integral_re (hFI _ _ _)).symm
    simp only [hre]
    symm
    rw [integral_finset_sum _ (fun i _ => ?_)]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finset_sum _ (fun j _ => ?_)]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_finset_sum _ (fun k _ => ?_)]
        exact (hFI _ _ _).re
      · exact integrable_finsetSum _ (fun k _ => (hFI _ _ _).re)
    · exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => (hFI _ _ _).re))
