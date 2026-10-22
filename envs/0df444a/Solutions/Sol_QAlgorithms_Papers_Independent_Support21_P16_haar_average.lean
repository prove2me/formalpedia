-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P16.haar_average
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T18:09:36.284318+00:00
-- url     : https://prove2.me/submissions/6addbe13-33db-4730-9084-858234927ced

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16
noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

open QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

open QAlgorithms

open scoped ComplexConjugate

instance g72gk1_borel (d : ℕ) : BorelSpace (UnitaryGroup d) := ⟨rfl⟩

open scoped Matrix.Norms.Elementwise in
instance g72gk1_compact (d : ℕ) : CompactSpace (UnitaryGroup d) := by
  have hc : IsClosed (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
    isClosed_unitary
  have hb : Bornology.IsBounded
      (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
    (show Bornology.IsBounded (Metric.closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1) from Metric.isBounded_closedBall).subset (by
      intro U hU
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact entrywise_sup_norm_bound_of_unitary hU)
  exact isCompact_iff_compactSpace.mp (Metric.isCompact_of_isClosed_isBounded hc hb)

lemma g72gk1_rinv {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (mu : Measure G) [mu.IsHaarMeasure] [IsProbabilityMeasure mu] :
    mu.IsMulRightInvariant := by
  constructor
  intro g
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace (Measure.map (· * g) mu) mu
  have hu : (Measure.map (· * g) mu) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ]; simp
  rw [h] at hu ⊢
  have : (Measure.haarScalarFactor (Measure.map (· * g) mu) mu : ENNReal) = 1 := by
    simpa using hu
  have h1 : Measure.haarScalarFactor (Measure.map (· * g) mu) mu = 1 := by exact_mod_cast this
  rw [h1, one_smul]

/-! piKron algebra (adapted from earlier helper library) -/

lemma g72gk1_tPA {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : TensorMat d n) (x y : Word n d) :
    (Schur.tensorPermutation d n σ * A) x y = A (x ∘ σ) y := by
  simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (x ∘ σ)]
  · rw [if_pos (by ext k; simp)]
  · intro b _ hb; rw [if_neg]; intro h; apply hb; rw [h]; ext k; simp
  · simp

lemma g72gk1_AtP {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : TensorMat d n) (x y : Word n d) :
    (A * Schur.tensorPermutation d n σ) x y = A x (y ∘ σ.symm) := by
  simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (y ∘ σ.symm)]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg hb]
  · simp

lemma g72gk1_pk_tP {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (σ : Equiv.Perm (Fin n)) :
    piKron n U * Schur.tensorPermutation d n σ = Schur.tensorPermutation d n σ * piKron n U := by
  ext x y
  rw [g72gk1_AtP, g72gk1_tPA]
  simp only [piKron, Matrix.of_apply, Function.comp_apply]
  rw [← Equiv.prod_comp σ]
  simp

lemma g72gk1_pk_P {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    piKron n U * boseProjector d n = boseProjector d n * piKron n U := by
  unfold boseProjector
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [g72gk1_pk_tP]

lemma g72gk1_pk_H {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : (piKron n U)ᴴ = piKron n Uᴴ := by
  ext x y
  simp [piKron, Matrix.conjTranspose_apply]

lemma g72gk1_pk_mul {d n : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) :
    piKron n U * piKron n V = piKron n (U * V) := by
  ext x y
  simp only [Matrix.mul_apply, piKron, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum (fun i c => U (x i) c * V c (y i))]

lemma g72gk1_pk_one {d n : ℕ} : piKron n (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra H; exact hxy (funext fun i => not_not.mp (fun hi => H ⟨i, hi⟩))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma g72gk1_pk_unit {d n : ℕ} (u : UnitaryGroup d) :
    piKron n (u : Matrix (Fin d) (Fin d) ℂ) * (piKron n (u : Matrix (Fin d) (Fin d) ℂ))ᴴ = 1 := by
  rw [g72gk1_pk_H, g72gk1_pk_mul]
  have : (u : Matrix (Fin d) (Fin d) ℂ) * (u : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp u.2
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [this, g72gk1_pk_one]

lemma g72gk1_pk_unit' {d n : ℕ} (u : UnitaryGroup d) :
    (piKron n (u : Matrix (Fin d) (Fin d) ℂ))ᴴ * piKron n (u : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  rw [g72gk1_pk_H, g72gk1_pk_mul]
  have : (u : Matrix (Fin d) (Fin d) ℂ)ᴴ * (u : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp u.2
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [this, g72gk1_pk_one]

lemma g72gk1_pk_PH {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    boseProjector d n * (piKron n U)ᴴ = (piKron n U)ᴴ * boseProjector d n := by
  rw [g72gk1_pk_H, g72gk1_pk_P]

lemma g72gk1_pk_cont {d n : ℕ} :
    Continuous (fun u : UnitaryGroup d => piKron n (u : Matrix (Fin d) (Fin d) ℂ)) := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  simp only [piKron, Matrix.of_apply]
  refine continuous_finsetProd _ fun i _ => ?_
  exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)

lemma g72gk1_pk_coh {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (phi : EuclideanSpace ℂ (Fin d)) :
    piKron n U * pureDensity (coherentTensor n phi) * (piKron n U)ᴴ =
      pureDensity (coherentTensor n (act U phi)) := by
  have hv : ∀ x, ∑ a, piKron n U x a * coherentTensor n phi a = coherentTensor n (act U phi) x := by
    intro x
    simp only [piKron, Matrix.of_apply, coherentTensor, powerVector, act, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun i c => U (x i) c * phi c)]
    simp [Matrix.mulVec, dotProduct]
  ext x y
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, Matrix.conjTranspose_apply]
  rw [← hv x, ← hv y, map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, Complex.star_def]
  ring

/-! integrals of matrix entries -/

lemma g72gk1_sum_int {G I J : Type*} [Fintype I] [Fintype J] [MeasurableSpace G] (mu : Measure G)
    (f : G → I → J → ℂ) (hf : ∀ x y, Integrable (fun u => f u x y) mu) (c : I → J → ℂ) :
    ∫ u, ∑ x, ∑ y, c x y * f u x y ∂mu = ∑ x, ∑ y, c x y * ∫ u, f u x y ∂mu := by
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => (hf x y).const_mul _))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum _ (fun y _ => (hf x y).const_mul _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact integral_const_mul _ _

lemma g72gk1_sum_int_ble {G I J : Type*} [Fintype I] [Fintype J] [MeasurableSpace G] (mu : Measure G)
    (f : G → I → J → ℂ) (hf : ∀ x y, Integrable (fun u => f u x y) mu) (c : I → J → ℂ) :
    Integrable (fun u => ∑ x, ∑ y, c x y * f u x y) mu :=
  integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => (hf x y).const_mul _))

lemma g72gk1_quad {I : Type*} [Fintype I] (A : Matrix I I ℂ) (v : I → ℂ) :
    star v ⬝ᵥ (A *ᵥ v) = ∑ x, ∑ y, (star (v x) * v y) * A x y := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma g72gk1_psd_int {G I : Type*} [Fintype I] [MeasurableSpace G] (mu : Measure G)
    (f : G → Matrix I I ℂ) (hf : ∀ x y, Integrable (fun u => f u x y) mu)
    (hp : ∀ u, (f u).PosSemidef) : (Matrix.of fun x y => ∫ u, f u x y ∂mu).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext x y
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [show star (∫ u, f u y x ∂mu) = (starRingEnd ℂ) (∫ u, f u y x ∂mu) from rfl, ← integral_conj]
    congr 1; ext u
    have := congrFun (congrFun (hp u).1 x) y
    simpa [Matrix.conjTranspose_apply] using this
  · intro v
    rw [g72gk1_quad]
    simp only [Matrix.of_apply]
    rw [← g72gk1_sum_int mu (fun u => f u) hf]
    simp_rw [← g72gk1_quad]
    have hg : ∀ u, star v ⬝ᵥ (f u *ᵥ v) = ((star v ⬝ᵥ (f u *ᵥ v)).re : ℂ) := by
      intro u
      have h := (hp u).dotProduct_mulVec_nonneg v
      apply Complex.ext
      · simp
      · simp [(Complex.nonneg_iff.mp h).2.symm]
    rw [integral_congr_ae (Filter.Eventually.of_forall hg), integral_complex_ofReal]
    refine Complex.zero_le_real.mpr (integral_nonneg fun u => ?_)
    exact (Complex.nonneg_iff.mp ((hp u).dotProduct_mulVec_nonneg v)).1

/-! complete positivity of conjugated maps -/

def g72gk1_conjL {I I' J J' : Type*} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (A : Matrix I I' ℂ) (B : Matrix J' J ℂ) :
    Matrix I' I' ℂ →ₗ[ℂ] Matrix J' J' ℂ where
  toFun X := B * L (A * X * Aᴴ) * Bᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, map_smul]

open scoped Kronecker in
lemma g72gk1_cp_conj {I I' J J' : Type*} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hL : Entanglement.IsCompletelyPositive L)
    (A : Matrix I I' ℂ) (B : Matrix J' J ℂ) :
    Entanglement.IsCompletelyPositive (g72gk1_conjL L A B) := by
  intro r X hX
  have blk : ∀ a b : Fin r, (Matrix.of fun i i' => (((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A) * X *
      ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A)ᴴ) (a, i) (b, i')) =
      A * (Matrix.of fun i i' => X (a, i) (b, i')) * Aᴴ := by
    intro a b; ext i i'
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul,
      apply_ite (star : ℂ → ℂ), star_zero, Finset.sum_mul]
    simp [Finset.sum_ite_eq]
  have key : idTensorSuperop (g72gk1_conjL L A B) X = ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ B) *
      idTensorSuperop L (((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A) * X *
        ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A)ᴴ) *
      ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ B)ᴴ := by
    ext p q
    have e1 : idTensorSuperop (g72gk1_conjL L A B) X p q =
        (B * L (A * (Matrix.of fun i i' => X (p.1, i) (q.1, i')) * Aᴴ) * Bᴴ) p.2 q.2 := rfl
    have e2 : ∀ a b : Fin r, ∀ j j', idTensorSuperop L (((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A) * X *
        ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A)ᴴ) (a, j) (b, j') =
        L (A * (Matrix.of fun i i' => X (a, i) (b, i')) * Aᴴ) j j' := by
      intro a b j j'
      simp only [idTensorSuperop, Matrix.of_apply]
      rw [blk]
    rw [e1]
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul,
      apply_ite (star : ℂ → ℂ), star_zero, Finset.sum_mul, e2]
    simp [Finset.sum_ite_eq]
  rw [key]
  exact (hL r _ (hX.mul_mul_conjTranspose_same _)).mul_mul_conjTranspose_same _

/-! channel output positivity and overlap bounds -/

lemma g72gk1_out_psd {d N M : ℕ} (T : CloneMap d N M) (hT : IsBoseInputChannel T)
    (A : TensorMat d N) (hA : A.PosSemidef) : (T A).PosSemidef := by
  obtain ⟨⟨L, hTL, hCP⟩, -, -⟩ := hT
  have h := hCP 1 (A.submatrix Prod.snd Prod.snd) (hA.submatrix _)
  have : T A = (idTensorSuperop L (A.submatrix Prod.snd Prod.snd)).submatrix
      (fun j => ((0 : Fin 1), j)) (fun j => ((0 : Fin 1), j)) := by
    ext x y
    simp only [Matrix.submatrix_apply, idTensorSuperop, Matrix.of_apply, hTL]
    rfl
  rw [this]; exact h.submatrix _

lemma g72gk1_pure_psd {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    (pureDensity v).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext x y; simp [pureDensity, Matrix.conjTranspose_apply, mul_comm]
  · intro w
    rw [g72gk1_quad]
    have : ∑ x, ∑ y, (star (w x) * w y) * pureDensity v x y =
        ((‖∑ x, star (w x) * v x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [pureDensity, Matrix.of_apply, map_mul, Complex.star_def, Complex.conj_conj]
      ring
    rw [this]; exact Complex.zero_le_real.mpr (by positivity)

lemma g72gk1_pure_H {ι : Type*} (v : EuclideanSpace ℂ ι) : (pureDensity v)ᴴ = pureDensity v := by
  ext x y; simp [pureDensity, Matrix.conjTranspose_apply, mul_comm]

lemma g72gk1_pure_idem {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι)
    (hv : ∑ a, v a * conj (v a) = 1) : pureDensity v * pureDensity v = pureDensity v := by
  ext a c
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply]
  calc _ = v a * conj (v c) * ∑ b, v b * conj (v b) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
    _ = _ := by rw [hv, mul_one]

lemma g72gk1_tr_nonneg {I : Type*} [Fintype I] (E ρ : Matrix I I ℂ) (hE : Eᴴ = E) (hEE : E * E = E)
    (hρ : ρ.PosSemidef) : 0 ≤ (E * ρ).trace.re := by
  have h1 : (E * ρ).trace = (E * ρ * Eᴴ).trace := by
    rw [hE, Matrix.trace_mul_comm (E * ρ) E, ← Matrix.mul_assoc, hEE]
  rw [h1]; exact (Complex.nonneg_iff.mp (hρ.mul_mul_conjTranspose_same E).trace_nonneg).1

lemma g72gk1_coh_norm {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    ∑ u : Word n d, coherentTensor n phi u * conj (coherentTensor n phi u) = 1 := by
  simp only [coherentTensor, powerVector, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin n) a => phi a * conj (phi a))]
  have : ∑ a, phi a * conj (phi a) = 1 := by
    have h2 : ‖phi‖ ^ 2 = 1 := by rw [hphi]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    simp only [Complex.mul_conj']
    exact_mod_cast h2
  simp [this]

lemma g72gk1_tP_H {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Schur.tensorPermutation d n σ)ᴴ = Schur.tensorPermutation d n σ⁻¹ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, Schur.tensorPermutation, Matrix.of_apply]
  rw [apply_ite (star : ℂ → ℂ), star_one, star_zero]
  congr 1
  apply propext
  constructor
  · intro h; rw [h]; ext k; simp [Equiv.Perm.inv_def]
  · intro h; rw [h]; ext k; simp [Equiv.Perm.inv_def]

lemma g72gk1_P_H {d n : ℕ} : (boseProjector d n)ᴴ = boseProjector d n := by
  unfold boseProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [g72gk1_tP_H]
  congr 1
  · simp
  · exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)

lemma g72gk1_coh_PD {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    boseProjector d n * pureDensity (coherentTensor n phi) = pureDensity (coherentTensor n phi) := by
  have hp : ∀ p : Equiv.Perm (Fin n),
      Schur.tensorPermutation d n p * pureDensity (coherentTensor n phi) =
        pureDensity (coherentTensor n phi) := by
    intro p
    ext y z
    rw [g72gk1_tPA]
    simp only [pureDensity, Matrix.of_apply, coherentTensor, powerVector, Function.comp_apply]
    congr 1
    exact Equiv.prod_comp p (fun k => phi (y k))
  rw [boseProjector, Matrix.smul_mul, Finset.sum_mul]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'), one_smul]

lemma g72gk1_coh_DP {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    pureDensity (coherentTensor n phi) * boseProjector d n = pureDensity (coherentTensor n phi) := by
  have h := congrArg Matrix.conjTranspose (g72gk1_coh_PD (n := n) phi)
  rw [Matrix.conjTranspose_mul, g72gk1_pure_H] at h
  rwa [g72gk1_P_H] at h

lemma g72gk1_ov_bounds {d N M : ℕ} (T : CloneMap d N M) (hT : IsBoseInputChannel T)
    (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    0 ≤ cloningOverlap T phi ∧ cloningOverlap T phi ≤ 1 := by
  have hρ := g72gk1_out_psd T hT _ (g72gk1_pure_psd (coherentTensor N phi))
  have hE := g72gk1_pure_H (coherentTensor M phi)
  have hEE := g72gk1_pure_idem (coherentTensor M phi) (g72gk1_coh_norm phi hphi)
  refine ⟨g72gk1_tr_nonneg _ _ hE hEE hρ, ?_⟩
  have h2 := g72gk1_tr_nonneg (1 - pureDensity (coherentTensor M phi)) _
    (by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hE])
    (by rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hEE, Matrix.one_mul, Matrix.mul_one,
          Matrix.one_mul]; abel) hρ
  have htr : (T (pureDensity (coherentTensor N phi))).trace = 1 := by
    rw [hT.2.2, Matrix.mul_assoc, g72gk1_coh_DP, g72gk1_coh_PD]
    rw [← g72gk1_coh_norm (n := N) phi hphi]; rfl
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul, htr] at h2
  unfold cloningOverlap
  simp only [Complex.sub_re, Complex.one_re] at h2
  linarith

lemma g72gk1_RL {d N M : ℕ} (T : CloneMap d N M) (L : TensorMat d N →ₗ[ℂ] TensorMat d M)
    (hTL : ∀ A, T A = L A) (u : UnitaryGroup d) (A : TensorMat d N) :
    rotatedCloner u T A = g72gk1_conjL L (piKron N (u : Matrix (Fin d) (Fin d) ℂ))
      (piKron M (u : Matrix (Fin d) (Fin d) ℂ))ᴴ A := by
  simp only [rotatedCloner, QAlgorithms.Papers.Independent.Renew46.P45.rotateCloner, g72gk1_conjL,
    LinearMap.coe_mk, AddHom.coe_mk, hTL, Matrix.conjTranspose_conjTranspose]

lemma g72gk1_R_cont {d N M : ℕ} (T : CloneMap d N M) (L : TensorMat d N →ₗ[ℂ] TensorMat d M)
    (hTL : ∀ A, T A = L A) (A : TensorMat d N) :
    Continuous (fun u : UnitaryGroup d => rotatedCloner u T A) := by
  simp only [g72gk1_RL T L hTL, g72gk1_conjL, LinearMap.coe_mk, AddHom.coe_mk]
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hP := g72gk1_pk_cont (d := d) (n := N)
  have hQ := g72gk1_pk_cont (d := d) (n := M)
  exact (hQ.matrix_conjTranspose.matrix_mul (hL.comp ((hP.matrix_mul continuous_const).matrix_mul
    hP.matrix_conjTranspose))).matrix_mul hQ.matrix_conjTranspose.matrix_conjTranspose

lemma g72gk1_entry_conj {I J : Type*} [Fintype J] (Q : Matrix I J ℂ) (Z : Matrix J J ℂ) (x y : I) :
    (Q * Z * Qᴴ) x y = ∑ a, ∑ b, (Q x a * star (Q y b)) * Z a b := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma g72gk1_trace_mul {I : Type*} [Fintype I] (W Z : Matrix I I ℂ) :
    (W * Z).trace = ∑ y, ∑ x, W x y * Z y x := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]

lemma g72gk1_rot_overlap {d N M : ℕ} (T : CloneMap d N M) (u : UnitaryGroup d)
    (phi : EuclideanSpace ℂ (Fin d)) :
    cloningOverlap (rotatedCloner u T) phi = cloningOverlap T (act (u : Matrix (Fin d) (Fin d) ℂ) phi) := by
  unfold cloningOverlap
  simp only [rotatedCloner, QAlgorithms.Papers.Independent.Renew46.P45.rotateCloner]
  set Q := piKron M (u : Matrix (Fin d) (Fin d) ℂ)
  set W := pureDensity (coherentTensor M phi)
  set X := T (piKron N (u : Matrix (Fin d) (Fin d) ℂ) * pureDensity (coherentTensor N phi) *
    (piKron N (u : Matrix (Fin d) (Fin d) ℂ))ᴴ)
  rw [show W * (Qᴴ * X * Q) = (W * Qᴴ * X) * Q by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm, show Q * (W * Qᴴ * X) = Q * W * Qᴴ * X by simp only [Matrix.mul_assoc]]
  simp only [Q, W, X, g72gk1_pk_coh]


lemma g72gk1_He {d N M : ℕ} (mu : Measure (UnitaryGroup d)) (T : CloneMap d N M) (A : TensorMat d N) (x y : Word M d) :
    haarAverage mu T A x y = ∫ u, rotatedCloner u T A x y ∂mu := rfl

section
variable {d N M : ℕ} (mu : Measure (UnitaryGroup d)) [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu]
  (T : CloneMap d N M) (L : TensorMat d N →ₗ[ℂ] TensorMat d M) (hTL : ∀ A, T A = L A)

include hTL in
lemma g72gk1_hint (A : TensorMat d N) (x y : Word M d) :
    Integrable (fun u : UnitaryGroup d => rotatedCloner u T A x y) mu :=
  (((continuous_apply y).comp ((continuous_apply x).comp (g72gk1_R_cont T L hTL A)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

include hTL in
lemma g72gk1_H_add (A B : TensorMat d N) :
    haarAverage mu T (A + B) = haarAverage mu T A + haarAverage mu T B := by
  funext x y
  rw [Matrix.add_apply, g72gk1_He, g72gk1_He, g72gk1_He,
    ← integral_add (g72gk1_hint mu T L hTL A x y) (g72gk1_hint mu T L hTL B x y)]
  congr 1; funext u
  simp only [g72gk1_RL T L hTL, map_add, Matrix.add_apply]

include hTL in
lemma g72gk1_H_smul (c : ℂ) (A : TensorMat d N) :
    haarAverage mu T (c • A) = c • haarAverage mu T A := by
  funext x y
  rw [Matrix.smul_apply, g72gk1_He, g72gk1_He, smul_eq_mul, ← integral_const_mul]
  congr 1; funext u
  simp only [g72gk1_RL T L hTL, map_smul, Matrix.smul_apply, smul_eq_mul]

def g72gk1_HL : TensorMat d N →ₗ[ℂ] TensorMat d M where
  toFun := haarAverage mu T
  map_add' := g72gk1_H_add mu T L hTL
  map_smul' := g72gk1_H_smul mu T L hTL

include hTL in
lemma g72gk1_HL_cp (hCP : Entanglement.IsCompletelyPositive L) :
    Entanglement.IsCompletelyPositive (g72gk1_HL mu T L hTL) := by
  intro r X hX
  have e : idTensorSuperop (g72gk1_HL mu T L hTL) X = Matrix.of fun p q => ∫ u, idTensorSuperop
      (g72gk1_conjL L (piKron N (u : Matrix (Fin d) (Fin d) ℂ))
        (piKron M (u : Matrix (Fin d) (Fin d) ℂ))ᴴ) X p q ∂mu := by
    funext p q
    show haarAverage mu T _ _ _ = _
    rw [g72gk1_He]
    congr 1; funext u
    rw [g72gk1_RL T L hTL]; rfl
  rw [e]
  refine g72gk1_psd_int mu _ (fun p q => ?_) (fun u => g72gk1_cp_conj L hCP _ _ r X hX)
  have := g72gk1_hint mu T L hTL (Matrix.of fun i i' => X (p.1, i) (q.1, i')) p.2 q.2
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  show rotatedCloner u T _ _ _ = _
  rw [g72gk1_RL T L hTL]; rfl

end

lemma g72gk1_Rcorn {d N M : ℕ} (T : CloneMap d N M)
    (hcorn : ∀ A, T A = T (boseProjector d N * A * boseProjector d N)) (u : UnitaryGroup d)
    (A : TensorMat d N) :
    rotatedCloner u T A = rotatedCloner u T (boseProjector d N * A * boseProjector d N) := by
  simp only [rotatedCloner, QAlgorithms.Papers.Independent.Renew46.P45.rotateCloner]
  rw [hcorn (piKron N (u : Matrix (Fin d) (Fin d) ℂ) * A * (piKron N (u : Matrix (Fin d) (Fin d) ℂ))ᴴ)]
  congr 3
  simp only [← Matrix.mul_assoc, g72gk1_pk_P]
  simp only [Matrix.mul_assoc, g72gk1_pk_PH]

lemma g72gk1_Rtr {d N M : ℕ} (T : CloneMap d N M)
    (htr : ∀ A, (T A).trace = (boseProjector d N * A * boseProjector d N).trace) (u : UnitaryGroup d)
    (A : TensorMat d N) :
    (rotatedCloner u T A).trace = (boseProjector d N * A * boseProjector d N).trace := by
  simp only [rotatedCloner, QAlgorithms.Papers.Independent.Renew46.P45.rotateCloner]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, g72gk1_pk_unit, Matrix.one_mul, htr,
    show boseProjector d N * (piKron N (u : Matrix (Fin d) (Fin d) ℂ) * A *
      (piKron N (u : Matrix (Fin d) (Fin d) ℂ))ᴴ) * boseProjector d N =
      piKron N (u : Matrix (Fin d) (Fin d) ℂ) * (boseProjector d N * A * boseProjector d N) *
      (piKron N (u : Matrix (Fin d) (Fin d) ℂ))ᴴ by
        simp only [← Matrix.mul_assoc, g72gk1_pk_P]
        simp only [Matrix.mul_assoc, g72gk1_pk_PH],
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, g72gk1_pk_unit', Matrix.one_mul]

lemma g72gk1_H_corner {d N M : ℕ} (mu : Measure (UnitaryGroup d)) [Measure.IsHaarMeasure mu]
    [IsProbabilityMeasure mu] (T : CloneMap d N M)
    (hcorn : ∀ A, T A = T (boseProjector d N * A * boseProjector d N)) (A : TensorMat d N) :
    haarAverage mu T A = haarAverage mu T (boseProjector d N * A * boseProjector d N) := by
  funext x y
  rw [g72gk1_He, g72gk1_He]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u =>
    congrFun (congrFun (g72gk1_Rcorn T hcorn u A) x) y)

lemma g72gk1_H_tr {d N M : ℕ} (mu : Measure (UnitaryGroup d)) [Measure.IsHaarMeasure mu]
    [IsProbabilityMeasure mu]
    (T : CloneMap d N M) (L : TensorMat d N →ₗ[ℂ] TensorMat d M) (hTL : ∀ A, T A = L A)
    (htr : ∀ A, (T A).trace = (boseProjector d N * A * boseProjector d N).trace) (A : TensorMat d N) :
    (haarAverage mu T A).trace = (boseProjector d N * A * boseProjector d N).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag, g72gk1_He]
  rw [← integral_finsetSum _ (fun x _ => g72gk1_hint mu T L hTL A x x)]
  have : ∀ u : UnitaryGroup d, ∑ x, rotatedCloner u T A x x =
      (boseProjector d N * A * boseProjector d N).trace := fun u => g72gk1_Rtr T htr u A
  simp only [this]
  simp

lemma g72gk1_adm {d N M : ℕ} (mu : Measure (UnitaryGroup d)) [Measure.IsHaarMeasure mu]
    [IsProbabilityMeasure mu] (T : CloneMap d N M) (hT : IsBoseInputChannel T) :
    IsBoseInputChannel (haarAverage mu T) := by
  obtain ⟨⟨L, hTL, hCP⟩, hcorn, htr⟩ := hT
  exact ⟨⟨g72gk1_HL mu T L hTL, fun A => rfl, g72gk1_HL_cp mu T L hTL hCP⟩,
    g72gk1_H_corner mu T hcorn, g72gk1_H_tr mu T L hTL htr⟩

lemma g72gk1_rot {d N M : ℕ} (T : CloneMap d N M) (u v : UnitaryGroup d) (A : TensorMat d N) :
    rotatedCloner u T (piKron N (v : Matrix (Fin d) (Fin d) ℂ) * A *
      (piKron N (v : Matrix (Fin d) (Fin d) ℂ))ᴴ) = piKron M (v : Matrix (Fin d) (Fin d) ℂ) *
        rotatedCloner (u * v) T A * (piKron M (v : Matrix (Fin d) (Fin d) ℂ))ᴴ := by
  simp only [rotatedCloner, QAlgorithms.Papers.Independent.Renew46.P45.rotateCloner,
    Matrix.conjTranspose_mul]
  rw [show ((u * v : UnitaryGroup d) : Matrix (Fin d) (Fin d) ℂ) = (u : Matrix (Fin d) (Fin d) ℂ) * v from rfl,
    ← g72gk1_pk_mul, ← g72gk1_pk_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have e1 := g72gk1_pk_unit (n := M) v
  set Pv := piKron M (v : Matrix (Fin d) (Fin d) ℂ)
  set Pu := piKron M (u : Matrix (Fin d) (Fin d) ℂ)
  set Y := T (piKron N (u : Matrix (Fin d) (Fin d) ℂ) * (piKron N (v : Matrix (Fin d) (Fin d) ℂ) * A *
    (piKron N (v : Matrix (Fin d) (Fin d) ℂ))ᴴ) * (piKron N (u : Matrix (Fin d) (Fin d) ℂ))ᴴ)
  have hY : T (piKron N (u : Matrix (Fin d) (Fin d) ℂ) * piKron N (v : Matrix (Fin d) (Fin d) ℂ) * A *
      ((piKron N (v : Matrix (Fin d) (Fin d) ℂ))ᴴ * (piKron N (u : Matrix (Fin d) (Fin d) ℂ))ᴴ)) = Y := by
    simp only [Y, Matrix.mul_assoc]
  rw [hY, show Pv * (Pvᴴ * Puᴴ * Y * (Pu * Pv)) * Pvᴴ = (Pv * Pvᴴ) * Puᴴ * Y * Pu * (Pv * Pvᴴ) by
    simp only [Matrix.mul_assoc], e1, Matrix.one_mul, Matrix.mul_one]

lemma g72gk1_cov {d N M : ℕ} (mu : Measure (UnitaryGroup d)) [Measure.IsHaarMeasure mu]
    [IsProbabilityMeasure mu] (T : CloneMap d N M) (hT : IsBoseInputChannel T) :
    IsCloningCovariant (haarAverage mu T) := by
  obtain ⟨⟨L, hTL, hCP⟩, hcorn, htr⟩ := hT
  haveI := g72gk1_rinv mu
  intro v A
  funext x y
  rw [g72gk1_He, g72gk1_entry_conj]
  simp only [g72gk1_He]
  simp_rw [g72gk1_rot, g72gk1_entry_conj]
  rw [g72gk1_sum_int mu (fun u => rotatedCloner (u * v) T A)
    (fun a b => (g72gk1_hint mu T L hTL A a b).comp_mul_right v)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact integral_mul_right_eq_self (fun u => rotatedCloner u T A a b) v

lemma g72gk1_fid_le {d N M : ℕ} (T : CloneMap d N M) (hT : IsBoseInputChannel T)
    (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) : cloningFidelity T ≤ cloningOverlap T phi :=
  csInf_le ⟨0, by rintro r ⟨ψ, hψ, rfl⟩; exact (g72gk1_ov_bounds T hT ψ hψ).1⟩ ⟨phi, hphi, rfl⟩

lemma g72gk1_unit_exists {d : ℕ} (hd : 0 < d) : ∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, hd⟩ 1, by simp⟩

lemma g72gk1_fid_le_one {d N M : ℕ} (hd : 0 < d) (T : CloneMap d N M) (hT : IsBoseInputChannel T) :
    cloningFidelity T ≤ 1 := by
  obtain ⟨phi, hphi⟩ := g72gk1_unit_exists hd
  exact (g72gk1_fid_le T hT phi hphi).trans (g72gk1_ov_bounds T hT phi hphi).2

lemma g72gk1_ov_int {d N M : ℕ} (mu : Measure (UnitaryGroup d)) [Measure.IsHaarMeasure mu]
    [IsProbabilityMeasure mu] (T : CloneMap d N M) (L : TensorMat d N →ₗ[ℂ] TensorMat d M)
    (hTL : ∀ A, T A = L A) (phi : EuclideanSpace ℂ (Fin d)) :
    Integrable (fun u : UnitaryGroup d => cloningOverlap (rotatedCloner u T) phi) mu := by
  unfold cloningOverlap
  simp_rw [g72gk1_trace_mul]
  exact (g72gk1_sum_int_ble mu _ (g72gk1_hint mu T L hTL _) _).re

lemma g72gk1_avg_overlap {d N M : ℕ} (mu : Measure (UnitaryGroup d)) [Measure.IsHaarMeasure mu]
    [IsProbabilityMeasure mu] (T : CloneMap d N M) (L : TensorMat d N →ₗ[ℂ] TensorMat d M)
    (hTL : ∀ A, T A = L A) (phi : EuclideanSpace ℂ (Fin d)) :
    cloningOverlap (haarAverage mu T) phi = ∫ u, cloningOverlap (rotatedCloner u T) phi ∂mu := by
  unfold cloningOverlap
  rw [g72gk1_trace_mul]
  simp only [g72gk1_He]
  rw [← g72gk1_sum_int mu (fun u => rotatedCloner u T (pureDensity (coherentTensor N phi)))
    (g72gk1_hint mu T L hTL _) (fun y x => pureDensity (coherentTensor M phi) x y)]
  have hI := g72gk1_sum_int_ble mu (fun u => rotatedCloner u T (pureDensity (coherentTensor N phi)))
    (g72gk1_hint mu T L hTL _) (fun y x => pureDensity (coherentTensor M phi) x y)
  have := integral_re hI
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  congr 1; funext u; rw [g72gk1_trace_mul]


theorem g72gk1_main (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M)
    (mu : Measure (UnitaryGroup d)) [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu]
    (T : CloneMap d N M) (hT : IsBoseInputChannel T) :
    (∀ A x y, Integrable (fun u : UnitaryGroup d => rotatedCloner u T A x y) mu) ∧
    IsBoseInputChannel (haarAverage mu T) ∧ IsCloningCovariant (haarAverage mu T) ∧
    (haarAverage mu T = T ↔ IsCloningCovariant T) ∧
    cloningFidelity T ≤ cloningFidelity (haarAverage mu T) ∧
    (cloningFidelity T = optimalFidelity d N M →
      cloningFidelity (haarAverage mu T) = optimalFidelity d N M) := by
  have hT' := hT
  obtain ⟨⟨L, hTL, hCP⟩, hcorn, htr⟩ := hT'
  have hadm := g72gk1_adm mu T hT
  have hcov := g72gk1_cov mu T hT
  have himp : cloningFidelity T ≤ cloningFidelity (haarAverage mu T) := by
    obtain ⟨phi0, hphi0⟩ := g72gk1_unit_exists hd
    refine le_csInf ⟨_, phi0, hphi0, rfl⟩ ?_
    rintro r ⟨phi, hphi, rfl⟩
    rw [g72gk1_avg_overlap mu T L hTL]
    calc cloningFidelity T = ∫ u : UnitaryGroup d, cloningFidelity T ∂mu := by simp
      _ ≤ _ := integral_mono (integrable_const _) (g72gk1_ov_int mu T L hTL phi) (fun u => by
          rw [g72gk1_rot_overlap]
          exact g72gk1_fid_le T hT _ (by rw [act_norm_of_mem_unitaryGroup u.2, hphi]))
  refine ⟨g72gk1_hint mu T L hTL, hadm, hcov, ⟨fun h => by rw [← h]; exact hcov, fun hc => ?_⟩,
    himp, fun h => ?_⟩
  · funext A x y
    rw [g72gk1_He]
    have : ∀ u : UnitaryGroup d, rotatedCloner u T A x y = T A x y := by
      intro u
      simp only [rotatedCloner, QAlgorithms.Papers.Independent.Renew46.P45.rotateCloner]
      rw [hc u A]
      simp only [Matrix.mul_assoc, g72gk1_pk_unit', Matrix.mul_one]
      simp only [← Matrix.mul_assoc, g72gk1_pk_unit', Matrix.one_mul]
    simp [this]
  · apply le_antisymm
    · exact le_csSup ⟨1, by rintro r ⟨S, hS, rfl⟩; exact g72gk1_fid_le_one hd S hS⟩ ⟨_, hadm, rfl⟩
    · rw [← h]; exact himp

/-- PDF p.9 Eq.(4.2) and its following proof: normalized Haar averaging is
integrable, admissible and covariant, fixes exactly covariant maps, improves
worst-case fidelity, and preserves optimality. The printed 'positive'
F-hat minus overlap has the wrong sign; no such sign assertion is used. -/
theorem solution (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M)
    (mu : Measure (UnitaryGroup d)) [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu]
    (T : CloneMap d N M) (hT : IsBoseInputChannel T) :
    (∀ A x y, Integrable (fun u : UnitaryGroup d => rotatedCloner u T A x y) mu) ∧
    IsBoseInputChannel (haarAverage mu T) ∧ IsCloningCovariant (haarAverage mu T) ∧
    (haarAverage mu T = T ↔ IsCloningCovariant T) ∧
    cloningFidelity T ≤ cloningFidelity (haarAverage mu T) ∧
    (cloningFidelity T = optimalFidelity d N M →
      cloningFidelity (haarAverage mu T) = optimalFidelity d N M) :=
  g72gk1_main d N M hd hN hNM mu T hT


end
