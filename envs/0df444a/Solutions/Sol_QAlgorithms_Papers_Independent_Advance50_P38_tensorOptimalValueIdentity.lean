-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.tensorOptimalValueIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:34:39.545872+00:00
-- url     : https://prove2.me/submissions/5453d959-ece1-4e38-abe8-eeefc40d5667

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
open QAlgorithms.Papers.Independent.Advance50.P38
open scoped Matrix

theorem colB {m : ℕ} (hm : 0 < m) (z : Fin m → ℂ) (hz : ∑ j, Complex.normSq (z j) = 1) :
    ∃ U : Matrix.specialUnitaryGroup (Fin m) ℂ, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ j, (U : Matrix (Fin m) (Fin m) ℂ) j ⟨0, hm⟩ = c * z j := by
  let v : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 z
  have hv : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : ∑ j, ‖v j‖ ^ 2 = 1 := by
      rw [← hz]
      exact Finset.sum_congr rfl fun j _ => by simp [v, Complex.normSq_eq_norm_sq]
    rw [this]; simp
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by simp
  have hon : Orthonormal ℂ (({⟨0, hm⟩} : Set (Fin m)).restrict (fun _ : Fin m => v)) := by
    refine ⟨fun i => hv, fun i j hij => ?_⟩
    exact absurd (Subtype.ext ((Set.mem_singleton_iff.1 i.2).trans (Set.mem_singleton_iff.1 j.2).symm)) hij
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hon
  have hb0 : b ⟨0, hm⟩ = v := hb ⟨0, hm⟩ rfl
  let W : Matrix (Fin m) (Fin m) ℂ := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.toMatrix b
  have hW : W ∈ Matrix.unitaryGroup (Fin m) ℂ :=
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _
  have hWj : ∀ j, W j ⟨0, hm⟩ = z j := by
    intro j
    simp only [W, Module.Basis.toMatrix_apply]
    rw [hb0]; simp [v]
  have hdn : ‖W.det‖ = 1 := by
    have := (EuclideanSpace.basisFun (Fin m) ℂ).det_to_matrix_orthonormalBasis b
    rwa [Module.Basis.det_apply] at this
  have hdd : W.det * star W.det = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hdn]; simp
  let s : ℂ := star W.det
  let D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal (fun i => if i = ⟨0, hm⟩ then s else 1)
  have hsn : s * star s = 1 := by
    simp only [s, star_star]
    rw [mul_comm]; exact hdd
  have hDu : D ∈ Matrix.unitaryGroup (Fin m) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp only [D, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : i = ⟨0, hm⟩
    · simp [h]; exact hsn
    · simp [h]
  have hDdet : D.det = s := by
    simp [D, Matrix.det_diagonal]
  refine ⟨⟨W * D, Matrix.mem_specialUnitaryGroup_iff.2 ⟨Submonoid.mul_mem _ hW hDu, ?_⟩⟩, s, ?_, ?_⟩
  · rw [Matrix.det_mul, hDdet]; exact hdd
  · simp only [s, norm_star, hdn]
  · intro j
    show (W * D) j ⟨0, hm⟩ = s * z j
    rw [Matrix.mul_apply]
    simp [D, Matrix.diagonal_apply, hWj, mul_comm]

theorem pst_eq {r : ℕ} (d : Fin r → ℕ) (hd : ∀ k, 0 < d k) (X : ArrayIndex d → ℂ)
    (U : (k : Fin r) → Matrix.specialUnitaryGroup (Fin (d k)) ℂ) :
    pureStateTransfer X (tensorSeed d) (tensorUnitary U) = Complex.normSq (vInner X
        (tensorProduct (fun k j => (U k : (Matrix (Fin (d k)) (Fin (d k)) ℂ)) j ⟨0, hd k⟩))) := by
  set y := tensorSeed d with hy
  set M := tensorUnitary U with hM
  set w : ArrayIndex d → ℂ := tensorProduct (fun k j => (U k : (Matrix (Fin (d k)) (Fin (d k)) ℂ)) j ⟨0, hd k⟩)
    with hw
  have hMy : ∀ i, (M *ᵥ y) i = w i := by
    intro i
    have hy' : ∀ j : ArrayIndex d, y j = if j = (fun k => ⟨0, hd k⟩) then 1 else 0 := by
      intro j
      simp only [hy, tensorSeed]
      by_cases h : ∀ k, (j k).val = 0
      · have : j = fun k => ⟨0, hd k⟩ := funext fun k => Fin.ext (h k)
        simp [h, this]
      · have : j ≠ fun k => ⟨0, hd k⟩ := fun e => h fun k => by rw [e]
        simp [h, this]
    simp only [Matrix.mulVec, dotProduct, hy']
    simp [hM, tensorUnitary, hw, tensorProduct]
  have hro : ∀ x : ArrayIndex d → ℂ, rankOneMatrix x = Matrix.vecMulVec x (star x) := by
    intro x
    ext a b
    simp [rankOneMatrix, QAlgorithms.pureDensity, Matrix.vecMulVec_apply]
  have hMy' : M *ᵥ y = w := funext hMy
  have hmain : Matrix.trace (rankOneMatrix X * M * rankOneMatrix y * M.conjTranspose) =
      (vInner X w) * star (vInner X w) := by
    rw [hro, hro, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec,
      Matrix.vecMulVec_mul]
    simp only [Matrix.smul_vecMul, Matrix.vecMulVec_smul, Matrix.trace_smul, Matrix.trace_vecMulVec,
      smul_eq_mul]
    have e1 : (star X ᵥ* M) ⬝ᵥ y = vInner X w := by
      rw [← Matrix.dotProduct_mulVec, hMy']
      simp [vInner, dotProduct]
    have e2 : X ⬝ᵥ (star y ᵥ* M.conjTranspose) = star (vInner X w) := by
      rw [← Matrix.star_mulVec, hMy']
      simp [vInner, dotProduct, star_sum, mul_comm]
    rw [e1, e2]
  unfold pureStateTransfer
  rw [hmain, Complex.star_def, Complex.mul_conj]
  simp

theorem solution {r : ℕ} (hr : 0 < r) (d : Fin r → ℕ)
    (hd : ∀ k, 0 < d k) (X : ArrayIndex d → ℂ) :
    (∀ U : (k : Fin r) → Matrix.specialUnitaryGroup (Fin (d k)) ℂ,
      pureStateTransfer X (tensorSeed d) (tensorUnitary U) = Complex.normSq (vInner X
        (tensorProduct (fun k j => (U k : (Matrix (Fin (d k)) (Fin (d k)) ℂ)) j ⟨0, hd k⟩)))) ∧
    ∃ v : ℝ,
      IsGreatest {v | ∃ U : (k : Fin r) → Matrix.specialUnitaryGroup (Fin (d k)) ℂ,
        v = pureStateTransfer X (tensorSeed d) (tensorUnitary U)} v ∧
      IsGreatest {v | ∃ z : (k : Fin r) → Fin (d k) → ℂ,
        unitTensorFactors z ∧ v = Complex.normSq (vInner X (tensorProduct z))} v := by
  refine ⟨fun U => pst_eq d hd X U, ?_⟩
  set f : ((k : Fin r) → Fin (d k) → ℂ) → ℂ := fun z => vInner X (tensorProduct z) with hf
  have hcomp : IsCompact {z : (k : Fin r) → Fin (d k) → ℂ | unitTensorFactors z} := by
    have h1 : {z : (k : Fin r) → Fin (d k) → ℂ | unitTensorFactors z} =
        Set.pi Set.univ (fun k => {y : Fin (d k) → ℂ | ∑ j, Complex.normSq (y j) = 1}) := by
      ext z; simp [unitTensorFactors]
    rw [h1]
    refine isCompact_univ_pi fun k => ?_
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_eq (continuous_finset_sum _ fun j _ =>
        Complex.continuous_normSq.comp (continuous_apply j)) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Fin (d k) → ℂ)) (r := 1)).subset ?_
      intro y hy
      simp only [Set.mem_setOf_eq] at hy
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      have h2 : Complex.normSq (y j) ≤ 1 := by
        rw [← hy]
        exact Finset.single_le_sum (f := fun j => Complex.normSq (y j))
          (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      rw [Complex.normSq_eq_norm_sq] at h2
      nlinarith [norm_nonneg (y j)]
  have hne : ({z : (k : Fin r) → Fin (d k) → ℂ | unitTensorFactors z}).Nonempty := by
    refine ⟨fun k j => if j = ⟨0, hd k⟩ then 1 else 0, fun k => ?_⟩
    simp
  have hcont : Continuous f := by
    simp only [hf, vInner, tensorProduct]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul
      (continuous_finset_prod _ fun k _ => (continuous_apply (i k)).comp (continuous_apply k))
  have hg : Continuous (fun z => Complex.normSq (f z)) := Complex.continuous_normSq.comp hcont
  obtain ⟨zs, hzs, hmax⟩ := hcomp.exists_isMaxOn hne hg.continuousOn
  have hmax' : ∀ w, unitTensorFactors w → Complex.normSq (f w) ≤ Complex.normSq (f zs) :=
    fun w hw => hmax hw
  have hcols : ∀ U : (k : Fin r) → Matrix.specialUnitaryGroup (Fin (d k)) ℂ,
      unitTensorFactors (fun k j => (U k : Matrix (Fin (d k)) (Fin (d k)) ℂ) j ⟨0, hd k⟩) := by
    intro U k
    have h := Matrix.mem_unitaryGroup_iff'.1 (Matrix.mem_specialUnitaryGroup_iff.1 (U k).2).1
    have h2 := congrFun (congrFun h ⟨0, hd k⟩) ⟨0, hd k⟩
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h2
    have h3 : ((∑ j, Complex.normSq ((U k : Matrix (Fin (d k)) (Fin (d k)) ℂ) j ⟨0, hd k⟩) : ℝ) : ℂ) = 1 := by
      rw [← h2]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    exact_mod_cast h3
  have hreal : ∀ z : (k : Fin r) → Fin (d k) → ℂ, unitTensorFactors z →
      ∃ U : (k : Fin r) → Matrix.specialUnitaryGroup (Fin (d k)) ℂ,
        Complex.normSq (f (fun k j => (U k : Matrix (Fin (d k)) (Fin (d k)) ℂ) j ⟨0, hd k⟩)) =
          Complex.normSq (f z) := by
    intro z hz
    have := fun k => colB (hd k) (z k) (hz k)
    choose U c hc hU using this
    refine ⟨U, ?_⟩
    have hcols' : (fun k j => (U k : Matrix (Fin (d k)) (Fin (d k)) ℂ) j ⟨0, hd k⟩) =
        fun k j => c k * z k j := funext fun k => funext fun j => hU k j
    have hT : ∀ i : ArrayIndex d, tensorProduct (fun k j => c k * z k j) i =
        (∏ k, c k) * tensorProduct z i := by
      intro i
      simp only [tensorProduct]
      rw [Finset.prod_mul_distrib]
    have h1 : f (fun k j => c k * z k j) = (∏ k, c k) * f z := by
      simp only [hf, vInner, hT]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : Complex.normSq (∏ k, c k) = 1 := by
      rw [map_prod]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Complex.normSq_eq_norm_sq, hc k]; norm_num
    rw [hcols', h1, map_mul, h2, one_mul]
  refine ⟨Complex.normSq (f zs), ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨U, hU⟩ := hreal zs hzs
    refine ⟨U, ?_⟩
    rw [pst_eq d hd X U, ← hU]
  · rintro v ⟨U, rfl⟩
    rw [pst_eq d hd X U]
    exact hmax' _ (hcols U)
  · exact ⟨zs, hzs, rfl⟩
  · rintro v ⟨z, hz, rfl⟩
    exact hmax' z hz
