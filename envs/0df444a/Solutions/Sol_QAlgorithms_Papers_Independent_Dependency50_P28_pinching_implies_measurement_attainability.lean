-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P28.pinching_implies_measurement_attainability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:16:57.907635+00:00
-- url     : https://prove2.me/submissions/7221ceee-fa9e-4860-b167-c57241c35f2c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open Module in

theorem g55c_joint {K : Type} [Fintype K] [DecidableEq K] (A B : Matrix K K ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ U : Matrix K K ℂ, U ∈ Matrix.unitaryGroup K ℂ ∧ ∃ a b : K → ℂ,
      A * U = U * Matrix.diagonal a ∧ B * U = U * Matrix.diagonal b := by
  classical
  set TA := Matrix.toEuclideanLin A
  set TB := Matrix.toEuclideanLin B
  have sA : TA.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have sB : TB.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hC : Commute TA TB := by
    show TA * TB = TB * TA
    apply LinearMap.ext; intro v
    show TA (TB v) = TB (TA v)
    simp only [TA, TB, Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAB.eq]
  have hInt := LinearMap.IsSymmetric.directSum_isInternal_of_commute sA sB hC
  have hOrth := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace sA sB
  set V := fun (i : ℂ × ℂ) => Module.End.eigenspace TA i.2 ⊓ Module.End.eigenspace TB i.1 with hV
  let ι := {i // V i ≠ ⊥}
  letI : Fintype ι := hInt.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  let W : ι → Submodule ℂ (EuclideanSpace ℂ K) := fun i => V i.1
  have hInt' : DirectSum.IsInternal W := DirectSum.isInternal_ne_bot_iff.mpr hInt
  have hOrth' : OrthogonalFamily ℂ (fun i => W i) fun i => (W i).subtypeₗᵢ :=
    hOrth.comp (Subtype.val_injective (p := fun i => V i ≠ ⊥))
  have hn : Module.finrank ℂ (EuclideanSpace ℂ K) = Fintype.card K := finrank_euclideanSpace
  let b0 := hInt'.subordinateOrthonormalBasis hn hOrth'
  let e := (Fintype.equivFin K)
  let b := b0.reindex e.symm
  let idx : K → ι := fun k => hInt'.subordinateOrthonormalBasisIndex hn (e k) hOrth'
  have hb : ∀ k, b k ∈ W (idx k) := by
    intro k
    have := hInt'.subordinateOrthonormalBasis_subordinate hn (e k) hOrth'
    simpa [b, b0, idx] using this
  refine ⟨(EuclideanSpace.basisFun K ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun K ℂ).toMatrix_orthonormalBasis_mem_unitary b,
    fun k => (idx k).1.2, fun k => (idx k).1.1, ?_, ?_⟩
  · ext i k
    have h1 := (Submodule.mem_inf.mp (hb k)).1
    rw [Module.End.mem_eigenspace_iff] at h1
    have h2 := congrArg (fun v => v i) h1
    simp only [TA, Matrix.toEuclideanLin_apply] at h2
    simp [Matrix.mul_apply, Basis.toMatrix_apply, Matrix.mulVec, dotProduct] at h2 ⊢
    rw [h2]; simp [Matrix.diagonal_apply, mul_comm]
  · ext i k
    have h1 := (Submodule.mem_inf.mp (hb k)).2
    rw [Module.End.mem_eigenspace_iff] at h1
    have h2 := congrArg (fun v => v i) h1
    simp only [TB, Matrix.toEuclideanLin_apply] at h2
    simp [Matrix.mul_apply, Basis.toMatrix_apply, Matrix.mulVec, dotProduct] at h2 ⊢
    rw [h2]; simp [Matrix.diagonal_apply, mul_comm]


theorem g55c_cfc_eig {K ι : Type} [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
    (σ : Matrix K K ℂ) (hσ : σ.IsHermitian) (U : Matrix K ι ℂ) (a : ι → ℂ)
    (hU : Uᴴ * U = 1) (h : σ * U = U * Matrix.diagonal a) (f : ℝ → ℝ) :
    cfc f σ * U = U * Matrix.diagonal (fun k => ((f (a k).re : ℝ) : ℂ)) ∧
      ∀ k, ∃ i, (hσ.eigenvalues i : ℂ) = a k := by
  set V : Matrix K K ℂ := (hσ.eigenvectorUnitary : Matrix K K ℂ) with hVdef
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hσ.eigenvectorUnitary.2
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hσ.eigenvectorUnitary.2
  have hrep : ∀ g : ℝ → ℝ, cfc g σ =
      V * Matrix.diagonal (fun i => ((g (hσ.eigenvalues i) : ℝ) : ℂ)) * Vᴴ := by
    intro g
    rw [hσ.cfc_eq]
    simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, hVdef, Matrix.star_eq_conjTranspose]
    rfl
  have hσrep : σ = V * Matrix.diagonal (fun i => ((hσ.eigenvalues i : ℝ) : ℂ)) * Vᴴ := by
    conv_lhs => rw [← cfc_id' ℝ σ]
    exact hrep id
  set W := Vᴴ * U with hW
  have hDW : Matrix.diagonal (fun i => ((hσ.eigenvalues i : ℝ) : ℂ)) * W = W * Matrix.diagonal a := by
    have : Vᴴ * σ * U = Vᴴ * (U * Matrix.diagonal a) := by rw [Matrix.mul_assoc, h]
    rw [hσrep] at this
    simp only [Matrix.mul_assoc] at this
    rw [← Matrix.mul_assoc Vᴴ V, hV1, Matrix.one_mul] at this
    rw [hW, Matrix.mul_assoc, this, ← Matrix.mul_assoc]
  have hent : ∀ i k, W i k ≠ 0 → (hσ.eigenvalues i : ℂ) = a k := by
    intro i k hik
    have := congrFun (congrFun hDW i) k
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm] at this
    exact mul_left_cancel₀ hik this
  refine ⟨?_, ?_⟩
  · have hDf : Matrix.diagonal (fun i => ((f (hσ.eigenvalues i) : ℝ) : ℂ)) * W =
        W * Matrix.diagonal (fun k => ((f (a k).re : ℝ) : ℂ)) := by
      ext i k
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
      by_cases hik : W i k = 0
      · simp [hik]
      · have := hent i k hik
        rw [← this, Complex.ofReal_re, mul_comm]
    calc cfc f σ * U = V * (Matrix.diagonal (fun i => ((f (hσ.eigenvalues i) : ℝ) : ℂ)) * W) := by
          rw [hrep, hW]; simp only [Matrix.mul_assoc]
      _ = (V * Vᴴ) * U * Matrix.diagonal (fun k => ((f (a k).re : ℝ) : ℂ)) := by
          rw [hDf, hW]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV2, Matrix.one_mul]
  · intro k
    have hWW : Wᴴ * W = 1 := by
      rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, hV2, Matrix.one_mul, hU]
    by_contra hne
    have h0 : ∀ i, W i k = 0 := fun i => by
      by_contra hik; exact hne ⟨i, hent i k hik⟩
    have := congrFun (congrFun hWW k) k
    simp [Matrix.mul_apply, h0] at this

/-- dephasing measurement in the orthonormal basis given by the columns of U. -/
def g55c_deph {K : Type} [Fintype K] [DecidableEq K] (U : Matrix K K ℂ) (hU1 : Uᴴ * U = 1) :
    CommutingRangeMeasurement K where
  out := K
  map :=
    { toFun := fun X => U * Matrix.diagonal (fun k => (Uᴴ * X * U) k k) * Uᴴ
      map_add' := by
        intro X Y
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        rw [← Matrix.diagonal_add]
        simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c X
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply]
        rw [show (Matrix.diagonal fun k => c • (Uᴴ * X * U) k k) =
          c • Matrix.diagonal (fun k => (Uᴴ * X * U) k k) by
            ext i j; by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]]
        simp only [Matrix.mul_smul, Matrix.smul_mul] }
  positive := by
    intro A hA
    show (U * Matrix.diagonal (fun k => (Uᴴ * A * U) k k) * Uᴴ).PosSemidef
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    apply Matrix.PosSemidef.diagonal
    intro k
    exact (hA.conjTranspose_mul_mul_same U).diag_nonneg
  tracePreserving := by
    intro A
    show (U * Matrix.diagonal (fun k => (Uᴴ * A * U) k k) * Uᴴ).trace = A.trace
    rw [Matrix.trace_mul_cycle, hU1, Matrix.one_mul, Matrix.trace_diagonal]
    change (Uᴴ * A * U).trace = A.trace
    rw [Matrix.trace_mul_cycle, mul_eq_one_comm.mp hU1, Matrix.one_mul]
  commuting := by
    intro A B
    show U * Matrix.diagonal (fun k => (Uᴴ * A * U) k k) * Uᴴ *
        (U * Matrix.diagonal (fun k => (Uᴴ * B * U) k k) * Uᴴ) =
      U * Matrix.diagonal (fun k => (Uᴴ * B * U) k k) * Uᴴ *
        (U * Matrix.diagonal (fun k => (Uᴴ * A * U) k k) * Uᴴ)
    have key : ∀ D1 D2 : Matrix K K ℂ, U * D1 * Uᴴ * (U * D2 * Uᴴ) = U * (D1 * D2) * Uᴴ := by
      intro D1 D2
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hU1, Matrix.one_mul]
    rw [key, key, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm]

theorem g55c_deph_apply {K : Type} [Fintype K] [DecidableEq K] (U : Matrix K K ℂ) (hU1 : Uᴴ * U = 1)
    (X : Matrix K K ℂ) :
    (g55c_deph U hU1).map X = U * Matrix.diagonal (fun k => (Uᴴ * X * U) k k) * Uᴴ := rfl

theorem g55c_main {K : Type} [Fintype K] [DecidableEq K] (rho sigma : Matrix K K ℂ)
    (hr : rho.IsHermitian) (hs : sigma.IsHermitian) :
    ∃ (U : Matrix K K ℂ) (hU1 : Uᴴ * U = 1),
      (g55c_deph U hU1).map rho = pinch sigma rho ∧ (g55c_deph U hU1).map sigma = sigma := by
  set P : ℝ → Matrix K K ℂ := fun l => cfc (fun x : ℝ => if x = l then (1:ℝ) else 0) sigma with hP
  have hPH : ∀ l, (P l)ᴴ = P l := fun l => by
    have : IsSelfAdjoint (P l) := cfc_predicate _ _
    exact this
  have hσP : ∀ l, sigma * P l = (l : ℂ) • P l := by
    intro l
    have hfin := sigma.finite_real_spectrum
    have hsa : IsSelfAdjoint sigma := hs
    conv_lhs => rw [← cfc_id' ℝ sigma]
    rw [hP]; simp only
    rw [← cfc_mul _ _ sigma (hfin.continuousOn _) (hfin.continuousOn _)]
    rw [show (l : ℂ) • cfc (fun x : ℝ => if x = l then (1:ℝ) else 0) sigma =
      l • cfc (fun x : ℝ => if x = l then (1:ℝ) else 0) sigma from (Complex.coe_smul l _).symm]
    rw [← cfc_smul l _ sigma (hfin.continuousOn _)]
    apply cfc_congr
    intro x _
    by_cases h : x = l <;> simp [h]
  have hPσ : ∀ l, P l * sigma = (l : ℂ) • P l := by
    intro l
    have := congrArg Matrix.conjTranspose (hσP l)
    rw [Matrix.conjTranspose_mul, hs.eq, hPH, Matrix.conjTranspose_smul, hPH] at this
    rw [this]; simp
  have hpin : pinch sigma rho = ∑ l ∈ Finset.univ.image hs.eigenvalues, P l * rho * P l := by
    rw [pinch, dif_pos hs]
  set π := pinch sigma rho with hπ
  have hπH : π.IsHermitian := by
    rw [hpin, Matrix.IsHermitian, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPH, hr.eq, Matrix.mul_assoc]
  have hcomm : Commute sigma π := by
    show sigma * π = π * sigma
    rw [hpin, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hσP, Matrix.mul_assoc, Matrix.mul_assoc, hPσ]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  obtain ⟨U, hUu, a, c, hA, hC⟩ := g55c_joint sigma π hs hπH hcomm
  have hU1 : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hUu
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hUu
  refine ⟨U, hU1, ?_, ?_⟩
  · rw [g55c_deph_apply]
    have hdiag : ∀ k, (Uᴴ * rho * U) k k = c k := by
      intro k
      have h1 : Uᴴ * π * U = Matrix.diagonal c := by
        rw [Matrix.mul_assoc, hC, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
      have h2 := congrFun (congrFun h1 k) k
      rw [Matrix.diagonal_apply_eq] at h2
      rw [← h2, hpin, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
      obtain ⟨i, hi⟩ := (g55c_cfc_eig sigma hs U a hU1 hA (fun x => 0)).2 k
      have hterm : ∀ l, (Uᴴ * (P l * rho * P l) * U) k k =
          (if (a k).re = l then 1 else 0) * (Uᴴ * rho * U) k k := by
        intro l
        have hPU := (g55c_cfc_eig sigma hs U a hU1 hA (fun x : ℝ => if x = l then (1:ℝ) else 0)).1
        set D : Matrix K K ℂ := Matrix.diagonal (fun k => (((if (a k).re = l then (1:ℝ) else 0) : ℝ) : ℂ)) with hD
        have hDH : Dᴴ = D := by
          rw [hD, Matrix.diagonal_conjTranspose]; congr 1; funext k; simp
        have hUP : Uᴴ * P l = D * Uᴴ := by
          have := congrArg Matrix.conjTranspose hPU
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPH, hDH] at this
          exact this
        have : Uᴴ * (P l * rho * P l) * U = D * (Uᴴ * rho * U) * D := by
          calc Uᴴ * (P l * rho * P l) * U = (Uᴴ * P l) * rho * (P l * U) := by
                simp only [Matrix.mul_assoc]
            _ = (D * Uᴴ) * rho * (U * D) := by rw [hUP, hPU]
            _ = _ := by simp only [Matrix.mul_assoc]
        rw [this, hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
        by_cases h : (a k).re = l <;> simp [h]
      simp only [hterm]
      rw [← Finset.sum_mul]
      have hmem : (a k).re ∈ Finset.univ.image hs.eigenvalues := by
        rw [← hi]; simp
      rw [Finset.sum_ite_eq, if_pos hmem, one_mul]
    rw [show (fun k => (Uᴴ * rho * U) k k) = c from funext hdiag, ← hC, Matrix.mul_assoc,
      hU2, Matrix.mul_one]
  · rw [g55c_deph_apply]
    have h1 : Uᴴ * sigma * U = Matrix.diagonal a := by
      rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
    rw [show (fun k => (Uᴴ * sigma * U) k k) = a from funext fun k => by rw [h1]; simp,
      ← hA, Matrix.mul_assoc, hU2, Matrix.mul_one]


theorem g55c_copies_herm {K : Type} [Fintype K] {X : Matrix K K ℂ} (hX : X.IsHermitian) (m : ℕ) :
    (copies m X).IsHermitian := by
  ext x y
  show star (∏ i, X (y i) (x i)) = ∏ i, X (x i) (y i)
  rw [Complex.star_def, map_prod]
  exact Finset.prod_congr rfl fun i _ => hX.apply (x i) (y i)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.21: Asymptotic pinching attainment implies measurement attainment. Measurements in the definition may output commuting matrices in the same space. A pair-dependent joint-eigenbasis dephasing matches both pinched outputs exactly, without an unassumed basis-invariance hypothesis. -/
theorem solution (d : Divergence) :
    AAP d → AAM d := by
  intro h K _ _ rho sigma hr hs
  have key : ∀ n : ℕ, ∃ (U : Matrix (Fin (n+1) → K) (Fin (n+1) → K) ℂ) (hU1 : Uᴴ * U = 1),
      (g55c_deph U hU1).map (copies (n+1) rho) = pinch (copies (n+1) sigma) (copies (n+1) rho) ∧
      (g55c_deph U hU1).map (copies (n+1) sigma) = copies (n+1) sigma :=
    fun n => g55c_main _ _ (g55c_copies_herm hr.1.isHermitian _) (g55c_copies_herm hs.1.isHermitian _)
  choose U hU1 h1 h2 using key
  refine ⟨fun n => g55c_deph (U n) (hU1 n), ?_⟩
  refine (h K rho sigma hr hs).congr (fun n => ?_)
  show _ = scaled n (d (Fin (n+1) → K) ((g55c_deph (U n) (hU1 n)).map (copies (n + 1) rho))
    ((g55c_deph (U n) (hU1 n)).map (copies (n + 1) sigma)))
  rw [h1 n, h2 n]


end

