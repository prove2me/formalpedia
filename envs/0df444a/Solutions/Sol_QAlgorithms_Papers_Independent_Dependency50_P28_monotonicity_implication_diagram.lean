-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P28.monotonicity_implication_diagram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T09:40:26.423982+00:00
-- url     : https://prove2.me/submissions/6af47260-cc94-443c-afda-d6150a03117f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open Module
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


theorem g56_jointF {K ι : Type} [Fintype K] [DecidableEq K] (T : ι → Matrix K K ℂ)
    (hH : ∀ p, (T p).IsHermitian) (hC : ∀ p q, Commute (T p) (T q)) :
    ∃ U : Matrix K K ℂ, U ∈ Matrix.unitaryGroup K ℂ ∧ ∀ p, ∃ a : K → ℂ,
      T p * U = U * Matrix.diagonal a := by
  classical
  let TL : ι → Module.End ℂ (EuclideanSpace ℂ K) := fun p => Matrix.toEuclideanLin (T p)
  have sT : ∀ p, (TL p).IsSymmetric := fun p => Matrix.isSymmetric_toEuclideanLin_iff.mpr (hH p)
  have hCL : Pairwise (Function.onFun Commute TL) := by
    intro p q _
    show TL p * TL q = TL q * TL p
    apply LinearMap.ext; intro v
    show TL p (TL q v) = TL q (TL p v)
    simp only [TL, Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hC p q).eq]
  have hInt := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute sT hCL
  have hOrth := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces sT
  set V := fun (γ : ι → ℂ) => (⨅ j, Module.End.eigenspace (TL j) (γ j) : Submodule ℂ (EuclideanSpace ℂ K)) with hV
  let κ := {γ // V γ ≠ ⊥}
  letI : Fintype κ := hInt.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  let W : κ → Submodule ℂ (EuclideanSpace ℂ K) := fun i => V i.1
  have hInt' : DirectSum.IsInternal W := DirectSum.isInternal_ne_bot_iff.mpr hInt
  have hOrth' : OrthogonalFamily ℂ (fun i => W i) fun i => (W i).subtypeₗᵢ :=
    hOrth.comp (Subtype.val_injective (p := fun i => V i ≠ ⊥))
  have hn : Module.finrank ℂ (EuclideanSpace ℂ K) = Fintype.card K := finrank_euclideanSpace
  let b0 := hInt'.subordinateOrthonormalBasis hn hOrth'
  let e := (Fintype.equivFin K)
  let b := b0.reindex e.symm
  let idx : K → κ := fun k => hInt'.subordinateOrthonormalBasisIndex hn (e k) hOrth'
  have hb : ∀ k, b k ∈ W (idx k) := by
    intro k
    have := hInt'.subordinateOrthonormalBasis_subordinate hn (e k) hOrth'
    simpa [b, b0, idx] using this
  refine ⟨(EuclideanSpace.basisFun K ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun K ℂ).toMatrix_orthonormalBasis_mem_unitary b,
    fun p => ⟨fun k => (idx k).1 p, ?_⟩⟩
  ext i k
  have h1 := (Submodule.mem_iInf _).mp (hb k) p
  rw [Module.End.mem_eigenspace_iff] at h1
  have h2 := congrArg (fun v => v i) h1
  simp only [TL, Matrix.toEuclideanLin_apply] at h2
  simp [Matrix.mul_apply, Basis.toMatrix_apply, Matrix.mulVec, dotProduct] at h2 ⊢
  rw [h2]; simp [Matrix.diagonal_apply, mul_comm]

theorem g56_psd_of_nonneg {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (hq : ∀ v : n → ℂ, 0 ≤ star v ⬝ᵥ (M *ᵥ v)) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ hq
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have h := hq (WithLp.ofLp v)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
  have him := (Complex.nonneg_iff.mp h).2
  have e : v.ofLp ⬝ᵥ star (M *ᵥ v.ofLp) = star (star v.ofLp ⬝ᵥ M *ᵥ v.ofLp) := by
    simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  rw [e]
  apply Complex.ext <;> simp; rw [← him]; simp

theorem g56_lin_expand {I O : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- E_ij as a combination of rank-one projectors. -/
theorem g56_single_eq {I : Type} [Fintype I] [DecidableEq I] (i j : I) :
    (Matrix.single i j (1 : ℂ) : Matrix I I ℂ) =
      (1 / 2 : ℂ) • (Matrix.vecMulVec (Pi.single i 1 + Pi.single j 1) (star (Pi.single i 1 + Pi.single j 1)) -
        Matrix.vecMulVec (Pi.single i 1) (star (Pi.single i 1)) - Matrix.vecMulVec (Pi.single j 1) (star (Pi.single j 1))) +
      (Complex.I / 2) • (Matrix.vecMulVec (Pi.single i 1 + Complex.I • Pi.single j 1)
          (star (Pi.single i 1 + Complex.I • Pi.single j 1)) -
        Matrix.vecMulVec (Pi.single i 1) (star (Pi.single i 1)) - Matrix.vecMulVec (Pi.single j 1) (star (Pi.single j 1))) := by
  ext a b
  simp only [Matrix.single_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Pi.add_apply, Pi.star_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, star_add, star_mul']
  by_cases hij : i = j
  · subst hij
    by_cases ha : a = i <;> by_cases hb : b = i <;> (try simp [Complex.conj_I, *]) <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring_nf) <;> (try tauto)
  · have hji : j ≠ i := Ne.symm hij
    by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases ha' : a = j <;> by_cases hb' : b = i <;>
      (try subst_vars) <;> (try simp [Complex.conj_I, *]) <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring_nf) <;> (try tauto)
theorem g55c_lin_expand {I O : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem g55c_kraus_of_cp {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hΦ : Entanglement.IsCompletelyPositive Φ) :
    ∃ (m : ℕ) (K : Fin m → Matrix J I ℂ), ∀ X, Φ X = ∑ l, K l * X * (K l)ᴴ := by
  set r := Fintype.card I
  let e : I ≃ Fin r := Fintype.equivFin I
  let ω : Fin r × I → ℂ := fun p => if p.1 = e p.2 then 1 else 0
  have hX0 := Matrix.posSemidef_vecMulVec_self_star ω
  have hY := hΦ r _ hX0
  let C : Matrix (J × I) (J × I) ℂ := fun p q => Φ (Matrix.single p.2 q.2 1) p.1 q.1
  have hC : C = (idTensorSuperop Φ (Matrix.vecMulVec ω (star ω))).submatrix
      (fun p => (e p.2, p.1)) (fun p => (e p.2, p.1)) := by
    ext ⟨o, i⟩ ⟨o', i'⟩
    have hω : (Matrix.of fun a b => Matrix.vecMulVec ω (star ω) (e i, a) (e i', b)) =
        Matrix.single i i' 1 := by
      ext a b
      simp only [Matrix.of_apply, Matrix.vecMulVec_apply, ω, Pi.star_apply, Matrix.single_apply]
      by_cases ha : i = a <;> by_cases hb : i' = b <;> simp [ha, hb, e.apply_eq_iff_eq]
    simp only [C, Matrix.submatrix_apply, idTensorSuperop, Matrix.of_apply]
    rw [hω]
  have hCpsd : C.PosSemidef := by rw [hC]; exact hY.submatrix _
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hCpsd
  refine ⟨m, fun l => Matrix.of fun o i => v l (o, i), fun X => ?_⟩
  rw [g55c_lin_expand Φ X]
  ext o o'
  have hE : ∀ i j, Φ (Matrix.single i j 1) o o' = C (o, i) (o', j) := fun _ _ => rfl
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hE, hv, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  let eq3 : I × I × Fin m ≃ Fin m × I × I :=
    { toFun := fun x => (x.2.2, x.2.1, x.1)
      invFun := fun x => (x.2.2, x.2.1, x.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv eq3 _ _ (fun x => ?_)
  simp only [eq3, Equiv.coe_fn_mk]; ring

theorem g55c_sum_psd {n ι : Type*} [Fintype n] (s : Finset ι) (A : ι → Matrix n n ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem g55c_kraus_single {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {m : ℕ} (K : Fin m → Matrix J I ℂ) (a b : I) (o o' : J) :
    (∑ l, K l * (Matrix.single a b (1:ℂ) : Matrix I I ℂ) * (K l)ᴴ) o o' = ∑ l, K l o a * star (K l o' b) := by
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and, Finset.sum_ite_eq,
    ite_mul]

theorem g55c_tensor_pos {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) {m : ℕ} (K : Fin m → Matrix J I ℂ)
    (hK : ∀ X, Φ X = ∑ l, K l * X * (K l)ᴴ) (n : ℕ) (A : Matrix (Fin n → I) (Fin n → I) ℂ)
    (hA : A.PosSemidef) :
    (piSuperop (fun _ : Fin n => (Φ : Matrix I I ℂ → Matrix J J ℂ)) A).PosSemidef := by
  let F : (Fin n → Fin m) → Matrix (Fin n → J) (Fin n → I) ℂ :=
    fun L => Matrix.of fun y x => ∏ i, K (L i) (y i) (x i)
  have heq : piSuperop (fun _ : Fin n => (Φ : Matrix I I ℂ → Matrix J J ℂ)) A =
      ∑ L, F L * A * (F L)ᴴ := by
    have hΦs : ∀ a b o o', Φ (Matrix.single a b 1) o o' = ∑ l, K l o a * star (K l o' b) := by
      intro a b o o'; rw [hK, g55c_kraus_single]
    ext y y'
    simp only [piSuperop, Matrix.of_apply, hΦs]
    rw [Matrix.sum_apply]
    simp only [Fintype.prod_sum]
    simp only [F, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum,
      Finset.sum_mul]
    simp only [← Fintype.sum_prod_type']
    let eq3 : (Fin n → I) × (Fin n → I) × (Fin n → Fin m) ≃ (Fin n → Fin m) × (Fin n → I) × (Fin n → I) :=
      { toFun := fun x => (x.2.2, x.2.1, x.1)
        invFun := fun x => (x.2.2, x.2.1, x.1)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine Fintype.sum_equiv eq3 _ _ (fun x => ?_)
    simp only [eq3, Equiv.coe_fn_mk, Finset.prod_mul_distrib, Complex.star_def, map_prod]
    ring
  rw [heq]
  exact g55c_sum_psd _ _ fun L => hA.mul_mul_conjTranspose_same _

open QAlgorithms.Papers.Independent.Dependency50.P28 in
theorem g55c_dual_kraus {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) {m : ℕ} (K : Fin m → Matrix J I ℂ)
    (hK : ∀ X, Φ X = ∑ l, K l * X * (K l)ᴴ) (B : Matrix J J ℂ) :
    hilbertSchmidtDual Φ B = ∑ l, (K l)ᴴ * B * K l := by
  have hΦs : ∀ a b o o', Φ (Matrix.single a b 1) o o' = ∑ l, K l o a * star (K l o' b) := by
    intro a b o o'; rw [hK, g55c_kraus_single]
  ext i j
  simp only [hilbertSchmidtDual, hΦs, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum, map_mul, Complex.star_def, Complex.conj_conj,
    Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  let eq3 : J × J × Fin m ≃ Fin m × J × J :=
    { toFun := fun x => (x.2.2, x.2.1, x.1)
      invFun := fun x => (x.2.2, x.2.1, x.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv eq3 _ _ (fun x => ?_)
  simp only [eq3, Equiv.coe_fn_mk]; ring

theorem g55c_kraus_tp {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) {m : ℕ} (K : Fin m → Matrix J I ℂ)
    (hK : ∀ X, Φ X = ∑ l, K l * X * (K l)ᴴ) (hT : ∀ X, (Φ X).trace = X.trace) :
    ∑ l, (K l)ᴴ * K l = 1 := by
  set G := ∑ l, (K l)ᴴ * K l
  have h : ∀ X, (G * X).trace = X.trace := by
    intro X
    rw [← hT X, hK, Matrix.trace_sum, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.trace_mul_comm (K l * X), ← Matrix.mul_assoc]
  ext i j
  have := h (Matrix.single j i 1)
  have e1 : (G * Matrix.single j i 1).trace = G i j := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]
  have e2 : (Matrix.single j i (1:ℂ)).trace = (1 : Matrix I I ℂ) i j := by
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hij), Matrix.one_apply_ne hij]
  rw [← e1, this, e2]

theorem g55c_schwarz_kraus {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {m : ℕ} (K : Fin m → Matrix J I ℂ) (hK1 : ∑ l, (K l)ᴴ * K l = 1) (A : Matrix J J ℂ) :
    ((∑ l, (K l)ᴴ * (Aᴴ * A) * K l) - (∑ l, (K l)ᴴ * A * K l)ᴴ * (∑ l, (K l)ᴴ * A * K l)).PosSemidef := by
  set Z := ∑ l, (K l)ᴴ * A * K l with hZ
  have hZH : Zᴴ = ∑ l, (K l)ᴴ * Aᴴ * K l := by
    rw [hZ, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hexp : ∑ l, (A * K l - K l * Z)ᴴ * (A * K l - K l * Z) =
      (∑ l, (K l)ᴴ * (Aᴴ * A) * K l) - (∑ l, (K l)ᴴ * Aᴴ * K l) * Z - Zᴴ * Z +
        Zᴴ * (∑ l, (K l)ᴴ * K l) * Z := by
    have hterm : ∀ l, (A * K l - K l * Z)ᴴ * (A * K l - K l * Z) =
        (K l)ᴴ * (Aᴴ * A) * K l - (K l)ᴴ * Aᴴ * K l * Z - Zᴴ * ((K l)ᴴ * A * K l) +
          Zᴴ * ((K l)ᴴ * K l) * Z := by
      intro l
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
      abel
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, ← hZ]
  rw [hK1, Matrix.mul_one, ← hZH] at hexp
  have : (∑ l, (K l)ᴴ * (Aᴴ * A) * K l) - Zᴴ * Z =
      ∑ l, (A * K l - K l * Z)ᴴ * (A * K l - K l * Z) := by
    rw [hexp]; abel
  rw [this]
  exact g55c_sum_psd _ _ fun l => Matrix.posSemidef_conjTranspose_mul_self _

def g56_choi {I O : Type*} (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) [DecidableEq I] : Matrix (O × I) (O × I) ℂ :=
  Matrix.of fun p q => M (Matrix.single p.2 q.2 1) p.1 q.1

theorem g56_sum_psd {n ι : Type*} [Fintype n] (s : Finset ι) (A : ι → Matrix n n ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem g56_swap22 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem g56_cp_of_choi {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hC : (g56_choi M).PosSemidef) :
    Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  obtain ⟨m2, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (o, i) * star (g l (o', j)) := by
    intro i j o o'
    have : g56_choi M (o, i) (o', j) = M (Matrix.single i j 1) o o' := rfl
    rw [← this, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  let F : Fin m1 → Fin m2 → (Fin r × O → ℂ) := fun a l q => ∑ i, v a (q.1, i) * g l (q.2, i)
  have hY : idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [g56_lin_expand]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [g56_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact g56_sum_psd _ _ fun a => g56_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _

theorem g56_cp_of_comm {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Mat I →ₗ[ℂ] Mat J) (hP : Positive M) (hC : ∀ A B, Commute (M A) (M B)) :
    Entanglement.IsCompletelyPositive M := by
  let vv : I × I × Fin 3 → (I → ℂ) := fun p =>
    if p.2.2 = 0 then Pi.single p.1 1 else if p.2.2 = 1 then Pi.single p.1 1 + Pi.single p.2.1 1
    else Pi.single p.1 1 + Complex.I • Pi.single p.2.1 1
  let T : I × I × Fin 3 → Mat J := fun p => M (Matrix.vecMulVec (vv p) (star (vv p)))
  have hTH : ∀ p, (T p).IsHermitian := fun p => (hP _ (Matrix.posSemidef_vecMulVec_self_star _)).1
  obtain ⟨U, hU, hdiag⟩ := g56_jointF T hTH (fun p q => hC _ _)
  have hU1 : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hU; rwa [Matrix.star_eq_conjTranspose] at this
  have hU2 : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).mp hU; rwa [Matrix.star_eq_conjTranspose] at this
  let D : Mat J → Prop := fun X => ∃ c : J → ℂ, X * U = U * Matrix.diagonal c
  have Dadd : ∀ X Y, D X → D Y → D (X + Y) := by
    rintro X Y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [Matrix.add_mul, hc, hd, ← Matrix.mul_add, Matrix.diagonal_add]; rfl⟩
  have Dsub : ∀ X Y, D X → D Y → D (X - Y) := by
    rintro X Y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c - d, by rw [Matrix.sub_mul, hc, hd, ← Matrix.mul_sub, Matrix.diagonal_sub]; rfl⟩
  have Dsmul : ∀ (z : ℂ) X, D X → D (z • X) := by
    rintro z X ⟨c, hc⟩
    exact ⟨z • c, by rw [Matrix.smul_mul, hc, ← Matrix.mul_smul, ← Matrix.diagonal_smul]⟩
  have hT0 : ∀ i, D (M (Matrix.vecMulVec (Pi.single i 1) (star (Pi.single i 1)))) := fun i => hdiag (i, i, 0)
  have hT1 : ∀ i j, D (M (Matrix.vecMulVec (Pi.single i 1 + Pi.single j 1) (star (Pi.single i 1 + Pi.single j 1)))) :=
    fun i j => hdiag (i, j, 1)
  have hT2 : ∀ i j, D (M (Matrix.vecMulVec (Pi.single i 1 + Complex.I • Pi.single j 1)
      (star (Pi.single i 1 + Complex.I • Pi.single j 1)))) := fun i j => hdiag (i, j, 2)
  have hE : ∀ i j, D (M (Matrix.single i j 1)) := by
    intro i j
    rw [g56_single_eq, map_add, map_smul, map_smul, map_sub, map_sub, map_sub, map_sub]
    exact Dadd _ _ (Dsmul _ _ (Dsub _ _ (Dsub _ _ (hT1 i j) (hT0 i)) (hT0 j)))
      (Dsmul _ _ (Dsub _ _ (Dsub _ _ (hT2 i j) (hT0 i)) (hT0 j)))
  let G : J → Matrix I I ℂ := fun k => Matrix.of fun i i' => (Uᴴ * M (Matrix.single i i' 1) * U) k k
  have hG : ∀ k, (G k).PosSemidef := by
    intro k
    apply g56_psd_of_nonneg
    intro x
    have hpsd := (hP _ (Matrix.posSemidef_vecMulVec_self_star (star x))).conjTranspose_mul_mul_same U
    have h0 := hpsd.diag_nonneg (i := k)
    convert h0 using 1
    rw [star_star, g56_lin_expand M (Matrix.vecMulVec (star x) x)]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Pi.star_apply, G,
      Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hME : ∀ i i' o o', M (Matrix.single i i' 1) o o' = ∑ k, U o k * G k i i' * star (U o' k) := by
    intro i i' o o'
    obtain ⟨c, hc⟩ := hE i i'
    have h1 : M (Matrix.single i i' 1) = U * Matrix.diagonal c * Uᴴ := by
      rw [← hc, Matrix.mul_assoc, hU2, Matrix.mul_one]
    have h2 : ∀ k, G k i i' = c k := by
      intro k
      simp only [G, Matrix.of_apply]
      rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, hU1, Matrix.one_mul, Matrix.diagonal_apply_eq]
    rw [h1]
    simp only [h2, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul, Finset.sum_ite_eq]
  let B : J → Matrix (J × I) I ℂ := fun k => Matrix.of fun p i'' => U p.1 k * if p.2 = i'' then 1 else 0
  have hchoi : g56_choi M = ∑ k, B k * G k * (B k)ᴴ := by
    ext ⟨o, i⟩ ⟨o', i'⟩
    simp only [g56_choi, Matrix.of_apply, hME, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [B, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul, mul_ite, Finset.sum_ite_eq,
      Finset.sum_ite_eq', apply_ite (starRingEnd ℂ)]
  apply g56_cp_of_choi
  rw [hchoi]
  exact g56_sum_psd _ _ fun k => (hG k).mul_mul_conjTranspose_same (B k)

theorem g56_pos_of_kraus {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Φ : Mat I →ₗ[ℂ] Mat J) {m : ℕ} (K : Fin m → Matrix J I ℂ)
    (hK : ∀ X, Φ X = ∑ l, K l * X * (K l)ᴴ) : Positive Φ := by
  intro A hA
  rw [hK]
  exact g56_sum_psd _ _ fun l => hA.mul_mul_conjTranspose_same (K l)

theorem g56_dual_transpose {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Φ : Mat I →ₗ[ℂ] Mat J) (B : Mat J) :
    hilbertSchmidtDual ((Matrix.transposeLinearEquiv J J ℂ ℂ).toLinearMap ∘ₗ Φ) B =
      hilbertSchmidtDual Φ Bᵀ := by
  ext i j
  simp only [hilbertSchmidtDual, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Matrix.transposeLinearEquiv_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem g56_bT_one {J : Type} [Fintype J] [DecidableEq J] (A : Mat J) :
    basisTranspose (1 : Matrix.unitaryGroup J ℂ) A = Aᵀ := by
  simp [basisTranspose]

theorem g56_cptp_schwarz {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Φ : Mat I →ₗ[ℂ] Mat J) (h : CPTP Φ) : Schwarz (hilbertSchmidtDual Φ) := by
  obtain ⟨m, K, hK⟩ := g55c_kraus_of_cp Φ h.1
  have hK1 := g55c_kraus_tp Φ K hK h.2
  intro A
  unfold Papers.Independent.Dependency50.P28.LE
  rw [g55c_dual_kraus Φ K hK, g55c_dual_kraus Φ K hK]
  exact g55c_schwarz_kraus K hK1 A

theorem solution (d : Divergence) :
    (SMON d → MON d) ∧ (EPPMON d → MON d) ∧
    (MON d → MMON d) ∧ (MMON d → PMON d) := by
  refine ⟨fun hS => ?_, fun hE => ?_, fun hM => ?_, fun hMM => ?_⟩
  · intro I J _ _ _ _ rho sigma hr hs Phi hPhi
    obtain ⟨m, K, hK⟩ := g55c_kraus_of_cp Phi hPhi.1
    refine hS I J rho sigma hr hs Phi (g56_pos_of_kraus Phi K hK) hPhi.2 ?_
    refine ⟨1, Phi, (Matrix.transposeLinearEquiv J J ℂ ℂ).toLinearMap ∘ₗ Phi, zero_le_one, le_rfl, hPhi.2,
      ?_, g56_cptp_schwarz Phi hPhi, ⟨1, ?_⟩, ?_⟩
    · intro A
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.transposeLinearEquiv_apply,
        Matrix.trace_transpose]
      exact hPhi.2 A
    · intro A
      have h := g56_cptp_schwarz Phi hPhi A
      simp only [g56_dual_transpose, g56_bT_one, Matrix.transpose_transpose]
      convert h using 3
    · intro A; simp
  · intro I J _ _ _ _ rho sigma hr hs Phi hPhi
    obtain ⟨m, K, hK⟩ := g55c_kraus_of_cp Phi hPhi.1
    exact hE I J rho sigma hr hs Phi hPhi.2 (fun n _ A hA => g55c_tensor_pos Phi K hK n A hA)
  · intro I _ _ rho sigma hr hs M
    exact hM I M.out rho sigma hr hs M.map ⟨g56_cp_of_comm M.map M.positive M.commuting, M.tracePreserving⟩
  · intro I _ _ rho sigma hr hs
    obtain ⟨U, hU1, h1, h2⟩ := g55c_main rho sigma hr.1.1 hs.1.1
    have := hMM I rho sigma hr hs (g55c_deph U hU1)
    change d I ((g55c_deph U hU1).map rho) ((g55c_deph U hU1).map sigma) ≤ d I rho sigma at this
    rw [h1, h2] at this
    exact this
