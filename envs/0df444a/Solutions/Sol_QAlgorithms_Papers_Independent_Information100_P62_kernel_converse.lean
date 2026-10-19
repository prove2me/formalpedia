-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.kernel_converse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T08:41:33.974234+00:00
-- url     : https://prove2.me/submissions/be3d7c35-0eb1-4cb7-8bee-ad8186dd4fa7

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

private lemma projection_frame {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : IsProjection P) (d : ℕ) (hd : P.rank = d) :
    ∃ V : Matrix I (Fin d) ℂ, Vᴴ * V = 1 ∧ V * Vᴴ = P := by
  classical
  let C := imageSpace P
  have hdim : Module.finrank ℂ C = d := by
    rw [← hd, Matrix.rank_eq_finrank_range_toLin P
      (EuclideanSpace.basisFun I ℂ).toBasis (EuclideanSpace.basisFun I ℂ).toBasis]
    rfl
  let b : OrthonormalBasis (Fin d) ℂ C :=
    (stdOrthonormalBasis ℂ C).reindex (finCongr hdim)
  let V : Matrix I (Fin d) ℂ := fun i a => (b a : EuclideanSpace ℂ I) i
  have hV : Vᴴ * V = 1 := by
    ext a c
    have hh := orthonormal_iff_ite.mp b.orthonormal a c
    rw [← inner_matrix_col_col]
    change inner ℂ (b a : EuclideanSpace ℂ I) (b c : EuclideanSpace ℂ I) = _
    simpa only [Submodule.coe_inner, Matrix.one_apply] using hh
  have hfix (x : C) : Matrix.toEuclideanLin P x = x := by
    obtain ⟨y,hy⟩ := x.property
    rw [← hy]
    have hh := congrArg (fun M => Matrix.toEuclideanLin M y) hP.2
    simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using hh
  have hs : Matrix.toEuclideanLin P = C.starProjection.toLinearMap := by
    apply LinearMap.ext
    intro x
    symm
    apply (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (show Matrix.toEuclideanLin P x ∈ C from ⟨x,rfl⟩) ?_)
    intro y hy
    have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hP.1) x y
    have hfy := hfix ⟨y,hy⟩
    rw [inner_sub_left, hsym, hfy, sub_self]
  have hPV : V * Vᴴ = P := by
    calc
      V * Vᴴ = ∑ a, Matrix.vecMulVec (b a : EuclideanSpace ℂ I)
          (star (b a : EuclideanSpace ℂ I)) := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
          Matrix.vecMulVec_apply, Pi.star_apply]
        rfl
      _ = Matrix.toEuclideanLin.symm C.starProjection.toLinearMap := by
        rw [b.starProjection_eq_sum_rankOne]
        simp only [ContinuousLinearMap.toLinearMap_sum, map_sum,
          InnerProductSpace.symm_toEuclideanLin_rankOne]
      _ = P := by rw [← hs]; simp
  exact ⟨V,hV,hPV⟩

private lemma rank_image {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (M : Matrix O I ℂ) :
    M.rank = Module.finrank ℂ (imageSpace M) := by
  rw [Matrix.rank_eq_finrank_range_toLin M
    (EuclideanSpace.basisFun O ℂ).toBasis (EuclideanSpace.basisFun I ℂ).toBasis]
  rfl

private lemma kill_code {I : Type} [Fintype I] [DecidableEq I]
    (S : Submodule ℂ (Matrix I I ℂ)) (P X : Matrix I I ℂ)
    (hP : Code S P) (hX : X ∈ S) (hpos : X.PosSemidef)
    (hrank : X.rank < P.rank) : X * P = 0 := by
  classical
  obtain ⟨z,hz⟩ := hP.2 X hX
  have hz0 : z = 0 := by
    by_contra h
    have hr := (Matrix.rank_mul_le_left (P * X) P).trans
      (Matrix.rank_mul_le_right P X)
    rw [hz, Matrix.rank_smul_of_mem_nonZeroDivisors P (mem_nonZeroDivisors_of_ne_zero h)] at hr
    omega
  have hzero : P * X * P = 0 := by simpa only [hz0,zero_smul] using hz
  open scoped MatrixOrder in
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos.nonneg
  have hfact : X = Bᴴ * B := hB
  have hBP : B * P = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [hfact] at hzero
    simpa only [Matrix.conjTranspose_mul, hP.1.1, Matrix.mul_assoc] using hzero
  rw [hfact,Matrix.mul_assoc,hBP,Matrix.mul_zero]

private lemma projection_linear {I : Type} [Fintype I] [DecidableEq I]
    (C : Submodule ℂ (EuclideanSpace ℂ I)) :
    Matrix.toEuclideanLin (projection C) = C.starProjection.toLinearMap := by
  apply (EuclideanSpace.basisFun I ℂ).toBasis.ext
  intro i
  ext j
  simp [projection, Matrix.toLpLin_apply,
    EuclideanSpace.basisFun_apply, QAlgorithms.ket]

private lemma projection_image {I : Type} [Fintype I] [DecidableEq I]
    (C : Submodule ℂ (EuclideanSpace ℂ I)) : imageSpace (projection C) = C := by
  unfold imageSpace
  rw [projection_linear]
  exact C.range_starProjection

private lemma image_killed {L I O : Type} [Fintype L] [Fintype I] [Fintype O]
    [DecidableEq L] [DecidableEq I] [DecidableEq O] (P : Matrix I L ℂ) (X : Matrix O I ℂ)
    (h : X * P = 0) : imageSpace P ≤ kernelSpace X := by
  rintro x ⟨y,rfl⟩
  change Matrix.toEuclideanLin X (Matrix.toEuclideanLin P y) = 0
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, h, map_zero, LinearMap.zero_apply]

theorem solution {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    {r : ℕ} (E : Fin r → Matrix O I ℂ) (hE : IsKrausFamily E) :
    (∀ C : Submodule ℂ (EuclideanSpace ℂ I), 0 < Module.finrank ℂ C →
      Code (graph (krausApply E)) (projection C) →
      C ≤ ⨅ X : {X : Matrix I I ℂ // X ∈ graph (krausApply E) ∧ X.PosSemidef ∧ X.rank < Module.finrank ℂ C},
        kernelSpace X.val) ∧
    ∀ A : Shape, Transmits (krausApply E) A → ∀ t : ℕ, 1 ≤ t →
      (∑ k ∈ univ.filter (fun k => t ≤ blockSize A k), blockSize A k) ≤
        Module.finrank ℂ (⨅ X : {X : Matrix I I ℂ // X ∈ graph (krausApply E) ∧ X.PosSemidef ∧ X.rank < t},
          kernelSpace X.val : Submodule ℂ (EuclideanSpace ℂ I)) ∧
      Module.finrank ℂ (⨅ X : {X : Matrix I I ℂ // X ∈ graph (krausApply E) ∧ X.PosSemidef ∧ X.rank < t},
          kernelSpace X.val : Submodule ℂ (EuclideanSpace ℂ I)) ≤
        Module.finrank ℂ (⨅ i : {i : Fin r // (E i).rank < t},
          kernelSpace (E i.val) : Submodule ℂ (EuclideanSpace ℂ I)) := by
  classical
  constructor
  · intro C _hC hcode
    apply le_iInf
    intro X
    have hr : (projection C).rank = Module.finrank ℂ C := by
      rw [rank_image,projection_image]
    have hh := image_killed _ _ (kill_code _ _ _ hcode X.property.1 X.property.2.1
      (X.property.2.2.trans_eq hr.symm))
    exact (projection_image C).symm.le.trans hh
  · intro A hA t _ht
    let N : Submodule ℂ (EuclideanSpace ℂ I) :=
      ⨅ X : {X : Matrix I I ℂ // X ∈ graph (krausApply E) ∧ X.PosSemidef ∧ X.rank < t},
        kernelSpace X.val
    constructor
    · obtain ⟨P,hP,horth⟩ := (orthogonal_codes (krausApply E)
        ⟨r,E,hE,fun _ => rfl⟩ A hA.1).mp hA
      choose W hW hWP using fun k => projection_frame (P k) (hP k).1.1 _ (hP k).2
      have hPW (k : Block A) : P k * W k = W k := by
        rw [← hWP k,Matrix.mul_assoc,hW k,Matrix.mul_one]
      have hWP' (k : Block A) : (W k)ᴴ * P k = (W k)ᴴ := by
        rw [← hWP k,← Matrix.mul_assoc,hW k,Matrix.one_mul]
      have hone : (1 : Matrix I I ℂ) ∈ graph (krausApply E) := by
        rw [← hE]
        apply Submodule.sum_mem
        intro i _
        exact Submodule.subset_span ⟨r,E,hE,fun _ => rfl,i,i,rfl⟩
      have hcross (k j : Block A) (hkj : k ≠ j) : (W k)ᴴ * W j = 0 := by
        calc
          (W k)ᴴ * W j = ((W k)ᴴ * P k) * (P j * W j) := by rw [hWP',hPW]
          _ = (W k)ᴴ * (P k * 1 * P j) * W j := by simp only [Matrix.mul_one,Matrix.mul_assoc]
          _ = 0 := by rw [horth k j hkj 1 hone,Matrix.mul_zero,Matrix.zero_mul]
      let B := {k : Block A // t ≤ blockSize A k}
      let L := (k : B) × Fin (blockSize A k.val)
      let V : Matrix I L ℂ := fun i a => W a.1.val i a.2
      have hV : Vᴴ * V = 1 := by
        ext ⟨k,a⟩ ⟨j,b⟩
        change ((W k.val)ᴴ * W j.val) a b = (1 : Matrix L L ℂ) ⟨k,a⟩ ⟨j,b⟩
        by_cases hkj : k = j
        · subst j
          rw [hW]
          simp [Matrix.one_apply]
        · rw [hcross _ _ (fun h => hkj (Subtype.ext h))]
          simp [hkj]
      have hrange : imageSpace V ≤ N := by
        apply le_iInf
        intro X
        apply image_killed
        have hkill (k : B) : X.val * W k.val = 0 := by
          have hx : X.val * P k.val = 0 := kill_code _ _ _ (hP k.val).1
            X.property.1 X.property.2.1
            (X.property.2.2.trans_le (k.property.trans_eq (hP k.val).2.symm))
          calc
            X.val * W k.val = X.val * (P k.val * W k.val) := by rw [hPW]
            _ = (X.val * P k.val) * W k.val := (Matrix.mul_assoc _ _ _).symm
            _ = 0 := by rw [hx,Matrix.zero_mul]
        ext i a
        change (X.val * W a.1.val) i a.2 = 0
        rw [hkill]
        rfl
      have hdim : Fintype.card L ≤ Module.finrank ℂ N := by
        calc
          Fintype.card L = (Vᴴ * V).rank := by rw [hV,Matrix.rank_one]
          _ ≤ V.rank := Matrix.rank_mul_le_right _ _
          _ = Module.finrank ℂ (imageSpace V) := rank_image V
          _ ≤ Module.finrank ℂ N := Submodule.finrank_mono hrange
      have hcard : Fintype.card L =
          ∑ k ∈ univ.filter (fun k => t ≤ blockSize A k), blockSize A k := by
        simp only [L,Fintype.card_sigma,Fintype.card_fin]
        exact (Finset.sum_subtype _ (by simp) (blockSize A)).symm
      simpa only [hcard] using hdim
    · apply Submodule.finrank_mono
      change N ≤ _
      apply le_iInf
      intro i
      have hmem : (E i.val)ᴴ * E i.val ∈ graph (krausApply E) :=
        Submodule.subset_span ⟨r,E,hE,fun _ => rfl,i.val,i.val,rfl⟩
      let X : {X : Matrix I I ℂ // X ∈ graph (krausApply E) ∧ X.PosSemidef ∧ X.rank < t} :=
        ⟨(E i.val)ᴴ * E i.val,hmem,Matrix.posSemidef_conjTranspose_mul_self _,
          by simpa only [Matrix.rank_conjTranspose_mul_self] using i.property⟩
      have hNX : N ≤ kernelSpace X.val := iInf_le _ X
      apply hNX.trans
      intro x hx
      change Matrix.toEuclideanLin (E i.val) x = 0
      change Matrix.toEuclideanLin ((E i.val)ᴴ * E i.val) x = 0 at hx
      simpa only [Matrix.toLpLin_apply,WithLp.toLp_eq_zero,
        Matrix.conjTranspose_mul_self_mulVec_eq_zero] using hx
