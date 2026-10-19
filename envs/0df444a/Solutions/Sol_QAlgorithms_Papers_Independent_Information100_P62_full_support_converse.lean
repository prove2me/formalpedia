-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.full_support_converse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T08:32:12.386986+00:00
-- url     : https://prove2.me/submissions/83b8a073-bdf0-492e-8188-b4062a9e9d0d

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

private lemma graph_one {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (F : Superop I O) (hF : IsChannel F) : (1 : Matrix I I ℂ) ∈ graph F := by
  obtain ⟨r,E,hE,hEq⟩ := hF
  rw [← hE]
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.subset_span ⟨r,E,hE,hEq,a,a,rfl⟩

private lemma sum_blocks (A : Shape) : ∑ k : Block A, blockSize A k = lengthDim A := by
  unfold blockSize lengthDim
  rw [← List.sum_ofFn, List.ofFn_get, Multiset.sum_toList]

private lemma full_frame {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Transmits F A)
    (hfull : lengthDim A = Fintype.card I) :
    ∃ V : Matrix I (Logical A) ℂ, Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      ∀ s ∈ graph F, ∃ z : Block A → ℂ,
        Vᴴ * s * V = Matrix.diagonal (fun i : Logical A => z i.1) := by
  classical
  obtain ⟨P,hP,horth⟩ := (orthogonal_codes F hF A hA.1).mp hA
  choose W hW hWP using fun k => projection_frame (P k) (hP k).1.1 _ (hP k).2
  have hPW (k : Block A) : P k * W k = W k := by
    rw [← hWP k, Matrix.mul_assoc, hW k, Matrix.mul_one]
  have hWP' (k : Block A) : (W k)ᴴ * P k = (W k)ᴴ := by
    rw [← hWP k, ← Matrix.mul_assoc, hW k, Matrix.one_mul]
  have hcross (k j : Block A) (hkj : k ≠ j) (s : Matrix I I ℂ) (hs : s ∈ graph F) :
      (W k)ᴴ * s * W j = 0 := by
    calc
      (W k)ᴴ * s * W j = ((W k)ᴴ * P k) * s * (P j * W j) := by rw [hWP',hPW]
      _ = (W k)ᴴ * (P k * s * P j) * W j := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [horth k j hkj s hs, Matrix.mul_zero, Matrix.zero_mul]
  have hscalar (k : Block A) (s : Matrix I I ℂ) (hs : s ∈ graph F) :
      ∃ z : ℂ, (W k)ᴴ * s * W k = z • 1 := by
    obtain ⟨z,hz⟩ := (hP k).1.2 s hs
    refine ⟨z,?_⟩
    calc
      (W k)ᴴ * s * W k = ((W k)ᴴ * P k) * s * (P k * W k) := by rw [hWP',hPW]
      _ = (W k)ᴴ * (P k * s * P k) * W k := by simp only [Matrix.mul_assoc]
      _ = z • 1 := by rw [hz, Matrix.mul_smul, Matrix.smul_mul, hWP', hW]
  let V : Matrix I (Logical A) ℂ := fun i a => W a.1 i a.2
  have hentry (s : Matrix I I ℂ) (a b : Logical A) :
      (Vᴴ * s * V) a b = ((W a.1)ᴴ * s * W b.1) a.2 b.2 := rfl
  have hcomp (s : Matrix I I ℂ) (hs : s ∈ graph F) :
      ∃ z : Block A → ℂ, Vᴴ * s * V = Matrix.diagonal (fun i : Logical A => z i.1) := by
    choose z hz using fun k => hscalar k s hs
    refine ⟨z,?_⟩
    ext ⟨k,a⟩ ⟨j,b⟩
    rw [hentry]
    by_cases hkj : k = j
    · subst j
      rw [hz]
      simp [Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply]
    · rw [hcross k j hkj s hs]
      simp [Matrix.diagonal, hkj]
  have hV : Vᴴ * V = 1 := by
    ext ⟨k,a⟩ ⟨j,b⟩
    have hh := hentry 1 ⟨k,a⟩ ⟨j,b⟩
    simp only [Matrix.mul_one] at hh
    rw [hh]
    by_cases hkj : k = j
    · subst j
      rw [hW]
      simp [Matrix.one_apply]
    · have hh := hcross k j hkj 1 (graph_one F hF)
      simp only [Matrix.mul_one] at hh
      rw [hh]
      simp [hkj]
  have hcard : Fintype.card (Logical A) = Fintype.card I := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using (sum_blocks A).trans hfull
  exact ⟨V,hV,(Matrix.mul_eq_one_comm_of_card_eq (Logical A) I ℂ hcard).mp hV,hcomp⟩

private lemma rank_compress {I L : Type} [Fintype I] [Fintype L]
    [DecidableEq I] [DecidableEq L] (V : Matrix I L ℂ) (hVV : V * Vᴴ = 1)
    (X : Matrix I I ℂ) : (Vᴴ * X * V).rank = X.rank := by
  apply Nat.le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have h : V * (Vᴴ * X * V) * Vᴴ = X := by
      simp only [← Matrix.mul_assoc, hVV, Matrix.one_mul]
      rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
    calc
      X.rank = (V * (Vᴴ * X * V) * Vᴴ).rank := congrArg Matrix.rank h.symm
      _ ≤ (Vᴴ * X * V).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

private lemma kernel_diagonal {I L : Type} [Fintype I] [Fintype L]
    [DecidableEq I] [DecidableEq L] (V : Matrix I L ℂ)
    (_hV : Vᴴ * V = 1) (hVV : V * Vᴴ = 1)
    (hc : Fintype.card I = Fintype.card L) (X : Matrix I I ℂ) (z : L → ℂ)
    (hz : Vᴴ * X * V = Matrix.diagonal z) :
    Module.finrank ℂ (kernelSpace X) = Fintype.card {a : L // z a = 0} := by
  classical
  have hr : X.rank = Fintype.card {a : L // z a ≠ 0} := by
    rw [← rank_compress V hVV X, hz, Matrix.rank_diagonal]
  have hn := LinearMap.finrank_range_add_finrank_ker (Matrix.toEuclideanLin X)
  have hrange : Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin X)) = X.rank := by
    rw [Matrix.rank_eq_finrank_range_toLin X
      (EuclideanSpace.basisFun I ℂ).toBasis (EuclideanSpace.basisFun I ℂ).toBasis]
    rfl
  rw [hrange, hr, finrank_euclideanSpace, hc] at hn
  have hcount : Fintype.card {a : L // z a ≠ 0} + Fintype.card {a : L // z a = 0} = Fintype.card L := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa only [not_not, Finset.card_univ] using Finset.card_filter_add_card_filter_not (s := (univ : Finset L)) (fun a : L => z a ≠ 0)
  change Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin X)) = _
  omega

theorem solution {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Transmits F A)
    (hfull : lengthDim A = Fintype.card I) :
    (∀ X ∈ graph F, ∀ Y ∈ graph F, X * Y = Y * X) ∧
    ∀ X ∈ graph F, X.IsHermitian → ∃ lam : Block A → ℝ, ∀ t : ℝ,
      Module.finrank ℂ (kernelSpace (X - (t : ℂ) • (1 : Matrix I I ℂ))) =
        ∑ k ∈ univ.filter (fun k => lam k = t), blockSize A k := by
  classical
  obtain ⟨V,hV,hVV,hcomp⟩ := full_frame F hF A hA hfull
  have hrecover (X : Matrix I I ℂ) : V * (Vᴴ * X * V) * Vᴴ = X := by
    simp only [← Matrix.mul_assoc, hVV, Matrix.one_mul]
    rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
  constructor
  · intro X hX Y hY
    obtain ⟨z,hz⟩ := hcomp X hX
    obtain ⟨w,hw⟩ := hcomp Y hY
    have hc : (Vᴴ * X * V) * (Vᴴ * Y * V) = (Vᴴ * Y * V) * (Vᴴ * X * V) := by
      rw [hz,hw,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have hmul (B C : Matrix I I ℂ) :
        (Vᴴ * B * V) * (Vᴴ * C * V) = Vᴴ * (B * C) * V := by
      calc
        (Vᴴ * B * V) * (Vᴴ * C * V) = Vᴴ * B * (V * Vᴴ) * C * V := by
          simp only [Matrix.mul_assoc]
        _ = Vᴴ * (B * C) * V := by rw [hVV]; simp only [Matrix.mul_one,Matrix.mul_assoc]
    rw [hmul,hmul] at hc
    calc
      X * Y = V * (Vᴴ * (X * Y) * V) * Vᴴ := (hrecover _).symm
      _ = V * (Vᴴ * (Y * X) * V) * Vᴴ := by rw [hc]
      _ = Y * X := hrecover _
  · intro X hX hherm
    obtain ⟨z,hz⟩ := hcomp X hX
    have hzreal (k : Block A) : conj (z k) = z k := by
      let a : Fin (blockSize A k) := ⟨0,hA.1.2 _ (Multiset.mem_toList.mp (List.get_mem _ _))⟩
      have hd : (Matrix.diagonal (fun i : Logical A => z i.1)).IsHermitian := by
        rw [← hz]
        exact Matrix.isHermitian_conjTranspose_mul_mul V hherm
      have hh := congrFun (congrFun hd ⟨k,a⟩) ⟨k,a⟩
      simpa [Matrix.conjTranspose_apply] using hh
    refine ⟨fun k => (z k).re,?_⟩
    intro t
    have hcard : Fintype.card I = Fintype.card (Logical A) := by
      rw [Fintype.card_sigma]
      simpa only [Fintype.card_fin] using ((sum_blocks A).trans hfull).symm
    have hshift : Vᴴ * (X - (t : ℂ) • 1) * V =
        Matrix.diagonal (fun i : Logical A => z i.1 - (t : ℂ)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hz, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hV]
      rw [Matrix.smul_one_eq_diagonal,Matrix.diagonal_sub]
    rw [kernel_diagonal V hV hVV hcard _ _ hshift]
    have hzre (k : Block A) : ((z k).re : ℂ) = z k := Complex.conj_eq_iff_re.mp (hzreal k)
    rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
    change (∑ i : Logical A, if z i.1 - (t : ℂ) = 0 then 1 else 0) = _
    rw [Fintype.sum_sigma, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    have he : z k - (t : ℂ) = 0 ↔ (z k).re = t := by
      rw [sub_eq_zero]
      constructor
      · intro h
        simpa only [Complex.ofReal_re] using congrArg Complex.re h
      · intro h
        rw [← hzre k, h]
    simp only [he, Finset.sum_ite_irrel, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, mul_zero]
