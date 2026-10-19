-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.orthogonal_codes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T08:20:55.455523+00:00
-- url     : https://prove2.me/submissions/5f17750d-6380-4962-8910-345fc03488c8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

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

private lemma frame_projection {I D : Type} [Fintype I] [Fintype D]
    [DecidableEq I] [DecidableEq D] (V : Matrix I D ℂ) (hV : Vᴴ * V = 1) :
    IsProjection (V * Vᴴ) ∧ (V * Vᴴ).rank = Fintype.card D := by
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  · rw [Matrix.rank_self_mul_conjTranspose,
      ← Matrix.rank_conjTranspose_mul_self V, hV, Matrix.rank_one]

private lemma graph_one {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (F : Superop I O) (hF : IsChannel F) : (1 : Matrix I I ℂ) ∈ graph F := by
  obtain ⟨r,E,hE,hEq⟩ := hF
  rw [← hE]
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.subset_span ⟨r,E,hE,hEq,a,a,rfl⟩

private lemma codes_transmit {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A)
    (P : Block A → Matrix I I ℂ)
    (hP : ∀ k, Code (graph F) (P k) ∧ (P k).rank = blockSize A k)
    (horth : ∀ k j, k ≠ j → ∀ s ∈ graph F, P k * s * P j = 0) :
    Transmits F A := by
  classical
  have hf := fun k => projection_frame (P k) (hP k).1.1 _ (hP k).2
  choose V hV hVP using hf
  have hPV (k : Block A) : P k * V k = V k := by
    rw [← hVP k, Matrix.mul_assoc, hV k, Matrix.mul_one]
  have hVP' (k : Block A) : (V k)ᴴ * P k = (V k)ᴴ := by
    rw [← hVP k, ← Matrix.mul_assoc, hV k, Matrix.one_mul]
  have hcross (k j : Block A) (hkj : k ≠ j) : (V k)ᴴ * V j = 0 := by
    calc
      (V k)ᴴ * V j = ((V k)ᴴ * P k) * (P j * V j) := by rw [hVP', hPV]
      _ = (V k)ᴴ * (P k * 1 * P j) * V j := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [horth k j hkj 1 (graph_one F hF), Matrix.mul_zero, Matrix.zero_mul]
  let g (X : Algebra A) : Matrix I I ℂ := ∑ k, V k * X k * (V k)ᴴ
  have hright (X : Algebra A) (k : Block A) : g X * V k = V k * X k := by
    dsimp [g]
    rw [Matrix.sum_mul, Finset.sum_eq_single k]
    · simp only [Matrix.mul_assoc, hV k, Matrix.mul_one]
    · intro j _ hj
      rw [Matrix.mul_assoc, hcross j k hj, Matrix.mul_zero]
    · simp
  have hleft (X : Algebra A) (k : Block A) : (V k)ᴴ * g X = X k * (V k)ᴴ := by
    dsimp [g]
    rw [Matrix.mul_sum, Finset.sum_eq_single k]
    · simp only [← Matrix.mul_assoc, hV k, Matrix.one_mul]
    · intro j _ hj
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcross k j (Ne.symm hj), Matrix.zero_mul,
        Matrix.zero_mul]
    · simp
  let f : Algebra A →ₗ[ℂ] Matrix I I ℂ :=
    { toFun := g
      map_add' := by intro X Y; simp [g, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c X; simp [g, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum] }
  have hf : Faithful f := by
    refine ⟨?_, ?_, ?_⟩
    · intro X Y h
      funext k
      have hh := congrArg (fun M => (V k)ᴴ * M * V k) h
      change (V k)ᴴ * g X * V k = (V k)ᴴ * g Y * V k at hh
      simpa only [hleft, Matrix.mul_assoc, hV k, Matrix.mul_one] using hh
    · intro X Y
      change g (X * Y) = g X * g Y
      calc
        g (X * Y) = ∑ k, (g X * V k) * Y k * (V k)ᴴ := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hright]
          simp only [Pi.mul_apply, Matrix.mul_assoc]
        _ = g X * g Y := by simp only [g, Matrix.mul_sum, Matrix.mul_assoc]
    · intro X
      change g (star X) = (g X)ᴴ
      simp only [g, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Pi.star_apply, Matrix.star_eq_conjTranspose,
        Matrix.mul_assoc]
  refine ⟨hA,f,hf,?_⟩
  intro X s hs
  have hunit : f 1 = ∑ k, P k := by
    change (∑ k, V k * (1 : Algebra A) k * (V k)ᴴ) = _
    simp only [Pi.one_apply, Matrix.mul_one, hVP]
  have hdiag : f 1 * s * f 1 = ∑ k, P k * s * P k := by
    rw [hunit, Matrix.sum_mul]
    simp only [Matrix.sum_mul, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_eq_single k
    · intro j _ hj
      exact horth j k hj s hs
    · simp
  have hcomm (k : Block A) : f X * P k = P k * f X := by
    change g X * P k = P k * g X
    rw [← hVP k, ← Matrix.mul_assoc, hright, Matrix.mul_assoc,
      Matrix.mul_assoc, hleft]
  rw [hdiag, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨z,hz⟩ := (hP k).1.2 s hs
  rw [hz, Matrix.mul_smul, Matrix.smul_mul, hcomm]

private def blockUnit (A : Shape) (k : Block A)
    (i j : Fin (blockSize A k)) : Algebra A := Pi.single k (Matrix.single i j (1 : ℂ))

private lemma blockUnit_mul (A : Shape) (k : Block A)
    (i j l : Fin (blockSize A k)) : blockUnit A k i j * blockUnit A k j l = blockUnit A k i l := by
  classical
  simp only [blockUnit, ← Pi.single_mul, Matrix.single_mul_single_same, mul_one]

private lemma blockUnit_mul_ne (A : Shape) (k : Block A)
    (i j l m : Fin (blockSize A k)) (hjl : j ≠ l) :
    blockUnit A k i j * blockUnit A k l m = 0 := by
  classical
  simp only [blockUnit, ← Pi.single_mul, Matrix.single_mul_single_of_ne (1 : ℂ) i j l hjl (1 : ℂ), Pi.single_zero]

private lemma blockUnit_cross (A : Shape) (k l : Block A) (hkl : k ≠ l)
    (i j : Fin (blockSize A k)) (a b : Fin (blockSize A l)) :
    blockUnit A k i j * blockUnit A l a b = 0 := by
  classical
  funext r
  by_cases hr : r = k
  · subst r
    simp [blockUnit, Pi.single_eq_of_ne hkl]
  · simp [blockUnit, Pi.single_eq_of_ne hr]

private lemma blockUnit_star (A : Shape) (k : Block A)
    (i j : Fin (blockSize A k)) : star (blockUnit A k i j) = blockUnit A k j i := by
  classical
  simp [blockUnit, Pi.star_single, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single]

private lemma projection_rank_pos {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : P ≠ 0) : 0 < P.rank := by
  by_contra! hz
  have hh : LinearMap.range P.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hz)
  have hlin : P.mulVecLin = 0 := LinearMap.range_eq_bot.mp hh
  exact hP (Matrix.toLin'.injective (by
    simpa only [Matrix.toLin'_apply', Matrix.mulVecLin_zero] using hlin))

private lemma unit_column {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : IsProjection P) (hne : P ≠ 0) :
    ∃ B : Matrix I Unit ℂ, Bᴴ * B = 1 ∧ P * B = B := by
  classical
  obtain ⟨V,hV,hVV⟩ := projection_frame P hP P.rank rfl
  let a : Fin P.rank := ⟨0,projection_rank_pos P hne⟩
  let B : Matrix I Unit ℂ := V.submatrix id (fun _ => a)
  have hB : Bᴴ * B = 1 := by
    ext i j
    have hh := congrFun (congrFun hV a) a
    simpa [B,Matrix.mul_apply,Matrix.conjTranspose_apply] using hh
  refine ⟨B,hB,?_⟩
  have hh : P * V = V := by
    calc
      P * V = (V * Vᴴ) * V := congrArg (fun M : Matrix I I ℂ => M * V) hVV.symm
      _ = V := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  ext i j
  exact congrFun (congrFun hh i) a

private lemma representation_codes {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A)
    (f : Algebra A →ₗ[ℂ] Matrix I I ℂ) (hf : Faithful f)
    (hcorr : ∀ X, ∀ s ∈ graph F, f X * (f 1 * s * f 1) = (f 1 * s * f 1) * f X) :
    ∃ P : Block A → Matrix I I ℂ,
      (∀ k, Code (graph F) (P k) ∧ (P k).rank = blockSize A k) ∧
      ∀ k j, k ≠ j → ∀ s ∈ graph F, P k * s * P j = 0 := by
  classical
  let z (k : Block A) : Fin (blockSize A k) :=
    ⟨0,hA.2 _ (Multiset.mem_toList.mp (List.get_mem _ _))⟩
  let E (k : Block A) (i j : Fin (blockSize A k)) := f (blockUnit A k i j)
  have hmul (k : Block A) (i j l : Fin (blockSize A k)) :
      E k i j * E k j l = E k i l := by
    dsimp [E]
    rw [← hf.2.1, blockUnit_mul]
  have hmul0 (k : Block A) (i j l m : Fin (blockSize A k)) (hjl : j ≠ l) :
      E k i j * E k l m = 0 := by
    dsimp [E]
    rw [← hf.2.1, blockUnit_mul_ne A k i j l m hjl, map_zero]
  have hcross (k l : Block A) (hkl : k ≠ l)
      (i j : Fin (blockSize A k)) (a b : Fin (blockSize A l)) :
      E k i j * E l a b = 0 := by
    dsimp [E]
    rw [← hf.2.1, blockUnit_cross A k l hkl, map_zero]
  have hstar (k : Block A) (i j : Fin (blockSize A k)) : (E k i j)ᴴ = E k j i := by
    dsimp [E]
    rw [← Matrix.star_eq_conjTranspose, ← hf.2.2, blockUnit_star]
  have hne (k : Block A) : E k (z k) (z k) ≠ 0 := by
    intro hh
    have hu := hf.1 (hh.trans (map_zero f).symm)
    have hentry := congrFun (congrFun (congrFun hu k) (z k)) (z k)
    simp [blockUnit] at hentry
  have hproj (k : Block A) : IsProjection (E k (z k) (z k)) :=
    ⟨hstar k _ _,hmul k _ _ _⟩
  choose B hB hEB using fun k => unit_column (E k (z k) (z k)) (hproj k) (hne k)
  have hunitR (X : Algebra A) : f X * f 1 = f X := by rw [← hf.2.1, mul_one]
  have hunitL (X : Algebra A) : f 1 * f X = f X := by rw [← hf.2.1, one_mul]
  have hPB (k : Block A) : f 1 * B k = B k := by
    calc
      f 1 * B k = f 1 * (E k (z k) (z k) * B k) := by rw [hEB]
      _ = B k := by rw [← Matrix.mul_assoc, hunitL, hEB]
  have hmove (X : Algebra A) (s : Matrix I I ℂ) (hs : s ∈ graph F) :
      f X * s * f 1 = f 1 * s * f X := by
    calc
      f X * s * f 1 = f X * (f 1 * s * f 1) := by
        simp only [← Matrix.mul_assoc, hunitR]
      _ = (f 1 * s * f 1) * f X := hcorr X s hs
      _ = f 1 * s * f X := by rw [Matrix.mul_assoc, hunitL]
  have hslide (X Y : Algebra A) (s : Matrix I I ℂ) (hs : s ∈ graph F) :
      f X * s * f Y = (f X * f Y) * s * f 1 := by
    calc
      f X * s * f Y = f X * (f 1 * s * f Y) := by
        simp only [← Matrix.mul_assoc, hunitR]
      _ = f X * (f Y * s * f 1) := by rw [hmove Y s hs]
      _ = (f X * f Y) * s * f 1 := by simp only [Matrix.mul_assoc]
  let V (k : Block A) : Matrix I (Fin (blockSize A k)) ℂ :=
    fun i a => (E k a (z k) * B k) i ()
  have hcol (k : Block A) (a : Fin (blockSize A k)) :
      (V k).submatrix id (fun _ : Unit => a) = E k a (z k) * B k := by
    ext i u
    cases u
    rfl
  have hsand (k j : Block A) (a : Fin (blockSize A k)) (b : Fin (blockSize A j))
      (s : Matrix I I ℂ) (hs : s ∈ graph F) :
      ((V k).submatrix id (fun _ : Unit => a))ᴴ * s *
        (V j).submatrix id (fun _ : Unit => b) =
      (B k)ᴴ * (E k (z k) a * E j b (z j)) * s * B j := by
    rw [hcol, hcol, Matrix.conjTranspose_mul, hstar]
    calc
      ((B k)ᴴ * E k (z k) a) * s * (E j b (z j) * B j) =
          (B k)ᴴ * (E k (z k) a * s * E j b (z j)) * B j := by
        simp only [Matrix.mul_assoc]
      _ = (B k)ᴴ * ((E k (z k) a * E j b (z j)) * s * f 1) * B j := by
        rw [hslide _ _ s hs]
      _ = (B k)ᴴ * (E k (z k) a * E j b (z j)) * s * B j := by
        simp only [Matrix.mul_assoc, hPB]
  have hsdiag (k : Block A) (s : Matrix I I ℂ) (hs : s ∈ graph F) :
      (V k)ᴴ * s * V k = (((B k)ᴴ * s * B k) () ()) • 1 := by
    ext a b
    have hh := congrFun (congrFun (hsand k k a b s hs) ()) ()
    change ((V k)ᴴ * s * V k) a b = _ at hh
    by_cases hab : a = b
    · subst b
      rw [hmul] at hh
      have hbE : (B k)ᴴ * E k (z k) (z k) = (B k)ᴴ := by
        simpa only [Matrix.conjTranspose_mul, hstar] using congrArg Matrix.conjTranspose (hEB k)
      simpa only [hbE, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hh
    · rw [hmul0 k _ _ _ _ hab] at hh
      simpa only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, Matrix.smul_apply,
        Matrix.one_apply_ne hab, smul_eq_mul, mul_zero] using hh
  have hV (k : Block A) : (V k)ᴴ * V k = 1 := by
    have hh := hsdiag k 1 (graph_one F hF)
    simpa only [Matrix.mul_one, hB, Matrix.one_apply_eq, one_smul] using hh
  have hVs (k j : Block A) (hkj : k ≠ j) (s : Matrix I I ℂ) (hs : s ∈ graph F) :
      (V k)ᴴ * s * V j = 0 := by
    ext a b
    have hh := congrFun (congrFun (hsand k j a b s hs) ()) ()
    change ((V k)ᴴ * s * V j) a b = _ at hh
    simpa only [hcross k j hkj, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply] using hh
  refine ⟨fun k => V k * (V k)ᴴ, ?_, ?_⟩
  · intro k
    obtain ⟨hp,hr⟩ := frame_projection (V k) (hV k)
    refine ⟨⟨hp,?_⟩, by simpa using hr⟩
    intro s hs
    refine ⟨((B k)ᴴ * s * B k) () (), ?_⟩
    calc
      (V k * (V k)ᴴ) * s * (V k * (V k)ᴴ) = V k * ((V k)ᴴ * s * V k) * (V k)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hsdiag k s hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  · intro k j hkj s hs
    calc
      (V k * (V k)ᴴ) * s * (V j * (V j)ᴴ) = V k * ((V k)ᴴ * s * V j) * (V j)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hVs k j hkj s hs, Matrix.mul_zero, Matrix.zero_mul]

theorem solution {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    [Nonempty I] [Nonempty O] (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A) :
    Transmits F A ↔ ∃ P : Block A → Matrix I I ℂ,
      (∀ k, Code (graph F) (P k) ∧ (P k).rank = blockSize A k) ∧
      ∀ k j, k ≠ j → ∀ s ∈ graph F, P k * s * P j = 0 := by
  constructor
  · rintro ⟨_,f,hf,hcorr⟩
    exact representation_codes F hF A hA f hf hcorr
  · rintro ⟨P,hP,horth⟩
    exact codes_transmit F hF A hA P hP horth
