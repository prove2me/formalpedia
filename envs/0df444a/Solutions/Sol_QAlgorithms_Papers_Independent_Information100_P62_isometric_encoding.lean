-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.isometric_encoding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:43:11.29587+00:00
-- url     : https://prove2.me/submissions/64e64aea-c8d6-4f07-a6ca-983365e8e900
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_output_representation

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

private lemma finite_kraus_channel {I O L : Type} [Fintype I] [Fintype O] [Fintype L]
    [DecidableEq I] (E : L → Matrix O I ℂ) (hE : IsKrausFamily E) :
    IsChannel (krausApply E) := by
  classical
  let e := (Fintype.equivFin L).symm
  refine ⟨Fintype.card L, E ∘ e, ?_, ?_⟩
  · exact (e.sum_comp (fun j => (E j)ᴴ * E j)).trans hE
  · intro X
    exact (e.sum_comp (fun j => E j * X * (E j)ᴴ)).symm

private lemma channel_comp {I O J : Type} [Fintype I] [Fintype O] [Fintype J]
    [DecidableEq I] [DecidableEq O]
    (F : Superop I O) (G : Superop O J) (hF : IsChannel F) (hG : IsChannel G) :
    IsChannel (G ∘ F) := by
  classical
  obtain ⟨r,E,hE,hEq⟩ := hF
  obtain ⟨s,B,hB,hBq⟩ := hG
  let C (p : Fin s × Fin r) := B p.1 * E p.2
  have hC : IsKrausFamily C := by
    change (∑ p, (C p)ᴴ * C p) = 1
    simp only [C,Matrix.conjTranspose_mul,Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [Matrix.mul_assoc, ← Matrix.mul_sum]
    simp only [← Matrix.mul_assoc, ← Matrix.sum_mul]
    change (∑ i, (E i)ᴴ * (∑ j, (B j)ᴴ * B j) * E i) = 1
    rw [hB]
    simpa only [IsKrausFamily,Matrix.mul_one] using hE
  have heq : G ∘ F = krausApply C := by
    funext X
    simp only [Function.comp_apply,hEq,hBq,krausApply,C,Fintype.sum_prod_type,
      Matrix.mul_sum,Matrix.sum_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [heq]
  exact finite_kraus_channel C hC

private def blockAlgebra (A : Shape) : Submodule ℂ (Matrix (Logical A) (Logical A) ℂ) where
  carrier := {X | ∀ i j, i.1 ≠ j.1 → X i j = 0}
  zero_mem' := by simp
  add_mem' := by intro X Y hX hY i j hij; simp [hX i j hij,hY i j hij]
  smul_mem' := by intro c X hX i j hij; simp [hX i j hij]

private lemma block_one (A : Shape) : (1 : Matrix (Logical A) (Logical A) ℂ) ∈ blockAlgebra A := by
  intro i j hij
  simp [show i ≠ j from fun h => hij (congrArg Sigma.fst h)]

private lemma block_single (A : Shape) (i j : Logical A) (hij : i.1 = j.1) :
    Matrix.single i j (1 : ℂ) ∈ blockAlgebra A := by
  intro a b hab
  simp only [Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h
    exact (hab hij).elim
  · rfl

private lemma block_mul (A : Shape) {X Y : Matrix (Logical A) (Logical A) ℂ}
    (hX : X ∈ blockAlgebra A) (hY : Y ∈ blockAlgebra A) : X * Y ∈ blockAlgebra A := by
  intro i j hij
  change (∑ a, X i a * Y a j) = 0
  apply Finset.sum_eq_zero
  intro a ha
  by_cases h : i.1 = a.1
  · rw [hY a j (fun hh => hij (h.trans hh)),mul_zero]
  · rw [hX i a h,zero_mul]

private lemma block_star (A : Shape) {X : Matrix (Logical A) (Logical A) ℂ}
    (hX : X ∈ blockAlgebra A) : Xᴴ ∈ blockAlgebra A := by
  intro i j hij
  simp [Matrix.conjTranspose_apply,hX j i (Ne.symm hij)]

private lemma channel_trace {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (F : Superop I O) (hF : IsChannel F) (X : Matrix I I ℂ) : (F X).trace = X.trace := by
  obtain ⟨r,E,hE,hEq⟩ := hF
  rw [hEq,krausApply,Matrix.trace_sum]
  have hc (i : Fin r) : (E i * X * (E i)ᴴ).trace = (X * ((E i)ᴴ * E i)).trace := by
    rw [Matrix.trace_mul_cycle,Matrix.trace_mul_comm]
  simp_rw [hc]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, hE, Matrix.mul_one]

private lemma channel_retraction (A : Shape) (H : Superop (Logical A) (Logical A))
    (hH : IsChannel H)
    (hfix : ∀ X ∈ blockAlgebra A, H X = X)
    (hrange : ∀ X, H X ∈ blockAlgebra A) : H = pinching A := by
  classical
  obtain ⟨r,E,hE,hEq⟩ := hH
  have hentry (i j a b : Logical A) (hij : i.1 = j.1) :
      (Matrix.single i j (1 : ℂ)) a b = ∑ t, E t a i * conj (E t b j) := by
    have h := congrFun (congrFun ((hfix _ (block_single A i j hij)).symm.trans
      (hEq _)) a) b
    simpa [krausApply,Matrix.sum_apply,Matrix.mul_apply,Matrix.single_apply,
      Matrix.conjTranspose_apply,ite_and] using h
  have hoff (t : Fin r) (a i : Logical A) (hai : a ≠ i) : E t a i = 0 := by
    have hz : ∑ t, Complex.normSq (E t a i) = 0 := by
      have h := congrArg Complex.re (hentry i i a a rfl)
      simpa [hai,Ne.symm hai,Matrix.single_apply,Complex.mul_conj,Complex.normSq_apply] using h.symm
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun t _ => Complex.normSq_nonneg (E t a i))).mp hz t (mem_univ _)
    exact Complex.normSq_eq_zero.mp ht
  have hdiag (t : Fin r) : E t = Matrix.diagonal (fun i => E t i i) := by
    ext i j
    by_cases h : i = j
    · subst j; simp
    · simpa [Matrix.diagonal_apply_ne _ h] using hoff t i j h
  funext X
  ext i j
  by_cases hij : i.1 = j.1
  · have hc : ∑ t, E t i i * conj (E t j j) = 1 := by
      simpa [Matrix.single_apply] using (hentry i j i j hij).symm
    rw [hEq]
    have hent (t : Fin r) : (E t * X * (E t)ᴴ) i j = E t i i * X i j * conj (E t j j) := by
      conv_lhs => rw [hdiag t]
      simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul,Matrix.mul_diagonal]
      rfl
    simp only [krausApply,Matrix.sum_apply,hent,pinching,if_pos hij]
    calc
      (∑ t, E t i i * X i j * conj (E t j j)) =
          X i j * ∑ t, E t i i * conj (E t j j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = X i j := by rw [hc,mul_one]
  · rw [hrange X i j hij]
    simp [pinching,hij]

private lemma decoder_from_representation {O : Type} [Fintype O] [DecidableEq O]
    (A : Shape) (hA : Valid A) [Nonempty (Logical A)]
    (H : Superop (Logical A) O) (hH : IsChannel H)
    (f : Matrix (Logical A) (Logical A) ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hmul : ∀ X ∈ blockAlgebra A, ∀ Y ∈ blockAlgebra A, f (X * Y) = f X * f Y)
    (hstar : ∀ X ∈ blockAlgebra A, f Xᴴ = (f X)ᴴ)
    (hrep : ∀ X ∈ blockAlgebra A, H X = H 1 * f X ∧ H X = f X * H 1) :
    ∃ D : Superop O (Logical A), IsChannel D ∧ D ∘ H = pinching A := by
  classical
  let U (i j : Logical A) : Matrix (Logical A) (Logical A) ℂ :=
    if i.1 = j.1 then Matrix.single i j 1 else 0
  have hU (i j : Logical A) : U i j ∈ blockAlgebra A := by
    dsimp [U]; split_ifs with h
    · exact block_single A i j h
    · exact Submodule.zero_mem _
  have hUs (i j : Logical A) : (U i j)ᴴ = U j i := by
    dsimp only [U]
    by_cases h : i.1 = j.1 <;> simp [h,eq_comm]
  have hUm (i j k l : Logical A) : U i j * U k l =
      if j = k ∧ i.1 = j.1 ∧ k.1 = l.1 then U i l else 0 := by
    by_cases hjk : j = k
    · subst k
      by_cases hij : i.1 = j.1 <;> by_cases hjl : j.1 = l.1
      · simp [U,hij,hjl,Matrix.single_mul_single_same]
      · simp [U,hij,hjl]
      · have hil : i.1 ≠ l.1 := fun hh => hij (hh.trans hjl.symm)
        simp [U,hjl,hil]
      · simp [U,hij,hjl]
    · by_cases hij : i.1 = j.1 <;> by_cases hkl : k.1 = l.1 <;>
        simp [U,hjk,hij,hkl,Matrix.single_mul_single_of_ne (1 : ℂ) i j k hjk (1 : ℂ)]
  let R (i j : Logical A) := f (U i j)
  have hRs (i j : Logical A) : (R i j)ᴴ = R j i := by
    dsimp [R]; rw [← hstar _ (hU i j),hUs]
  have hRm (i j k l : Logical A) : R i j * R k l =
      if j = k ∧ i.1 = j.1 ∧ k.1 = l.1 then R i l else 0 := by
    rw [← hmul _ (hU i j) _ (hU k l),hUm]
    split_ifs <;> simp [R]
  let b (k : Block A) : Logical A := ⟨k,0, hA.2 _ (by
    unfold blockSize
    exact Multiset.mem_toList.mp (List.get_mem A.toList k))⟩
  let W (k : Block A) (a : O) : Matrix (Logical A) O ℂ := fun i o => R (b k) i a o
  have hWW (k : Block A) :
      ∑ a, (W k a)ᴴ * W k a = ∑ i : Logical A, R i (b k) * R (b k) i := by
    ext o p
    simp only [Matrix.sum_apply]
    change (∑ a : O, ∑ i : Logical A, conj (R (b k) i a o) * R (b k) i a p) =
      ∑ i : Logical A, ∑ a : O, R i (b k) o a * R (b k) i a p
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    have hh := congrFun (congrFun (hRs (b k) i) o) a
    change conj (R (b k) i a o) = R i (b k) o a at hh
    rw [hh]
  have hnormal : ∑ k, ∑ a, (W k a)ᴴ * W k a = f 1 := by
    simp_rw [hWW,hRm]
    rw [Finset.sum_comm]
    have hu : (∑ i : Logical A, U i i) = 1 := by
      simp only [U,ite_true]
      ext a c
      simp [Matrix.sum_apply,Matrix.single_apply,Matrix.one_apply,ite_and]
    rw [← hu,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i.1]
    · simp [b,R]
    · intro k _ hk
      simp [b,hk,Ne.symm hk]
    · simp
  let P := f 1
  have hPs : Pᴴ = P := by simpa [P] using (hstar 1 (block_one A)).symm
  have hPP : P * P = P := by rw [← hmul 1 (block_one A) 1 (block_one A),Matrix.one_mul]
  let Q := 1 - P
  have hQs : Qᴴ = Q := by simp [Q,hPs]
  have hQQ : Q * Q = Q := by
    dsimp [Q]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,hPP,sub_self,sub_zero]
  let i₀ : Logical A := Classical.choice inferInstance
  let Z (a : O) : Matrix (Logical A) O ℂ := fun i o => if i = i₀ then Q a o else 0
  have hZZ : ∑ a, (Z a)ᴴ * Z a = Q := by
    have heq : ∑ a, (Z a)ᴴ * Z a = Qᴴ * Q := by
      ext o p
      simp only [Matrix.sum_apply]
      change (∑ a : O, ∑ i : Logical A,
        conj (if i = i₀ then Q a o else 0) * (if i = i₀ then Q a p else 0)) = _
      simp [Matrix.mul_apply,Matrix.conjTranspose_apply]
    rw [heq,hQs,hQQ]
  let K : (Block A × O) ⊕ O → Matrix (Logical A) O ℂ :=
    Sum.elim (fun p => W p.1 p.2) Z
  have hK : IsKrausFamily K := by
    change (∑ a, (K a)ᴴ * K a) = 1
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
    change (∑ k, ∑ a, (W k a)ᴴ * W k a) + (∑ a, (Z a)ᴴ * Z a) = 1
    rw [hnormal,hZZ]
    simp [P,Q]
  let D := krausApply K
  have hD : IsChannel D := finite_kraus_channel K hK
  have hWform (Y : Matrix O O ℂ) (i j : Logical A) :
      (∑ k : Block A, ∑ a : O, W k a * Y * (W k a)ᴴ) i j =
        if i.1 = j.1 then (Y * R j i).trace else 0 := by
    have heq (k : Block A) :
        (∑ a : O, W k a * Y * (W k a)ᴴ) i j =
          (R (b k) i * Y * R j (b k)).trace := by
      simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.trace,Matrix.diag_apply,W]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro o _
      have hh := congrFun (congrFun (hRs (b k) j) o) a
      change conj (R (b k) j a o) = R j (b k) o a at hh
      change ((∑ p, R (b k) i a p * Y p o) * conj (R (b k) j a o)) = _
      rw [hh]
    have hprod : (∑ k : Block A, R j (b k) * R (b k) i) =
        if i.1 = j.1 then R j i else 0 := by
      simp_rw [hRm]
      rw [Finset.sum_eq_single j.1]
      · simp [b,eq_comm]
      · intro k _ hk
        simp [b,Ne.symm hk]
      · simp
    have hc (k : Block A) : (R (b k) i * Y * R j (b k)).trace =
        (Y * (R j (b k) * R (b k) i)).trace := by
      rw [Matrix.trace_mul_cycle,Matrix.trace_mul_comm]
    rw [Matrix.sum_apply]
    simp_rw [heq,hc]
    rw [← Matrix.trace_sum,← Matrix.mul_sum,hprod]
    split_ifs <;> simp
  have hZform (Y : Matrix O O ℂ) (i j : Logical A) :
      (∑ a, Z a * Y * (Z a)ᴴ) i j =
        if i = i₀ ∧ j = i₀ then (Q * Y * Q).trace else 0 := by
    simp only [Matrix.sum_apply]
    change (∑ a : O, ∑ p : O, (∑ o : O,
      (if i = i₀ then Q a o else 0) * Y o p) * conj (if j = i₀ then Q a p else 0)) = _
    have hs (a p : O) : conj (Q a p) = Q p a := by
      exact congrFun (congrFun hQs p) a
    by_cases hi : i = i₀ <;> by_cases hj : j = i₀ <;>
      simp [hi,hj,hs,Matrix.trace,Matrix.mul_apply,Matrix.diag_apply]
  have hDform (Y : Matrix O O ℂ) (i j : Logical A) :
      D Y i j = (if i.1 = j.1 then (Y * R j i).trace else 0) +
        (if i = i₀ ∧ j = i₀ then (Q * Y * Q).trace else 0) := by
    change (∑ a, K a * Y * (K a)ᴴ) i j = _
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
    change ((∑ k, ∑ a, W k a * Y * (W k a)ᴴ) + (∑ a, Z a * Y * (Z a)ᴴ)) i j = _
    rw [Matrix.add_apply,hWform,hZform]
  have hfix (X : Matrix (Logical A) (Logical A) ℂ) (hX : X ∈ blockAlgebra A) : D (H X) = X := by
    have hQH : Q * H X = 0 := by
      rw [(hrep X hX).1]
      have hP1 := (hrep 1 (block_one A)).2
      change H 1 = P * H 1 at hP1
      have hh : Q * H 1 = 0 := by dsimp [Q]; rw [Matrix.sub_mul,Matrix.one_mul,← hP1,sub_self]
      rw [← Matrix.mul_assoc,hh,Matrix.zero_mul]
    ext i j
    rw [hDform,hQH,Matrix.zero_mul,Matrix.trace_zero]
    simp only [ite_self,add_zero]
    by_cases hij : i.1 = j.1
    · rw [if_pos hij]
      have hprod := (hrep (X * U j i) (block_mul A hX (hU j i))).1
      rw [hmul X hX _ (hU j i)] at hprod
      rw [← Matrix.mul_assoc,← (hrep X hX).1] at hprod
      rw [← hprod,channel_trace H hH]
      simp [U,hij,Matrix.trace_mul_single]
    · rw [if_neg hij,hX i j hij]
  have hrange (Y : Matrix O O ℂ) : D Y ∈ blockAlgebra A := by
    intro i j hij
    rw [hDform,if_neg hij]
    have hh : ¬ (i = i₀ ∧ j = i₀) := by rintro ⟨rfl,rfl⟩; exact hij rfl
    simp [hh]
  refine ⟨D,hD,channel_retraction A (D ∘ H) (channel_comp H D hH hD) hfix ?_⟩
  intro X
  exact hrange _

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

private lemma encoding_frame {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Transmits F A)
    :
    ∃ V : Matrix I (Logical A) ℂ, Vᴴ * V = 1 ∧
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
  exact ⟨V,hV,hcomp⟩

private def conjLinear {I L : Type} [Fintype L] (V : Matrix I L ℂ) :
    Matrix L L ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun := fun X => V * X * Vᴴ
  map_add' := by intro X Y; simp [Matrix.mul_add,Matrix.add_mul]
  map_smul' := by intro c X; simp [Matrix.mul_smul,Matrix.smul_mul]

private lemma conj_compress {I L : Type} [Fintype I] [Fintype L] [DecidableEq L]
    (V : Matrix I L ℂ) (hV : Vᴴ * V = 1) (X : Matrix L L ℂ) :
    Vᴴ * conjLinear V X * V = X := by
  change Vᴴ * (V * X * Vᴴ) * V = X
  calc
    _ = (Vᴴ * V) * X * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hV]; simp

private lemma conjugation_mul {I L : Type} [Fintype I] [Fintype L] [DecidableEq L]
    (V : Matrix I L ℂ) (hV : Vᴴ * V = 1) (X Y : Matrix L L ℂ) :
    conjLinear V (X * Y) = conjLinear V X * conjLinear V Y := by
  change V * (X * Y) * Vᴴ = (V * X * Vᴴ) * (V * Y * Vᴴ)
  calc
    _ = V * X * (Vᴴ * V) * Y * Vᴴ := by rw [hV]; simp [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

private lemma conj_star {I L : Type} [Fintype L] (V : Matrix I L ℂ) (X : Matrix L L ℂ) :
    conjLinear V Xᴴ = (conjLinear V X)ᴴ := by
  change V * Xᴴ * Vᴴ = (V * X * Vᴴ)ᴴ
  simp [Matrix.conjTranspose_mul,Matrix.mul_assoc]

private lemma isometry_channel {I L : Type} [Fintype I] [Fintype L] [DecidableEq L]
    (V : Matrix I L ℂ) (hV : Vᴴ * V = 1) : IsChannel (conjSuperop V) := by
  refine ⟨1,fun _ => V,?_,?_⟩
  · simpa [IsKrausFamily] using hV
  · intro X
    simp [conjSuperop,krausApply]

private lemma pinchingSystem_form (A : Shape) (X : Matrix (Logical A) (Logical A) ℂ)
    (hX : X ∈ pinchingSystem A) :
    ∃ z : Block A → ℂ, X = Matrix.diagonal (fun i => z i.1) := by
  change X ∈ Submodule.span ℂ _ at hX
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨z,rfl⟩ := hX; exact ⟨z,rfl⟩
  | zero => exact ⟨0,by simp⟩
  | add X Y hX hY iX iY =>
      obtain ⟨x,rfl⟩ := iX; obtain ⟨y,rfl⟩ := iY
      exact ⟨x+y,by simp [Matrix.diagonal_add]⟩
  | smul c X hX iX =>
      obtain ⟨x,rfl⟩ := iX
      refine ⟨c • x,?_⟩
      rw [← Matrix.diagonal_smul]
      rfl

private lemma block_comm (A : Shape) (Y : Matrix (Logical A) (Logical A) ℂ)
    (hY : Y ∈ blockAlgebra A) (Z : Matrix (Logical A) (Logical A) ℂ)
    (hZ : Z ∈ pinchingSystem A) : Y * Z = Z * Y := by
  obtain ⟨z,rfl⟩ := pinchingSystem_form A Z hZ
  ext i j
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases h : i.1 = j.1
  · rw [h]; ring
  · rw [hY i j h]; simp

private lemma isometry_transmits {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O]
    (F : Superop I O) (A : Shape) (hA : Valid A)
    (V : Matrix I (Logical A) ℂ) (hV : Vᴴ * V = 1)
    (hcomp : ∀ s ∈ graph F, Vᴴ * s * V ∈ pinchingSystem A) : Transmits F A := by
  let g : Algebra A →ₗ[ℂ] Matrix (Logical A) (Logical A) ℂ :=
    { toFun := Matrix.blockDiagonal'
      map_add' := Matrix.blockDiagonal'_add
      map_smul' := fun c X => Matrix.blockDiagonal'_smul c X }
  let f := (conjLinear V).comp g
  have hf : Faithful f := by
    refine ⟨?_,?_,?_⟩
    · intro X Y h
      apply Matrix.blockDiagonal'_injective
      exact (conj_compress V hV (g X)).symm.trans
        ((congrArg (fun M => Vᴴ * M * V) h).trans (conj_compress V hV (g Y)))
    · intro X Y
      change conjLinear V (Matrix.blockDiagonal' (fun k => X k * Y k)) = _
      rw [Matrix.blockDiagonal'_mul,conjugation_mul V hV]
      rfl
    · intro X
      change conjLinear V (Matrix.blockDiagonal' (fun k => (X k)ᴴ)) = _
      rw [← Matrix.blockDiagonal'_conjTranspose,conj_star]
      rfl
  refine ⟨hA,f,hf,?_⟩
  intro X s hs
  have hg : g X ∈ blockAlgebra A := by
    intro i j hij
    exact dif_neg hij
  have hc := block_comm A (g X) hg _ (hcomp s hs)
  have hu : g 1 = 1 := by exact Matrix.blockDiagonal'_one
  change (V * g X * Vᴴ) * ((V * g 1 * Vᴴ) * s * (V * g 1 * Vᴴ)) =
    ((V * g 1 * Vᴴ) * s * (V * g 1 * Vᴴ)) * (V * g X * Vᴴ)
  rw [hu]
  simp only [Matrix.mul_one]
  calc
    _ = V * (g X * (Vᴴ * s * V)) * Vᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V,hV,Matrix.one_mul]
    _ = V * ((Vᴴ * s * V) * g X) * Vᴴ := by rw [hc]
    _ = _ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V,hV,Matrix.one_mul]

private lemma recovery_from_output {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A)
    [Nonempty (Logical A)] (V : Matrix I (Logical A) ℂ) (hV : Vᴴ * V = 1)
    (hcomp : ∀ s ∈ graph F, Vᴴ * s * V ∈ pinchingSystem A) :
    ∃ D : Superop O (Logical A), IsChannel D ∧ D ∘ F ∘ conjSuperop V = pinching A := by
  let c := conjLinear V
  let B := (blockAlgebra A).map c
  let P := c 1
  have hinj : Function.Injective c := by
    intro X Y h
    exact (conj_compress V hV X).symm.trans
      ((congrArg (fun M => Vᴴ * M * V) h).trans (conj_compress V hV Y))
  have hmem (X : Matrix (Logical A) (Logical A) ℂ) (hX : X ∈ blockAlgebra A) : c X ∈ B :=
    ⟨X,hX,rfl⟩
  have hcorner : IsCornerAlgebra B P := by
    refine ⟨hmem 1 (block_one A),?_,⟨?_,?_⟩,?_,?_,?_⟩
    · intro hz
      have he : (1 : Matrix (Logical A) (Logical A) ℂ) = 0 := hinj (hz.trans (map_zero c).symm)
      exact one_ne_zero he
    · exact (conj_star V 1).symm.trans (by simp [P,c])
    · rw [← conjugation_mul V hV]
      simp [P,c]
    · rintro Y ⟨X,hX,rfl⟩
      rw [← conj_star]
      exact hmem _ (block_star A hX)
    · rintro Y ⟨X,hX,rfl⟩ Z ⟨W,hW,rfl⟩
      rw [← conjugation_mul V hV]
      exact hmem _ (block_mul A hX hW)
    · rintro Y ⟨X,hX,rfl⟩
      constructor <;> rw [← conjugation_mul V hV] <;> simp [c]
  have hcorrect : Correctable F B P := by
    rintro Y ⟨X,hX,rfl⟩ s hs
    have hc := block_comm A X hX _ (hcomp s hs)
    change (V * X * Vᴴ) * ((V * (1 : Matrix (Logical A) (Logical A) ℂ) * Vᴴ) * s * (V * (1 : Matrix (Logical A) (Logical A) ℂ) * Vᴴ)) =
      ((V * (1 : Matrix (Logical A) (Logical A) ℂ) * Vᴴ) * s * (V * (1 : Matrix (Logical A) (Logical A) ℂ) * Vᴴ)) * (V * X * Vᴴ)
    simp only [Matrix.mul_one]
    calc
      _ = V * (X * (Vᴴ * s * V)) * Vᴴ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Vᴴ V,hV,Matrix.one_mul]
      _ = V * ((Vᴴ * s * V) * X) * Vᴴ := by rw [hc]
      _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Vᴴ V,hV,Matrix.one_mul]
  obtain ⟨f,hf,hrep⟩ := (output_representation F hF B P hcorner).1.mp hcorrect
  let fL := f.comp c
  let H := F ∘ conjSuperop V
  have hH : IsChannel H := channel_comp _ _ (isometry_channel V hV) hF
  have hmul : ∀ X ∈ blockAlgebra A, ∀ Y ∈ blockAlgebra A, fL (X * Y) = fL X * fL Y := by
    intro X hX Y hY
    change f (c (X * Y)) = f (c X) * f (c Y)
    rw [conjugation_mul V hV]
    exact hf.2.1 _ (hmem X hX) _ (hmem Y hY)
  have hstar : ∀ X ∈ blockAlgebra A, fL Xᴴ = (fL X)ᴴ := by
    intro X hX
    change f (c Xᴴ) = (f (c X))ᴴ
    rw [conj_star]
    exact hf.2.2 _ (hmem X hX)
  have hrepL : ∀ X ∈ blockAlgebra A, H X = H 1 * fL X ∧ H X = fL X * H 1 := by
    intro X hX
    exact hrep _ (hmem X hX)
  obtain ⟨D,hD,hDH⟩ := decoder_from_representation A hA H hH fL hmul hstar hrepL
  exact ⟨D,hD,hDH⟩

theorem solution {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A) :
    Transmits F A ↔ ∃ V : Matrix I (Logical A) ℂ, Vᴴ * V = 1 ∧
      (∀ s ∈ graph F, Vᴴ * s * V ∈ pinchingSystem A) ∧
      ∃ D : Superop O (Logical A), IsChannel D ∧ D ∘ F ∘ conjSuperop V = pinching A := by
  classical
  have hnB : Nonempty (Block A) := by
    have hcard : 0 < A.toList.length := by
      rw [Multiset.length_toList]
      exact Multiset.card_pos.mpr hA.1
    exact ⟨⟨0,hcard⟩⟩
  let k : Block A := Classical.choice hnB
  have hd : 0 < blockSize A k := hA.2 _ (Multiset.mem_toList.mp (List.get_mem _ _))
  have : Nonempty (Logical A) := ⟨⟨k,⟨0,hd⟩⟩⟩
  constructor
  · intro ht
    obtain ⟨V,hV,hcomp⟩ := encoding_frame F hF A ht
    have hc : ∀ s ∈ graph F, Vᴴ * s * V ∈ pinchingSystem A := by
      intro s hs
      obtain ⟨z,hz⟩ := hcomp s hs
      rw [hz]
      exact Submodule.subset_span ⟨z,rfl⟩
    exact ⟨V,hV,hc,recovery_from_output F hF A hA V hV hc⟩
  · rintro ⟨V,hV,hcomp,_⟩
    exact isometry_transmits F A hA V hV hcomp

#print axioms solution
