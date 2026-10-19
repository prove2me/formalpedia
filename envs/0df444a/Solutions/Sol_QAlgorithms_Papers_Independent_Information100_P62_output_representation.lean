-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.output_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:01:45.473453+00:00
-- url     : https://prove2.me/submissions/6aac4e99-9faf-48ea-b17f-2225700771d4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

private lemma spectral_inverse {O : Type} [Fintype O] [DecidableEq O]
    (D : Matrix O O ℂ) (hD : D.IsHermitian) :
    ∃ S : Matrix O O ℂ, Sᴴ = S ∧ Commute D S ∧ D * S * D = D ∧ S * D * S = S ∧
      ∀ B, Commute D B → Commute S B := by
  classical
  let C := Unitary.conjStarAlgAut ℂ (Matrix O O ℂ) hD.eigenvectorUnitary
  let d : O → ℂ := fun i => (hD.eigenvalues i : ℂ)
  let s : O → ℂ := fun i => (d i)⁻¹
  have heq : D = C (Matrix.diagonal d) := hD.spectral_theorem
  refine ⟨C (Matrix.diagonal s), ?_, ?_, ?_, ?_, ?_⟩
  · change star (C (Matrix.diagonal s)) = _
    rw [← map_star]
    congr 1
    ext i j
    by_cases h : i = j
    · subst j; simp [s,d]
    · simp [h, Ne.symm h]
  · rw [heq]
    change C (Matrix.diagonal d) * C (Matrix.diagonal s) =
      C (Matrix.diagonal s) * C (Matrix.diagonal d)
    rw [← map_mul, ← map_mul]
    congr 1
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · rw [heq, ← map_mul, ← map_mul]
    congr 1
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : d i = 0 <;> simp [s,h]
  · rw [heq, ← map_mul, ← map_mul]
    congr 1
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : d i = 0 <;> simp [s,h]

  · intro B hB
    have hs' : C (Matrix.diagonal s) = hD.cfc (fun t : ℝ => t⁻¹) := by
      change C (Matrix.diagonal s) = C (Matrix.diagonal (fun i => (((hD.eigenvalues i)⁻¹ : ℝ) : ℂ)))
      congr 1
      congr 1
      funext i
      exact (Complex.ofReal_inv (hD.eigenvalues i)).symm
    rw [hs',← hD.cfc_eq]
    exact hB.cfc_real (fun t : ℝ => t⁻¹)

private lemma sum_gram_zero {I O L : Type} [Fintype I] [Fintype O] [Fintype L]
    (B : L → Matrix O I ℂ) (h : ∑ i, B i * (B i)ᴴ = 0) : ∀ i, B i = 0 := by
  classical
  intro i
  ext a b
  have hz : ∑ t, ∑ j, Complex.normSq (B t a j) = 0 := by
    have hh := congrArg (fun M : Matrix O O ℂ => (M a a).re) h
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.mul_conj] using hh
  have ht := (Finset.sum_eq_zero_iff_of_nonneg
    (fun t _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg (B t a j)))).mp hz i (mem_univ _)
  have hb := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg (B i a j))).mp ht b (mem_univ _)
  exact Complex.normSq_eq_zero.mp hb

private lemma projection_support {O : Type} [Fintype O] [DecidableEq O]
    (Q : Matrix O O ℂ) (hQ : IsProjection Q) : support Q = Q := by
  let C := imageSpace Q
  have hfix (x : C) : Matrix.toEuclideanLin Q x = x := by
    obtain ⟨y,hy⟩ := x.property
    rw [← hy]
    have hh := congrArg (fun M => Matrix.toEuclideanLin M y) hQ.2
    simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using hh
  have hs : Matrix.toEuclideanLin Q = C.starProjection.toLinearMap := by
    apply LinearMap.ext
    intro x
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (show Matrix.toEuclideanLin Q x ∈ C from ⟨x,rfl⟩)
    intro y hy
    have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ.1) x y
    rw [inner_sub_left, hsym, hfix ⟨y,hy⟩, sub_self]
  ext i j
  have hh := congrArg (fun f : EuclideanSpace ℂ O →ₗ[ℂ] EuclideanSpace ℂ O => f (ket j) i) hs
  simpa [support,projection,C,Matrix.toLpLin_apply,ket,Matrix.mulVec,
    dotProduct] using hh.symm

private lemma channel_trace {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (F : Superop I O) (hF : IsChannel F) (X : Matrix I I ℂ) : (F X).trace = X.trace := by
  obtain ⟨r,E,hE,hEq⟩ := hF
  rw [hEq,krausApply,Matrix.trace_sum]
  have hc (i : Fin r) : (E i * X * (E i)ᴴ).trace = (X * ((E i)ᴴ * E i)).trace := by
    rw [Matrix.trace_mul_cycle,Matrix.trace_mul_comm]
  simp_rw [hc]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, hE, Matrix.mul_one]

private def krausLinear {I O L : Type} [Fintype I] [Fintype O] [Fintype L]
    (E : L → Matrix O I ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun := krausApply E
  map_add' X Y := by simp [krausApply,Matrix.mul_add,Matrix.add_mul,Finset.sum_add_distrib]
  map_smul' c X := by simp [krausApply,Matrix.mul_smul,Matrix.smul_mul,Finset.smul_sum]

private lemma kraus_star {I O L : Type} [Fintype I] [Fintype O] [Fintype L]
    (E : L → Matrix O I ℂ) (X : Matrix I I ℂ) :
    krausApply E Xᴴ = (krausApply E X)ᴴ := by
  simp [krausApply,Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,Matrix.mul_assoc]

private lemma kraus_product {I O L : Type} [Fintype I] [Fintype O] [Fintype L]
    (E : L → Matrix O I ℂ) (X Y : Matrix I I ℂ)
    (hcomm : ∀ i j, X * ((E i)ᴴ * E j) = ((E i)ᴴ * E j) * X) :
    krausApply E X * krausApply E Y =
      (∑ i, E i * (E i)ᴴ) * krausApply E (X * Y) := by
  simp only [krausApply, Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  calc
    (E i * X * (E i)ᴴ) * (E j * Y * (E j)ᴴ) =
        E i * (X * ((E i)ᴴ * E j)) * Y * (E j)ᴴ := by simp [Matrix.mul_assoc]
    _ = E i * (((E i)ᴴ * E j) * X) * Y * (E j)ᴴ := by rw [hcomm]
    _ = (E i * (E i)ᴴ) * (E j * (X * Y) * (E j)ᴴ) := by simp [Matrix.mul_assoc]

private lemma gram_compression {I O L : Type} [Fintype I] [Fintype O] [Fintype L]
    (E : L → Matrix O I ℂ) (T : Matrix O O ℂ) :
    (∑ i, (T * E i) * (T * E i)ᴴ) = T * (∑ i, E i * (E i)ᴴ) * Tᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

private lemma gram_support {I O L : Type} [Fintype I] [Fintype O] [Fintype L]
    [DecidableEq O] (E : L → Matrix O I ℂ) (D S : Matrix O O ℂ)
    (hD : D = ∑ i, E i * (E i)ᴴ) (hherm : Dᴴ = D) (hS : Sᴴ = S)
    (hcomm : Commute D S) (hDSD : D * S * D = D) (hSDS : S * D * S = S) :
    (∀ i, (S * D) * E i = E i) ∧ S * D = support D := by
  let Q := S * D
  have hQ : IsProjection Q := by
    constructor
    · dsimp [Q]
      rw [Matrix.conjTranspose_mul,hherm,hS]
      exact hcomm.eq
    · dsimp [Q]
      rw [← Matrix.mul_assoc, hSDS]
  have hQD : Q * D = D := by
    dsimp [Q]
    rw [hcomm.symm.eq,hDSD]
  have hz : (1 - Q) * D = 0 := by rw [Matrix.sub_mul,Matrix.one_mul,hQD,sub_self]
  have hg : ∑ i, ((1 - Q) * E i) * ((1 - Q) * E i)ᴴ = 0 := by
    rw [gram_compression,← hD,hz,Matrix.zero_mul]
  have hfix (i : L) : Q * E i = E i := by
    have hh := sum_gram_zero _ hg i
    rw [Matrix.sub_mul,Matrix.one_mul] at hh
    exact (sub_eq_zero.mp hh).symm
  refine ⟨hfix, ?_⟩
  have him : imageSpace D = imageSpace Q := by
    apply le_antisymm
    · rintro _ ⟨v,rfl⟩
      refine ⟨Matrix.toEuclideanLin D v, ?_⟩
      have hh := congrArg (fun M => Matrix.toEuclideanLin M v) hQD
      simpa only [Matrix.toLpLin_mul_same,LinearMap.comp_apply] using hh
    · rintro _ ⟨v,rfl⟩
      refine ⟨Matrix.toEuclideanLin S v, ?_⟩
      have hh := congrArg (fun M => Matrix.toEuclideanLin M v) hcomm.eq
      simpa only [Q,Matrix.toLpLin_mul_same,LinearMap.comp_apply] using hh
  change Q = support D
  rw [support,him,← support,projection_support Q hQ]

private lemma forward_representation {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O]
    (F : Superop I O) (hF : IsChannel F) (A : Submodule ℂ (Matrix I I ℂ))
    (P : Matrix I I ℂ) (hA : IsCornerAlgebra A P) (hcorr : Correctable F A P) :
    ∃ f : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ, RepresentationOn A f ∧
      (∀ X ∈ A, F X = F P * f X ∧ F X = f X * F P) ∧ f P = support (F P) := by
  classical
  obtain ⟨r,E,hE,hEq⟩ := hF
  rcases hA with ⟨hPA,hP0,hP,hstar,hmul,hunit⟩
  let K (i : Fin r) := E i * P
  have hK (X : Matrix I I ℂ) (hX : X ∈ A) : F X = krausApply K X := by
    rw [hEq]
    apply Finset.sum_congr rfl
    intro i _
    change E i * X * (E i)ᴴ = (E i * P) * X * (E i * P)ᴴ
    rw [Matrix.conjTranspose_mul,hP.1]
    calc
      E i * X * (E i)ᴴ = E i * (P * X * P) * (E i)ᴴ := by rw [(hunit X hX).1,(hunit X hX).2]
      _ = (E i * P) * X * (P * (E i)ᴴ) := by simp only [Matrix.mul_assoc]
  have hD : F P = ∑ i, K i * (K i)ᴴ := by
    rw [hK P hPA]
    apply Finset.sum_congr rfl
    intro i _
    change (E i * P) * P * (K i)ᴴ = (E i * P) * (K i)ᴴ
    rw [Matrix.mul_assoc (E i) P P,hP.2]
  have hherm : (F P)ᴴ = F P := by
    rw [hD]
    simp only [Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have hprod (X Y : Matrix I I ℂ) (hX : X ∈ A) (hY : Y ∈ A) :
      F X * F Y = F P * F (X * Y) := by
    rw [hK X hX,hK Y hY,hK (X * Y) (hmul X hX Y hY),hD]
    apply kraus_product
    intro i j
    have hh := hcorr X hX ((E i)ᴴ * E j) (Submodule.subset_span ⟨r,E,hE,hEq,i,j,rfl⟩)
    simpa only [K,Matrix.conjTranspose_mul,hP.1,Matrix.mul_assoc] using hh
  obtain ⟨S,hS,hDS,hDSD,hSDS,hSC⟩ := spectral_inverse (F P) hherm
  obtain ⟨hfixK,hsupport⟩ := gram_support K (F P) S hD hherm hS hDS hDSD hSDS
  have hfix (X : Matrix I I ℂ) (hX : X ∈ A) : (S * F P) * F X = F X := by
    rw [hK X hX,krausApply,Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hfixK]
  have hDC (X : Matrix I I ℂ) (hX : X ∈ A) : Commute (F P) (F X) := by
    have hh := hprod X P hX hPA
    rw [(hunit X hX).2] at hh
    exact hh.symm
  have hSCX (X : Matrix I I ℂ) (hX : X ∈ A) : S * F X = F X * S :=
    (hSC _ (hDC X hX)).eq
  let f : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ := (LinearMap.mulLeft ℂ S).comp (krausLinear E)
  have hf (X : Matrix I I ℂ) : f X = S * F X := by
    change S * krausApply E X = S * F X
    rw [hEq]
  have hfinter (X : Matrix I I ℂ) (hX : X ∈ A) :
      F X = F P * f X ∧ F X = f X * F P := by
    rw [hf]
    constructor
    · rw [← Matrix.mul_assoc,hDS.eq]
      exact (hfix X hX).symm
    · rw [Matrix.mul_assoc,← (hDC X hX).eq,← Matrix.mul_assoc]
      exact (hfix X hX).symm
  have hfmul (X : Matrix I I ℂ) (hX : X ∈ A) (Y : Matrix I I ℂ) (hY : Y ∈ A) :
      f (X * Y) = f X * f Y := by
    simp only [hf]
    calc
      S * F (X * Y) = S * ((S * F P) * F (X * Y)) := by rw [hfix _ (hmul X hX Y hY)]
      _ = S * (S * (F X * F Y)) := by rw [Matrix.mul_assoc,hprod X Y hX hY]
      _ = S * ((S * F X) * F Y) :=
        congrArg (fun T => S * T) (Matrix.mul_assoc S (F X) (F Y)).symm
      _ = S * ((F X * S) * F Y) :=
        congrArg (fun T => S * (T * F Y)) (hSCX X hX)
      _ = (S * F X) * (S * F Y) := by simp only [Matrix.mul_assoc]
  have hfstar (X : Matrix I I ℂ) (hX : X ∈ A) : f Xᴴ = (f X)ᴴ := by
    simp only [hf,Matrix.conjTranspose_mul,hS]
    have hh : F Xᴴ = (F X)ᴴ := by rw [hEq,hEq]; exact kraus_star E X
    rw [← hh]
    exact hSCX Xᴴ (hstar X hX)
  have hfinj : Set.InjOn f A := by
    intro X hX Y hY hXY
    have hZ : X - Y ∈ A := A.sub_mem hX hY
    have hz : f (X - Y) = 0 := by rw [map_sub,hXY,sub_self]
    have hmulz : f ((X - Y)ᴴ * (X - Y)) = 0 := by
      rw [hfmul _ (hstar _ hZ) _ hZ,hz,Matrix.mul_zero]
    have hFz : F ((X - Y)ᴴ * (X - Y)) = 0 := by
      rw [(hfinter _ (hmul _ (hstar _ hZ) _ hZ)).1,hmulz,Matrix.mul_zero]
    have htr := channel_trace F ⟨r,E,hE,hEq⟩ ((X - Y)ᴴ * (X - Y))
    rw [hFz,Matrix.trace_zero] at htr
    exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr.symm)
  refine ⟨f,⟨hfinj,hfmul,hfstar⟩,hfinter,?_⟩
  rw [hf,hsupport]

private lemma gram_difference {I O L : Type} [Fintype I] [Fintype O] [Fintype L]
    (K T : L → Matrix O I ℂ) (R : Matrix O O ℂ) :
    (∑ i, (R * K i - T i) * (R * K i - T i)ᴴ) =
      R * (∑ i, K i * (K i)ᴴ) * Rᴴ - R * (∑ i, K i * (T i)ᴴ) -
      (∑ i, T i * (K i)ᴴ) * Rᴴ + ∑ i, T i * (T i)ᴴ := by
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,Matrix.sub_mul,
    Matrix.mul_sub,Finset.sum_sub_distrib,Matrix.mul_sum,Matrix.sum_mul]
  simp only [Matrix.mul_assoc]
  abel

private lemma converse_representation {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O]
    (F : Superop I O) (A : Submodule ℂ (Matrix I I ℂ))
    (P : Matrix I I ℂ) (hA : IsCornerAlgebra A P)
    (f : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hf : RepresentationOn A f)
    (hinter : ∀ X ∈ A, F X = F P * f X ∧ F X = f X * F P) :
    Correctable F A P := by
  classical
  rcases hA with ⟨hPA,hP0,hP,hstar,hmul,hunit⟩
  have intertwine {r : ℕ} (E : Fin r → Matrix O I ℂ)
      (hEq : ∀ X, F X = krausApply E X) (X : Matrix I I ℂ) (hX : X ∈ A) :
      ∀ i, f X * (E i * P) = E i * X := by
    let K (i : Fin r) := E i * P
    let T (i : Fin r) := E i * X
    have hKK : ∑ i, K i * (K i)ᴴ = F P := by
      rw [hEq]
      apply Finset.sum_congr rfl
      intro i _
      simp only [K,Matrix.conjTranspose_mul,hP.1,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P P (E i)ᴴ,hP.2]
    have hKT : ∑ i, K i * (T i)ᴴ = F Xᴴ := by
      rw [hEq]
      apply Finset.sum_congr rfl
      intro i _
      simp only [K,T,Matrix.conjTranspose_mul,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Xᴴ (E i)ᴴ,(hunit Xᴴ (hstar X hX)).1]
    have hTK : ∑ i, T i * (K i)ᴴ = F X := by
      rw [hEq]
      apply Finset.sum_congr rfl
      intro i _
      simp only [K,T,Matrix.conjTranspose_mul,hP.1,← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (E i) X P,(hunit X hX).2]
    have hTT : ∑ i, T i * (T i)ᴴ = F (X * Xᴴ) := by
      rw [hEq]
      simp only [T,krausApply,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    have hXX : X * Xᴴ ∈ A := hmul X hX Xᴴ (hstar X hX)
    have hRstar : f Xᴴ = (f X)ᴴ := hf.2.2 X hX
    have hRmul : f (X * Xᴴ) = f X * (f X)ᴴ := by rw [hf.2.1 X hX Xᴴ (hstar X hX),hRstar]
    have h1 : f X * F P * (f X)ᴴ = F (X * Xᴴ) := by
      rw [← (hinter X hX).2,(hinter X hX).1,Matrix.mul_assoc,← hRmul]
      exact ((hinter _ hXX).1).symm
    have h2 : f X * F Xᴴ = F (X * Xᴴ) := by
      rw [(hinter Xᴴ (hstar X hX)).1,hRstar,← Matrix.mul_assoc,h1]
    have h3 : F X * (f X)ᴴ = F (X * Xᴴ) := by
      rw [(hinter X hX).2,h1]
    have hz : ∑ i, (f X * K i - T i) * (f X * K i - T i)ᴴ = 0 := by
      rw [gram_difference,hKK,hKT,hTK,hTT,h1,h2,h3]
      abel
    intro i
    exact sub_eq_zero.mp (sum_gram_zero _ hz i)
  intro X hX s hs
  apply Submodule.span_induction (p := fun s _ => X * (P * s * P) = (P * s * P) * X) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨r,E,hE,hEq,i,j,rfl⟩
    have hi := intertwine E hEq Xᴴ (hstar X hX) i
    have hj := intertwine E hEq X hX j
    have hi' : P * (E i)ᴴ * f X = X * (E i)ᴴ := by
      have hh := congrArg Matrix.conjTranspose hi
      simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hP.1,
        hf.2.2 X hX,Matrix.conjTranspose_conjTranspose] using hh
    calc
      X * (P * ((E i)ᴴ * E j) * P) = (X * (E i)ᴴ) * (E j * P) := by
        simp only [← Matrix.mul_assoc,(hunit X hX).2]
      _ = (P * (E i)ᴴ * f X) * (E j * P) := by rw [hi']
      _ = (P * (E i)ᴴ) * (E j * X) := by rw [Matrix.mul_assoc,hj]
      _ = (P * ((E i)ᴴ * E j) * P) * X := by
        simp only [Matrix.mul_assoc,(hunit X hX).1]
  · simp
  · intro s t _ _ hs ht
    simp only [Matrix.mul_add,Matrix.add_mul,hs,ht]
  · intro c s _ hs
    simp only [Matrix.mul_smul,Matrix.smul_mul,hs]

theorem solution {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Submodule ℂ (Matrix I I ℂ))
    (P : Matrix I I ℂ) (hA : IsCornerAlgebra A P) :
    (Correctable F A P ↔ ∃ f : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ,
      RepresentationOn A f ∧ ∀ X ∈ A, F X = F P * f X ∧ F X = f X * F P) ∧
    (Correctable F A P → ∃ f : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ,
      RepresentationOn A f ∧ (∀ X ∈ A, F X = F P * f X ∧ F X = f X * F P) ∧ f P = support (F P)) := by
  refine ⟨⟨?_,?_⟩,forward_representation F hF A P hA⟩
  · intro h
    obtain ⟨f,hrep,hinter,_⟩ := forward_representation F hF A P hA h
    exact ⟨f,hrep,hinter⟩
  · rintro ⟨f,hrep,hinter⟩
    exact converse_representation F A P hA f hrep hinter

#print axioms solution
