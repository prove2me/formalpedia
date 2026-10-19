-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.graph_characterization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T08:06:44.407395+00:00
-- url     : https://prove2.me/submissions/a87dc06d-da69-4698-b172-95a52779a79b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_isometric_encoding

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

private lemma block_compress {I J : Type} [Fintype I] [Fintype J]
    {e : ℕ} (V : Matrix (J × Fin e) I ℂ) (X : Matrix J J ℂ) (a b : Fin e) :
    (V.submatrix (fun j => (j,a)) id)ᴴ * X *
      (V.submatrix (fun j => (j,b)) id) =
      Vᴴ * Matrix.kronecker X (Matrix.single a b 1) * V := by
  ext i k
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.single_apply, Matrix.conjTranspose_apply, ite_and, Finset.sum_mul]

private lemma code_image {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (hT : (1 : Matrix J J ℂ) ∈ T) (e : ℕ) (he : 0 < e)
    (V : Matrix (J × Fin e) I ℂ) (hV : Vᴴ * V = 1)
    (hcomp : ∀ X ∈ T, ∀ Y : Matrix (Fin e) (Fin e) ℂ,
      Vᴴ * Matrix.kronecker X Y * V ∈ S)
    (P : Matrix I I ℂ) (hP : Code S P) :
    ∃ Q : Matrix J J ℂ, Code T Q ∧ Q.rank = P.rank ∧
      ∃ (a : Fin e) (z : ℂ),
        let B := V.submatrix (fun j => (j,a)) id * P
        Q = z • (B * Bᴴ) := by
  classical
  by_cases hp0 : P = 0
  · refine ⟨0, ⟨⟨by simp, by simp⟩, ?_⟩, by simp [hp0], ⟨0,he⟩, 0, by simp⟩
    intro X hX
    exact ⟨0,by simp⟩
  let C (a : Fin e) : Matrix J I ℂ := V.submatrix (fun j => (j,a)) id
  have hC : ∃ a, C a * P ≠ 0 := by
    by_contra! hz
    have hzV : V * P = 0 := by
      ext ⟨j,a⟩ i
      have hh := congrFun (congrFun (hz a) j) i
      simpa [C,Matrix.mul_apply] using hh
    have hh := congrArg (fun M => Vᴴ * M) hzV
    rw [← Matrix.mul_assoc, hV] at hh
    simp at hh
    exact hp0 hh
  obtain ⟨a,ha⟩ := hC
  let A : Matrix J I ℂ := C a * P
  have hAP : A * P = A := by
    dsimp [A]
    rw [Matrix.mul_assoc, hP.1.2]
  have hPA : P * Aᴴ = Aᴴ := by
    simpa [Matrix.conjTranspose_mul, hP.1.1] using congrArg Matrix.conjTranspose hAP
  have hPX (X : Matrix J J ℂ) (hX : X ∈ T) :
      ∃ c : ℂ, Aᴴ * X * A = c • P := by
    have hm : (C a)ᴴ * X * C a ∈ S := by
      dsimp [C]
      rw [block_compress]
      exact hcomp X hX _
    obtain ⟨c,hc⟩ := hP.2 _ hm
    refine ⟨c, ?_⟩
    simpa [A,Matrix.conjTranspose_mul,hP.1.1,Matrix.mul_assoc] using hc
  obtain ⟨z,hz⟩ := hPX 1 hT
  simp only [Matrix.mul_one] at hz
  have hz0 : z ≠ 0 := by
    intro hh
    have hAA : Aᴴ * A = 0 := by simpa [hh] using hz
    have hAz : A = 0 := (Matrix.conjTranspose_mul_self_eq_zero).mp hAA
    exact ha hAz
  have hstar : star z = z := by
    apply smul_left_injective ℂ hp0
    calc
      star z • P = (z • P)ᴴ := by rw [Matrix.conjTranspose_smul,hP.1.1]
      _ = (Aᴴ * A)ᴴ := congrArg Matrix.conjTranspose hz.symm
      _ = z • P := by simpa using hz
  let Q : Matrix J J ℂ := z⁻¹ • (A * Aᴴ)
  have hQ : IsProjection Q := by
    constructor
    · simp [Q,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,hstar]
    · change (z⁻¹ • (A * Aᴴ)) * (z⁻¹ • (A * Aᴴ)) = z⁻¹ • (A * Aᴴ)
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have heq : (A * Aᴴ) * (A * Aᴴ) = z • (A * Aᴴ) := by
        calc
          (A * Aᴴ) * (A * Aᴴ) = A * (Aᴴ * A) * Aᴴ := by simp [Matrix.mul_assoc]
          _ = z • (A * Aᴴ) := by rw [hz,Matrix.mul_smul,Matrix.smul_mul,hAP]
      rw [heq,smul_smul]
      field_simp
  refine ⟨Q, ⟨hQ, ?_⟩, ?_, a, z⁻¹, rfl⟩
  · intro X hX
    obtain ⟨c,hc⟩ := hPX X hX
    refine ⟨z⁻¹ * c, ?_⟩
    change (z⁻¹ • (A * Aᴴ)) * X * (z⁻¹ • (A * Aᴴ)) =
      (z⁻¹ * c) • (z⁻¹ • (A * Aᴴ))
    rw [Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    have heq : (A * Aᴴ * X) * (A * Aᴴ) = c • (A * Aᴴ) := by
      calc
        (A * Aᴴ * X) * (A * Aᴴ) = A * (Aᴴ * X * A) * Aᴴ := by simp [Matrix.mul_assoc]
        _ = c • (A * Aᴴ) := by rw [hc,Matrix.mul_smul,Matrix.smul_mul,hAP]
    rw [heq,smul_smul,smul_smul]
    congr 1
    ring
  · calc
      Q.rank = (A * Aᴴ).rank := Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero hz0))
      _ = A.rank := Matrix.rank_self_mul_conjTranspose A
      _ = (Aᴴ * A).rank := (Matrix.rank_conjTranspose_mul_self A).symm
      _ = P.rank := by
        rw [hz]
        exact Matrix.rank_smul_of_mem_nonZeroDivisors P (mem_nonZeroDivisors_of_ne_zero hz0)

private lemma orthogonal_family_transfer {I J L : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (hT : (1 : Matrix J J ℂ) ∈ T) (h : GraphHom S T)
    (P : L → Matrix I I ℂ) (hP : ∀ k, Code S (P k))
    (horth : ∀ k j, k ≠ j → ∀ X ∈ S, P k * X * P j = 0) :
    ∃ Q : L → Matrix J J ℂ,
      (∀ k, Code T (Q k) ∧ (Q k).rank = (P k).rank) ∧
      ∀ k j, k ≠ j → ∀ X ∈ T, Q k * X * Q j = 0 := by
  classical
  obtain ⟨e,he,V,hV,hcomp⟩ := h
  choose Q hQ hr a z hz using fun k => code_image S T hT e he V hV hcomp (P k) (hP k)
  refine ⟨Q, fun k => ⟨hQ k,hr k⟩, ?_⟩
  intro k j hkj X hX
  let C (b : Fin e) : Matrix J I ℂ := V.submatrix (fun j => (j,b)) id
  have hc : (C (a k))ᴴ * X * C (a j) ∈ S := by
    dsimp [C]
    rw [block_compress]
    exact hcomp X hX _
  have hzero : P k * ((C (a k))ᴴ * X * C (a j)) * P j = 0 :=
    horth k j hkj _ hc
  rw [hz k, hz j]
  change (z k • ((C (a k) * P k) * (C (a k) * P k)ᴴ)) * X *
    (z j • ((C (a j) * P j) * (C (a j) * P j)ᴴ)) = 0
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have heq : (((C (a k) * P k) * (C (a k) * P k)ᴴ) * X) *
      ((C (a j) * P j) * (C (a j) * P j)ᴴ) =
      C (a k) * (P k * ((C (a k))ᴴ * X * C (a j)) * P j) *
        (C (a j) * P j)ᴴ := by
    simp only [Matrix.conjTranspose_mul, (hP k).1.1, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (P k) (P k), (hP k).1.2]
  rw [heq, hzero]
  simp

private lemma graph_one {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (F : Superop I O) (hF : IsChannel F) : (1 : Matrix I I ℂ) ∈ graph F := by
  obtain ⟨r,E,hE,hEq⟩ := hF
  rw [← hE]
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.subset_span ⟨r,E,hE,hEq,a,a,rfl⟩


private def logicalProjection (A : Shape) (k : Block A) : Matrix (Logical A) (Logical A) ℂ :=
  Matrix.diagonal (fun i => if i.1 = k then 1 else 0)

private lemma logicalProjection_idem (A : Shape) (k : Block A) :
    IsProjection (logicalProjection A k) := by
  constructor
  · ext i j
    simp [logicalProjection, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  · rw [logicalProjection, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp

private lemma logicalProjection_rank (A : Shape) (k : Block A) :
    (logicalProjection A k).rank = blockSize A k := by
  have hid := (logicalProjection_idem A k).2
  have hi : IsIdempotentElem (Matrix.toLin' (logicalProjection A k)) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hid]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  have htrace : (logicalProjection A k).trace =
      ((logicalProjection A k).rank : ℂ) := by
    rw [← Matrix.trace_toLin_eq _ (Pi.basisFun ℂ (Logical A)),
      Matrix.toLin_eq_toLin', ht, Matrix.rank]
    rfl
  have hc : (logicalProjection A k).trace = (blockSize A k : ℂ) := by
    rw [logicalProjection,Matrix.trace_diagonal]
    rw [Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp
    · intro j hj hjk
      simp [hjk]
    · simp
  exact_mod_cast htrace.symm.trans hc

private lemma pinchingSystem_form (A : Shape) (X : Matrix (Logical A) (Logical A) ℂ)
    (hX : X ∈ pinchingSystem A) :
    ∃ z : Block A → ℂ, X = Matrix.diagonal (fun i => z i.1) := by
  change X ∈ Submodule.span ℂ _ at hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨z,rfl⟩ := hX
      exact ⟨z,rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add X Y hX hY iX iY =>
      obtain ⟨x,rfl⟩ := iX
      obtain ⟨y,rfl⟩ := iY
      exact ⟨x+y, by simp [Matrix.diagonal_add]⟩
  | smul c X hX iX =>
      obtain ⟨x,rfl⟩ := iX
      refine ⟨c • x, ?_⟩
      rw [← Matrix.diagonal_smul]
      rfl

private lemma logicalProjection_code (A : Shape) (k : Block A) :
    Code (pinchingSystem A) (logicalProjection A k) := by
  refine ⟨logicalProjection_idem A k, ?_⟩
  intro X hX
  obtain ⟨z,rfl⟩ := pinchingSystem_form A X hX
  refine ⟨z k, ?_⟩
  simp only [logicalProjection, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  change ((if i.1 = k then (1 : ℂ) else 0) * z i.1) *
    (if i.1 = k then 1 else 0) = z k * (if i.1 = k then 1 else 0)
  split_ifs with h
  · simp [h]
  · simp

private lemma logicalProjection_orthogonal (A : Shape) (k j : Block A) (hkj : k ≠ j)
    (X : Matrix (Logical A) (Logical A) ℂ) (hX : X ∈ pinchingSystem A) :
    logicalProjection A k * X * logicalProjection A j = 0 := by
  obtain ⟨z,rfl⟩ := pinchingSystem_form A X hX
  simp only [logicalProjection, Matrix.diagonal_mul_diagonal]
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.zero_apply]
  split_ifs with hab hak haj <;> simp_all

private lemma isometry_graphHom {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (hcomp : ∀ X ∈ T, Vᴴ * X * V ∈ S) : GraphHom S T := by
  let W : Matrix (J × Fin 1) I ℂ := fun a i => V a.1 i
  refine ⟨1, by omega, W, ?_, ?_⟩
  · have heq : Wᴴ * W = Vᴴ * V := by
      ext i j
      simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
      simp [W, Fintype.sum_prod_type]
    rw [heq,hV]
  · intro X hX Y
    have heq : Wᴴ * Matrix.kronecker X Y * W = (Y 0 0) • (Vᴴ * X * V) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.smul_apply, smul_eq_mul]
      simp only [W, Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.kronecker, Matrix.kronecker_apply]
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    rw [heq]
    exact S.smul_mem _ (hcomp X hX)

theorem solution {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A) :
    Transmits F A ↔ GraphHom (pinchingSystem A) (graph F) := by
  constructor
  · intro h
    obtain ⟨V,hV,hcomp,_⟩ := (isometric_encoding F hF A hA).mp h
    exact isometry_graphHom _ _ V hV hcomp
  · intro h
    obtain ⟨Q,hQ,horth⟩ := orthogonal_family_transfer (pinchingSystem A) (graph F)
      (graph_one F hF) h (logicalProjection A) (logicalProjection_code A)
      (logicalProjection_orthogonal A)
    apply (orthogonal_codes F hF A hA).mpr
    exact ⟨Q,fun k => ⟨(hQ k).1,(hQ k).2.trans (logicalProjection_rank A k)⟩,horth⟩

#print axioms solution
