-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.conditional_expectation_simulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:27:32.641977+00:00
-- url     : https://prove2.me/submissions/009bd55a-5415-4924-af8f-e2d92c85117f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_isometric_encoding
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_processing_systems
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_graph_transmission
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes

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

private lemma pinching_channel (A : Shape) : IsChannel (pinching A) := by
  have hK : IsKrausFamily (logicalProjection A) := by
    change (∑ k, (logicalProjection A k)ᴴ * logicalProjection A k) = 1
    simp only [(logicalProjection_idem A _).1,(logicalProjection_idem A _).2]
    ext i j
    simp [Matrix.sum_apply,logicalProjection,Matrix.diagonal_apply,Matrix.one_apply]
  have heq : pinching A = krausApply (logicalProjection A) := by
    funext X
    unfold krausApply
    simp_rw [(logicalProjection_idem A _).1]
    ext i j
    simp only [Matrix.sum_apply,logicalProjection,Matrix.diagonal_mul,
      Matrix.mul_diagonal,pinching]
    by_cases h : i.1 = j.1
    · simp [h]
    · simp [h,eq_comm]
  rw [heq]
  exact finite_kraus_channel _ hK

private lemma kraus_pinching_form (A : Shape) {r : ℕ}
    (E : Fin r → Matrix (Logical A) (Logical A) ℂ)
    (hE : ∀ X, pinching A X = krausApply E X) :
    ∀ t, ∃ z : Block A → ℂ, E t = Matrix.diagonal (fun i => z i.1) := by
  classical
  have hentry (i j a b : Logical A) :
      (if i.1 = j.1 then (Matrix.single i j (1 : ℂ)) a b else 0) =
        ∑ t, E t a i * conj (E t b j) := by
    have h := congrFun (congrFun (hE (Matrix.single i j 1)) a) b
    simp only [pinching,krausApply,Matrix.sum_apply,Matrix.mul_apply,
      Matrix.single_apply,Matrix.conjTranspose_apply] at h
    simp only [ite_and] at h
    by_cases hai : i = a <;> by_cases hjb : j = b <;> simp_all
  have hoff (t : Fin r) (a i : Logical A) (hai : a ≠ i) : E t a i = 0 := by
    have hz : ∑ t, Complex.normSq (E t a i) = 0 := by
      have h := congrArg Complex.re (hentry i i a a)
      simpa [hai,Ne.symm hai,Matrix.single_apply,Complex.mul_conj,Complex.normSq_apply] using h.symm
    have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => Complex.normSq_nonneg (E t a i))).mp hz t (mem_univ _)
    exact Complex.normSq_eq_zero.mp ht
  have hdiag (t : Fin r) (i j : Logical A) (hij : i.1 = j.1) : E t i i = E t j j := by
    have hi : ∑ t, Complex.normSq (E t i i) = 1 := by
      have h := congrArg Complex.re (hentry i i i i)
      simpa [Matrix.single_apply,Complex.mul_conj] using h.symm
    have hj : ∑ t, Complex.normSq (E t j j) = 1 := by
      have h := congrArg Complex.re (hentry j j j j)
      simpa [Matrix.single_apply,Complex.mul_conj] using h.symm
    have hc : ∑ t, (E t i i * conj (E t j j)).re = 1 := by
      have h := congrArg Complex.re (hentry i j i j)
      simpa [hij,Matrix.single_apply] using h.symm
    have hz : ∑ t, Complex.normSq (E t i i - E t j j) = 0 := by
      simp only [Complex.normSq_sub,Finset.sum_sub_distrib,Finset.sum_add_distrib,
        ← Finset.mul_sum,hi,hj]
      rw [hc]
      norm_num
    have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => Complex.normSq_nonneg (E t i i - E t j j))).mp hz t (mem_univ _)
    exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp ht)
  intro t
  let z (k : Block A) : ℂ := if h : Nonempty (Fin (blockSize A k)) then
    E t ⟨k,Classical.choice h⟩ ⟨k,Classical.choice h⟩ else 0
  refine ⟨z, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    dsimp [z]
    rw [dif_pos ⟨i.2⟩]
    exact hdiag t i _ rfl
  · simpa only [Matrix.diagonal_apply_ne _ hij] using hoff t i j hij

private lemma pinching_graph (A : Shape) : graph (pinching A) ≤ pinchingSystem A := by
  apply Submodule.span_le.mpr
  rintro X ⟨r,E,_,hE,i,j,rfl⟩
  obtain ⟨z,hz⟩ := kraus_pinching_form A E hE i
  obtain ⟨w,hw⟩ := kraus_pinching_form A E hE j
  rw [hz,hw,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  apply Submodule.subset_span
  exact ⟨fun k => star (z k) * w k,rfl⟩

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

private lemma pinching_transmits (A : Shape) (hA : Valid A)
    [Nonempty (Logical A)] : Transmits (pinching A) A := by
  apply (orthogonal_codes (pinching A) (pinching_channel A) A hA).mpr
  refine ⟨logicalProjection A,?_,?_⟩
  · intro k
    exact ⟨⟨logicalProjection_idem A k,fun X hX =>
      (logicalProjection_code A k).2 X (pinching_graph A hX)⟩,
      logicalProjection_rank A k⟩
  · intro k j hkj X hX
    exact logicalProjection_orthogonal A k j hkj X (pinching_graph A hX)

private lemma isometry_channel {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] (V : Matrix J I ℂ) (hV : Vᴴ * V = 1) :
    IsChannel (conjSuperop V) := by
  refine ⟨1, fun _ => V, ?_, ?_⟩
  · simpa [IsKrausFamily] using hV
  · intro X
    simp [conjSuperop,krausApply]

theorem solution {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A) :
    Transmits F A ↔ ∃ E : Superop (Logical A) I, ∃ D : Superop O (Logical A),
      IsChannel E ∧ IsChannel D ∧ D ∘ F ∘ E = pinching A := by
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
    obtain ⟨V,hV,_,D,hD,heq⟩ := (isometric_encoding F hF A hA).mp ht
    exact ⟨conjSuperop V,D,isometry_channel V hV,hD,heq⟩
  · rintro ⟨E,D,hE,hD,heq⟩
    have hFE := channel_comp E F hE hF
    have hle : graph (F ∘ E) ≤ graph (pinching A) := by
      have h := (processing_systems (F ∘ E) D hFE hD).1
      have heq' : D ∘ (F ∘ E) = pinching A := heq
      rwa [heq'] at h
    obtain ⟨_,f,hf,hcorr⟩ := pinching_transmits A hA
    have ht : Transmits (F ∘ E) A :=
      ⟨hA,f,hf,fun X s hs => hcorr X s (hle hs)⟩
    exact graph_transmission (F ∘ E) F hFE hF
      (processing_systems E F hE hF).2 A ht

#print axioms solution
