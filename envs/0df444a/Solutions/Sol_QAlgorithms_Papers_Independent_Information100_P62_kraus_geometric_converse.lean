-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.kraus_geometric_converse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:16:07.099092+00:00
-- url     : https://prove2.me/submissions/36f72f57-b579-4e84-8cfb-1bc5a952570c

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset Module

private lemma rank_image {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (M : Matrix O I ℂ) :
    M.rank = Module.finrank ℂ (imageSpace M) := by
  rw [Matrix.rank_eq_finrank_range_toLin M
    (EuclideanSpace.basisFun O ℂ).toBasis (EuclideanSpace.basisFun I ℂ).toBasis]
  rfl

private lemma projection_linear {I : Type} [Fintype I] [DecidableEq I]
    (C : Submodule ℂ (EuclideanSpace ℂ I)) :
    Matrix.toEuclideanLin (projection C) = C.starProjection.toLinearMap := by
  apply (EuclideanSpace.basisFun I ℂ).toBasis.ext
  intro i
  ext j
  simp [projection, Matrix.toLpLin_apply,
    EuclideanSpace.basisFun_apply, QAlgorithms.ket]

private lemma map_nullity {O : Type} [Fintype O]
    (Y : Submodule ℂ (EuclideanSpace ℂ O)) (f : EuclideanSpace ℂ O →ₗ[ℂ] EuclideanSpace ℂ O) :
    Module.finrank ℂ (Y.map f) + Module.finrank ℂ (Y ⊓ f.ker : Submodule ℂ (EuclideanSpace ℂ O)) =
      Module.finrank ℂ Y := by
  have h := (f.domRestrict Y).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have he : f.ker.comap Y.subtype = (Y ⊓ f.ker).comap Y.subtype := by ext; simp
  rw [he, (Submodule.comapSubtypeEquivOfLe (inf_le_left : Y ⊓ f.ker ≤ Y)).finrank_eq] at h
  exact h

private lemma geometric_bound {O : Type} [Fintype O] [DecidableEq O]
    (U V X Y : Submodule ℂ (EuclideanSpace ℂ O))
    (hUX : U ≤ X) (hVY : V ≤ Y) (hUV : U.IsOrtho V) :
    (Module.finrank ℂ V : ℤ) + max 0
      ((Module.finrank ℂ (Y.map (Matrix.toEuclideanLin (projection X))) : ℤ) -
        Module.finrank ℂ X + Module.finrank ℂ U) ≤ Module.finrank ℂ Y := by
  let p := X.starProjection.toLinearMap
  have hp : p.ker = Xᗮ := X.ker_starProjection
  have hnullY := map_nullity Y p
  have hnullV := map_nullity V p
  rw [hp] at hnullY hnullV
  have hproj : V.map p ≤ Uᗮ ⊓ X := by
    rintro z ⟨v,hv,rfl⟩
    refine ⟨?_, X.starProjection_apply_mem v⟩
    change X.starProjection v ∈ Uᗮ
    apply (Submodule.mem_orthogonal U _).mpr
    intro u hu
    change inner ℂ u (X.starProjection v) = 0
    rw [← X.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hUX hu)]
    exact hUV.inner_eq hu hv
  have hdim := Submodule.finrank_mono hproj
  have hcomp := Submodule.finrank_add_inf_finrank_orthogonal hUX
  have hinter := Submodule.finrank_mono (inf_le_inf_right Xᗮ hVY)
  have hle := Submodule.finrank_mono hVY
  rw [projection_linear]
  change (Module.finrank ℂ V : ℤ) + max 0
    ((Module.finrank ℂ (Y.map p) : ℤ) - Module.finrank ℂ X + Module.finrank ℂ U) ≤ _
  omega

private def spanFin {B O : Type} [Fintype O]
    (C : B → Submodule ℂ (EuclideanSpace ℂ O)) (S : Finset B) :
    Submodule ℂ (EuclideanSpace ℂ O) := ⨆ k : {k // k ∈ S}, C k.val

private lemma spanFin_empty {B O : Type} [Fintype O]
    (C : B → Submodule ℂ (EuclideanSpace ℂ O)) : spanFin C ∅ = ⊥ := by
  apply le_antisymm
  · exact iSup_le fun k => False.elim (notMem_empty k.val k.property)
  · exact bot_le

private lemma spanFin_insert {B O : Type} [Fintype O] [DecidableEq B]
    (C : B → Submodule ℂ (EuclideanSpace ℂ O)) (a : B) (S : Finset B) :
    spanFin C (insert a S) = C a ⊔ spanFin C S := by
  apply le_antisymm
  · apply iSup_le
    intro k
    rcases mem_insert.mp k.property with h | h
    · rw [h]; exact le_sup_left
    · exact (le_iSup (fun j : {j // j ∈ S} => C j.val) ⟨k.val,h⟩).trans le_sup_right
  · apply sup_le
    · exact le_iSup_of_le ⟨a,mem_insert_self a S⟩ le_rfl
    · exact iSup_le fun k => le_iSup_of_le ⟨k.val,mem_insert_of_mem k.property⟩ le_rfl

private lemma spanFin_orthogonal {B O : Type} [Fintype O]
    (C : B → Submodule ℂ (EuclideanSpace ℂ O)) (S T : Finset B)
    (h : ∀ k ∈ S, ∀ j ∈ T, (C k).IsOrtho (C j)) :
    (spanFin C S).IsOrtho (spanFin C T) := by
  change (⨆ k : {k // k ∈ S}, C k.val) ≤ (⨆ j : {j // j ∈ T}, C j.val)ᗮ
  rw [← Submodule.iInf_orthogonal]
  exact iSup_le fun k => le_iInf fun j => h k.val k.property j.val j.property

private lemma spanFin_dimension {B O : Type} [Fintype O]
    (C : B → Submodule ℂ (EuclideanSpace ℂ O))
    (h : Pairwise (fun k j => (C k).IsOrtho (C j))) (S : Finset B) :
    Module.finrank ℂ (spanFin C S) = ∑ k ∈ S, Module.finrank ℂ (C k) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [spanFin_empty]; simp
  | @insert a S ha ih =>
    have ho : (C a).IsOrtho (spanFin C S) := by
      change C a ≤ (⨆ j : {j // j ∈ S}, C j.val)ᗮ
      rw [← Submodule.iInf_orthogonal]
      exact le_iInf fun j => h (by intro haj; exact ha (haj ▸ j.property))
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (C a) (spanFin C S)
    rw [ho.disjoint.eq_bot,finrank_bot,add_zero] at hd
    rw [spanFin_insert,hd,ih,sum_insert ha]

private lemma spanFin_dimension_le {B O : Type} [Fintype O]
    (C : B → Submodule ℂ (EuclideanSpace ℂ O)) (S : Finset B) :
    Module.finrank ℂ (spanFin C S) ≤ ∑ k ∈ S, Module.finrank ℂ (C k) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [spanFin_empty]; simp
  | @insert a S ha ih =>
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (C a) (spanFin C S)
    rw [spanFin_insert,sum_insert ha]
    omega

private lemma image_ortho {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (M N : Matrix O I ℂ) (h : Mᴴ * N = 0) :
    (imageSpace M).IsOrtho (imageSpace N) := by
  apply Submodule.IsOrtho.symm
  change imageSpace N ≤ (LinearMap.range (Matrix.toEuclideanLin M))ᗮ
  rw [LinearMap.orthogonal_range]
  rintro x ⟨y,rfl⟩
  change (Matrix.toEuclideanLin M).adjoint (Matrix.toEuclideanLin N y) = 0
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← LinearMap.comp_apply,
    ← Matrix.toLpLin_mul_same, h, map_zero, LinearMap.zero_apply]

private lemma choose_kraus {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] {r : ℕ}
    (E : Fin r → Matrix O I ℂ) (hE : IsKrausFamily E)
    (P : Matrix I I ℂ) (hP : Code (graph (krausApply E)) P) (hpos : 0 < P.rank) :
    ∃ i : Fin r, (E i * P).rank = P.rank := by
  classical
  have hex : ∃ i : Fin r, P * ((E i)ᴴ * E i) * P ≠ 0 := by
    by_contra hn
    have hz : ∀ i : Fin r, P * ((E i)ᴴ * E i) * P = 0 := by simpa using hn
    have heq : ∑ i, P * ((E i)ᴴ * E i) * P = P := by
      rw [← Finset.sum_mul, ← Finset.mul_sum,hE,Matrix.mul_one,hP.1.2]
    have hzero : P = 0 := by rw [← heq]; exact Finset.sum_eq_zero fun i _ => hz i
    simp [hzero] at hpos
  obtain ⟨i,hi⟩ := hex
  have hmem : (E i)ᴴ * E i ∈ graph (krausApply E) :=
    Submodule.subset_span ⟨r,E,hE,fun _ => rfl,i,i,rfl⟩
  obtain ⟨z,hz⟩ := hP.2 _ hmem
  have hz0 : z ≠ 0 := by intro hh; exact hi (by simpa [hh] using hz)
  refine ⟨i,?_⟩
  calc
    (E i * P).rank = ((E i * P)ᴴ * (E i * P)).rank :=
      (Matrix.rank_conjTranspose_mul_self _).symm
    _ = (z • P).rank := by
      congr 1
      simpa only [Matrix.conjTranspose_mul,hP.1.1,Matrix.mul_assoc] using hz
    _ = P.rank := Matrix.rank_smul_of_mem_nonZeroDivisors P (mem_nonZeroDivisors_of_ne_zero hz0)

private lemma image_mul_le {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (M : Matrix O I ℂ) (P : Matrix I I ℂ) :
    imageSpace (M * P) ≤ imageSpace M := by
  rw [imageSpace,Matrix.toLpLin_mul_same]
  exact LinearMap.range_comp_le_range _ _

private lemma kraus_full_span {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] {r : ℕ} (E : Fin r → Matrix O I ℂ) :
    (⨆ i : Fin r, imageSpace (E i)) = imageSpace (krausApply E 1) := by
  classical
  let M : Matrix O (Fin r × I) ℂ := fun o a => E a.1 o a.2
  have hMM : M * Mᴴ = krausApply E 1 := by
    ext o q
    change (∑ a : Fin r × I, E a.1 o a.2 * star (E a.1 q a.2)) = _
    simp only [krausApply,Matrix.mul_one,Matrix.sum_apply,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Fintype.sum_prod_type]
  have hr : imageSpace (M * Mᴴ) = imageSpace M := by
    unfold imageSpace
    rw [Matrix.toLpLin_mul_same,Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.range_self_comp_adjoint]
  have horth : (imageSpace M)ᗮ = (⨆ i : Fin r, imageSpace (E i))ᗮ := by
    rw [← Submodule.iInf_orthogonal]
    simp only [imageSpace,LinearMap.orthogonal_range,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    ext x
    simp only [Submodule.mem_iInf,LinearMap.mem_ker]
    constructor
    · intro hx i
      ext a
      have hh := congrArg (fun v : EuclideanSpace ℂ (Fin r × I) => v (i,a)) hx
      exact hh
    · intro hx
      ext ⟨i,a⟩
      have hh := congrArg (fun v : EuclideanSpace ℂ I => v a) (hx i)
      exact hh
  have heq : imageSpace M = ⨆ i : Fin r, imageSpace (E i) := by
    have hh := congrArg (fun C : Submodule ℂ (EuclideanSpace ℂ O) => Cᗮ) horth
    simpa only [Submodule.orthogonal_orthogonal] using hh
  rw [← heq,← hr,hMM]

theorem solution {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    {r : ℕ} (E : Fin r → Matrix O I ℂ) (hE : IsKrausFamily E)
    (A : Shape) (hA : Transmits (krausApply E) A) :
    (∃ f : Block A → Fin r, ∀ U V : Finset (Block A), Disjoint U V →
      (∑ k ∈ V, (blockSize A k : ℤ)) +
        max 0 ((Module.finrank ℂ ((selectedSpan E f V).map
          (Matrix.toEuclideanLin (projection (selectedSpan E f U)))) : ℤ) -
          Module.finrank ℂ (selectedSpan E f U) + ∑ k ∈ U, (blockSize A k : ℤ)) ≤
        Module.finrank ℂ (selectedSpan E f V)) ∧
    (∀ k : Block A, blockSize A k ≤ univ.sup (fun i => (E i).rank)) ∧
    (∀ t : ℕ, 1 ≤ t →
      (∑ k ∈ univ.filter (fun k => t ≤ blockSize A k), blockSize A k) ≤
        Module.finrank ℂ (⨆ i : {i : Fin r // t ≤ (E i).rank}, imageSpace (E i.val) :
          Submodule ℂ (EuclideanSpace ℂ O)) ∧
      Module.finrank ℂ (⨆ i : {i : Fin r // t ≤ (E i).rank}, imageSpace (E i.val) :
          Submodule ℂ (EuclideanSpace ℂ O)) ≤
        ∑ i ∈ univ.filter (fun i => t ≤ (E i).rank), (E i).rank) ∧
    (⨆ i : Fin r, imageSpace (E i)) = imageSpace (krausApply E 1) := by
  classical
  obtain ⟨P,hP,horth⟩ := (orthogonal_codes (krausApply E)
    ⟨r,E,hE,fun _ => rfl⟩ A hA.1).mp hA
  have hpos (k : Block A) : 0 < (P k).rank := by
    rw [(hP k).2]
    exact hA.1.2 _ (by
      have hh := List.get_mem A.toList k
      simpa only [Multiset.mem_toList,blockSize] using hh)
  choose f hf using fun k => choose_kraus E hE (P k) (hP k).1 (hpos k)
  let C : Block A → Submodule ℂ (EuclideanSpace ℂ O) :=
    fun k => imageSpace (E (f k) * P k)
  have hdim (k : Block A) : Module.finrank ℂ (C k) = blockSize A k := by
    rw [← rank_image,hf,(hP k).2]
  have hCorth : Pairwise (fun k j => (C k).IsOrtho (C j)) := by
    intro k j hkj
    apply image_ortho
    have hs : (E (f k))ᴴ * E (f j) ∈ graph (krausApply E) :=
      Submodule.subset_span ⟨r,E,hE,fun _ => rfl,f k,f j,rfl⟩
    simpa only [Matrix.conjTranspose_mul,(hP k).1.1.1,Matrix.mul_assoc] using
      horth k j hkj _ hs
  have hsum (S : Finset (Block A)) :
      Module.finrank ℂ (spanFin C S) = ∑ k ∈ S, blockSize A k := by
    rw [spanFin_dimension C hCorth]
    exact sum_congr rfl fun k _ => hdim k
  have hsub (S : Finset (Block A)) : spanFin C S ≤ selectedSpan E f S := by
    apply iSup_le
    intro k
    exact le_iSup_of_le k (image_mul_le _ _)
  have hblock (k : Block A) : blockSize A k ≤ (E (f k)).rank := by
    rw [← (hP k).2,← hf]
    exact Matrix.rank_mul_le_left _ _
  refine ⟨⟨f,?_⟩,?_,?_,kraus_full_span E⟩
  · intro U V hUV
    have ho := spanFin_orthogonal C U V (by
      intro k hk j hj
      apply hCorth
      intro hh
      exact (Finset.disjoint_left.mp hUV) hk (hh ▸ hj))
    have hg := geometric_bound (spanFin C U) (spanFin C V)
      (selectedSpan E f U) (selectedSpan E f V) (hsub U) (hsub V) ho
    rw [hsum,hsum] at hg
    simpa only [Nat.cast_sum] using hg
  · intro k
    exact (hblock k).trans (Finset.le_sup (f := fun i => (E i).rank) (mem_univ _))
  · intro t _ht
    let S := univ.filter (fun k : Block A => t ≤ blockSize A k)
    let T : Submodule ℂ (EuclideanSpace ℂ O) :=
      ⨆ i : {i : Fin r // t ≤ (E i).rank}, imageSpace (E i.val)
    have hle : spanFin C S ≤ T := by
      apply iSup_le
      intro k
      have hk : t ≤ (E (f k.val)).rank :=
        (mem_filter.mp k.property).2.trans (hblock k.val)
      exact (image_mul_le _ _).trans (le_iSup (fun i : {i : Fin r // t ≤ (E i).rank} =>
        imageSpace (E i.val)) ⟨f k.val,hk⟩)
    constructor
    · rw [← hsum S]
      exact Submodule.finrank_mono hle
    · have heq : T = spanFin (fun i => imageSpace (E i))
          (univ.filter (fun i => t ≤ (E i).rank)) := by
        apply le_antisymm
        · exact iSup_le fun i => le_iSup_of_le ⟨i.val,mem_filter.mpr ⟨mem_univ _,i.property⟩⟩ le_rfl
        · exact iSup_le fun i => le_iSup_of_le ⟨i.val,(mem_filter.mp i.property).2⟩ le_rfl
      change Module.finrank ℂ T ≤ _
      rw [heq]
      have hh := spanFin_dimension_le (fun i => imageSpace (E i))
        (univ.filter (fun i => t ≤ (E i).rank))
      simpa only [← rank_image] using hh

#print axioms solution
