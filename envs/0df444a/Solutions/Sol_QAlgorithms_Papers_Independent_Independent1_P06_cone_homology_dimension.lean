-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.cone_homology_dimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:51:36.998271+00:00
-- url     : https://prove2.me/submissions/210fcde9-b8a6-4932-ba5a-993fb3fba4d0

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Module LinearMap
open QAlgorithms QAlgorithms.Surgery
open QAlgorithms.Papers.Independent.Independent1.P06

private lemma dim_comap {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (P Q : Submodule K V) (h : Q ≤ P) :
    finrank K (Q.comap P.subtype) = finrank K Q :=
  (Submodule.comapSubtypeEquivOfLe h).finrank_eq

private lemma dim_map {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (g : V →ₗ[K] W) (S : Submodule K V) :
    finrank K (S.map g) + finrank K ((ker g).comap S.subtype) = finrank K S := by
  have h := (g.comp S.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  exact h

private lemma dim_quot_image {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B S : Submodule K V) :
    finrank K (S.map B.mkQ) + finrank K B = finrank K ↥(B ⊔ S) := by
  have h := dim_map B.mkQ (B ⊔ S)
  rw [Submodule.ker_mkQ, dim_comap (B ⊔ S) B le_sup_left] at h
  have he : (B ⊔ S).map B.mkQ = S.map B.mkQ := by
    rw [Submodule.map_sup]
    simp
  rw [he] at h
  exact h

private def block {K V A X B : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
    [AddCommGroup X] [Module K X] [AddCommGroup B] [Module K B]
    (d : V →ₗ[K] X) (f : A →ₗ[K] X) (b : A →ₗ[K] B) :
    V × A →ₗ[K] X × B :=
  ((d.comp (fst K V A)) + (f.comp (snd K V A))).prod (b.comp (snd K V A))

/-- Project the block image to its second coordinate; its kernel is the indicated sum. -/
private lemma dim_block {K V A X B : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
    [AddCommGroup X] [Module K X] [AddCommGroup B] [Module K B]
    [FiniteDimensional K V] [FiniteDimensional K A]
    [FiniteDimensional K X] [FiniteDimensional K B]
    (d : V →ₗ[K] X) (f : A →ₗ[K] X) (b : A →ₗ[K] B) :
    finrank K (range (block d f b)) = finrank K (range b) +
      finrank K ↥(range d ⊔ (ker b).map f) := by
  let R := range (block d f b)
  let p := (snd K X B).domRestrict R
  have hr : range p = range b := by
    ext y
    constructor
    · rintro ⟨⟨z, ⟨⟨v,a⟩, rfl⟩⟩, rfl⟩
      exact ⟨a,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨⟨block d f b (0,a), ⟨(0,a),rfl⟩⟩,rfl⟩
  let S := range d ⊔ (ker b).map f
  let g : ker p →ₗ[K] S :=
    { toFun := fun z => ⟨z.val.val.1, by
        rcases z.val.property with ⟨⟨v,a⟩,ha⟩
        have hba : b a = 0 := by
          have hz := z.property
          change z.val.val.2 = 0 at hz
          simpa [block, ← ha] using hz
        have hs : d v + f a ∈ S := Submodule.add_mem_sup ⟨v,rfl⟩ ⟨a,hba,rfl⟩
        simpa [S, block, ← ha] using hs⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e : ker p ≃ₗ[K] S := LinearEquiv.ofBijective g
    ⟨by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val h
      · exact x.property.trans y.property.symm,
     by
      rintro ⟨x,hx⟩
      rcases Submodule.mem_sup.mp hx with ⟨u,⟨v,rfl⟩,w,⟨a,ha,rfl⟩,he⟩
      refine ⟨⟨⟨block d f b (v,a),⟨(v,a),rfl⟩⟩,?_⟩,?_⟩
      · change b a = 0
        exact ha
      · exact Subtype.ext he⟩
  have h := p.finrank_range_add_finrank_ker
  rw [hr,e.finrank_eq] at h
  exact h.symm

private def D (C : BasedBinaryComplex) (j k : ℤ) :
    (Basis C k → F2) →ₗ[F2] (Basis C j → F2) :=
  (C.differential.submatrix (Subtype.val : Basis C j → C.Cell)
    (Subtype.val : Basis C k → C.Cell)).mulVecLin

private lemma sum_grade {T : Type*} [Fintype T] (deg : T → ℤ) (j : ℤ)
    (g : T → F2) (h : ∀ t, g t ≠ 0 → deg t = j) :
    ∑ t : {t // deg t = j}, g t = ∑ t, g t := by
  classical
  have he := Fintype.sum_subtype_add_sum_subtype (fun t => deg t = j) g
  have hz : ∑ t : {t // ¬ deg t = j}, g t = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    by_contra hn
    exact t.property (h t hn)
  rwa [hz,add_zero] at he

/-- Restrict the square-zero differential to the three consecutive graded bases. -/
private lemma dd (C : BasedBinaryComplex) (i : ℤ) :
    (D C (i-1) i).comp (D C i (i+1)) = 0 := by
  unfold D
  rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_zero]
  congr 1
  ext r c
  rw [Matrix.mul_apply]
  change (∑ t : Basis C i, C.differential r t * C.differential t c) = 0
  rw [sum_grade C.degree i (fun t : C.Cell => C.differential r.val t * C.differential t c.val) (by
    intro t ht
    have h1 : C.differential r t ≠ 0 := (mul_ne_zero_iff.mp ht).1
    have h2 := C.lowers r t h1
    have h3 := r.property
    omega)]
  exact congrFun (congrFun C.square r) c

private lemma dcycle (C : BasedBinaryComplex) (i : ℤ) :
    range (D C i (i+1)) ≤ cycles C i := by
  rintro _ ⟨v,rfl⟩
  change D C (i-1) i (D C i (i+1) v) = 0
  exact congrArg (fun g => g v) (dd C i)

private lemma dim_homology (C : BasedBinaryComplex) (i : ℤ) :
    finrank F2 (Homology C i) + finrank F2 (range (D C i (i+1))) +
      finrank F2 (range (D C (i-1) i)) = finrank F2 (Basis C i → F2) := by
  have hq := (boundaries C i).finrank_quotient_add_finrank
  change finrank F2 (Homology C i) +
    finrank F2 ((range (D C i (i+1))).comap (cycles C i).subtype) =
      finrank F2 (cycles C i) at hq
  rw [dim_comap _ _ (dcycle C i)] at hq
  have hd := (D C (i-1) i).finrank_range_add_finrank_ker
  change _ + finrank F2 (cycles C i) = _ at hd
  omega

private lemma fmap_cycles {A C : BasedBinaryComplex} (f : BasedChainMap A C) (i : ℤ) :
    (cycles A i).map (component f i).mulVecLin ≤ cycles C i := by
  rintro _ ⟨v,hv,rfl⟩
  have hm : (D C (i-1) i).comp (component f i).mulVecLin =
      (f.matrix.submatrix (Subtype.val : Basis C (i-1) → C.Cell)
        (Subtype.val : Basis A (i-1) → A.Cell)).mulVecLin.comp (D A (i-1) i) := by
    unfold D
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul]
    congr 1
    ext r c
    change (∑ t : Basis C i, C.differential r t * f.matrix t c) =
      ∑ t : Basis A (i-1), f.matrix r t * A.differential t c
    rw [sum_grade C.degree i (fun t : C.Cell => C.differential r.val t * f.matrix t c.val) (by
      intro t ht
      have hd := C.lowers r t (mul_ne_zero_iff.mp ht).1
      have hr := r.property
      omega)]
    rw [sum_grade A.degree (i-1) (fun t : A.Cell => f.matrix r.val t * A.differential t c.val) (by
      intro t ht
      have hd := A.lowers t c (mul_ne_zero_iff.mp ht).2
      have hc := c.property
      omega)]
    exact congrFun (congrFun f.commutes r) c
  change D C (i-1) i ((component f i).mulVecLin v) = 0
  have he := congrArg (fun g => g v) hm
  change D A (i-1) i v = 0 at hv
  simpa [hv] using he

/-- The induced homology image is the cycle image modulo the original boundaries. -/
private lemma dim_image (A C : BasedBinaryComplex) (f : BasedChainMap A C) (i : ℤ) :
    finrank F2 (homologyImage f i) + finrank F2 (range (D C i (i+1))) =
      finrank F2 ↥(range (D C i (i+1)) ⊔ (cycles A i).map (component f i).mulVecLin) := by
  let Z := cycles C i
  let B := range (D C i (i+1))
  let S := (cycles A i).map (component f i).mulVecLin
  have hb : B ≤ Z := dcycle C i
  have hs : S ≤ Z := fmap_cycles f i
  have hi : homologyImage f i =
      (S.comap Z.subtype).map (B.comap Z.subtype).mkQ := by
    unfold homologyImage
    rw [LinearMap.range_comp,Submodule.range_subtype]
    rfl
  have he : ((B.comap Z.subtype) ⊔ (S.comap Z.subtype)).map Z.subtype = B ⊔ S := by
    rw [Submodule.map_sup,Submodule.map_comap_subtype,Submodule.map_comap_subtype,
      inf_eq_right.mpr hb,inf_eq_right.mpr hs]
  have hd := dim_quot_image (B.comap Z.subtype) (S.comap Z.subtype)
  rw [← hi,dim_comap _ _ hb] at hd
  have heq := Submodule.finrank_map_subtype_eq Z ((B.comap Z.subtype) ⊔ (S.comap Z.subtype))
  rw [he] at heq
  exact hd.trans heq.symm

/-- Split each graded cone coordinate into its original and shifted auxiliary parts. -/
private def coneBasis {A C : BasedBinaryComplex} (f : BasedChainMap A C) (i : ℤ) :
    Basis (mappingCone f) i ≃ Basis C i ⊕ Basis A (i-1) where
  toFun x := match x with
    | ⟨.inl c,h⟩ => .inl ⟨c,h⟩
    | ⟨.inr a,h⟩ => .inr ⟨a,by change A.degree a+1=i at h; omega⟩
  invFun x := match x with
    | .inl c => ⟨.inl c.val,c.property⟩
    | .inr a => ⟨.inr a.val,by change A.degree a.val+1=i; have h:=a.property; omega⟩
  left_inv x := by rcases x with ⟨x,h⟩; cases x <;> rfl
  right_inv x := by cases x <;> rfl

private def splitCone {A C : BasedBinaryComplex} (f : BasedChainMap A C) (i : ℤ) :
    (Basis (mappingCone f) i → F2) ≃ₗ[F2]
      (Basis C i → F2) × (Basis A (i-1) → F2) :=
  (LinearEquiv.funCongrLeft F2 F2 (coneBasis f i).symm).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ F2 F2)

private lemma split_d {A C : BasedBinaryComplex} (f : BasedChainMap A C) (i : ℤ) :
    (splitCone f (i-1)).toLinearMap.comp (D (mappingCone f) (i-1) i) =
      (block (D C (i-1) i) (component f (i-1)).mulVecLin (D A (i-1-1) (i-1))).comp
        (splitCone f i).toLinearMap := by
  ext v : 1
  apply Prod.ext
  · funext r
    change (∑ t : Basis (mappingCone f) i,
      (mappingCone f).differential (.inl r.val) t.val * v t) = _
    rw [← (coneBasis f i).symm.sum_comp]
    rw [Fintype.sum_sum_type]
    rfl
  · funext r
    change (∑ t : Basis (mappingCone f) i,
      (mappingCone f).differential (.inr r.val) t.val * v t) = _
    rw [← (coneBasis f i).symm.sum_comp]
    rw [Fintype.sum_sum_type]
    have hz : (∑ a : Basis C i,
        (mappingCone f).differential (.inr r.val) ((coneBasis f i).symm (.inl a)).val *
          v ((coneBasis f i).symm (.inl a))) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      change (0 : F2) * _ = 0
      exact zero_mul _
    rw [hz,zero_add]
    rfl

private lemma dim_split_range {K V W X Y : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (e : V ≃ₗ[K] X) (g : W ≃ₗ[K] Y) (a : V →ₗ[K] W) (b : X →ₗ[K] Y)
    (h : g.toLinearMap.comp a = b.comp e.toLinearMap) :
    finrank K (range a) = finrank K (range b) := by
  have hr := congrArg LinearMap.range h
  rw [LinearMap.range_comp,LinearMap.range_comp_of_range_eq_top b (by simp)] at hr
  rw [← hr]
  exact (LinearEquiv.finrank_map_eq g (range a)).symm

private lemma dim_cone_boundary {A C : BasedBinaryComplex} (f : BasedChainMap A C) (i : ℤ) :
    finrank F2 (range (D (mappingCone f) (i-1) i)) =
      finrank F2 (range (D A (i-1-1) (i-1))) +
      finrank F2 (range (D C (i-1) i)) + finrank F2 (homologyImage f (i-1)) := by
  rw [dim_split_range (splitCone f i) (splitCone f (i-1)) _ _ (split_d f i), dim_block]
  have h := dim_image A C f (i-1)
  have he : i-1+1=i := by omega
  rw [he] at h
  change finrank F2 (range (D A (i-1-1) (i-1))) +
    finrank F2 ↥(range (D C (i-1) i) ⊔ (cycles A (i-1)).map (component f (i-1)).mulVecLin) = _
  omega

theorem solution {A C : BasedBinaryComplex} (f : BasedChainMap A C) (i : ℤ) :
    finrank F2 (Homology (mappingCone f) i) + finrank F2 (homologyImage f i) +
      finrank F2 (homologyImage f (i-1)) =
    finrank F2 (Homology C i) + finrank F2 (Homology A (i-1)) := by
  -- Rank-nullity in the three complexes, with the two adjacent block-rank identities.
  have hcone := dim_homology (mappingCone f) i
  have hC := dim_homology C i
  have hA := dim_homology A (i-1)
  have hb := dim_cone_boundary f i
  have hu := dim_cone_boundary f (i+1)
  have he : i+1-1=i := by omega
  have ha : i-1+1=i := by omega
  rw [he] at hu
  rw [ha] at hA
  have hc := (splitCone f i).finrank_eq
  rw [Module.finrank_prod] at hc
  omega

#print axioms solution
