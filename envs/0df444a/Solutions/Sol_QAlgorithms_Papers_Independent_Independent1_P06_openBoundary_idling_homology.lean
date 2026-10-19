-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.openBoundary_idling_homology
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:11:40.903569+00:00
-- url     : https://prove2.me/submissions/5124bb97-5ec3-4a71-acec-3ffd1f4e3566

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

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

private lemma cone_formula {A C : BasedBinaryComplex} (f : BasedChainMap A C) (i : ℤ) :
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

private lemma dim_homology_empty (C : BasedBinaryComplex) (i : ℤ)
    (h : ∀ c, C.degree c ≠ i) : finrank F2 (Homology C i) = 0 := by
  have : IsEmpty (Basis C i) := ⟨fun c => h c.val c.property⟩
  have hh := dim_homology C i
  have hz : finrank F2 (Basis C i → F2) = 0 := by simp
  omega

private lemma dim_bottom (C : BasedBinaryComplex) (i : ℤ)
    (h : ∀ c, C.degree c ≠ i-1) :
    finrank F2 (Homology C i) =
      finrank F2 (ker (C.differential.submatrix
        (Subtype.val : Basis C i → C.Cell)
        (Subtype.val : Basis C (i+1) → C.Cell)).transpose.mulVecLin) := by
  have : IsEmpty (Basis C (i-1)) := ⟨fun c => h c.val c.property⟩
  have hz : D C (i-1) i = 0 := by ext v r; exact isEmptyElim r
  have hh := dim_homology C i
  rw [hz,range_zero,finrank_bot,add_zero] at hh
  have ht := (C.differential.submatrix
        (Subtype.val : Basis C i → C.Cell)
        (Subtype.val : Basis C (i+1) → C.Cell)).transpose.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank,Matrix.rank_transpose] at ht
  change finrank F2 (range (D C i (i+1))) +
    finrank F2 (ker (C.differential.submatrix
      (Subtype.val : Basis C i → C.Cell)
      (Subtype.val : Basis C (i+1) → C.Cell)).transpose.mulVecLin) =
    finrank F2 (Basis C i → F2) at ht
  omega

private def dualBasis (C : BasedBinaryComplex) (s i : ℤ) :
    Basis (dualComplex s C) i ≃ Basis C (s-i) where
  toFun x := ⟨x.val,by have h := x.property; change s-C.degree x.val=i at h; omega⟩
  invFun x := ⟨x.val,by have h := x.property; change s-C.degree x.val=i; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma dual_rank (C : BasedBinaryComplex) (s i j : ℤ) :
    finrank F2 (range (D (dualComplex s C) i j)) =
      finrank F2 (range (D C (s-j) (s-i))) := by
  change ((dualComplex s C).differential.submatrix
    (Subtype.val : Basis (dualComplex s C) i → C.Cell)
    (Subtype.val : Basis (dualComplex s C) j → C.Cell)).rank =
    (C.differential.submatrix
      (Subtype.val : Basis C (s-j) → C.Cell)
      (Subtype.val : Basis C (s-i) → C.Cell)).rank
  have he : (dualComplex s C).differential.submatrix
      (Subtype.val : Basis (dualComplex s C) i → C.Cell)
      (Subtype.val : Basis (dualComplex s C) j → C.Cell) =
      (C.differential.submatrix
        (Subtype.val : Basis C (s-j) → C.Cell)
        (Subtype.val : Basis C (s-i) → C.Cell)).transpose.submatrix
        (dualBasis C s i) (dualBasis C s j) := rfl
  rw [he,Matrix.rank_submatrix,Matrix.rank_transpose]

private lemma dim_dual (C : BasedBinaryComplex) (s i : ℤ) :
    finrank F2 (Homology (dualComplex s C) i) =
      finrank F2 (Homology C (s-i)) := by
  have hd := dim_homology (dualComplex s C) i
  rw [dual_rank,dual_rank] at hd
  have hc := dim_homology C (s-i)
  have he : s-(i+1)=s-i-1 := by omega
  have hf : s-(i-1)=s-i+1 := by omega
  rw [he,hf] at hd
  have hb := (LinearEquiv.funCongrLeft F2 F2 (dualBasis C s i)).finrank_eq
  omega

private abbrev T (C : BasedBinaryComplex) (l : ℕ) (hl : 0 < l) :=
  tensorComplex (repetitionComplex l hl) C

private def node (C : BasedBinaryComplex) (l : ℕ) (hl : 0 < l)
    (v : Fin l) (c : Basis C 0) : Basis (T C l hl) 0 :=
  ⟨(.inl v,c.val),by change 0+C.degree c.val=0; omega⟩

private def memcol (C : BasedBinaryComplex) (l : ℕ) (hl : 0 < l)
    (v : Fin l) (c : Basis C 1) : Basis (T C l hl) 1 :=
  ⟨(.inl v,c.val),by change 0+C.degree c.val=1; omega⟩

private def edgecol (C : BasedBinaryComplex) (l : ℕ) (hl : 0 < l)
    (v : Fin (l-1)) (c : Basis C 0) : Basis (T C l hl) 1 :=
  ⟨(.inr v,c.val),by change 1+C.degree c.val=1; omega⟩

private def timeBasis0 (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) : Basis (T C l hl) 0 ≃ Fin l × Basis C 0 where
  toFun x := match x with
    | ⟨(.inl v,c),h⟩ => (v,⟨c,by change 0+C.degree c=0 at h; omega⟩)
    | ⟨(.inr _,c),h⟩ => False.elim (by
        have hc := (css c).1; change 1+C.degree c=0 at h; omega)
  invFun x := node C l hl x.1 x.2
  left_inv x := by
    rcases x with ⟨⟨r,c⟩,h⟩
    cases r with
    | inl v => rfl
    | inr v => have hc := (css c).1; change 1+C.degree c=0 at h; omega
  right_inv _ := rfl

private abbrev B (C : BasedBinaryComplex) :=
  C.differential.submatrix (Subtype.val : Basis C 0 → C.Cell)
    (Subtype.val : Basis C 1 → C.Cell)

open Classical in
private lemma diff_mem (C : BasedBinaryComplex) (l : ℕ) (hl : 0 < l)
    (v w : Fin l) (c : Basis C 0) (d : Basis C 1) :
    (T C l hl).differential (.inl v,c.val) (.inl w,d.val) =
      if v=w then C.differential c.val d.val else 0 := by
  classical
  let : DecidableEq (Fin l ⊕ Fin (l-1)) := Classical.decEq _
  change (Matrix.kronecker (repetitionComplex l hl).differential
    (1 : Matrix C.Cell C.Cell F2) +
    Matrix.kronecker (1 : Matrix (repetitionComplex l hl).Cell (repetitionComplex l hl).Cell F2)
      C.differential) (.inl v,c.val) (.inl w,d.val) = _
  rw [Matrix.add_apply]
  unfold Matrix.kronecker Matrix.kroneckerMap
  dsimp only [Matrix.of_apply]
  change (0 : F2) * _ + (1 : Matrix (Fin l ⊕ Fin (l-1)) (Fin l ⊕ Fin (l-1)) F2) (.inl v) (.inl w) * _ = _
  simp [Matrix.one_apply]

open Classical in
private lemma diff_edge (C : BasedBinaryComplex) (l : ℕ) (hl : 0 < l)
    (v : Fin l) (e : Fin (l-1)) (c d : Basis C 0) :
    (T C l hl).differential (.inl v,c.val) (.inr e,d.val) =
      if c=d then
        (if v=⟨e.val,by omega⟩ then 1 else 0) +
        (if v=⟨e.val+1,by omega⟩ then 1 else 0) else 0 := by
  classical
  let : DecidableEq (Fin l ⊕ Fin (l-1)) := Classical.decEq _
  change (Matrix.kronecker (repetitionComplex l hl).differential
    (1 : Matrix C.Cell C.Cell F2) +
    Matrix.kronecker (1 : Matrix (repetitionComplex l hl).Cell (repetitionComplex l hl).Cell F2)
      C.differential) (.inl v,c.val) (.inr e,d.val) = _
  rw [Matrix.add_apply]
  unfold Matrix.kronecker Matrix.kroneckerMap
  dsimp only [Matrix.of_apply]
  change (if v.val=e.val ∨ v.val=e.val+1 then (1:F2) else 0) *
    (1 : Matrix C.Cell C.Cell F2) c.val d.val +
    (1 : Matrix (Fin l ⊕ Fin (l-1)) (Fin l ⊕ Fin (l-1)) F2) (.inl v) (.inr e) * _ = _
  have hn : ¬ (v.val=e.val ∧ v.val=e.val+1) := by omega
  by_cases h : c=d
  · subst d
    simp only [Matrix.one_apply_eq,Matrix.one_apply_ne (Sum.inl_ne_inr),
      zero_mul,add_zero,ite_true,mul_one]
    simp only [Fin.ext_iff]
    rcases eq_or_ne v.val e.val with hv|hv <;>
      rcases eq_or_ne v.val (e.val+1) with hw|hw <;> simp_all
  · have hv : c.val ≠ d.val := fun hh => h (Subtype.ext hh)
    simp [h,hv]

private lemma memory_column (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) (x : Basis (T C l hl) 0 → F2)
    (v : Fin l) (c : Basis C 1) :
    (B (T C l hl)).transpose.mulVec x (memcol C l hl v c) =
      (B C).transpose.mulVec (fun r => x (node C l hl v r)) c := by
  change (∑ r, (T C l hl).differential r.val (memcol C l hl v c).val * x r) = _
  rw [← (timeBasis0 C css l hl).symm.sum_comp,Fintype.sum_prod_type]
  change (∑ w : Fin l, ∑ r : Basis C 0,
    (T C l hl).differential (.inl w,r.val) (.inl v,c.val) * x (node C l hl w r)) = _
  simp_rw [diff_mem,ite_mul,zero_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

private lemma edge_column (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) (x : Basis (T C l hl) 0 → F2)
    (e : Fin (l-1)) (c : Basis C 0) :
    (B (T C l hl)).transpose.mulVec x (edgecol C l hl e c) =
      x (node C l hl ⟨e.val,by omega⟩ c) +
      x (node C l hl ⟨e.val+1,by omega⟩ c) := by
  change (∑ r, (T C l hl).differential r.val (edgecol C l hl e c).val * x r) = _
  rw [← (timeBasis0 C css l hl).symm.sum_comp,Fintype.sum_prod_type]
  change (∑ w : Fin l, ∑ r : Basis C 0,
    (T C l hl).differential (.inl w,r.val) (.inr e,c.val) * x (node C l hl w r)) = _
  simp_rw [diff_edge,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp [add_mul,ite_mul,Finset.sum_add_distrib]

private lemma time_constant (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) (x : ker (B (T C l hl)).transpose.mulVecLin)
    (v : Fin l) (c : Basis C 0) :
    x.val (node C l hl v c) = x.val (node C l hl ⟨0,hl⟩ c) := by
  have hs : ∀ a, ∀ ha : a+1 < l,
      x.val (node C l hl ⟨a+1,ha⟩ c) = x.val (node C l hl ⟨a,by omega⟩ c) := by
    intro a ha
    have he := congrFun x.property (edgecol C l hl ⟨a,by omega⟩ c)
    change (B (T C l hl)).transpose.mulVec x.val (edgecol C l hl ⟨a,by omega⟩ c) = 0 at he
    rw [edge_column C css l hl] at he
    change _ + _ = 0 at he
    exact ((eq_neg_of_add_eq_zero_left he).trans (CharTwo.neg_eq _)).symm
  rcases v with ⟨v,hv⟩
  induction v with
  | zero => rfl
  | succ v ih => exact (hs v hv).trans (ih (by omega))

private def evalCocycle (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) :
    ker (B (T C l hl)).transpose.mulVecLin →ₗ[F2] ker (B C).transpose.mulVecLin where
  toFun x := ⟨fun c => x.val (node C l hl ⟨0,hl⟩ c),by
    ext c
    have he := congrFun x.property (memcol C l hl ⟨0,hl⟩ c)
    exact (memory_column C css l hl x.val ⟨0,hl⟩ c).symm.trans he⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma evalCocycle_bijective (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) : Function.Bijective (evalCocycle C css l hl) := by
  constructor
  · intro x y h
    apply Subtype.ext
    funext r
    let v := (timeBasis0 C css l hl r).1
    let c := (timeBasis0 C css l hl r).2
    have hr : r = node C l hl v c :=
      ((timeBasis0 C css l hl).symm_apply_apply r).symm
    rw [hr,time_constant C css l hl x,time_constant C css l hl y]
    exact congrFun (congrArg Subtype.val h) c
  · intro z
    let x : Basis (T C l hl) 0 → F2 := fun r => z.val (timeBasis0 C css l hl r).2
    have hx : x ∈ ker (B (T C l hl)).transpose.mulVecLin := by
      ext r
      rcases r with ⟨⟨r,c⟩,h⟩
      cases r with
      | inl v =>
        have hc : C.degree c = 1 := by change 0+C.degree c=1 at h; omega
        change (B (T C l hl)).transpose.mulVec x (memcol C l hl v ⟨c,hc⟩) = 0
        rw [memory_column C css l hl]
        exact congrFun z.property ⟨c,hc⟩
      | inr e =>
        have hc : C.degree c = 0 := by change 1+C.degree c=1 at h; omega
        change (B (T C l hl)).transpose.mulVec x (edgecol C l hl e ⟨c,hc⟩) = 0
        rw [edge_column C css l hl]
        exact CharTwo.add_self_eq_zero _
    exact ⟨⟨x,hx⟩,rfl⟩

private lemma dim_bulk0 (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) :
    finrank F2 (Homology (T C l hl) 0) = finrank F2 (Homology C 0) := by
  rw [dim_bottom (T C l hl) 0 (by
    rintro ⟨r,c⟩ h; have hc := (css c).1
    cases r with
    | inl v => change 0+C.degree c=0-1 at h; omega
    | inr e => change 1+C.degree c=0-1 at h; omega),
    dim_bottom C 0 (by intro c h; have hc := (css c).1; omega)]
  exact (LinearEquiv.ofBijective (evalCocycle C css l hl)
    (evalCocycle_bijective C css l hl)).finrank_eq
private def cone0Basis (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) :
    Basis (mappingCone (temporalEntryMap C css l hl)) 0 ≃ Basis (T C l hl) 0 where
  toFun x := match x with
    | ⟨.inl r,h⟩ => ⟨r,h⟩
    | ⟨.inr a,h⟩ => False.elim (by change (0:ℤ)+1=0 at h; omega)
  invFun x := ⟨.inl x.val,x.property⟩
  left_inv x := by
    rcases x with ⟨r,h⟩; cases r with
    | inl r => rfl
    | inr a => change (0:ℤ)+1=0 at h; omega
  right_inv _ := rfl

private lemma dim_open0 (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) :
    finrank F2 (Homology (mappingCone (temporalEntryMap C css l hl)) 0) = 0 := by
  classical
  let f := temporalEntryMap C css l hl
  let M := mappingCone f
  rw [dim_bottom M 0 (by
    intro r h
    cases r with
    | inl r =>
      rcases r with ⟨r,c⟩
      have hc := (css c).1
      cases r with
      | inl v => change 0+C.degree c=0-1 at h; omega
      | inr e => change 1+C.degree c=0-1 at h; omega
    | inr a => change (0:ℤ)+1=0-1 at h; omega)]
  have hk : ker (B M).transpose.mulVecLin = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    change z = 0
    let x : Basis (T C l hl) 0 → F2 := fun r => z ((cone0Basis C css l hl).symm r)
    have hx : x ∈ ker (B (T C l hl)).transpose.mulVecLin := by
      ext c
      have he := congrFun hz (⟨.inl c.val,c.property⟩ : Basis M 1)
      change (∑ r : Basis M 0, M.differential r.val (.inl c.val)*z r) = 0 at he
      rw [← (cone0Basis C css l hl).symm.sum_comp] at he
      exact he
    have hzero : ∀ c : Basis C 0, x (node C l hl ⟨0,hl⟩ c) = 0 := by
      intro c
      have he := congrFun hz (⟨.inr (false,c),rfl⟩ : Basis M 1)
      change (∑ r : Basis M 0, M.differential r.val (.inr (false,c))*z r) = 0 at he
      rw [← (cone0Basis C css l hl).symm.sum_comp] at he
      change (∑ r : Basis (T C l hl) 0, f.matrix r.val (false,c)*x r) = 0 at he
      have hm : ∀ r : Basis (T C l hl) 0, f.matrix r.val (false,c) =
          if r = node C l hl ⟨0,hl⟩ c then 1 else 0 := by
        intro r
        change (if r.val = (Sum.inl ⟨0,hl⟩,c.val) then (1:F2) else 0) = _
        simp only [Subtype.ext_iff,node]
        rfl
      simp_rw [hm] at he
      simpa using he
    funext r
    have ht := time_constant C css l hl ⟨x,hx⟩
      (timeBasis0 C css l hl ((cone0Basis C css l hl) r)).1
      (timeBasis0 C css l hl ((cone0Basis C css l hl) r)).2
    change x ((timeBasis0 C css l hl).symm
      ((timeBasis0 C css l hl) ((cone0Basis C css l hl) r))) =
      x (node C l hl ⟨0,hl⟩ ((timeBasis0 C css l hl) ((cone0Basis C css l hl) r)).2) at ht
    rw [Equiv.symm_apply_apply,hzero] at ht
    simpa only [x,Equiv.symm_apply_apply,Pi.zero_apply] using ht
  change finrank F2 (ker (B M).transpose.mulVecLin) = 0
  rw [hk,finrank_bot]

private lemma dim_entry0 (C : BasedBinaryComplex) :
    finrank F2 (Homology (entryComplex C) 0) = 2 * Fintype.card (Basis C 0) := by
  have hr (i j : ℤ) : finrank F2 (range (D (entryComplex C) i j)) = 0 := by
    change (0 : Matrix (Basis (entryComplex C) i) (Basis (entryComplex C) j) F2).rank = 0
    exact Matrix.rank_zero
  have hd := dim_homology (entryComplex C) 0
  rw [hr,hr,add_zero,add_zero] at hd
  rw [hd,Module.finrank_pi]
  have he : Basis (entryComplex C) 0 ≃ Bool × Basis C 0 :=
    { toFun := Subtype.val
      invFun := fun a => ⟨a,rfl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr he,Fintype.card_prod,Fintype.card_bool]

private lemma dim_image_entry (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) (i : ℤ) (hi : i ≠ 0) :
    finrank F2 (homologyImage (temporalEntryMap C css l hl) i) = 0 := by
  have : IsEmpty (Basis (entryComplex C) i) := ⟨fun c => hi (by
    have h := c.property; change (0:ℤ)=i at h; exact h.symm)⟩
  have he : (component (temporalEntryMap C css l hl) i).mulVecLin = 0 := by
    ext v r
    simp [Matrix.mulVec,dotProduct]
  unfold homologyImage
  rw [he,LinearMap.zero_comp,range_zero,Submodule.comap_bot,
    LinearMap.ker_eq_bot.mpr (cycles (T C l hl) i).injective_subtype,
    Submodule.map_bot,finrank_bot]
private lemma x_result (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) :
    (finrank F2 (Homology (mappingCone (temporalEntryMap C css l hl)) 1) +
      finrank F2 (Homology C 0) =
      finrank F2 (Homology (T C l hl) 1) + 2 * Fintype.card (Basis C 0)) ∧
    finrank F2 (Homology (mappingCone (temporalEntryMap C css l hl)) 0) = 0 := by
  have h0 := cone_formula (temporalEntryMap C css l hl) 0
  have h1 := cone_formula (temporalEntryMap C css l hl) 1
  have hm := dim_image_entry C css l hl (-1) (by decide)
  have hp := dim_image_entry C css l hl 1 (by decide)
  have he := dim_homology_empty (entryComplex C) (-1) (by intro c; change (0:ℤ)≠ -1; decide)
  have hz := dim_open0 C css l hl
  have hb := dim_bulk0 C css l hl
  have ha := dim_entry0 C
  rw [show (0:ℤ)-1 = -1 by omega] at h0
  rw [show (1:ℤ)-1 = 0 by omega] at h1
  rw [hm,he,hz,zero_add,add_zero,add_zero] at h0
  rw [hp,add_zero,ha,h0,hb] at h1
  exact ⟨h1,hz⟩

theorem solution (C : Surgery.BasedBinaryComplex)
    (css : Surgery.IsCSSComplex C) (l : ℕ) (positive : 0 < l) :
    let F := Surgery.tensorComplex (Surgery.repetitionComplex l positive) C
    let FX := Surgery.openIdlingVolume C css l positive .X
    let FZ := Surgery.openIdlingVolume C css l positive .Z
    let Fdual := Surgery.dualComplex 3
      (Surgery.tensorComplex (Surgery.repetitionComplex l positive) (Surgery.dualComplex 2 C))
    (Module.finrank F2 (Surgery.Homology FX 1) + Module.finrank F2 (Surgery.Homology C 0) =
      Module.finrank F2 (Surgery.Homology F 1) + 2 * Fintype.card (Surgery.Basis C 0)) ∧
    Module.finrank F2 (Surgery.Homology FX 0) = 0 ∧
    (Module.finrank F2 (Surgery.Homology FZ 2) + Module.finrank F2 (Surgery.Homology C 2) =
      Module.finrank F2 (Surgery.Homology Fdual 2) + 2 * Fintype.card (Surgery.Basis C 2)) ∧
    Module.finrank F2 (Surgery.Homology FZ 3) = 0 := by
  let cssD : IsCSSComplex (dualComplex 2 C) := fun c => by
    have hc := css c
    dsimp [dualComplex]
    omega
  have hx := x_result C css l positive
  have hz := x_result (dualComplex 2 C) cssD l positive
  have hc := dim_dual C 2 0
  have hf := dim_dual (T (dualComplex 2 C) l positive) 3 2
  have hz2 := dim_dual (mappingCone (temporalEntryMap (dualComplex 2 C) cssD l positive)) 3 2
  have hz3 := dim_dual (mappingCone (temporalEntryMap (dualComplex 2 C) cssD l positive)) 3 3
  have hcard := Fintype.card_congr (dualBasis C 2 0)
  rw [show (2:ℤ)-0=2 by omega] at hc hcard
  rw [show (3:ℤ)-2=1 by omega] at hf hz2
  rw [show (3:ℤ)-3=0 by omega] at hz3
  dsimp only
  refine ⟨hx.1,hx.2,?_,?_⟩
  · change finrank F2 (Homology (dualComplex 3
      (mappingCone (temporalEntryMap (dualComplex 2 C) cssD l positive))) 2) + _ = _
    rw [hz2,← hc,hf,← hcard]
    exact hz.1
  · exact hz3.trans hz.2

#print axioms solution
