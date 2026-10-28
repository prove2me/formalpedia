-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.entropyThreshold_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:47:16.351457+00:00
-- url     : https://prove2.me/submissions/02aae6c0-3148-4a70-bfd3-d24cc789f531

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P38_strongSubadditivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq
namespace X9Supermodular

private def reindexStar {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro A; exact Matrix.conjTranspose_reindex e e A
    map_smul' := by intros; rfl }

private lemma entropy_reindex {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (A : Matrix I I ℂ) :
    vnEntropy (Matrix.reindex e e A) = vnEntropy A := by
  let f : ℝ → ℝ := fun x => x * Real.logb 2 x
  let phi := reindexStar e
  have ht (B : Matrix I I ℂ) : (phi B).trace = B.trace :=
    Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  have hc : cfc f (phi A) = phi (cfc f A) := by
    by_cases hA : A.IsHermitian
    · have hphiA : (phi A).IsHermitian := hA.submatrix e.symm
      have hf : Continuous f := by
        simpa [f, Real.logb, mul_div_assoc] using
          Real.continuous_mul_log.div_const (Real.log 2)
      exact (StarAlgHomClass.map_cfc (S := ℂ) phi f A hf.continuousOn
        (by change Continuous (fun B : Matrix I I ℂ => B.submatrix e.symm e.symm); fun_prop)
        hA hphiA).symm
    · have hphiA : ¬ (phi A).IsHermitian := by
        intro h
        apply hA
        have hh := h.submatrix e
        convert hh using 1 <;> ext i j <;> simp [phi, reindexStar, Matrix.submatrix]
      have hz : cfc f A = 0 := cfc_apply_of_not_predicate A hA
      have hz' : cfc f (phi A) = 0 := cfc_apply_of_not_predicate (phi A) hphiA
      exact hz'.trans ((map_zero phi).symm.trans (congrArg phi hz.symm))
  change -(cfc f (phi A)).trace.re = -(cfc f A).trace.re
  rw [hc, ht]

private def red {X A : Type} [Fintype X] (rho : Matrix X X ℂ)
    (keep : X → A) (rel : X → X → Prop) : Matrix A A ℂ :=
  fun a b => ∑ x, ∑ y, if keep x = a ∧ keep y = b ∧ rel x y then rho x y else 0

private lemma fiberEquiv {X A B : Type} (f : X → A) (g : X → B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ x y, f x = f y ↔ g x = g y) :
    ∃ e : A ≃ B, ∀ x, e (f x) = g x := by
  let sec : A → X := fun a => Classical.choose (hf a)
  have hs (a : A) : f (sec a) = a := Classical.choose_spec (hf a)
  let k : A → B := g ∘ sec
  have hk (x : X) : k (f x) = g x := (h _ _).mp (hs (f x))
  have hinj : Function.Injective k := by
    intro a b hab
    have := (h (sec a) (sec b)).mpr hab
    simpa only [hs] using this
  have hsurj : Function.Surjective k := by
    intro b
    obtain ⟨x,rfl⟩ := hg b
    exact ⟨f x,hk x⟩
  exact ⟨Equiv.ofBijective k ⟨hinj,hsurj⟩,hk⟩

private lemma red_entropy {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (e : X ≃ Y) (rho : Matrix X X ℂ)
    (f : X → A) (g : Y → B) (r : X → X → Prop) (s : Y → Y → Prop)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hkeep : ∀ x y, f x = f y ↔ g (e x) = g (e y))
    (hrel : ∀ x y, r x y ↔ s (e x) (e y)) :
    vnEntropy (red rho f r) =
      vnEntropy (red (Matrix.reindex e e rho) g s) := by
  obtain ⟨a,ha⟩ := fiberEquiv f (g ∘ e) hf (hg.comp e.surjective) hkeep
  dsimp only [Function.comp_def] at ha
  have heq : Matrix.reindex a a (red rho f r) =
      red (Matrix.reindex e e rho) g s := by
    ext i j
    change red rho f r (a.symm i) (a.symm j) = _
    unfold red
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro y _
    have hi : f x = a.symm i ↔ g (e x) = i := by
      rw [← ha x, ← Equiv.apply_eq_iff_eq_symm_apply]
    have hj : f y = a.symm j ↔ g (e y) = j := by
      rw [← ha y, ← Equiv.apply_eq_iff_eq_symm_apply]
    simp only [hi,hj,hrel,Matrix.reindex_apply,Equiv.symm_apply_apply,Matrix.submatrix_apply]
  convert (entropy_reindex a (red rho f r)).symm.trans (congrArg vnEntropy heq) using 1

private def keepReg {n : ℕ} {D : Fin n → Type} {E : Type} (s : Finset (Fin n))
    (x : RegisterBasis D × E) : SubBasis D s × E := (fun i => x.1 i.val,x.2)

private def outside {n : ℕ} {D : Fin n → Type} {E : Type} (s : Finset (Fin n))
    (x y : RegisterBasis D × E) : Prop := ∀ i, i ∉ s → x.1 i = y.1 i

private lemma keepReg_surj {n : ℕ} {D : Fin n → Type} [∀ i, Nonempty (D i)]
    {E : Type} (s : Finset (Fin n)) :
    Function.Surjective (@keepReg n D E s) := by
  rintro ⟨a,e⟩
  refine ⟨(fun i => if h : i ∈ s then a ⟨i,h⟩ else Classical.choice inferInstance,e),?_⟩
  apply Prod.ext
  · funext i; simp [keepReg,i.property]
  · rfl

private lemma register_red {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    {E : Type} [Fintype E] (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Finset (Fin n)) : registerMarginal rho s = red rho (keepReg s) (outside s) := by
  ext a b
  unfold registerMarginal red
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Eq.symm
  have hh (x y : RegisterBasis D) (e e' : E) :
      keepReg s (x,e) = a ∧ keepReg s (y,e') = b ∧ outside s (x,e) (y,e') ↔
      e = a.2 ∧ e' = b.2 ∧
        (∀ i (hi : i ∈ s), x i = a.1 ⟨i,hi⟩ ∧ y i = b.1 ⟨i,hi⟩) ∧
        (∀ i, i ∉ s → x i = y i) := by
    simp only [keepReg, Prod.ext_iff, funext_iff, Subtype.forall, outside]
    aesop
  simp only [hh,ite_and,Finset.sum_ite_irrel,Finset.sum_ite_eq,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_const_zero]
  rw [Finset.sum_comm]

private def restrict {n : ℕ} {I : Fin n → Type} (s : Finset (Fin n))
    (x : ∀ i, I i) : (i : {i // i ∈ s}) → I i.val := fun i => x i.val

private lemma restrict_surj {n : ℕ} {I : Fin n → Type} [∀ i, Nonempty (I i)]
    (s : Finset (Fin n)) : Function.Surjective (@restrict n I s) := by
  intro a
  refine ⟨(fun i => if h : i ∈ s then a ⟨i,h⟩ else Classical.choice inferInstance),?_⟩
  funext i; simp [restrict,i.property]

private lemma subsystem_red {n : ℕ} (I : Fin n → Type) [∀ i, Fintype (I i)]
    (rho : Matrix (∀ i, I i) (∀ i, I i) ℂ) (s : Finset (Fin n)) :
    QAlgorithms.Papers.Independent.Gap48.P38.subsystemReduction I rho s =
      red rho (restrict s) (fun x y => ∀ i, i ∉ s → x i = y i) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) I
  ext a b
  unfold red
  rw [← Equiv.sum_comp e.symm]
  simp only [Fintype.sum_prod_type]
  have hkeep (x) : restrict s (e.symm x) = x.1 := by
    funext i; simp [restrict,e,i.property]
  have hrel (x y) : (∀ i, i ∉ s → e.symm x i = e.symm y i) ↔ x.2 = y.2 := by
    simp only [funext_iff, Subtype.forall]
    constructor <;> intro h i hi
    · simpa [e,Equiv.piEquivPiSubtypeProd,hi] using h i hi
    · simpa [e,Equiv.piEquivPiSubtypeProd,hi] using h i hi
  conv_rhs =>
    arg 2
    ext x
    arg 2
    ext z
    rw [← Equiv.sum_comp e.symm]
  simp only [Fintype.sum_prod_type,hkeep,hrel]
  simp only [ite_and,Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,if_true,Finset.sum_const_zero]
  change (∑ z, rho
    (QAlgorithms.Papers.Independent.Gap48.P38.subsystemIndex I s a z)
    (QAlgorithms.Papers.Independent.Gap48.P38.subsystemIndex I s b z)) = _
  let c : {i : Fin n // i ∈ Finset.univ \ s} ≃ {i : Fin n // i ∉ s} :=
    Equiv.subtypeEquivRight (by intro i; simp)
  let ec := Equiv.piCongrLeft (fun i : {i : Fin n // i ∉ s} => I i.val) c
  apply Fintype.sum_equiv ec
  intro z
  rw [Finset.sum_eq_single b]
  · simp only [if_pos rfl]
    rw [Finset.sum_eq_single (ec z)]
    · simp only [if_pos rfl]
      congr 2 <;> funext i <;> by_cases hi : i ∈ s <;>
        simp [e, Equiv.piEquivPiSubtypeProd,
          QAlgorithms.Papers.Independent.Gap48.P38.subsystemIndex,hi,ec,c]
    · intro v _ hv
      simp only [if_neg (Ne.symm hv),ite_self]
    · simp
  · intro u _ hu
    simp only [if_neg hu,Finset.sum_const_zero]
  · simp

private def groups {n : ℕ} (D : Fin n → Type) (E : Type) (K L : Finset (Fin n)) :
    Fin 4 → Type := ![SubBasis D (K ∪ L)ᶜ, SubBasis D (K ∩ L) × E,
      SubBasis D (K \ L), SubBasis D (L \ K)]

private instance groups_fintype {n : ℕ} (D : Fin n → Type) [∀ i, Fintype (D i)]
    (E : Type) [Fintype E] (K L : Finset (Fin n)) (i : Fin 4) :
    Fintype (groups D E K L i) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
    (fun l => Fin.cases ?_ (fun z => Fin.elim0 z) l) k) j) i <;>
    dsimp [groups] <;> infer_instance

private instance groups_nonempty {n : ℕ} (D : Fin n → Type) [∀ i, Nonempty (D i)]
    (E : Type) [Nonempty E] (K L : Finset (Fin n)) (i : Fin 4) :
    Nonempty (groups D E K L i) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
    (fun l => Fin.cases ?_ (fun z => Fin.elim0 z) l) k) j) i <;>
    dsimp [groups] <;> infer_instance

private def group {n : ℕ} {D : Fin n → Type} {E : Type} (K L : Finset (Fin n))
    (x : RegisterBasis D × E) : ∀ i, groups D E K L i := by
  exact Fin.cases (fun j => x.1 j.val)
    (Fin.cases ((fun j => x.1 j.val),x.2)
      (Fin.cases (fun j => x.1 j.val) (Fin.cases (fun j => x.1 j.val) (fun z => Fin.elim0 z))))

@[simp] private lemma group_zero {n : ℕ} {D : Fin n → Type} {E : Type}
    (K L : Finset (Fin n)) (x : RegisterBasis D × E) :
    group K L x 0 = (fun j : {j // j ∈ (K ∪ L)ᶜ} => x.1 j.val) := rfl
@[simp] private lemma group_one {n : ℕ} {D : Fin n → Type} {E : Type}
    (K L : Finset (Fin n)) (x : RegisterBasis D × E) :
    group K L x 1 = keepReg (K ∩ L) x := rfl
@[simp] private lemma group_two {n : ℕ} {D : Fin n → Type} {E : Type}
    (K L : Finset (Fin n)) (x : RegisterBasis D × E) :
    group K L x 2 = (fun j : {j // j ∈ K \ L} => x.1 j.val) := rfl
@[simp] private lemma group_three {n : ℕ} {D : Fin n → Type} {E : Type}
    (K L : Finset (Fin n)) (x : RegisterBasis D × E) :
    group K L x 3 = (fun j : {j // j ∈ L \ K} => x.1 j.val) := rfl

private lemma group_eq {n : ℕ} {D : Fin n → Type} {E : Type} (K L : Finset (Fin n))
    (x y : RegisterBasis D × E) : group K L x = group K L y ↔ x = y := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    change (fun j : {j // j ∈ (K ∪ L)ᶜ} => x.1 j.val) = (fun j : {j // j ∈ (K ∪ L)ᶜ} => y.1 j.val) at h0
    change keepReg (K ∩ L) x = keepReg (K ∩ L) y at h1
    change (fun j : {j // j ∈ K \ L} => x.1 j.val) = (fun j : {j // j ∈ K \ L} => y.1 j.val) at h2
    change (fun j : {j // j ∈ L \ K} => x.1 j.val) = (fun j : {j // j ∈ L \ K} => y.1 j.val) at h3
    apply Prod.ext
    · funext j
      by_cases hk : j ∈ K <;> by_cases hl : j ∈ L
      · exact congrFun (congrArg Prod.fst h1) ⟨j,by simp [hk,hl]⟩
      · exact congrFun h2 ⟨j,by simp [hk,hl]⟩
      · exact congrFun h3 ⟨j,by simp [hk,hl]⟩
      · exact congrFun h0 ⟨j,by simp [hk,hl]⟩
    · exact congrArg (fun a : SubBasis D (K ∩ L) × E => a.2) h1
  · rintro rfl; rfl

private def ungroup {n : ℕ} {D : Fin n → Type} {E : Type} (K L : Finset (Fin n))
    (x : ∀ i, groups D E K L i) : RegisterBasis D × E :=
  (fun j => if hk : j ∈ K then
      if hl : j ∈ L then (x 1).1 ⟨j,by simp [hk,hl]⟩
      else x 2 ⟨j,by simp [hk,hl]⟩
    else if hl : j ∈ L then x 3 ⟨j,by simp [hk,hl]⟩
      else x 0 ⟨j,by simp [hk,hl]⟩,
   (x 1).2)

private lemma group_ungroup {n : ℕ} {D : Fin n → Type} {E : Type} (K L : Finset (Fin n))
    (x : ∀ i, groups D E K L i) : group K L (ungroup K L x) = x := by
  funext i
  fin_cases i
  · funext j
    have hj := j.property
    simp only [Finset.mem_compl,Finset.mem_union,not_or] at hj
    simp [keepReg,ungroup,hj.1,hj.2]
  · apply Prod.ext
    · funext j
      have hj := Finset.mem_inter.mp j.property
      simp [keepReg,ungroup,hj.1,hj.2]
    · rfl
  · funext j
    have hj := Finset.mem_sdiff.mp j.property
    simp [keepReg,ungroup,hj.1,hj.2]
  · funext j
    have hj := Finset.mem_sdiff.mp j.property
    simp [keepReg,ungroup,hj.1,hj.2]

private def groupEquiv {n : ℕ} {D : Fin n → Type} {E : Type} (K L : Finset (Fin n)) :
    RegisterBasis D × E ≃ (∀ i, groups D E K L i) :=
  Equiv.ofBijective (group K L) ⟨fun _ _ h => (group_eq K L _ _).mp h,
    fun x => ⟨ungroup K L x,group_ungroup K L x⟩⟩

private lemma group_match {n : ℕ} {D : Fin n → Type} {E : Type}
    (K L : Finset (Fin n)) (x y : RegisterBasis D × E) :
    ((∀ i, i ∈ ({2,1} : Finset (Fin 4)) → group K L x i = group K L y i) ↔
      keepReg K x = keepReg K y) ∧
    ((∀ i, i ∉ ({2,1} : Finset (Fin 4)) → group K L x i = group K L y i) ↔
      outside K x y) ∧
    ((∀ i, i ∈ ({3,1} : Finset (Fin 4)) → group K L x i = group K L y i) ↔
      keepReg L x = keepReg L y) ∧
    ((∀ i, i ∉ ({3,1} : Finset (Fin 4)) → group K L x i = group K L y i) ↔
      outside L x y) ∧
    ((∀ i, i ∈ ({1} : Finset (Fin 4)) → group K L x i = group K L y i) ↔
      keepReg (K ∩ L) x = keepReg (K ∩ L) y) ∧
    ((∀ i, i ∉ ({1} : Finset (Fin 4)) → group K L x i = group K L y i) ↔
      outside (K ∩ L) x y) ∧
    ((∀ i, i ∈ ({2,3,1} : Finset (Fin 4)) → group K L x i = group K L y i) ↔
      keepReg (K ∪ L) x = keepReg (K ∪ L) y) ∧
    ((∀ i, i ∉ ({2,3,1} : Finset (Fin 4)) → group K L x i = group K L y i) ↔
      outside (K ∪ L) x y) := by
  have h0 : group K L x 0 = group K L y 0 ↔
      ∀ i, i ∉ K → i ∉ L → x.1 i = y.1 i := by
    change (fun j : {j // j ∈ (K ∪ L)ᶜ} => x.1 j.val) =
      (fun j : {j // j ∈ (K ∪ L)ᶜ} => y.1 j.val) ↔ _
    simp only [funext_iff,Subtype.forall,Finset.mem_compl,Finset.mem_union,
      not_or,and_imp]
  have h1 : group K L x 1 = group K L y 1 ↔
      (∀ i, i ∈ K → i ∈ L → x.1 i = y.1 i) ∧ x.2 = y.2 := by
    change ((fun j : {j // j ∈ K ∩ L} => x.1 j.val),x.2) =
      ((fun j : {j // j ∈ K ∩ L} => y.1 j.val),y.2) ↔ _
    simp only [Prod.mk.injEq,funext_iff,Subtype.forall,Finset.mem_inter,and_imp]
  have h2 : group K L x 2 = group K L y 2 ↔
      ∀ i, i ∈ K → i ∉ L → x.1 i = y.1 i := by
    change (fun j : {j // j ∈ K \ L} => x.1 j.val) =
      (fun j : {j // j ∈ K \ L} => y.1 j.val) ↔ _
    simp only [funext_iff,Subtype.forall,Finset.mem_sdiff,and_imp]
  have h3 : group K L x 3 = group K L y 3 ↔
      ∀ i, i ∈ L → i ∉ K → x.1 i = y.1 i := by
    change (fun j : {j // j ∈ L \ K} => x.1 j.val) =
      (fun j : {j // j ∈ L \ K} => y.1 j.val) ↔ _
    simp only [funext_iff,Subtype.forall,Finset.mem_sdiff,and_imp]
  have hr (s : Finset (Fin n)) : keepReg s x = keepReg s y ↔
      (∀ i, i ∈ s → x.1 i = y.1 i) ∧ x.2 = y.2 := by
    change ((fun j : {j // j ∈ s} => x.1 j.val),x.2) =
      ((fun j : {j // j ∈ s} => y.1 j.val),y.2) ↔ _
    simp only [Prod.mk.injEq,funext_iff,Subtype.forall]
  have henum (P : Fin 4 → Prop) : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
    constructor
    · intro h; exact ⟨h 0,h 1,h 2,h 3⟩
    · rintro ⟨h0,h1,h2,h3⟩ i
      fin_cases i <;> assumption
  simp only [henum,Finset.mem_insert,Finset.mem_singleton,
    Fin.reduceEq, or_false, false_or, not_true_eq_false, not_false_eq_true,
    forall_const, true_implies, false_implies, and_true, true_and]
  simp only [h0,h1,h2,h3,hr,outside,Finset.mem_inter,Finset.mem_union]
  and_intros <;> grind

private lemma grouped_entropy {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] {E : Type} [Fintype E] [Nonempty E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (K L s : Finset (Fin n)) (t : Finset (Fin 4))
    (hk : ∀ x y : RegisterBasis D × E, (∀ i, i ∈ t → group K L x i = group K L y i) ↔
      keepReg s x = keepReg s y)
    (hr : ∀ x y : RegisterBasis D × E, (∀ i, i ∉ t → group K L x i = group K L y i) ↔ outside s x y) :
    entropyAt rho s = QAlgorithms.Papers.Independent.Gap48.P38.registerEntropy
      (groups D E K L) (Matrix.reindex (groupEquiv K L) (groupEquiv K L) rho) t := by
  unfold entropyAt QAlgorithms.Papers.Independent.Gap48.P38.registerEntropy
  rw [register_red,subsystem_red]
  have hke (x y : RegisterBasis D × E) : keepReg s x = keepReg s y ↔
      restrict t ((groupEquiv K L) x) = restrict t ((groupEquiv K L) y) :=
    (hk x y).symm.trans (by simp [restrict,funext_iff,Subtype.forall,groupEquiv])
  have hre (x y : RegisterBasis D × E) : outside s x y ↔
      ∀ i, i ∉ t → (groupEquiv K L) x i = (groupEquiv K L) y i := (hr x y).symm
  convert red_entropy (groupEquiv K L) rho (keepReg s) (restrict t) (outside s)
    (fun x y => ∀ i, i ∉ t → x i = y i) (keepReg_surj s) (restrict_surj t) hke hre using 1 <;> congr 1

end X9Supermodular

open X9Supermodular

theorem solution {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    [hD : ∀ i, Nonempty (D i)] {R : Type} [Fintype R] [hR : Nonempty R]
    (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1)
    (hm : 0 < m) (K L : Finset (Fin m)) :
    entropyThreshold (pureDensity phi) K + entropyThreshold (pureDensity phi) L ≤
      entropyThreshold (pureDensity phi) (K ∪ L) +
      entropyThreshold (pureDensity phi) (K ∩ L) := by
  let e := groupEquiv (D := D) (E := R) K L
  let psi := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e phi
  have hpsi : ‖psi‖ = 1 := (LinearIsometryEquiv.norm_map _ phi).trans hphi
  have hpure : Matrix.reindex e e (pureDensity phi) = pureDensity psi := by
    ext x y; rfl
  have hK := grouped_entropy (pureDensity phi) K L K {2,1}
    (fun x y => (group_match K L x y).1)
    (fun x y => (group_match K L x y).2.1)
  have hL := grouped_entropy (pureDensity phi) K L L {3,1}
    (fun x y => (group_match K L x y).2.2.1)
    (fun x y => (group_match K L x y).2.2.2.1)
  have hI := grouped_entropy (pureDensity phi) K L (K ∩ L) {1}
    (fun x y => (group_match K L x y).2.2.2.2.1)
    (fun x y => (group_match K L x y).2.2.2.2.2.1)
  have hU := grouped_entropy (pureDensity phi) K L (K ∪ L) {2,3,1}
    (fun x y => (group_match K L x y).2.2.2.2.2.2.1)
    (fun x y => (group_match K L x y).2.2.2.2.2.2.2)
  have hssa := QAlgorithms.Papers.Independent.Gap48.P38.strongSubadditivity
    (groups D R K L) psi hpsi
  unfold QAlgorithms.Papers.Independent.Gap48.P38.registerCMI at hssa
  have h21 : ({2} ∪ {1} : Finset (Fin 4)) = {2,1} := by decide
  have h31 : ({3} ∪ {1} : Finset (Fin 4)) = {3,1} := by decide
  have h231 : ({2} ∪ {3} ∪ {1} : Finset (Fin 4)) = {2,3,1} := by decide
  rw [h21,h31,h231,← hpure] at hssa
  change 0 ≤ _ at hssa
  rw [← hK,← hL,← hI,← hU] at hssa
  have hsum := Finset.sum_union_inter (s₁ := K) (s₂ := L)
    (f := fun i => entropyAt (trivialExtension (forgetEnvironment (pureDensity phi))) {i})
  unfold entropyThreshold
  linarith
