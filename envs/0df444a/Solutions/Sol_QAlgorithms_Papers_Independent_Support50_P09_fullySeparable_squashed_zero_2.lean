-- Prove2me | solution 2 for QAlgorithms.Papers.Independent.Support50.P09.fullySeparable_squashed_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:47:16.019479+00:00
-- url     : https://prove2.me/submissions/3e451505-e828-45aa-b294-71bd2fde1163

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.LinearAlgebra.Matrix.Reindex
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_proposition1
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq
namespace X9Separable

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

private def ptrace {X Y Z : Type} [Fintype Z] (e : X ≃ Y × Z)
    (rho : Matrix X X ℂ) : Matrix Y Y ℂ :=
  fun a b => ∑ z, rho (e.symm (a,z)) (e.symm (b,z))

private lemma partial_density {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (e : X ≃ Y × Z) (rho : Matrix X X ℂ) (hrho : IsDensityMatrix rho) :
    IsDensityMatrix (ptrace e rho) := by
  constructor
  · have hp : ptrace e rho = ∑ z, rho.submatrix (fun y => e.symm (y,z))
        (fun y => e.symm (y,z)) := by ext a b; simp [ptrace,Matrix.sum_apply]
    rw [hp]
    exact Matrix.posSemidef_sum _ (fun z _ => hrho.1.submatrix _)
  · change (∑ y, ∑ z, rho (e.symm (y,z)) (e.symm (y,z))) = 1
    have ht := Equiv.sum_comp e.symm (fun x => rho x x)
    simp only [Fintype.sum_prod_type] at ht
    exact ht.trans hrho.2

private lemma red_partial {X Y Z A : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (e : X ≃ Y × Z) (rho : Matrix X X ℂ) (g : Y → A) (r : Y → Y → Prop) :
    red (ptrace e rho) g r = red rho (fun x => g (e x).1)
      (fun x y => (e x).2 = (e y).2 ∧ r (e x).1 (e y).1) := by
  ext a b
  unfold red ptrace
  rw [← Equiv.sum_comp e.symm]
  conv_rhs =>
    arg 2; ext x
    rw [← Equiv.sum_comp e.symm]
  simp only [Fintype.sum_prod_type,Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro y _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_const_zero]
  by_cases hga : g y = a <;> by_cases hgb : g v = b <;> by_cases hr : r y v <;>
    simp [hga,hgb,hr]

private lemma red_id {Y : Type} [Fintype Y] (rho : Matrix Y Y ℂ) :
    red rho id (fun _ _ => True) = rho := by
  ext a b
  simp [red,ite_and]

private abbrev Triple {n : ℕ} (D : Fin n → Type) (E : Type) (K L : Finset (Fin n)) :=
  SubBasis D (K \ L) × (SubBasis D (L \ K) × (SubBasis D (K ∩ L) × E))

private def splitRegs {n : ℕ} {D : Fin n → Type} {E : Type}
    (K L : Finset (Fin n)) (x : RegisterBasis D × E) :
    Triple D E K L × SubBasis D (K ∪ L)ᶜ :=
  (((fun j => x.1 j.val), ((fun j => x.1 j.val), ((fun j => x.1 j.val), x.2))),
    (fun j => x.1 j.val))

private def joinRegs {n : ℕ} {D : Fin n → Type} {E : Type}
    (K L : Finset (Fin n)) (x : Triple D E K L × SubBasis D (K ∪ L)ᶜ) :
    RegisterBasis D × E :=
  ((fun j => if hk : j ∈ K then
      if hl : j ∈ L then x.1.2.2.1 ⟨j,by simp [hk,hl]⟩
      else x.1.1 ⟨j,by simp [hk,hl]⟩
    else if hl : j ∈ L then x.1.2.1 ⟨j,by simp [hk,hl]⟩
      else x.2 ⟨j,by simp [hk,hl]⟩), x.1.2.2.2)

private def splitEquiv {n : ℕ} {D : Fin n → Type} {E : Type} (K L : Finset (Fin n)) :
    RegisterBasis D × E ≃ Triple D E K L × SubBasis D (K ∪ L)ᶜ where
  toFun := splitRegs K L
  invFun := joinRegs K L
  left_inv := by
    intro x
    apply Prod.ext
    · funext j
      by_cases hk : j ∈ K <;> by_cases hl : j ∈ L <;>
        simp [splitRegs,joinRegs,hk,hl]
    · rfl
  right_inv := by
    rintro ⟨⟨c,r,b,e⟩,z⟩
    apply Prod.ext
    · apply Prod.ext
      · funext j; have hj := Finset.mem_sdiff.mp j.property
        simp [splitRegs,joinRegs,hj.1,hj.2]
      · apply Prod.ext
        · funext j; have hj := Finset.mem_sdiff.mp j.property
          simp [splitRegs,joinRegs,hj.1,hj.2]
        · apply Prod.ext
          · funext j; have hj := Finset.mem_inter.mp j.property
            simp [splitRegs,joinRegs,hj.1,hj.2]
          · rfl
    · funext j
      have hj := j.property
      simp only [Finset.mem_compl,Finset.mem_union,not_or] at hj
      simp [splitRegs,joinRegs,hj.1,hj.2]

private lemma entropy_match {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] {E : Type} [Fintype E] [Nonempty E]
    {A : Type} [Fintype A]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (K L s : Finset (Fin n)) (g : Triple D E K L → A)
    (r : Triple D E K L → Triple D E K L → Prop) (hg : Function.Surjective g)
    (hk : ∀ x y : RegisterBasis D × E, keepReg s x = keepReg s y ↔
      g (splitRegs K L x).1 = g (splitRegs K L y).1)
    (hr : ∀ x y : RegisterBasis D × E, outside s x y ↔
      (splitRegs K L x).2 = (splitRegs K L y).2 ∧
        r (splitRegs K L x).1 (splitRegs K L y).1) :
    entropyAt rho s = vnEntropy (red (ptrace (splitEquiv K L) rho) g r) := by
  unfold entropyAt
  rw [register_red,red_partial]
  have hsur : Function.Surjective (fun x : RegisterBasis D × E =>
      g ((splitEquiv K L) x).1) := hg.comp (Prod.fst_surjective.comp (splitEquiv K L).surjective)
  convert red_entropy (Equiv.refl _) rho (keepReg s)
    (fun x => g ((splitEquiv K L) x).1) (outside s)
    (fun x y => ((splitEquiv K L) x).2 = ((splitEquiv K L) y).2 ∧
      r ((splitEquiv K L) x).1 ((splitEquiv K L) y).1)
    (keepReg_surj s) hsur hk hr using 1 <;> congr 1

private lemma split_match {n : ℕ} {D : Fin n → Type} {E : Type}
    (K L : Finset (Fin n)) (x y : RegisterBasis D × E) :
    (keepReg K x = keepReg K y ↔
      ((splitRegs K L x).1.1, (splitRegs K L x).1.2.2) =
      ((splitRegs K L y).1.1, (splitRegs K L y).1.2.2)) ∧
    (outside K x y ↔ (splitRegs K L x).2 = (splitRegs K L y).2 ∧
      (splitRegs K L x).1.2.1 = (splitRegs K L y).1.2.1) ∧
    (keepReg L x = keepReg L y ↔ (splitRegs K L x).1.2 = (splitRegs K L y).1.2) ∧
    (outside L x y ↔ (splitRegs K L x).2 = (splitRegs K L y).2 ∧
      (splitRegs K L x).1.1 = (splitRegs K L y).1.1) ∧
    (keepReg (K ∩ L) x = keepReg (K ∩ L) y ↔
      (splitRegs K L x).1.2.2 = (splitRegs K L y).1.2.2) ∧
    (outside (K ∩ L) x y ↔ (splitRegs K L x).2 = (splitRegs K L y).2 ∧
      ((splitRegs K L x).1.1, (splitRegs K L x).1.2.1) =
      ((splitRegs K L y).1.1, (splitRegs K L y).1.2.1)) ∧
    (keepReg (K ∪ L) x = keepReg (K ∪ L) y ↔
      (splitRegs K L x).1 = (splitRegs K L y).1) ∧
    (outside (K ∪ L) x y ↔ (splitRegs K L x).2 = (splitRegs K L y).2 ∧ True) := by
  simp only [splitRegs,keepReg,outside,Prod.mk.injEq,funext_iff,Subtype.forall,
    Finset.mem_compl,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,not_or,and_imp]
  and_intros <;> grind

private lemma entropy_submodular {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] {E : Type} [Fintype E] [Nonempty E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (hrho : IsDensityMatrix rho) (K L : Finset (Fin n)) :
    0 ≤ entropyAt rho K + entropyAt rho L - entropyAt rho (K ∩ L) -
      entropyAt rho (K ∪ L) := by
  let sigma := ptrace (splitEquiv (D := D) (E := E) K L) rho
  have hsigma : IsDensityMatrix sigma := partial_density _ rho hrho
  have hk := entropy_match rho K L K (fun p => (p.1,p.2.2))
    (fun p q => p.2.1 = q.2.1) (by rintro ⟨c,b⟩; exact ⟨(c,Classical.choice inferInstance,b),rfl⟩)
    (fun x y => (split_match K L x y).1) (fun x y => (split_match K L x y).2.1)
  have hl := entropy_match rho K L L (fun p => p.2) (fun p q => p.1 = q.1)
    (by intro b; exact ⟨(Classical.choice inferInstance,b),rfl⟩)
    (fun x y => (split_match K L x y).2.2.1) (fun x y => (split_match K L x y).2.2.2.1)
  have hi := entropy_match rho K L (K ∩ L) (fun p => p.2.2)
    (fun p q => (p.1,p.2.1) = (q.1,q.2.1))
    (by intro b; exact ⟨(Classical.choice inferInstance,Classical.choice inferInstance,b),rfl⟩)
    (fun x y => (split_match K L x y).2.2.2.2.1)
    (fun x y => (split_match K L x y).2.2.2.2.2.1)
  have hu := entropy_match rho K L (K ∪ L) id (fun _ _ => True) Function.surjective_id
    (fun x y => (split_match K L x y).2.2.2.2.2.2.1)
    (fun x y => (split_match K L x y).2.2.2.2.2.2.2)
  rw [hk,hl,hi,hu,red_id]
  have hssa := QAlgorithms.Papers.Independent.Gap48.P20.strongSubadditivity sigma hsigma
  unfold QAlgorithms.Papers.Independent.Gap48.P20.subsystemEntropy
    QAlgorithms.Papers.Independent.Gap48.P20.redistributionMarginal at hssa
  convert hssa using 1 <;> congr 2

private lemma total_nonneg {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] {E : Type} [Fintype E] [Nonempty E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (hrho : IsDensityMatrix rho) (hm : 0 < m) :
    0 ≤ conditionalMultipartiteInformation .total rho (singleParties m) ∅ := by
  have h (s : Finset (Fin m)) :
      0 ≤ (∑ i ∈ s, entropyAt rho {i}) - entropyAt rho s -
        ((s.card : ℝ) - 1) * entropyAt rho ∅ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      have hi : s ∩ {a} = ∅ := by simp [Finset.inter_singleton_of_notMem ha]
      have hu : s ∪ {a} = insert a s := by ext i; simp
      have hh := entropy_submodular rho hrho s {a}
      rw [hi,hu] at hh
      rw [Finset.sum_insert ha,Finset.card_insert_of_notMem ha]
      push_cast
      linarith
  have hall : allParties (singleParties m) = Finset.univ := by
    ext i; simp [allParties,singleParties]
  simpa [conditionalMultipartiteInformation,singleParties,hall,
    Nat.cast_sub (Nat.succ_le_of_lt hm),Finset.card_univ] using h Finset.univ

private def localProduct {m : ℕ} {D : Fin m → Type}
    (r : (i : Fin m) → Matrix (D i) (D i) ℂ) :
    Matrix (RegisterBasis D) (RegisterBasis D) ℂ :=
  fun x y => ∏ i, r i (x i) (y i)

private lemma localProduct_density {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (r : (i : Fin m) → Matrix (D i) (D i) ℂ)
    (hr : ∀ i, IsDensityMatrix (r i)) : IsDensityMatrix (localProduct r) := by
  constructor
  · have hp (s : Finset (Fin m)) :
        (Matrix.of (fun x y : RegisterBasis D => ∏ i ∈ s, r i (x i) (y i))).PosSemidef := by
      induction s using Finset.induction_on with
      | empty =>
        simpa [Matrix.vecMulVec] using
          (Matrix.posSemidef_vecMulVec_self_star (fun _ : RegisterBasis D => (1 : ℂ)))
      | @insert i s hi ih =>
        convert ((hr i).1.submatrix (fun x : RegisterBasis D => x i)).hadamard ih using 1 <;>
          first | rfl | (ext x y; simp [Finset.prod_insert hi,Matrix.hadamard_apply])
    exact hp Finset.univ
  · change (∑ x : RegisterBasis D, ∏ i, r i (x i) (x i)) = 1
    rw [← Fintype.prod_sum (fun i a => r i a a)]
    have ht (i : Fin m) : (∑ a, r i a a) = 1 := (hr i).2
    simp only [ht,Finset.prod_const_one]

private lemma localProduct_marginal {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (r : (i : Fin m) → Matrix (D i) (D i) ℂ)
    (hr : ∀ i, IsDensityMatrix (r i)) (i : Fin m) :
    localMarginal (localProduct r) i = r i := by
  ext a b
  let g (j : Fin m) (x y : D j) : Prop :=
    if j = i then True else x = y
  let f (j : Fin m) (x y : D j) : ℂ :=
    if g j x y then r j x y else 0
  have hsum (j : Fin m) (hj : j ≠ i) : (∑ x, ∑ y, f j x y) = 1 := by
    simp [f,g,hj,show (∑ x, r j x x) = 1 from (hr j).2]
  have hterm (x y : RegisterBasis D) :
      (if x i = a ∧ y i = b ∧ (∀ j, j ≠ i → x j = y j)
        then localProduct r x y else 0) =
      ∏ j, if j = i then (if x i = a ∧ y i = b then r j (x j) (y j) else 0)
        else f j (x j) (y j) := by
    have he : ∀ j, (if j = i then (if x i = a ∧ y i = b then r j (x j) (y j) else 0)
        else f j (x j) (y j)) =
        if (if j = i then x i = a ∧ y i = b else x j = y j)
          then r j (x j) (y j) else 0 := by
      intro j; by_cases hj : j = i <;> simp [hj,f,g]
    simp_rw [he]
    rw [Finset.prod_ite_zero]
    have hh : (∀ j ∈ (Finset.univ : Finset (Fin m)),
        if j = i then x i = a ∧ y i = b else x j = y j) ↔
        x i = a ∧ y i = b ∧ (∀ j, j ≠ i → x j = y j) := by
      simp only [Finset.mem_univ,forall_true_left]
      constructor
      · intro h
        have hh : x i = a ∧ y i = b := by simpa using h i
        exact ⟨hh.1,hh.2,fun j hj => by simpa [hj] using h j⟩
      · rintro ⟨ha,hb,h⟩ j
        by_cases hj : j = i
        · simp [hj,ha,hb]
        · simp [hj,h j hj]
    simp only [hh,localProduct]
  unfold localMarginal
  simp_rw [hterm]
  -- Make the distinguished factor use its own dependent coordinates.
  let q (j : Fin m) (x y : D j) : ℂ :=
    if hj : j = i then
      if hj ▸ x = a ∧ hj ▸ y = b then r j x y else 0
    else f j x y
  have hq (x y : RegisterBasis D) :
      (∏ j, if j = i then (if x i = a ∧ y i = b then r j (x j) (y j) else 0)
        else f j (x j) (y j)) = ∏ j, q j (x j) (y j) := by
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j = i
    · subst j; simp [q]
    · simp [hj,q]
  simp_rw [hq]
  have hy (x : RegisterBasis D) : (∑ y : RegisterBasis D, ∏ j, q j (x j) (y j)) =
      ∏ j, ∑ y, q j (x j) y := (Fintype.prod_sum (fun j y => q j (x j) y)).symm
  simp_rw [hy]
  rw [← Fintype.prod_sum (fun j x => ∑ y, q j x y)]
  rw [Finset.prod_eq_single i]
  · dsimp only [q]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro y _ hy; simp [hy]
      · simp
    · intro x _ hx; simp [hx]
    · simp
  · intro j _ hj
    simpa [q,hj] using hsum j hj
  · simp



private def diagComplex {I : Type} [Fintype I] [DecidableEq I] : (I → ℂ) →⋆ₐ[ℂ] Matrix I I ℂ where
  toFun := Matrix.diagonal
  map_zero' := by ext i j; simp [Matrix.diagonal]
  map_one' := by ext i j; simp [Matrix.diagonal, Matrix.one_apply]
  map_add' := by intro a b; exact (Matrix.diagonal_add a b).symm
  map_mul' := by intro a b; exact (Matrix.diagonal_mul_diagonal a b).symm
  commutes' := by intro r; rfl
  map_star' := by
    intro a
    change Matrix.diagonal (star a) = (Matrix.diagonal a).conjTranspose
    rw [Matrix.diagonal_conjTranspose]

private lemma entropy_diagonal {I : Type} [Fintype I] [DecidableEq I] (v : I → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (v i : ℂ))) = - ∑ i, v i * Real.logb 2 (v i) := by
  let f : ℝ → ℝ := fun t => t * Real.logb 2 t
  let w : I → ℂ := fun i => (v i : ℂ)
  have hf : Continuous f := by
    simpa [f,Real.logb,mul_div_assoc] using Real.continuous_mul_log.div_const (Real.log 2)
  have hv : IsSelfAdjoint w := by ext i; simp [w]
  have hd : IsSelfAdjoint (diagComplex w) := hv.map diagComplex
  have hc := StarAlgHomClass.map_cfc (S := ℂ) diagComplex f w hf.continuousOn
    (by change Continuous (fun v : I → ℂ => Matrix.diagonal v); fun_prop) hv hd
  have hp : cfc f w = fun i => (f (v i) : ℂ) := by
    rw [cfc_map_pi (S := ℂ) f w (by exact hf.continuousOn) hv (by intro i; change star (v i : ℂ) = (v i : ℂ); simp)]
    funext i
    dsimp only [w]
    exact cfc_algebraMap (v i) f
  rw [hp] at hc
  change -(cfc f (diagComplex w)).trace.re = _
  rw [← hc]
  simp [diagComplex,Matrix.trace,f]

private lemma entropy_unitary {I : Type} [Fintype I] [DecidableEq I]
    (u : unitary (Matrix I I ℂ)) (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    vnEntropy (Unitary.conjStarAlgAut ℂ _ u A) = vnEntropy A := by
  let f : ℝ → ℝ := fun t => t * Real.logb 2 t
  let phi := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) u
  have hf : Continuous f := by
    simpa [f,Real.logb,mul_div_assoc] using Real.continuous_mul_log.div_const (Real.log 2)
  have hphi : IsSelfAdjoint (phi A) := hA.isSelfAdjoint.map phi
  have hc := StarAlgHomClass.map_cfc (S := ℂ) phi f A hf.continuousOn
    (by change Continuous (fun B : Matrix I I ℂ => (u : Matrix I I ℂ) * B * (star u : Matrix I I ℂ)); fun_prop) hA hphi
  unfold vnEntropy
  rw [← hc]
  congr 1
  change ((u : Matrix I I ℂ) * cfc f A * (star u : Matrix I I ℂ)).trace.re = _
  rw [Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,Matrix.one_mul]

private def tensor {m : ℕ} {D : Fin m → Type}
    (r : (i : Fin m) → Matrix (D i) (D i) ℂ) :
    Matrix (RegisterBasis D) (RegisterBasis D) ℂ :=
  fun x y => ∏ i, r i (x i) (y i)

private lemma tensor_mul {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (r s : (i : Fin m) → Matrix (D i) (D i) ℂ) :
    tensor r * tensor s = tensor (fun i => r i * s i) := by
  ext x y
  simp only [Matrix.mul_apply,tensor,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i z => r i (x i) z * s i z (y i))).symm

private lemma tensor_star {m : ℕ} {D : Fin m → Type}
    (r : (i : Fin m) → Matrix (D i) (D i) ℂ) :
    star (tensor r) = tensor (fun i => star (r i)) := by
  ext x y
  simp [tensor,Matrix.star_apply]

private lemma tensor_one {m : ℕ} {D : Fin m → Type} :
    tensor (fun i => (1 : Matrix (D i) (D i) ℂ)) = 1 := by
  ext x y
  simp only [tensor,Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one,Finset.mem_univ,forall_true_left]
  congr 1
  exact propext funext_iff.symm

private lemma tensor_diagonal {m : ℕ} {D : Fin m → Type}
    (v : (i : Fin m) → D i → ℝ) :
    tensor (fun i => Matrix.diagonal (fun a => (v i a : ℂ))) =
      Matrix.diagonal (fun x : RegisterBasis D => ((∏ i, v i (x i) : ℝ) : ℂ)) := by
  ext x y
  simp only [tensor,Matrix.diagonal_apply, ← Complex.ofReal_prod]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ,forall_true_left]
  simp [funext_iff]

private def tensorUnitary {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (u : (i : Fin m) → unitary (Matrix (D i) (D i) ℂ)) :
    unitary (Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :=
  ⟨tensor (fun i => (u i : Matrix (D i) (D i) ℂ)), by
    constructor
    · rw [tensor_star,tensor_mul]
      simpa only [Unitary.coe_star_mul_self] using (tensor_one (D := D))
    · rw [tensor_star,tensor_mul]
      simpa only [← Unitary.coe_star,Unitary.coe_mul_star_self] using (tensor_one (D := D))⟩

private lemma tensor_spectral {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (r : (i : Fin m) → Matrix (D i) (D i) ℂ) (hr : ∀ i, (r i).IsHermitian) :
    tensor r = Unitary.conjStarAlgAut ℂ _ (tensorUnitary (fun i => (hr i).eigenvectorUnitary))
      (Matrix.diagonal (fun x : RegisterBasis D => ((∏ i, (hr i).eigenvalues (x i) : ℝ) : ℂ))) := by
  rw [← tensor_diagonal]
  change tensor r = tensor _ * tensor _ * star (tensor _)
  rw [tensor_star,tensor_mul,tensor_mul]
  congr 1
  funext i
  exact (hr i).spectral_theorem

private lemma log_product {m : ℕ} (p : Fin m → ℝ) :
    (∏ i, p i) * Real.logb 2 (∏ i, p i) =
      ∑ i, ∏ j, if j = i then p j * Real.logb 2 (p j) else p j := by
  have hterm (i : Fin m) :
      (∏ j, if j = i then p j * Real.logb 2 (p j) else p j) =
      (p i * Real.logb 2 (p i)) * ∏ j ∈ Finset.univ.erase i, p j := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [if_true]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [Finset.ne_of_mem_erase hj]
  simp_rw [hterm]
  by_cases hzero : ∃ i, p i = 0
  · obtain ⟨k,hk⟩ := hzero
    have hz : (∏ i, p i) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) hk
    rw [hz,zero_mul]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases hik : k = i
    · subst i; simp [hk]
    · have hh : (∏ j ∈ Finset.univ.erase i, p j) = 0 :=
        Finset.prod_eq_zero (by simp [hik]) hk
      simp [hh]
  · have hn (i : Fin m) : p i ≠ 0 := fun hi => hzero ⟨i,hi⟩
    rw [Real.logb_prod _ _ (fun i _ => hn i),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)]
    ring

private lemma entropy_product_distribution {m : ℕ} {D : Fin m → Type}
    [∀ i, Fintype (D i)] (p : (i : Fin m) → D i → ℝ)
    (hs : ∀ i, (∑ a, p i a) = 1) :
    (∑ x : RegisterBasis D, (∏ i, p i (x i)) * Real.logb 2 (∏ i, p i (x i))) =
      ∑ i, ∑ a, p i a * Real.logb 2 (p i a) := by
  simp_rw [log_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fintype.prod_sum (fun j a => if j = i then p j a * Real.logb 2 (p j a) else p j a)]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji,hs j]
  · simp

private lemma entropy_spectral {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    vnEntropy A = - ∑ i, hA.eigenvalues i * Real.logb 2 (hA.eigenvalues i) := by
  have h := entropy_unitary hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)))
    (by apply Matrix.isHermitian_diagonal_of_self_adjoint; ext i; simp)
  have hs : A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) := hA.spectral_theorem
  exact (congrArg vnEntropy hs).trans (h.trans (entropy_diagonal hA.eigenvalues))

private lemma tensor_entropy {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (r : (i : Fin m) → Matrix (D i) (D i) ℂ) (hr : ∀ i, IsDensityMatrix (r i)) :
    vnEntropy (tensor r) = ∑ i, vnEntropy (r i) := by
  let hherm (i : Fin m) := (hr i).1.isHermitian
  have hs (i : Fin m) : (∑ a, (hherm i).eigenvalues a) = 1 := by
    have h := (hherm i).trace_eq_sum_eigenvalues
    rw [(hr i).2] at h
    simpa using (congrArg Complex.re h).symm
  let u := tensorUnitary (fun i => (hherm i).eigenvectorUnitary)
  let v (x : RegisterBasis D) : ℝ := ∏ i, (hherm i).eigenvalues (x i)
  have ht : vnEntropy (tensor r) = - ∑ x, v x * Real.logb 2 (v x) := by
    have h := entropy_unitary u (Matrix.diagonal (fun x => (v x : ℂ)))
      (by apply Matrix.isHermitian_diagonal_of_self_adjoint; ext i; simp)
    rw [tensor_spectral r hherm]
    convert h.trans (entropy_diagonal v) using 1
  rw [ht]
  dsimp only [v]
  rw [entropy_product_distribution _ hs]
  simp_rw [entropy_spectral _ (hherm _)]
  simp only [Finset.sum_neg_distrib]


private lemma entropy_instances {I : Type} [Fintype I] (a b : DecidableEq I)
    (A : Matrix I I ℂ) : @vnEntropy I _ a A = @vnEntropy I _ b A := by
  have h : a = b := Subsingleton.elim _ _
  cases h
  rfl

private lemma entropy_canonical {I : Type} [Fintype I] [d : DecidableEq I]
    (A : Matrix I I ℂ) : @vnEntropy I _ d A = @vnEntropy I _ (Classical.decEq I) A :=
  entropy_instances _ _ _

private lemma reindex_trivial {m : ℕ} {D : Fin m → Type}
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    Matrix.reindex (Equiv.prodUnique (RegisterBasis D) Unit)
      (Equiv.prodUnique (RegisterBasis D) Unit) (trivialExtension rho) = rho := by
  ext x y
  rfl

private lemma entropy_singleton_local {m : ℕ} {D : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (i : Fin m) :
    entropyAt (trivialExtension rho) {i} = vnEntropy (localMarginal rho i) := by
  unfold entropyAt
  rw [register_red]
  have h := red_entropy (Equiv.prodUnique (RegisterBasis D) Unit) (trivialExtension rho)
    (keepReg {i}) (fun x : RegisterBasis D => x i) (outside {i})
    (fun x y : RegisterBasis D => ∀ j, j ≠ i → x j = y j)
    (keepReg_surj {i}) (Function.surjective_eval i)
    (by intro x y; simp [keepReg,funext_iff,Subtype.forall])
    (by intro x y; simp [outside])
  rw [reindex_trivial] at h
  simp only [entropy_canonical] at h ⊢
  convert h using 1
  congr 1
  ext a b
  unfold red localMarginal
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hc : x i = a ∧ y i = b ∧ (∀ j, j ≠ i → x j = y j) <;> simp [hc]


private lemma entropy_univ_local {m : ℕ} {D : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    entropyAt (trivialExtension rho) Finset.univ = vnEntropy rho := by
  unfold entropyAt
  rw [register_red]
  have h := red_entropy (Equiv.prodUnique (RegisterBasis D) Unit) (trivialExtension rho)
    (keepReg Finset.univ) id (outside Finset.univ) (fun _ _ => True)
    (keepReg_surj Finset.univ) Function.surjective_id
    (by intro x y; simp [keepReg,funext_iff,Subtype.forall])
    (by intro x y; simp [outside])
  rw [red_id] at h
  rw [reindex_trivial] at h
  simp only [entropy_canonical] at h ⊢
  convert h using 1 <;> (congr 1; ext a b; simp [red,localMarginal])

private lemma entropy_empty_local {m : ℕ} {D : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    entropyAt (trivialExtension rho) ∅ = 0 := by
  unfold entropyAt
  rw [register_red]
  have h := red_entropy (Equiv.prodUnique (RegisterBasis D) Unit) (trivialExtension rho)
    (keepReg ∅) (fun _ : RegisterBasis D => ()) (outside ∅)
    (fun x y : RegisterBasis D => y = x)
    (keepReg_surj ∅) (by rintro ⟨⟩; exact ⟨Classical.choice inferInstance,rfl⟩)
    (by intro x y; simp [keepReg,funext_iff,Subtype.forall])
    (by intro x y; simp [outside,funext_iff,eq_comm])
  have he : red (Matrix.reindex (Equiv.prodUnique (RegisterBasis D) Unit)
      (Equiv.prodUnique (RegisterBasis D) Unit) (trivialExtension rho))
      (fun _ : RegisterBasis D => ()) (fun x y => y = x) =
      Matrix.diagonal (fun _ : Unit => (1 : ℂ)) := by
    ext a b
    cases a; cases b
    rw [reindex_trivial]
    simp [red,Matrix.trace,show (∑ x, rho x x) = 1 from hrho.2]
  rw [he] at h
  have hz : @vnEntropy Unit _ (Classical.decEq Unit) (1 : Matrix Unit Unit ℂ) = 0 := by
    let A : Matrix Unit Unit ℂ := @Matrix.diagonal Unit ℂ (Classical.decEq Unit) _
      (fun _ => (1 : ℂ))
    have he : A = (1 : Matrix Unit Unit ℂ) := by
      ext a b
      cases a; cases b
      simp [A,Matrix.diagonal_apply,Matrix.one_apply]
    have hh := @entropy_diagonal Unit _ (Classical.decEq Unit) (fun _ => (1 : ℝ))
    have hh0 : @vnEntropy Unit _ (Classical.decEq Unit) A = 0 := by
      simpa only [Complex.ofReal_one,one_mul,Real.logb_one,Finset.sum_const_zero,neg_zero] using hh
    rwa [he] at hh0
  simp only [entropy_canonical,Matrix.diagonal_one] at h ⊢
  exact h.trans hz

private lemma info_unconditional {m : ℕ} {D : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    info .total rho (singleParties m) ∅ =
      (∑ i, vnEntropy (localMarginal rho i)) - vnEntropy rho := by
  have hall : allParties (singleParties m) = Finset.univ := by
    ext i; simp [allParties,singleParties]
  simp [info,conditionalMultipartiteInformation,singleParties,hall,
    entropy_singleton_local,entropy_univ_local,entropy_empty_local rho hrho]

private lemma localProduct_info {m : ℕ} (hm : 0 < m) {D : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (r : (i : Fin m) → Matrix (D i) (D i) ℂ)
    (hr : ∀ i, IsDensityMatrix (r i)) :
    info .total (localProduct r) (singleParties m) ∅ = 0 := by
  rw [info_unconditional _ (localProduct_density r hr)]
  simp_rw [localProduct_marginal r hr]
  have ht : vnEntropy (localProduct r) = ∑ i, vnEntropy (r i) := tensor_entropy r hr
  rw [ht,sub_self]


private def cqState {m k : ℕ} {D : Fin m → Type}
    (p : Fin k → ℝ)
    (r : Fin k → Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    Matrix (RegisterBasis D × Fin k) (RegisterBasis D × Fin k) ℂ :=
  fun x y => if x.2 = y.2 then (p x.2 : ℂ) * r x.2 x.1 y.1 else 0

private lemma cq_density {m k : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (p : Fin k → ℝ)
    (r : Fin k → Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hp : ∀ j, 0 ≤ p j) (hsum : (∑ j, p j) = 1)
    (hr : ∀ j, IsDensityMatrix (r j)) : IsDensityMatrix (cqState p r) := by
  constructor
  · let v (j : Fin k) : RegisterBasis D × Fin k → ℂ :=
      fun x => if x.2 = j then 1 else 0
    let B (j : Fin k) :=
      ((r j).submatrix Prod.fst Prod.fst).hadamard (Matrix.vecMulVec (v j) (star (v j)))
    have hb (j : Fin k) : (B j).PosSemidef :=
      ((hr j).1.submatrix Prod.fst).hadamard (Matrix.posSemidef_vecMulVec_self_star (v j))
    have hB (j : Fin k) (x y : RegisterBasis D × Fin k) :
        B j x y = if x.2 = j ∧ y.2 = j then r j x.1 y.1 else 0 := by
      dsimp [B,Matrix.hadamard,Matrix.vecMulVec,v]
      split_ifs <;> simp_all
    have he : cqState p r = ∑ j, (p j : ℂ) • B j := by
      ext x y
      simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,hB]
      by_cases hxy : x.2 = y.2
      · simp [cqState,← hxy, mul_ite]
      · have hn (j : Fin k) : ¬ (x.2 = j ∧ y.2 = j) := by grind
        simp [cqState,hxy,hn]
    rw [he]
    exact Matrix.posSemidef_sum _ (fun j _ => (hb j).smul (by exact_mod_cast hp j))
  · change (∑ x : RegisterBasis D × Fin k, cqState p r x x) = 1
    simp only [cqState,if_true]
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have ht (j : Fin k) : (∑ x, r j x x) = 1 := (hr j).2
    simp only [ht,mul_one,← Complex.ofReal_sum,hsum,Complex.ofReal_one]

private lemma cq_forget {m k : ℕ} {D : Fin m → Type}
    (p : Fin k → ℝ)
    (r : Fin k → Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    forgetEnvironment (cqState p r) = ∑ j, (p j : ℂ) • r j := by
  ext x y
  simp [forgetEnvironment,cqState,Matrix.sum_apply,Matrix.smul_apply]

private lemma cq_info {m k : ℕ} (hm : 2 ≤ m) {D : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho)
    (p : Fin k → ℝ)
    (r : Fin k → Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hp : ∀ j, 0 ≤ p j) (hsum : (∑ j, p j) = 1)
    (hr : ∀ j, IsDensityMatrix (r j)) :
    conditionalMultipartiteInformation .total (cqState p r) (singleParties m) ∅ =
      ∑ j, p j * info .total (r j) (singleParties m) ∅ := by
  obtain ⟨l,hl⟩ := Nat.exists_eq_add_of_le hm
  have hm' : m = l+2 := by omega
  clear hl
  subst m
  have hd : DisjointRegisters (singleParties (l+2)) ∅ := by
    constructor
    · intro i j hij; simp [singleParties,hij]
    · intro i; simp
  have h := QAlgorithms.Papers.Independent.Claimed50.P33.proposition1 (k := l) rho hrho
    (singleParties (l+2)) ∅ hd
  exact h.2.2.2.2.2.2.2 k p r hp hsum hr .total

end X9Separable

open X9Separable

theorem solution {m : ℕ} (hm : 0 < m) (s : FiniteState m)
    (hsep : IsMixedFullySeparable s) : halfExtensionSquashed .total s.rho = 0 := by
  letI (i : Fin m) : NeZero (s.dims i) := ⟨Nat.ne_of_gt (s.positive i)⟩
  obtain ⟨k,p,r,hp,hsum,hr,hrepr⟩ := hsep
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    simp at hsum
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let r' (j : Fin k) := localProduct (r j)
  have hr' (j : Fin k) : IsDensityMatrix (r' j) := localProduct_density _ (hr j)
  let sigma := cqState p r'
  have hden : IsDensityMatrix sigma := cq_density p r' hp hsum hr'
  have hforget : forgetEnvironment sigma = s.rho := by
    rw [cq_forget]
    ext x y
    simpa [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,r',localProduct] using
      (hrepr x y).symm
  have hi : conditionalMultipartiteInformation .total sigma (singleParties m) ∅ = 0 := by
    by_cases hm1 : m = 1
    · subst m
      simp [conditionalMultipartiteInformation,singleParties,allParties]
    · rw [cq_info (by omega) s.rho s.normalized p r' hp hsum hr']
      simp only [r',localProduct_info hm _ (hr _),mul_zero,Finset.sum_const_zero]
  let S : Set ℝ := {v : ℝ | ∃ e : ℕ, 0 < e ∧
    ∃ sigma : Matrix (RegisterBasis (fun i => Fin (s.dims i)) × Fin e)
      (RegisterBasis (fun i => Fin (s.dims i)) × Fin e) ℂ,
      IsDensityMatrix sigma ∧ forgetEnvironment sigma = s.rho ∧
      (false = true → IsClassicalExtension sigma) ∧
      v = conditionalMultipartiteInformation .total sigma (singleParties m) ∅}
  have hz : (0 : ℝ) ∈ S := ⟨k,hk,sigma,hden,hforget,by simp,hi.symm⟩
  have hl : ∀ v ∈ S, 0 ≤ v := by
    rintro v ⟨e,he,tau,htau,hred,hclass,rfl⟩
    letI : NeZero e := ⟨Nat.ne_of_gt he⟩
    exact total_nonneg tau htau hm
  have hS : sInf S = 0 := le_antisymm (csInf_le ⟨0,hl⟩ hz)
    (le_csInf ⟨0,hz⟩ hl)
  change sInf S / 2 = 0
  rw [hS]; norm_num

end
