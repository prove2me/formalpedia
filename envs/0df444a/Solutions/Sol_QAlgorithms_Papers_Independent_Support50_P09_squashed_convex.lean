-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.squashed_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:04:50.987992+00:00
-- url     : https://prove2.me/submissions/881e572f-aaf2-459e-9b7b-62b3c4c9b39d

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq
namespace X9Convex

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

private lemma one_info {D : Fin 1 → Type} [∀ i, Fintype (D i)]
    {E : Type} [Fintype E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) :
    conditionalMultipartiteInformation .total rho (singleParties 1) ∅ = 0 := by
  simp [conditionalMultipartiteInformation,singleParties,allParties]

private lemma one_squashed {D : Fin 1 → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    halfExtensionSquashed .total rho = 0 := by
  let S : Set ℝ := {v : ℝ | ∃ e : ℕ, 0 < e ∧
    ∃ sigma : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ,
      IsDensityMatrix sigma ∧ forgetEnvironment sigma = rho ∧
      (false = true → IsClassicalExtension sigma) ∧
      v = conditionalMultipartiteInformation .total sigma (singleParties 1) ∅}
  have hz {v : ℝ} (hv : v ∈ S) : v = 0 := by
    obtain ⟨e,he,sigma,hden,hred,hclass,hval⟩ := hv
    exact hval.trans (one_info sigma)
  have hi : sInf S = 0 := by
    by_cases h : S.Nonempty
    · have he : S = {0} := Set.Subset.antisymm
        (fun _ hv => by simpa using hz hv)
        (Set.singleton_subset_iff.mpr (by
          obtain ⟨v,hv⟩ := h
          simpa only [hz hv] using hv))
      rw [he]; exact csInf_singleton 0
    · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]
  change sInf S / 2 = 0
  rw [hi]; norm_num

private abbrev values {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : Set ℝ :=
  {v : ℝ | ∃ e : ℕ, 0 < e ∧
    ∃ sigma : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ,
      IsDensityMatrix sigma ∧ forgetEnvironment sigma = rho ∧
      (false = true → IsClassicalExtension sigma) ∧
      v = conditionalMultipartiteInformation .total sigma (singleParties m) ∅}

private lemma values_nonempty {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    (values rho).Nonempty := by
  let sigma : Matrix (RegisterBasis D × Fin 1) (RegisterBasis D × Fin 1) ℂ :=
    fun a b => rho a.1 b.1
  have hd : IsDensityMatrix sigma := by
    refine ⟨hrho.1.submatrix Prod.fst,?_⟩
    simpa [Matrix.trace,sigma,Fintype.sum_prod_type] using hrho.2
  exact ⟨_,1,by omega,sigma,hd,by ext a b; simp [forgetEnvironment,sigma],
    by simp, rfl⟩

private lemma values_bdd {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (hm : 0 < m)
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : BddBelow (values rho) := by
  refine ⟨0,?_⟩
  rintro v ⟨e,he,sigma,hd,hred,hclass,rfl⟩
  letI : NeZero e := ⟨by omega⟩
  exact total_nonneg sigma hd hm

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

private lemma entropy_spectral {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    vnEntropy A = - ∑ i, hA.eigenvalues i * Real.logb 2 (hA.eigenvalues i) := by
  have h := entropy_unitary hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)))
    (by apply Matrix.isHermitian_diagonal_of_self_adjoint; ext i; simp)
  have hs : A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) := hA.spectral_theorem
  exact (congrArg vnEntropy hs).trans (h.trans (entropy_diagonal hA.eigenvalues))

private def envTransport {m : ℕ} {D : Fin m → Type} {E Z : Type}
    (e : E ≃ Z) (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) :
    Matrix (RegisterBasis D × Z) (RegisterBasis D × Z) ℂ :=
  Matrix.reindex (Equiv.prodCongr (Equiv.refl _) e) (Equiv.prodCongr (Equiv.refl _) e) rho

private lemma env_density {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {E Z : Type} [Fintype E] [Fintype Z]
    (e : E ≃ Z) (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (hrho : IsDensityMatrix rho) : IsDensityMatrix (envTransport e rho) := by
  refine ⟨hrho.1.submatrix _,?_⟩
  exact (Fintype.sum_equiv (Equiv.prodCongr (Equiv.refl _) e).symm _ _
    (fun _ => rfl)).trans hrho.2

private lemma env_forget {m : ℕ} {D : Fin m → Type}
    {E Z : Type} [Fintype E] [Fintype Z]
    (e : E ≃ Z) (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) :
    forgetEnvironment (envTransport e rho) = forgetEnvironment rho := by
  ext a b
  exact Equiv.sum_comp e.symm (fun t => rho (a,t) (b,t))

private lemma env_entropy {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {E Z : Type} [Fintype E] [Fintype Z]
    (e : E ≃ Z) (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Finset (Fin m)) : entropyAt (envTransport e rho) s = entropyAt rho s := by
  have he : registerMarginal (envTransport e rho) s =
      Matrix.reindex (Equiv.prodCongr (Equiv.refl _) e) (Equiv.prodCongr (Equiv.refl _) e)
        (registerMarginal rho s) := rfl
  unfold entropyAt
  rw [he]
  exact entropy_reindex _ _

private lemma env_info {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {E Z : Type} [Fintype E] [Fintype Z]
    (e : E ≃ Z) (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) :
    conditionalMultipartiteInformation .total (envTransport e rho) (singleParties m) ∅ =
      conditionalMultipartiteInformation .total rho (singleParties m) ∅ := by
  simp only [conditionalMultipartiteInformation,env_entropy]

private def blockStar {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    (Matrix I I ℂ × Matrix J J ℂ) →⋆ₐ[ℂ] Matrix (I ⊕ J) (I ⊕ J) ℂ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_zero' := Matrix.fromBlocks_zero
  map_one' := Matrix.fromBlocks_one
  map_add' := by intros; simp [Matrix.fromBlocks_add]
  map_mul' := by intros; simp [Matrix.fromBlocks_multiply]
  commutes' := by
    intro c
    ext i j
    cases i <;> cases j <;> simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  map_star' := by
    intro p
    change Matrix.fromBlocks p.1.conjTranspose 0 0 p.2.conjTranspose =
      (Matrix.fromBlocks p.1 0 0 p.2).conjTranspose
    simp [Matrix.fromBlocks_conjTranspose]

open scoped Matrix.Norms.L2Operator in
private lemma entropy_blocks {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    vnEntropy (Matrix.fromBlocks A 0 0 B) = vnEntropy A + vnEntropy B := by
  let f : ℝ → ℝ := fun t => t * Real.logb 2 t
  have hf : Continuous f := by
    simpa [f,Real.logb,mul_div_assoc] using Real.continuous_mul_log.div_const (Real.log 2)
  have hp : IsSelfAdjoint (A,B) := Prod.ext hA hB
  have hb : IsSelfAdjoint (blockStar (A,B)) := hp.map blockStar
  have hc := StarAlgHomClass.map_cfc (S := ℂ) blockStar f (A,B) hf.continuousOn
    (by change Continuous (fun p : Matrix I I ℂ × Matrix J J ℂ => Matrix.fromBlocks p.1 0 0 p.2); fun_prop) hp hb
  rw [cfc_map_prod (S := ℂ) f A B hf.continuousOn hp hA hB] at hc
  unfold vnEntropy
  change -(cfc f (blockStar (A,B))).trace.re = _
  rw [← hc]
  simp [blockStar,Matrix.trace,Fintype.sum_sum_type,f,add_comm]
  congr 3 <;> rfl

private lemma weighted_log (c x : ℝ) :
    (c*x) * Real.logb 2 (c*x) = c * (x * Real.logb 2 x) + x * (c * Real.logb 2 c) := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hx : x = 0
  · simp [hx]
  rw [Real.logb_mul hc hx]
  ring

private lemma entropy_scale {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (c : ℝ) :
    vnEntropy (c • A) = c * vnEntropy A - A.trace.re * (c * Real.logb 2 c) := by
  let v := hA.eigenvalues
  have heq : c • A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => ((c * v i : ℝ) : ℂ))) := by
    conv_lhs => rw [hA.spectral_theorem]
    change c • ((hA.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun i => (v i : ℂ)) * (star hA.eigenvectorUnitary : Matrix I I ℂ)) =
      (hA.eigenvectorUnitary : Matrix I I ℂ) * Matrix.diagonal (fun i => ((c*v i : ℝ) : ℂ)) *
      (star hA.eigenvectorUnitary : Matrix I I ℂ)
    rw [← smul_mul_assoc,← mul_smul_comm]
    congr 2
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal,h,v]
  have hs : (∑ i, v i) = A.trace.re := by
    simpa [v] using (congrArg Complex.re hA.trace_eq_sum_eigenvalues).symm
  rw [heq,entropy_unitary _ _ (by apply Matrix.isHermitian_diagonal_of_self_adjoint; ext i; simp),
    entropy_diagonal,entropy_spectral A hA]
  simp_rw [weighted_log]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,hs]
  ring

private lemma entropy_weighted_blocks {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) (hA : IsDensityMatrix A) (hB : IsDensityMatrix B)
    (c : ℝ) :
    vnEntropy (Matrix.fromBlocks (c • A) 0 0 ((1-c) • B)) =
      (-(c * Real.logb 2 c) - (1-c) * Real.logb 2 (1-c)) +
      c * vnEntropy A + (1-c) * vnEntropy B := by
  rw [entropy_blocks _ _ (hA.1.isHermitian.smul (show IsSelfAdjoint c from by simp [IsSelfAdjoint]))
      (hB.1.isHermitian.smul (show IsSelfAdjoint (1-c) from by simp [IsSelfAdjoint])),
    entropy_scale _ hA.1.isHermitian,entropy_scale _ hB.1.isHermitian,hA.2,hB.2]
  simp only [Complex.one_re]
  ring
private def marginalEquiv {n : ℕ} {D : Fin n → Type} {E : Type} (s : Finset (Fin n)) :
    RegisterBasis D × E ≃ (SubBasis D s × E) × ((i : {i // i ∉ s}) → D i.val) where
  toFun x := ((fun i => x.1 i.val,x.2),fun i => x.1 i.val)
  invFun x := (fun i => if h : i ∈ s then x.1.1 ⟨i,h⟩ else x.2 ⟨i,h⟩,x.1.2)
  left_inv := by
    intro x
    apply Prod.ext
    · funext i; by_cases h : i ∈ s <;> simp [h]
    · rfl
  right_inv := by
    rintro ⟨⟨a,e⟩,b⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i; simp [i.property]
      · rfl
    · funext i; simp [i.property]

private lemma register_density {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    {E : Type} [Fintype E] (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (hrho : IsDensityMatrix rho) (s : Finset (Fin n)) :
    IsDensityMatrix (registerMarginal rho s) := by
  let e := marginalEquiv (D := D) (E := E) s
  have h := red_partial e rho id (fun _ _ => True)
  rw [red_id] at h
  have hrel : (fun x y : RegisterBasis D × E =>
      (e x).2 = (e y).2 ∧ True) = outside s := by
    funext x y
    simp [e,marginalEquiv,outside,funext_iff,Subtype.forall]
  rw [hrel] at h
  have heq : (fun x => id (e x).1) = keepReg s := rfl
  rw [heq,← register_red] at h
  rw [← h]
  exact partial_density e rho hrho

open scoped MatrixOrder in
private lemma block_pos {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact map_nonneg blockStar (show 0 ≤ (A,B) from ⟨hA.nonneg,hB.nonneg⟩)

private def flagged {n : ℕ} {D : Fin n → Type} {E Z : Type}
    (c : ℝ) (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Matrix (RegisterBasis D × Z) (RegisterBasis D × Z) ℂ) :
    Matrix (RegisterBasis D × (E ⊕ Z)) (RegisterBasis D × (E ⊕ Z)) ℂ :=
  Matrix.reindex (Equiv.prodSumDistrib _ _ _).symm (Equiv.prodSumDistrib _ _ _).symm
    (Matrix.fromBlocks (c • r) 0 0 ((1-c) • s))

private lemma flagged_density {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    {E Z : Type} [Fintype E] [Fintype Z]
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Matrix (RegisterBasis D × Z) (RegisterBasis D × Z) ℂ)
    (hr : IsDensityMatrix r) (hs : IsDensityMatrix s) : IsDensityMatrix (flagged c r s) := by
  refine ⟨(block_pos _ _ (hr.1.smul hc) (hs.1.smul (sub_nonneg.mpr hc1))).submatrix _,?_⟩
  have ht := Equiv.sum_comp (Equiv.prodSumDistrib (RegisterBasis D) E Z)
    (fun x => (Matrix.fromBlocks (c • r) 0 0 ((1-c) • s)) x x)
  change (∑ i, (Matrix.fromBlocks (c • r) 0 0 ((1-c) • s))
    ((Equiv.prodSumDistrib _ _ _) i) ((Equiv.prodSumDistrib _ _ _) i)) = 1
  rw [ht]
  simp [Matrix.trace,Fintype.sum_sum_type,← Finset.mul_sum,← Complex.ofReal_sub,
    show (∑ i, r i i) = 1 from hr.2,show (∑ i, s i i) = 1 from hs.2]
  push_cast
  ring

private lemma flagged_forget {n : ℕ} {D : Fin n → Type}
    {E Z : Type} [Fintype E] [Fintype Z]
    (c : ℝ) (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Matrix (RegisterBasis D × Z) (RegisterBasis D × Z) ℂ) :
    forgetEnvironment (flagged c r s) = stateMixture c (forgetEnvironment r) (forgetEnvironment s) := by
  ext a b
  simp [forgetEnvironment,flagged,stateMixture,Fintype.sum_sum_type,← Finset.mul_sum]

private lemma flagged_marginal {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    {E Z : Type} [Fintype E] [Fintype Z]
    (c : ℝ) (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Matrix (RegisterBasis D × Z) (RegisterBasis D × Z) ℂ) (K : Finset (Fin n)) :
    registerMarginal (flagged c r s) K =
      Matrix.reindex (Equiv.prodSumDistrib _ _ _).symm (Equiv.prodSumDistrib _ _ _).symm
        (Matrix.fromBlocks (c • registerMarginal r K) 0 0 ((1-c) • registerMarginal s K)) := by
  ext ⟨a,e⟩ ⟨b,f⟩
  cases e <;> cases f <;>
    simp [registerMarginal,flagged,Matrix.reindex_apply,Matrix.submatrix_apply,
      Finset.mul_sum, mul_ite, mul_zero]

private lemma entropy_instances {I : Type} [Fintype I] (a b : DecidableEq I)
    (A : Matrix I I ℂ) : @vnEntropy I _ a A = @vnEntropy I _ b A := by
  have h : a = b := Subsingleton.elim _ _
  cases h
  rfl

private lemma entropy_canonical {I : Type} [Fintype I] [d : DecidableEq I]
    (A : Matrix I I ℂ) : @vnEntropy I _ d A = @vnEntropy I _ (Classical.decEq I) A :=
  entropy_instances _ _ _

private lemma flagged_entropy {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    {E Z : Type} [Fintype E] [Fintype Z]
    (c : ℝ) (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Matrix (RegisterBasis D × Z) (RegisterBasis D × Z) ℂ)
    (hr : IsDensityMatrix r) (hs : IsDensityMatrix s) (K : Finset (Fin n)) :
    entropyAt (flagged c r s) K =
      (-(c * Real.logb 2 c) - (1-c) * Real.logb 2 (1-c)) +
      c * entropyAt r K + (1-c) * entropyAt s K := by
  have heq := congrArg (fun M => @vnEntropy _ _ (Classical.decEq _) M) (flagged_marginal c r s K)
  have he := entropy_reindex (Equiv.prodSumDistrib (SubBasis D K) E Z).symm
    (Matrix.fromBlocks (c • registerMarginal r K) 0 0 ((1-c) • registerMarginal s K))
  have hb := entropy_weighted_blocks _ _ (register_density r hr K) (register_density s hs K) c
  unfold entropyAt
  simp only [entropy_canonical] at heq he hb ⊢
  exact heq.trans (he.trans hb)

private lemma flagged_info {m : ℕ} (hm : 0 < m) {D : Fin m → Type} [∀ i, Fintype (D i)]
    {E Z : Type} [Fintype E] [Fintype Z]
    (c : ℝ) (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Matrix (RegisterBasis D × Z) (RegisterBasis D × Z) ℂ)
    (hr : IsDensityMatrix r) (hs : IsDensityMatrix s) :
    conditionalMultipartiteInformation .total (flagged c r s) (singleParties m) ∅ =
      c * conditionalMultipartiteInformation .total r (singleParties m) ∅ +
      (1-c) * conditionalMultipartiteInformation .total s (singleParties m) ∅ := by
  simp only [conditionalMultipartiteInformation,flagged_entropy c r s hr hs,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ← Finset.mul_sum,Nat.cast_sub (Nat.succ_le_of_lt hm),Nat.cast_one]
  ring
private lemma convex_value {m : ℕ} (hm : 0 < m) {D : Fin m → Type}
    [∀ i, Fintype (D i)] (rho sigma : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {x y : ℝ} (hx : x ∈ values rho) (hy : y ∈ values sigma) :
    c*x + (1-c)*y ∈ values (stateMixture c rho sigma) := by
  obtain ⟨e,he,r,hr,hrf,hclass,rfl⟩ := hx
  obtain ⟨z,hz,s,hs,hsf,hclass',rfl⟩ := hy
  let q := flagged c r s
  let t := envTransport finSumFinEquiv q
  refine ⟨e+z,by omega,t,env_density _ q (flagged_density c hc hc1 r s hr hs),?_,by simp,?_⟩
  · rw [env_forget,flagged_forget,hrf,hsf]
  · rw [env_info,flagged_info hm c r s hr hs]

end X9Convex
open X9Convex

theorem solution {m : ℕ} (hm : 0 < m) {D : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho sigma : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    halfExtensionSquashed .total (stateMixture lambda rho sigma) ≤
      lambda * halfExtensionSquashed .total rho +
      (1-lambda) * halfExtensionSquashed .total sigma := by
  by_cases h0 : lambda = 0
  · subst lambda
    have h : stateMixture 0 rho sigma = sigma := by ext a b; simp [stateMixture]
    simp [h]
  by_cases h1 : lambda = 1
  · subst lambda
    have h : stateMixture 1 rho sigma = rho := by ext a b; simp [stateMixture]
    simp [h]
  have hc : 0 < lambda := lt_of_le_of_ne hlambda (Ne.symm h0)
  have hd : 0 < 1-lambda := sub_pos.mpr (lt_of_le_of_ne hlambda1 h1)
  let A := values rho
  let B := values sigma
  let C := values (stateMixture lambda rho sigma)
  have ha : A.Nonempty := values_nonempty rho hrho
  have hb : B.Nonempty := values_nonempty sigma hsigma
  have hbound (x : ℝ) (hx : x ∈ A) (y : ℝ) (hy : y ∈ B) :
      sInf C ≤ lambda*x+(1-lambda)*y :=
    csInf_le (values_bdd hm _) (convex_value hm rho sigma lambda hlambda hlambda1 hx hy)
  have hfirst (y : ℝ) (hy : y ∈ B) : sInf C ≤ lambda*sInf A+(1-lambda)*y := by
    have h : (sInf C-(1-lambda)*y)/lambda ≤ sInf A := by
      apply le_csInf ha
      intro x hx
      apply (div_le_iff₀ hc).mpr
      linarith [hbound x hx y hy]
    have h' := (div_le_iff₀ hc).mp h
    linarith
  have hsecond : (sInf C-lambda*sInf A)/(1-lambda) ≤ sInf B := by
    apply le_csInf hb
    intro y hy
    apply (div_le_iff₀ hd).mpr
    linarith [hfirst y hy]
  have h' := (div_le_iff₀ hd).mp hsecond
  change sInf C / 2 ≤ lambda * (sInf A / 2) + (1-lambda) * (sInf B / 2)
  linarith
