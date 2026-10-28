-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.squashed_product_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:00:39.116377+00:00
-- url     : https://prove2.me/submissions/93c7d293-690e-4ff1-9da4-fc660e6cbe15

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.LinearAlgebra.Matrix.Reindex
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_proposition1
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq
namespace X9Product

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

private def productEquiv {m : ℕ} (D F : Fin m → Type) (E Z : Type) :
    (RegisterBasis D × E) × (RegisterBasis F × Z) ≃
      RegisterBasis (fun i => D i × F i) × (E × Z) where
  toFun x := (fun i => (x.1.1 i,x.2.1 i),(x.1.2,x.2.2))
  invFun x := ((fun i => (x.1 i).1,x.2.1),(fun i => (x.1 i).2,x.2.2))
  left_inv _ := rfl
  right_inv x := by ext i <;> rfl

private lemma paired_density {m : ℕ} {D F : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)] {E Z : Type} [Fintype E] [Fintype Z]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (sigma : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    IsDensityMatrix (pairedProduct rho sigma) := by
  open scoped Kronecker in
  have hp : pairedProduct rho sigma = Matrix.reindex (productEquiv D F E Z)
      (productEquiv D F E Z) (rho ⊗ₖ sigma) := rfl
  rw [hp]
  refine ⟨(hrho.1.kronecker hsigma.1).submatrix _,?_⟩
  have ht : ∀ A : Matrix ((RegisterBasis D × E) × (RegisterBasis F × Z))
      ((RegisterBasis D × E) × (RegisterBasis F × Z)) ℂ,
      (Matrix.reindex (productEquiv D F E Z) (productEquiv D F E Z) A).trace = A.trace := by
    intro A
    exact Fintype.sum_equiv (productEquiv D F E Z).symm _ _ (fun _ => rfl)
  rw [ht,Matrix.trace_kronecker,hrho.2,hsigma.2,mul_one]

private lemma forget_paired {m : ℕ} {D F : Fin m → Type}
    {E Z : Type} [Fintype E] [Fintype Z]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (sigma : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ) :
    forgetEnvironment (pairedProduct rho sigma) =
      partyProduct (forgetEnvironment rho) (forgetEnvironment sigma) := by
  ext a b
  simp [forgetEnvironment,pairedProduct,partyProduct,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]

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

private lemma paired_info {m : ℕ} {D F : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    {E Z : Type} [Fintype E] [Fintype Z] [Nonempty E] [Nonempty Z]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (sigma : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (hm : 2 ≤ m)
    (r : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hr : IsDensityMatrix r) :
    conditionalMultipartiteInformation .total (pairedProduct rho sigma) (singleParties m) ∅ =
      conditionalMultipartiteInformation .total rho (singleParties m) ∅ +
        conditionalMultipartiteInformation .total sigma (singleParties m) ∅ := by
  have h := QAlgorithms.Papers.Independent.Claimed50.P33.proposition1 r hr
    (fun _ : Fin 2 => ∅) ∅ (by constructor <;> intros <;> simp)
  exact h.2.2.2.2.1 m D F E Z rho sigma hm hrho hsigma .total

private lemma product_value {m : ℕ} {D F : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (sigma : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hrho : IsDensityMatrix rho) (hm : 2 ≤ m)
    {x y : ℝ} (hx : x ∈ values rho) (hy : y ∈ values sigma) :
    x+y ∈ values (partyProduct rho sigma) := by
  obtain ⟨e,he,r,hr,her,hclass,rfl⟩ := hx
  obtain ⟨z,hz,s,hs,hzs,hclass',rfl⟩ := hy
  letI : NeZero e := ⟨by omega⟩
  letI : NeZero z := ⟨by omega⟩
  let f : Fin e × Fin z ≃ Fin (e*z) := finProdFinEquiv
  refine ⟨e*z,Nat.mul_pos he hz,envTransport f (pairedProduct r s),
    env_density f _ (paired_density r s hr hs),?_,by simp,?_⟩
  · rw [env_forget,forget_paired,her,hzs]
  · rw [env_info,paired_info r s hr hs hm rho hrho]

end X9Product

open X9Product

theorem solution {m : ℕ} (hm : 0 < m) {D F : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (sigma : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    halfExtensionSquashed .total (partyProduct rho sigma) ≤
      halfExtensionSquashed .total rho + halfExtensionSquashed .total sigma := by
  by_cases hm1 : m = 1
  · subst m
    simp [one_squashed]
  have hm2 : 2 ≤ m := by omega
  have hx := values_nonempty rho hrho
  have hy := values_nonempty sigma hsigma
  have hb := values_bdd hm (partyProduct rho sigma)
  have h (x : ℝ) (hx' : x ∈ values rho) :
      sInf (values (partyProduct rho sigma)) - x ≤ sInf (values sigma) := by
    apply le_csInf hy
    intro y hy'
    have hh := csInf_le hb (product_value rho sigma hrho hm2 hx' hy')
    linarith
  have hh : sInf (values (partyProduct rho sigma)) - sInf (values sigma) ≤
      sInf (values rho) := by
    apply le_csInf hx
    intro x hx'
    have := h x hx'
    linarith
  change sInf (values (partyProduct rho sigma)) / 2 ≤
    sInf (values rho) / 2 + sInf (values sigma) / 2
  linarith

end
