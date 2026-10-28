-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P33.corollary1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:30:47.24599+00:00
-- url     : https://prove2.me/submissions/b6ae286c-3192-4c95-96c3-c170fd88abc3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_lemma1

-- ===== C1A =====

/-! Strong subadditivity for disjoint register sets (Claimed50.P33 conventions). -/

noncomputable section

namespace X4C1
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

lemma vn_inst {ι : Type*} [Fintype ι] (d1 d2 : DecidableEq ι) (X : Matrix ι ι ℂ) :
    @vnEntropy ι _ d1 X = @vnEntropy ι _ d2 X := by
  congr

lemma rm_comp {X K F K' F' : Type*} [Fintype X] [Fintype K] (ρ : Matrix X X ℂ)
    (k : X → K) (f : X → F) (k' : K → K') (f' : K → F') :
    redistributionMarginal (redistributionMarginal ρ k f) k' f' =
      redistributionMarginal ρ (k' ∘ k) (fun x => (f' (k x), f x)) := by
  ext a b
  simp only [redistributionMarginal]
  have h1 : ∀ u v : K, (if k' u = a ∧ k' v = b ∧ f' u = f' v then
      ∑ x : X, ∑ y : X, (if k x = u ∧ k y = v ∧ f x = f y then ρ x y else 0) else 0) =
      ∑ x : X, ∑ y : X, if k x = u then (if k y = v then
        (if k' (k x) = a ∧ k' (k y) = b ∧ (f' (k x), f x) = (f' (k y), f y) then ρ x y else 0)
        else 0) else 0 := by
    intro u v
    split_ifs with h
    · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      by_cases hx : k x = u <;> by_cases hy : k y = v <;> simp [hx, hy, h, Prod.ext_iff]
    · symm; refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
      by_cases hx : k x = u <;> by_cases hy : k y = v <;> simp only [hx, hy, if_false, if_true]
      subst hx hy
      rw [if_neg]; intro h'; apply h
      exact ⟨h'.1, h'.2.1, (Prod.ext_iff.1 h'.2.2).1⟩
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset K)) (t := (Finset.univ : Finset X))]
  simp [Finset.sum_ite_eq', Function.comp]

noncomputable def selM {X K F : Type*} (k : X → K) (f : X → F) (φ : F) : Matrix K X ℂ :=
  Matrix.of fun a x => if k x = a ∧ f x = φ then (1:ℂ) else 0

lemma rmA {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] (ρ : Matrix X X ℂ)
    (k : X → K) (f : X → F) :
    redistributionMarginal ρ k f = ∑ φ : F, selM k f φ * ρ * (selM k f φ)ᴴ := by
  ext a b
  simp only [redistributionMarginal, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, selM, of_apply,
    Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset F)) (t := (Finset.univ : Finset X))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (f x)]
  · by_cases hx : k x = a <;> by_cases hy : k y = b <;> by_cases hxy : f x = f y <;>
      simp [hx, hy, hxy, eq_comm]
  · intro φ _ hφ
    have : ¬ f x = φ := fun h => hφ h.symm
    simp [this]
  · simp

lemma rm_equiv {X K1 K2 F1 F2 : Type*} [Fintype X] (ρ : Matrix X X ℂ)
    (k1 : X → K1) (f1 : X → F1) (k2 : X → K2) (f2 : X → F2) (g : K1 ≃ K2)
    (hk : ∀ x, k2 x = g (k1 x)) (hf : ∀ x y, f1 x = f1 y ↔ f2 x = f2 y) :
    redistributionMarginal ρ k2 f2 = (redistributionMarginal ρ k1 f1).submatrix g.symm g.symm := by
  ext a b
  simp only [redistributionMarginal, submatrix_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hk, hk]; congr 1; apply propext
  rw [hf, Equiv.apply_eq_iff_eq_symm_apply, Equiv.apply_eq_iff_eq_symm_apply]

lemma rm_density {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] (ρ : Matrix X X ℂ)
    (k : X → K) (f : X → F) (hinj : ∀ x y, k x = k y → f x = f y → x = y)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (redistributionMarginal ρ k f) := by
  have hA := rmA ρ k f
  refine ⟨?_, ?_⟩
  · rw [hA]
    exact Matrix.posSemidef_sum _ fun φ _ => hρ.1.mul_mul_conjTranspose_same (selM k f φ)
  · rw [← hρ.2]
    simp only [Matrix.trace, Matrix.diag, redistributionMarginal]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single (k x)]
      · simp
      · intro b _ hb; rw [if_neg]; rintro ⟨h1, _⟩; exact hb h1.symm
      · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [if_neg]; rintro ⟨h1, h2, h3⟩; exact hy (hinj _ _ (h1.trans h2.symm) h3).symm
    · simp

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

/-- Restriction to a register set. -/
def restr (s : Finset (Fin n)) (x : RegisterBasis D) : SubBasis D s := fun i => x i.1

/-- Restriction to the complement of a register set. -/
def restrC (s : Finset (Fin n)) (x : RegisterBasis D) : (i : {i : Fin n // i ∉ s}) → D i.1 :=
  fun i => x i.1

lemma restr_eq {s : Finset (Fin n)} {x y : RegisterBasis D} :
    restr s x = restr s y ↔ ∀ i ∈ s, x i = y i := by
  simp [restr, funext_iff]

lemma restr_eq' {s : Finset (Fin n)} {x : RegisterBasis D} {c : SubBasis D s} :
    restr s x = c ↔ ∀ i (hi : i ∈ s), x i = c ⟨i, hi⟩ := by
  simp [restr, funext_iff]

lemma restrC_eq {s : Finset (Fin n)} {x y : RegisterBasis D} :
    restrC s x = restrC s y ↔ ∀ i, i ∉ s → x i = y i := by
  simp [restrC, funext_iff]

lemma reg_rm {E : Type} [Fintype E] (ρ : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Finset (Fin n)) :
    registerMarginal ρ s = redistributionMarginal ρ (fun x => (restr s x.1, x.2))
      (fun x => restrC s x.1) := by
  ext a b
  simp only [registerMarginal, redistributionMarginal, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single a.2]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single b.2]
    · congr 1
      apply propext
      simp only [Prod.ext_iff, restr_eq', restrC_eq, and_true]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun i hi => (h1 i hi).1, fun i hi => (h1 i hi).2, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨fun i hi => ⟨h1 i hi, h2 i hi⟩, h3⟩
    · intro e _ he; rw [if_neg]; intro h; exact he (Prod.ext_iff.1 h.2.1).2
    · simp
  · intro e _ he; refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun e' _ => ?_
    rw [if_neg]; intro h; exact he (Prod.ext_iff.1 h.1).2
  · simp

/-- Splitting a disjoint union of register sets. -/
def uE (s t : Finset (Fin n)) (h : Disjoint s t) : SubBasis D (s ∪ t) ≃ SubBasis D s × SubBasis D t where
  toFun f := (fun i => f ⟨i.1, Finset.mem_union_left _ i.2⟩,
    fun i => f ⟨i.1, Finset.mem_union_right _ i.2⟩)
  invFun p i := if hi : i.1 ∈ s then p.1 ⟨i.1, hi⟩ else
    p.2 ⟨i.1, (Finset.mem_union.1 i.2).resolve_left hi⟩
  left_inv f := by
    funext i; by_cases hi : i.1 ∈ s <;> simp [hi]
  right_inv p := by
    obtain ⟨p1, p2⟩ := p
    ext i
    · simp [i.2]
    · have : i.1 ∉ s := Finset.disjoint_right.1 h i.2
      simp [this]

end X4C1

end

-- ===== C1B =====

/-! Conditional mutual information of disjoint register sets is nonnegative. -/

noncomputable section

namespace X4C1
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

lemma vn_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) {X : Matrix ι ι ℂ} (hX : IsSelfAdjoint X) :
    vnEntropy (X.submatrix e e) = vnEntropy X := by
  let φ : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix κ κ ℂ :=
    { (Matrix.reindexAlgEquiv ℂ ℂ e.symm).toAlgHom with
      map_star' := fun M => by
        ext a b; simp [Matrix.star_eq_conjTranspose, Matrix.reindexAlgEquiv] }
  have hφ : ∀ M, φ M = M.submatrix e e := fun M => by
    ext a b; simp [φ, Matrix.reindexAlgEquiv]
  have hc : Continuous φ := by
    have : (φ : Matrix ι ι ℂ → Matrix κ κ ℂ) = fun M => M.submatrix e e := funext hφ
    rw [this]; fun_prop
  have hXs : IsSelfAdjoint (φ X) := hX.map φ
  unfold vnEntropy
  rw [← hφ, ← StarAlgHom.map_cfc φ (fun x : ℝ => x * Real.logb 2 x) X (hf := Matrix.finite_real_spectrum.continuousOn _) (hφ := hc) (ha := hX) (hφa := hXs), hφ]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [e.sum_comp (fun i => cfc (fun x : ℝ => x * Real.logb 2 x) X i i)]

lemma vn_reindex' {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι) {X : Matrix ι ι ℂ}
    (hX : IsSelfAdjoint X) (d1 : DecidableEq ι) (d2 : DecidableEq κ) :
    @vnEntropy κ _ d2 (X.submatrix e e) = @vnEntropy ι _ d1 X := by
  obtain rfl : d1 = Classical.decEq _ := Subsingleton.elim _ _
  obtain rfl : d2 = Classical.decEq _ := Subsingleton.elim _ _
  exact @vn_reindex ι κ _ _ _ _ e X hX

lemma restr_inj {s : Finset (Fin n)} {a b : RegisterBasis D} (h1 : restr s a = restr s b)
    (h2 : restrC s a = restrC s b) : a = b := by
  funext i
  by_cases hi : i ∈ s
  · exact restr_eq.1 h1 i hi
  · exact restrC_eq.1 h2 i hi

lemma ent_id {E : Type} [Fintype E] (ρ' : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (hρ' : IsDensityMatrix ρ') (s : Finset (Fin n)) {K2 F2 : Type} [Fintype K2]
    (k2 : RegisterBasis D × E → K2) (f2 : RegisterBasis D × E → F2) (g : SubBasis D s × E ≃ K2)
    (hk : ∀ x, k2 x = g (restr s x.1, x.2))
    (hf : ∀ x y, restrC s x.1 = restrC s y.1 ↔ f2 x = f2 y) (d : DecidableEq K2) :
    @vnEntropy K2 _ d (redistributionMarginal ρ' k2 f2) = entropyAt ρ' s := by
  rw [vn_inst d (Classical.decEq _)]
  have hd := rm_density ρ' (fun x => (restr s x.1, x.2)) (fun x => restrC s x.1)
    (fun x y h1 h2 => Prod.ext (restr_inj (Prod.ext_iff.1 h1).1 h2) (Prod.ext_iff.1 h1).2) hρ'
  rw [rm_equiv ρ' (fun x => (restr s x.1, x.2)) (fun x => restrC s x.1) k2 f2 g hk hf,
    vn_reindex' g.symm hd.1.isHermitian _ _, entropyAt, reg_rm]

variable [∀ i, Nonempty (D i)]

theorem ssa_reg (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hρ : IsDensityMatrix ρ)
    (X Y Z : Finset (Fin n)) (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    entropyAt (trivialExtension ρ) (X ∪ Y ∪ Z) + entropyAt (trivialExtension ρ) Z ≤
      entropyAt (trivialExtension ρ) (X ∪ Z) + entropyAt (trivialExtension ρ) (Y ∪ Z) := by
  set ρ' := trivialExtension ρ
  set S := X ∪ Y ∪ Z with hS
  let K : RegisterBasis D × Unit → SubBasis D X × (SubBasis D Y × SubBasis D Z) :=
    fun x => (restr X x.1, (restr Y x.1, restr Z x.1))
  let F : RegisterBasis D × Unit → ((i : {i : Fin n // i ∉ S}) → D i.1) := fun x => restrC S x.1
  have hρ' : IsDensityMatrix ρ' := by
    refine ⟨?_, ?_⟩
    · have e : ρ' = ρ.submatrix Prod.fst Prod.fst := rfl
      rw [e]; exact hρ.1.submatrix _
    · rw [← hρ.2]; simp [Matrix.trace, ρ', trivialExtension, Fintype.sum_prod_type]
  have hτ : IsDensityMatrix (redistributionMarginal ρ' K F) :=
    rm_density ρ' K F (fun x y h1 h2 => by
      have hx : x.1 = y.1 := by
        funext i
        by_cases hi : i ∈ S
        · simp only [hS, Finset.mem_union] at hi
          rcases hi with (hi | hi) | hi
          · exact restr_eq.1 (Prod.ext_iff.1 h1).1 i hi
          · exact restr_eq.1 (Prod.ext_iff.1 (Prod.ext_iff.1 h1).2).1 i hi
          · exact restr_eq.1 (Prod.ext_iff.1 (Prod.ext_iff.1 h1).2).2 i hi
        · exact restrC_eq.1 h2 i hi
      exact Prod.ext hx (Subsingleton.elim _ _)) hρ'
  have hssa := strongSubadditivity _ hτ
  rw [subsystemEntropy, subsystemEntropy, subsystemEntropy, rm_comp, rm_comp, rm_comp] at hssa
  rw [ent_id ρ' hρ' S K F ((Equiv.prodUnique _ Unit).trans ((uE (X ∪ Y) Z
      (Finset.disjoint_union_left.2 ⟨hXZ, hYZ⟩)).trans (((uE X Y hXY).prodCongr
      (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)))) (fun x => rfl) (fun x y => Iff.rfl) _] at hssa
  rw [ent_id ρ' hρ' (X ∪ Z) ((fun p => (p.1, p.2.2)) ∘ K) (fun x => ((K x).2.1, F x)) ((Equiv.prodUnique _ Unit).trans (uE X Z hXZ)) (fun x => rfl) (by
    intro x y
    simp only [Prod.ext_iff, restrC_eq, restr_eq, hS, Finset.mem_union, K, F]
    constructor
    · intro h
      exact ⟨fun i hi => h i (by
        rintro (h' | h')
        · exact Finset.disjoint_left.1 hXY h' hi
        · exact Finset.disjoint_left.1 hYZ hi h'),
        fun i hi => h i (by tauto)⟩
    · rintro ⟨h1, h2⟩ i hi
      by_cases hy : i ∈ Y
      · exact h1 i hy
      · exact h2 i (by tauto)) _] at hssa
  rw [ent_id ρ' hρ' (Y ∪ Z) ((fun p => p.2) ∘ K) (fun x => ((K x).1, F x)) ((Equiv.prodUnique _ Unit).trans (uE Y Z hYZ)) (fun x => rfl) (by
    intro x y
    simp only [Prod.ext_iff, restrC_eq, restr_eq, hS, Finset.mem_union, K, F]
    constructor
    · intro h
      exact ⟨fun i hi => h i (by
        rintro (h' | h')
        · exact Finset.disjoint_left.1 hXY hi h'
        · exact Finset.disjoint_left.1 hXZ hi h'),
        fun i hi => h i (by tauto)⟩
    · rintro ⟨h1, h2⟩ i hi
      by_cases hx : i ∈ X
      · exact h1 i hx
      · exact h2 i (by tauto)) _] at hssa
  rw [ent_id ρ' hρ' Z ((fun p => p.2.2) ∘ K) (fun x => (((K x).1, (K x).2.1), F x)) (Equiv.prodUnique _ Unit) (fun x => rfl) (by
    intro x y
    simp only [Prod.ext_iff, restrC_eq, restr_eq, hS, Finset.mem_union, K, F]
    constructor
    · intro h
      exact ⟨⟨fun i hi => h i (fun h' => Finset.disjoint_left.1 hXZ hi h'),
        fun i hi => h i (fun h' => Finset.disjoint_left.1 hYZ hi h')⟩,
        fun i hi => h i (by tauto)⟩
    · rintro ⟨⟨h1, h1'⟩, h2⟩ i hi
      by_cases hx : i ∈ X
      · exact h1 i hx
      by_cases hy : i ∈ Y
      · exact h1' i hy
      · exact h2 i (by tauto)) _] at hssa
  linarith

theorem cmi_nonneg (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hρ : IsDensityMatrix ρ)
    (X Y Z : Finset (Fin n)) (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    0 ≤ info .total ρ ![X, Y] Z := by
  have h := ssa_reg ρ hρ X Y Z hXY hXZ hYZ
  have hA : allParties ![X, Y] = X ∪ Y := by
    ext i; simp [allParties, Fin.exists_fin_two]
  simp only [info, conditionalMultipartiteInformation, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, hA]
  norm_num
  rw [Finset.union_assoc] at h
  linarith

end X4C1

end

-- ===== C1Sol =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

end QAlgorithms.Papers.Independent.Claimed50.P33

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (a ap b bp c cp e : Finset (Fin n))
    (hdis : DisjointRegisters ![a,ap,b,bp,c,cp] e) :
    ∀ kind : InformationKind,
      info kind rho ![a,b,c] (ap ∪ bp ∪ cp ∪ e) +
        info kind rho ![ap,bp,cp] e ≤
      info kind rho ![a ∪ ap,b ∪ bp,c ∪ cp] e := by
  obtain ⟨h1, h2⟩ := lemma1 rho hrho a ap b bp c cp e hdis
  have d := hdis.1
  have h01 : Disjoint a ap := d 0 1 (by decide)
  have h02 : Disjoint a b := d 0 2 (by decide)
  have h03 : Disjoint a bp := d 0 3 (by decide)
  have h04 : Disjoint a c := d 0 4 (by decide)
  have h05 : Disjoint a cp := d 0 5 (by decide)
  have h12 : Disjoint ap b := d 1 2 (by decide)
  have h13 : Disjoint ap bp := d 1 3 (by decide)
  have h14 : Disjoint ap c := d 1 4 (by decide)
  have h15 : Disjoint ap cp := d 1 5 (by decide)
  have h23 : Disjoint b bp := d 2 3 (by decide)
  have h24 : Disjoint b c := d 2 4 (by decide)
  have h25 : Disjoint b cp := d 2 5 (by decide)
  have h34 : Disjoint bp c := d 3 4 (by decide)
  have h35 : Disjoint bp cp := d 3 5 (by decide)
  have h45 : Disjoint c cp := d 4 5 (by decide)
  have e0 : Disjoint a e := hdis.2 0
  have e1 : Disjoint ap e := hdis.2 1
  have e2 : Disjoint b e := hdis.2 2
  have e3 : Disjoint bp e := hdis.2 3
  have e4 : Disjoint c e := hdis.2 4
  have e5 : Disjoint cp e := hdis.2 5
  intro kind
  cases kind
  · rw [h1]
    have r1 := X4C1.cmi_nonneg rho hrho a (bp ∪ cp) (ap ∪ e)
      (by simp [Finset.disjoint_union_right, *]) (by simp [Finset.disjoint_union_right, *])
      (by simp [Finset.disjoint_union_left, Finset.disjoint_union_right, *, disjoint_comm])
    have r2 := X4C1.cmi_nonneg rho hrho b (ap ∪ cp) (bp ∪ e)
      (by simp [Finset.disjoint_union_right, *, disjoint_comm])
      (by simp [Finset.disjoint_union_right, *])
      (by simp [Finset.disjoint_union_left, Finset.disjoint_union_right, *, disjoint_comm])
    have r3 := X4C1.cmi_nonneg rho hrho c (ap ∪ bp) (cp ∪ e)
      (by simp [Finset.disjoint_union_right, *, disjoint_comm])
      (by simp [Finset.disjoint_union_right, *])
      (by simp [Finset.disjoint_union_left, Finset.disjoint_union_right, *, disjoint_comm])
    linarith
  · rw [h2]
    have r1 := X4C1.cmi_nonneg rho hrho (a ∪ b) cp (ap ∪ bp ∪ e)
      (by simp [Finset.disjoint_union_left, *])
      (by simp [Finset.disjoint_union_left, Finset.disjoint_union_right, *, disjoint_comm])
      (by simp [Finset.disjoint_union_right, *, disjoint_comm])
    have r2 := X4C1.cmi_nonneg rho hrho (a ∪ c) bp (ap ∪ cp ∪ e)
      (by simp [Finset.disjoint_union_left, *, disjoint_comm])
      (by simp [Finset.disjoint_union_left, Finset.disjoint_union_right, *, disjoint_comm])
      (by simp [Finset.disjoint_union_right, *, disjoint_comm])
    have r3 := X4C1.cmi_nonneg rho hrho (b ∪ c) ap (bp ∪ cp ∪ e)
      (by simp [Finset.disjoint_union_left, *, disjoint_comm])
      (by simp [Finset.disjoint_union_left, Finset.disjoint_union_right, *, disjoint_comm])
      (by simp [Finset.disjoint_union_right, *, disjoint_comm])
    linarith

