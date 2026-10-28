-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P33.proposition2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:54:22.352395+00:00
-- url     : https://prove2.me/submissions/66e0e07e-624f-4bd8-93f3-890512b3a974

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_proposition1
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

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

-- ===== P2P1 =====

/-! Proposition 2 part 1 (local conditioning) from Proposition 1. -/

noncomputable section

namespace X4P2
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

theorem part1 {n k : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (a : Fin (k+2) → Finset (Fin n))
    (x : Finset (Fin n)) (hdis : DisjointRegisters a x) :
    ∀ kind : InformationKind, info kind rho a x ≤ info kind rho (attachFirst a x) ∅ := by
  obtain ⟨h1, -, h3, -⟩ := proposition1 rho hrho a x hdis
  intro kind
  cases kind with
  | total =>
    rw [h1]
    have : 0 ≤ ∑ i ∈ Finset.univ.erase 0, info .total rho ![x, a i] ∅ :=
      Finset.sum_nonneg fun i _ => X4C1.cmi_nonneg rho hrho x (a i) ∅
        (hdis.2 i).symm (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)
    linarith
  | dual =>
    rw [h3]
    have : 0 ≤ info .total rho ![x, laterParties a] ∅ := by
      refine X4C1.cmi_nonneg rho hrho x _ ∅ ?_ (Finset.disjoint_empty_right _)
        (Finset.disjoint_empty_right _)
      rw [laterParties, Finset.disjoint_biUnion_right]
      exact fun i _ => (hdis.2 i).symm
    linarith

end X4P2

end

-- ===== KFA =====

/-! Generic: two families with equal Gram data are related by a unitary matrix. -/

noncomputable section

namespace X4KF
open scoped Matrix ComplexConjugate InnerProductSpace

variable {P : Type*} [Fintype P]

end X4KF

end

-- ===== KFD =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFD (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix

variable {d e : ℕ}

end X4KF

end

-- ===== KFF =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFF (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix Polynomial

-- entropy swap S(VVᴴ) = S((VᴴV)ᵀ), copied from Solutions/X4/TRC.lean
theorem x4_tr_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem x4_tr_cfc_eq {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M1 : Matrix ι ι ℂ) (M2 : Matrix κ κ ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (h : ∀ k : ℕ, 1 ≤ k → (M1 ^ k).trace = (M2 ^ k).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f M1).trace = (cfc f M2).trace := by
  classical
  let S : Finset ℝ := Finset.univ.image h1.eigenvalues ∪ Finset.univ.image h2.eigenvalues ∪ {0}
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have e1 : cfc f M1 = cfc (fun x => p.eval x) M1 := by
    apply cfc_congr
    intro x hx
    rw [h1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have e2 : cfc f M2 = cfc (fun x => p.eval x) M2 := by
    apply cfc_congr
    intro x hx
    rw [h2.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [S]), hf]
  rw [e1, e2, cfc_polynomial p M1, cfc_polynomial p M2, x4_tr_aeval, x4_tr_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · rw [h i hi]

theorem x4_pow_mul {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem x4_tr_pow_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [x4_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- tr f(V Vᴴ) = tr f((Vᴴ V)ᵀ) when f 0 = 0. -/
theorem x4_ent_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) :
    QAlgorithms.vnEntropy (V * Vᴴ) = QAlgorithms.vnEntropy ((Vᴴ * V)ᵀ) := by
  unfold QAlgorithms.vnEntropy
  rw [x4_tr_cfc_eq (V * Vᴴ) ((Vᴴ * V)ᵀ) (isHermitian_mul_conjTranspose_self V)
    (isHermitian_conjTranspose_mul_self V).transpose _ _ (by simp)]
  intro k hk
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, x4_tr_pow_swap _ _ k hk]

variable {d m : ℕ}

end X4KF

end

-- ===== KFG =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] instKFF

namespace X4KF
open Matrix

variable {d m : ℕ}

variable {e : ℕ}

end X4KF

end

-- ===== DP =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) instDP (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _


namespace X4DP
open Matrix X4KF
open scoped InnerProductSpace

variable {d e : ℕ}

end X4DP

end QAlgorithms.Papers.Independent.Support50.P41

end


-- ===== FanoLib =====

/-! Generic: Schur concavity of von Neumann entropy and the (quantum) Fano bound. -/

noncomputable section

namespace X4FN
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

end X4FN

end

-- ===== SFB =====

/-! Generic: `Σ_k |tr(ρ E_k)|² ≤ F(ρ, Σ_k E_k ρ E_kᴴ)²` for PSD `ρ`. -/

noncomputable section

namespace X4SF
open Matrix QAlgorithms
open scoped Matrix ComplexOrder ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

end X4SF

end

-- ===== SUB =====

/-! Generic: subadditivity of von Neumann entropy, `S(AB) ≤ S(A) + S(B)`. -/

noncomputable section

namespace X4SU
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

end X4SU

end

-- ===== ZEA =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open scoped Matrix ComplexConjugate ComplexOrder

/-- spectral decomposition as a sum of eigenprojectors. -/
lemma spec_sum {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (h : ρ.IsHermitian) :
    ρ = ∑ k, ((h.eigenvalues k : ℝ) : ℂ) • pureDensity (h.eigenvectorBasis k) := by
  conv_lhs => rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [Matrix.mul_apply, diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    pureDensity, smul_eq_mul, Function.comp_apply, Matrix.star_apply, RCLike.star_def,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
    Finset.sum_ite_eq, Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.ofReal_eq_complex_ofReal]
  ring

end X4ZE

end

-- ===== LEA =====

/-! Generic von Neumann entropy facts: scaling, orthogonal rank-one sums, `S(Σσ) ≤ ΣS(σ)`
for unnormalized PSD terms, and concavity `Σ (S(σ_m) + p_m log p_m) ≤ S(Σσ)`. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

/-- square-root eigen-amplitudes of a PSD matrix. -/
def amp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (k a : ι) : ℂ :=
  ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * hσ.1.eigenvectorBasis k a

lemma amp_decomp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) :
    σ = ∑ k, Matrix.of fun a b => amp hσ k a * conj (amp hσ k b) := by
  conv_lhs => rw [X4ZE.spec_sum hσ.1]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext a b
  have hs : ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) =
      ((hσ.1.eigenvalues k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hσ.eigenvalues_nonneg k)]
  simp only [Matrix.smul_apply, pureDensity, Matrix.of_apply, smul_eq_mul, amp, map_mul,
    Complex.conj_ofReal]
  rw [← hs]; ring

end X4LE

end

-- ===== LEB =====

/-! Kraus branches of a bipartite pure vector: Bob marginals, the unnormalized entanglement
functional `Gv` and its monotonicity under Alice-side Kraus families. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)
open scoped Matrix ComplexConjugate ComplexOrder

variable {a b : ℕ}

end X4LE

end

-- ===== ERA =====

/-! Generic entropy facts: scaling with `c ≥ 0`, additivity on orthogonal PSD summands,
invariance under isometric conjugation, pure states, and the qubit bound `S ≤ 1`. -/

noncomputable section

namespace X4ER
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

/-- entropy is invariant under conjugation by an isometry. -/
lemma vn_conj_iso {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef) (J : Matrix κ ι ℂ) (hJ : Jᴴ * J = 1) :
    vnEntropy (J * X * Jᴴ) = vnEntropy X := by
  set V : Matrix ι ι ℂ := Matrix.of fun a k => X4LE.amp hX k a
  have hV : X = V * Vᴴ := by
    conv_lhs => rw [X4LE.amp_decomp hX]
    ext a b; simp [V, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
  have h1 : J * X * Jᴴ = (J * V) * (J * V)ᴴ := by
    rw [hV, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have h2 : (J * V)ᴴ * (J * V) = Vᴴ * V := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul]
  rw [h1, X4KF.x4_ent_swap, h2, ← X4KF.x4_ent_swap, ← hV]

end X4ER

end

-- ===== DPI =====

/-! Data processing for conditional entropy: a local channel on `A` (in Kraus form) does not
decrease `H(C | A Y)`, i.e. `S(AY) - S(AYC)` can only decrease. Proof: Stinespring isometry
from the Kraus family, isometric invariance of entropy, and strong subadditivity. -/

noncomputable section

namespace X4DPI
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

lemma rm_e {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] (M : Matrix X X ℂ) (e : X ≃ K × F)
    (k : X → K) (f : X → F) (hk : ∀ x, k x = (e x).1) (hf : ∀ x, f x = (e x).2) (a b : K) :
    redistributionMarginal M k f a b = ∑ φ, M (e.symm (a, φ)) (e.symm (b, φ)) := by
  simp only [redistributionMarginal, hk, hf]
  rw [← e.symm.sum_comp]
  simp_rw [← e.symm.sum_comp (fun y => if _ then _ else _)]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a, Finset.sum_comm, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_eq_single φ]
    · simp
    · intro ψ _ h; simp [Ne.symm h]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun φ _ => Finset.sum_eq_zero fun ψ _ => ?_
    simp [hc]
  · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun φ _ => Finset.sum_eq_zero fun ψ _ => Finset.sum_eq_zero fun d _ => ?_
    simp [hc]
  · simp

lemma sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

variable {A A' Y C R : Type} [Fintype A] [Fintype A'] [Fintype Y] [Fintype C] [Fintype R]
  {N : ℕ} (E : Fin N → Matrix A' A ℂ)

/-- Local action of the Kraus family on the first factor. -/
def act (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    Matrix ((A' × Y) × (C × R)) ((A' × Y) × (C × R)) ℂ :=
  fun u v => ∑ k, ∑ a, ∑ b, E k u.1.1 a * ρ ((a, u.1.2), u.2) ((b, v.1.2), v.2) * conj (E k v.1.1 b)

/-- Trace out `R`. -/
def M1 {B : Type} (X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ) :
    Matrix ((B × Y) × C) ((B × Y) × C) ℂ :=
  fun u v => ∑ r, X (u.1, (u.2, r)) (v.1, (v.2, r))

/-- Trace out `C × R`. -/
def M2 {B : Type} (X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ) :
    Matrix (B × Y) (B × Y) ℂ :=
  fun u v => ∑ c, ∑ r, X (u, (c, r)) (v, (c, r))

/-- Trace out the first factor. -/
def M0 {B : Type} [Fintype B] (X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ) :
    Matrix (Y × (C × R)) (Y × (C × R)) ℂ :=
  fun u v => ∑ a, X ((a, u.1), u.2) ((a, v.1), v.2)

lemma M0_rm {B : Type} [Fintype B] (X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ) :
    M0 X = redistributionMarginal X (fun x => (x.1.2, x.2)) (fun x => x.1.1) := by
  funext u v
  rw [rm_e X ((Equiv.prodAssoc _ _ _).trans (Equiv.prodComm _ _)) (fun x => (x.1.2, x.2)) (fun x => x.1.1)
    (fun _ => rfl) (fun _ => rfl)]
  rfl

lemma M1_rm {B : Type} [Fintype B] (X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ) :
    M1 X = redistributionMarginal X (fun x => (x.1, x.2.1)) (fun x => x.2.2) := by
  funext u v
  rw [rm_e X (Equiv.prodAssoc _ _ _).symm (fun x => (x.1, x.2.1)) (fun x => x.2.2) (fun _ => rfl) (fun _ => rfl)]
  rfl

lemma M2_rm {B : Type} [Fintype B] (X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ) :
    M2 X = redistributionMarginal X (fun x => x.1) (fun x => x.2) := by
  funext u v
  rw [rm_e X (Equiv.refl _) (fun x => x.1) (fun x => x.2) (fun _ => rfl) (fun _ => rfl)]
  simp only [M2, Fintype.sum_prod_type]
  rfl

/-- Kraus operators of the local action. -/
def L (Y C R : Type) (k : Fin N) : Matrix ((A' × Y) × (C × R)) ((A × Y) × (C × R)) ℂ :=
  Matrix.of fun u x => if u.1.2 = x.1.2 ∧ u.2 = x.2 then E k u.1.1 x.1.1 else 0

lemma L_mul (k : Fin N) (g : (A × Y) × (C × R) → ℂ) (u : (A' × Y) × (C × R)) :
    ∑ x, L E Y C R k u x * g x = ∑ a, E k u.1.1 a * g ((a, u.1.2), u.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_eq_single u.1.2]
  · simp [L]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, Ne.symm hy]
  · simp
  · intro z _ hz; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, Ne.symm hz]
  · simp

lemma L_mul' (k : Fin N) (g : (A × Y) × (C × R) → ℂ) (u : (A' × Y) × (C × R)) :
    ∑ x, star (L E Y C R k u x) * g x = ∑ a, star (E k u.1.1 a) * g ((a, u.1.2), u.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_eq_single u.1.2]
  · simp [L]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, Ne.symm hy]
  · simp
  · intro z _ hz; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, Ne.symm hz]
  · simp

lemma L_iso (hE : ∑ k, (E k)ᴴ * E k = 1) :
    ∑ k, (L E Y C R k)ᴴ * L E Y C R k = 1 := by
  ext u v
  have h := congrFun (congrFun hE u.1.1) v.1.1
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply] at h
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply]
  have key : ∀ k, ∑ x : (A' × Y) × (C × R), star (L E Y C R k x u) * L E Y C R k x v =
      if u.1.2 = v.1.2 ∧ u.2 = v.2 then ∑ a, star (E k a u.1.1) * E k a v.1.1 else 0 := by
    intro k
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2, Fintype.sum_prod_type,
      Finset.sum_comm, Finset.sum_eq_single u.1.2]
    · by_cases h1 : u.1.2 = v.1.2 <;> by_cases h2 : u.2 = v.2 <;> simp [L, h1, h2]
    · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, hy]
    · simp
    · intro z _ hz; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, hz]
    · simp
  simp_rw [key]
  by_cases hc : u.1.2 = v.1.2 ∧ u.2 = v.2
  · simp only [hc, and_self, if_true, h, Matrix.one_apply]
    obtain ⟨⟨a, y⟩, z⟩ := u; obtain ⟨⟨b, y'⟩, z'⟩ := v
    obtain ⟨h1, h2⟩ := hc; simp only at h1 h2; subst h1 h2
    simp [Prod.ext_iff]
  · simp only [hc, if_false, Finset.sum_const_zero, Matrix.one_apply]
    rw [if_neg]; rintro rfl; exact hc ⟨rfl, rfl⟩

lemma act_eq (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    act E ρ = ∑ k, L E Y C R k * ρ * (L E Y C R k)ᴴ := by
  ext u v
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [L_mul E k (fun x => ρ x _), Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  have : ∀ i, ∑ x, E k u.1.1 i * ρ ((i, u.1.2), u.2) x * star (L E Y C R k v x) =
      ∑ b, star (E k v.1.1 b) * (E k u.1.1 i * ρ ((i, u.1.2), u.2) ((b, v.1.2), v.2)) := by
    intro i
    simp_rw [mul_comm _ (star (L E Y C R k v _))]
    exact L_mul' E k (fun x => E k u.1.1 i * ρ ((i, u.1.2), u.2) x) v
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [RCLike.star_def]; ring

lemma act_M0 (hE : ∑ k, (E k)ᴴ * E k = 1) (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    M0 (act E ρ) = M0 ρ := by
  funext u v
  simp only [M0, act]
  have h : ∀ a b : A, ∑ k, ∑ a', E k a' a * conj (E k a' b) = if b = a then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hE b) a
    simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a' _ => ?_
    simp [mul_comm]
  calc ∑ a', ∑ k, ∑ a, ∑ b, E k a' a * ρ ((a, u.1), u.2) ((b, v.1), v.2) * conj (E k a' b)
      = ∑ a, ∑ b, ρ ((a, u.1), u.2) ((b, v.1), v.2) * ∑ k, ∑ a', E k a' a * conj (E k a' b) := by
        rw [sum4 (fun a' k a b => E k a' a * ρ ((a, u.1), u.2) ((b, v.1), v.2) * conj (E k a' b))]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
        ring
    _ = _ := by
        simp_rw [h]
        simp

lemma act_density (hE : ∑ k, (E k)ᴴ * E k = 1)
    {ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (act E ρ) := by
  rw [act_eq]
  refine ⟨Matrix.posSemidef_sum _ fun k _ => hρ.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (L E Y C R _)]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, L_iso E hE, one_mul, hρ.2]

/-- The SSA state: Stinespring dilation of the `R`-marginal, reordered as `K × (C × (A' × Y))`. -/
def om (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    Matrix (Fin N × (C × (A' × Y))) (Fin N × (C × (A' × Y))) ℂ :=
  fun u v => ∑ r, ∑ a, ∑ b, E u.1 u.2.2.1 a * ρ ((a, u.2.2.2), (u.2.1, r)) ((b, v.2.2.2), (v.2.1, r)) *
    conj (E v.1 v.2.2.1 b)

def W1 (Y C : Type) : Matrix (Fin N × (C × (A' × Y))) ((A × Y) × C) ℂ :=
  Matrix.of fun u x => if x.1.2 = u.2.2.2 ∧ x.2 = u.2.1 then E u.1 u.2.2.1 x.1.1 else 0

def W2 (Y : Type) : Matrix (Fin N × (A' × Y)) (A × Y) ℂ :=
  Matrix.of fun u x => if x.2 = u.2.2 then E u.1 u.2.1 x.1 else 0

lemma W1_mul (g : (A × Y) × C → ℂ) (u : Fin N × (C × (A' × Y))) :
    ∑ x, W1 E Y C u x * g x = ∑ a, E u.1 u.2.2.1 a * g ((a, u.2.2.2), u.2.1) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2.1, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_eq_single u.2.2.2]
  · simp [W1]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W1, hy]
  · simp
  · intro z _ hz; refine Finset.sum_eq_zero fun a _ => ?_; simp [W1, hz]
  · simp

lemma W1_mul' (g : (A × Y) × C → ℂ) (u : Fin N × (C × (A' × Y))) :
    ∑ x, star (W1 E Y C u x) * g x = ∑ a, star (E u.1 u.2.2.1 a) * g ((a, u.2.2.2), u.2.1) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2.1, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_eq_single u.2.2.2]
  · simp [W1]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W1, hy]
  · simp
  · intro z _ hz; refine Finset.sum_eq_zero fun a _ => ?_; simp [W1, hz]
  · simp

lemma W2_mul (g : A × Y → ℂ) (u : Fin N × (A' × Y)) :
    ∑ x, W2 E Y u x * g x = ∑ a, E u.1 u.2.1 a * g (a, u.2.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2.2]
  · simp [W2]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W2, hy]
  · simp

lemma W2_mul' (g : A × Y → ℂ) (u : Fin N × (A' × Y)) :
    ∑ x, star (W2 E Y u x) * g x = ∑ a, star (E u.1 u.2.1 a) * g (a, u.2.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2.2]
  · simp [W2]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W2, hy]
  · simp

lemma W1_iso (hE : ∑ k, (E k)ᴴ * E k = 1) : (W1 E Y C)ᴴ * W1 E Y C = 1 := by
  ext u v
  have h := congrFun (congrFun hE u.1.1) v.1.1
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply] at h
  simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  have key : ∀ k, ∑ y : C × (A' × Y), star (W1 E Y C (k, y) u) * W1 E Y C (k, y) v =
      if u.1.2 = v.1.2 ∧ u.2 = v.2 then ∑ a, star (E k a u.1.1) * E k a v.1.1 else 0 := by
    intro k
    rw [Fintype.sum_prod_type, Finset.sum_eq_single u.2]
    · rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.1.2]
      · by_cases h1 : u.1.2 = v.1.2 <;> by_cases h2 : u.2 = v.2 <;> simp [W1, h1, h2, eq_comm]
      · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W1, Ne.symm hy]
      · simp
    · intro z _ hz; refine Finset.sum_eq_zero fun y _ => ?_
      simp [W1, Ne.symm hz]
    · simp
  simp_rw [key]
  by_cases hc : u.1.2 = v.1.2 ∧ u.2 = v.2
  · simp only [hc, and_self, if_true, h, Matrix.one_apply]
    obtain ⟨⟨a, y⟩, z⟩ := u; obtain ⟨⟨b, y'⟩, z'⟩ := v
    obtain ⟨h1, h2⟩ := hc; simp only at h1 h2; subst h1 h2
    simp [Prod.ext_iff]
  · simp only [hc, if_false, Finset.sum_const_zero, Matrix.one_apply]
    rw [if_neg]; rintro rfl; exact hc ⟨rfl, rfl⟩

lemma W2_iso (hE : ∑ k, (E k)ᴴ * E k = 1) : (W2 E Y)ᴴ * W2 E Y = 1 := by
  ext u v
  have h := congrFun (congrFun hE u.1) v.1
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply] at h
  simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  have key : ∀ k, ∑ y : A' × Y, star (W2 E Y (k, y) u) * W2 E Y (k, y) v =
      if u.2 = v.2 then ∑ a, star (E k a u.1) * E k a v.1 else 0 := by
    intro k
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2]
    · by_cases h1 : u.2 = v.2 <;> simp [W2, h1, eq_comm]
    · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W2, Ne.symm hy]
    · simp
  simp_rw [key]
  by_cases hc : u.2 = v.2
  · simp only [hc, if_true, h, Matrix.one_apply]
    obtain ⟨a, y⟩ := u; obtain ⟨b, y'⟩ := v
    simp only at hc; subst hc
    simp [Prod.ext_iff]
  · simp only [hc, if_false, Finset.sum_const_zero, Matrix.one_apply]
    rw [if_neg]; rintro rfl; exact hc rfl

lemma om_eq (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    om E ρ = W1 E Y C * M1 ρ * (W1 E Y C)ᴴ := by
  ext u v
  simp only [Matrix.mul_apply, conjTranspose_apply]
  simp_rw [W1_mul E (fun x => M1 ρ x _), Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ i, ∑ x, E u.1 u.2.2.1 i * M1 ρ ((i, u.2.2.2), u.2.1) x * star (W1 E Y C v x) =
      ∑ b, star (E v.1 v.2.2.1 b) * (E u.1 u.2.2.1 i * M1 ρ ((i, u.2.2.2), u.2.1) ((b, v.2.2.2), v.2.1)) := by
    intro i
    simp_rw [mul_comm _ (star (W1 E Y C v _))]
    exact W1_mul' E (fun x => E u.1 u.2.2.1 i * M1 ρ ((i, u.2.2.2), u.2.1) x) v
  simp_rw [this]
  simp only [om, M1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun r _ => ?_
  simp only [RCLike.star_def]; ring

lemma rm_om1 (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    redistributionMarginal (om E ρ) (fun p => (p.1, p.2.2)) (fun p => p.2.1) =
      W2 E Y * M2 ρ * (W2 E Y)ᴴ := by
  funext u v
  rw [rm_e (om E ρ) (((Equiv.refl (Fin N)).prodCongr (Equiv.prodComm C (A' × Y))).trans
    (Equiv.prodAssoc _ _ _).symm) (fun p => (p.1, p.2.2)) (fun p => p.2.1) (fun _ => rfl) (fun _ => rfl)]
  simp only [Matrix.mul_apply, conjTranspose_apply]
  simp_rw [W2_mul E (fun x => M2 ρ x _), Finset.sum_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (A × Y)))]
  have : ∀ i, ∑ x, E u.1 u.2.1 i * M2 ρ (i, u.2.2) x * star (W2 E Y v x) =
      ∑ b, star (E v.1 v.2.1 b) * (E u.1 u.2.1 i * M2 ρ (i, u.2.2) (b, v.2.2)) := by
    intro i
    simp_rw [mul_comm _ (star (W2 E Y v _))]
    exact W2_mul' E (fun x => E u.1 u.2.1 i * M2 ρ (i, u.2.2) x) v
  simp_rw [this]
  simp only [om, M2, Finset.mul_sum, Equiv.trans_apply, Equiv.prodAssoc_symm_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.refl_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.map, Prod.swap, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.prodAssoc_apply]
  rw [sum4 (fun x x_1 x_2 i => star (E v.1 v.2.1 x_1) * (E u.1 u.2.1 x * ρ ((x, u.2.2), x_2, i) ((x_1, v.2.2), x_2, i)))]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  simp only [RCLike.star_def]; ring

lemma rm_om2 (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    redistributionMarginal (om E ρ) (fun p => p.2) (fun p => p.1) =
      (M1 (act E ρ)).submatrix (Equiv.prodComm C (A' × Y)) (Equiv.prodComm C (A' × Y)) := by
  funext u v
  rw [rm_e (om E ρ) (Equiv.prodComm (Fin N) (C × (A' × Y))) (fun p => p.2) (fun p => p.1)
    (fun _ => rfl) (fun _ => rfl)]
  simp only [om, M1, act, Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap]
  rw [Finset.sum_comm]

lemma rm_om3 (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    redistributionMarginal (om E ρ) (fun p => p.2.2) (fun p => (p.1, p.2.1)) = M2 (act E ρ) := by
  funext u v
  rw [rm_e (om E ρ) ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _)) (fun p => p.2.2)
    (fun p => (p.1, p.2.1)) (fun _ => rfl) (fun _ => rfl)]
  simp only [om, M2, act, Fintype.sum_prod_type, Equiv.symm_trans_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.swap, Equiv.symm_symm, Equiv.prodAssoc_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

theorem dpi [Nonempty A] [Nonempty A'] [Nonempty Y] [Nonempty C] [Nonempty R]
    (hE : ∑ k, (E k)ᴴ * E k = 1) {ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ}
    (hρ : IsDensityMatrix ρ) :
    vnEntropy (M2 (act E ρ)) - vnEntropy (M1 (act E ρ)) ≤ vnEntropy (M2 ρ) - vnEntropy (M1 ρ) := by
  have hN : Nonempty (Fin N) := by
    rcases N with _ | N
    · exfalso
      obtain ⟨a⟩ := ‹Nonempty A›
      have := congrFun (congrFun hE a) a
      simp at this
    · exact ⟨0⟩
  have hM1 : ∀ {B : Type} [Fintype B] {X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ},
      IsDensityMatrix X → IsDensityMatrix (M1 X) := fun {B} _ {X} hX => by
    rw [M1_rm]
    exact X4C1.rm_density _ _ _ (fun x y h1 h2 => by
      obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y
      simp only [Prod.mk.injEq] at h1 h2 ⊢; exact ⟨h1.1, h1.2, h2⟩) hX
  have hM2 : IsDensityMatrix (M2 ρ) := by
    rw [M2_rm]
    exact X4C1.rm_density _ _ _ (fun x y h1 h2 => Prod.ext h1 h2) hρ
  have hσ := act_density E hE hρ
  have hω : IsDensityMatrix (om E ρ) := by
    rw [om_eq]
    refine ⟨(hM1 hρ).1.mul_mul_conjTranspose_same _, ?_⟩
    rw [Matrix.trace_mul_cycle, W1_iso E hE, Matrix.one_mul, (hM1 hρ).2]
  have h := strongSubadditivity (om E ρ) hω
  simp only [subsystemEntropy] at h
  rw [rm_om1, rm_om2, rm_om3, om_eq] at h
  have key : 0 ≤ vnEntropy (W2 E Y * M2 ρ * (W2 E Y)ᴴ) +
      vnEntropy ((M1 (act E ρ)).submatrix (Equiv.prodComm C (A' × Y)) (Equiv.prodComm C (A' × Y))) -
      vnEntropy (M2 (act E ρ)) - vnEntropy (W1 E Y C * M1 ρ * (W1 E Y C)ᴴ) := by
    convert h
  have e1 : vnEntropy (W1 E Y C * M1 ρ * (W1 E Y C)ᴴ) = vnEntropy (M1 ρ) :=
    X4ER.vn_conj_iso (hM1 hρ).1 _ (W1_iso E hE)
  have e2 : vnEntropy (W2 E Y * M2 ρ * (W2 E Y)ᴴ) = vnEntropy (M2 ρ) :=
    X4ER.vn_conj_iso hM2.1 _ (W2_iso E hE)
  have e3 : vnEntropy ((M1 (act E ρ)).submatrix (Equiv.prodComm C (A' × Y))
      (Equiv.prodComm C (A' × Y))) = vnEntropy (M1 (act E ρ)) :=
    X4C1.vn_reindex _ (hM1 hσ).1.isHermitian
  linarith

end X4DPI

end

-- ===== P2B =====

/-! Register bookkeeping for local channels in Claimed50.P33: the register state, read in the
coordinates `(D p × (U\{p}, E)) × (C × rest)`, is acted on by the Kraus family on the first factor. -/

noncomputable section

namespace X4P2
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} (p : Fin n) (U C : Finset (Fin n))

/-- Rest registers outside `S`. -/
abbrev Rest (G : Fin n → Type) (S : Finset (Fin n)) := (i : {i : Fin n // i ∉ S}) → G i.1

/-- Coordinates of the global basis. -/
def eG (G : Fin n → Type) (E : Type) (hp : p ∈ U) (hUC : Disjoint U C) :
    RegisterBasis G × E ≃ (G p × (SubBasis G (U.erase p) × E)) × (SubBasis G C × Rest G (U ∪ C)) where
  toFun x := ((x.1 p, (fun i => x.1 i.1, x.2)), (fun i => x.1 i.1, fun i => x.1 i.1))
  invFun q := (fun i => if h : i = p then cast (by rw [h]) q.1.1 else
      if hi : i ∈ U then q.1.2.1 ⟨i, Finset.mem_erase.2 ⟨h, hi⟩⟩ else
      if hc : i ∈ C then q.2.1 ⟨i, hc⟩ else q.2.2 ⟨i, by simp [hi, hc]⟩, q.1.2.2)
  left_inv x := by
    obtain ⟨x, e⟩ := x
    ext i
    · simp only
      by_cases h : i = p
      · subst h; simp
      · simp only [h, dite_false]
        by_cases hi : i ∈ U
        · simp [hi]
        · by_cases hc : i ∈ C <;> simp [hi, hc]
    · rfl
  right_inv q := by
    obtain ⟨⟨a, y, e⟩, c, r⟩ := q
    have hpC : p ∉ C := Finset.disjoint_left.1 hUC hp
    ext i
    · simp
    · obtain ⟨i, hi⟩ := i
      have h1 := (Finset.mem_erase.1 hi)
      simp [h1.1, h1.2]
    · rfl
    · obtain ⟨i, hi⟩ := i
      have h1 : i ≠ p := fun h => hpC (h ▸ hi)
      have h2 : i ∉ U := Finset.disjoint_right.1 hUC hi
      simp [h1, h2, hi]
    · obtain ⟨i, hi⟩ := i
      have h1 : i ≠ p := fun h => hi (h ▸ Finset.mem_union_left _ hp)
      simp only [Finset.mem_union, not_or] at hi
      simp [h1, hi.1, hi.2]

/-- Split off register `p`. -/
def splitS (G : Fin n → Type) (s : Finset (Fin n)) (hs : p ∈ s) :
    SubBasis G s ≃ G p × SubBasis G (s.erase p) where
  toFun f := (f ⟨p, hs⟩, fun i => f ⟨i.1, Finset.mem_of_mem_erase i.2⟩)
  invFun q i := if h : i.1 = p then cast (by rw [h]) q.1 else q.2 ⟨i.1, Finset.mem_erase.2 ⟨h, i.2⟩⟩
  left_inv f := by
    funext ⟨i, hi⟩
    by_cases h : i = p
    · subst h; simp
    · simp [h]
  right_inv q := by
    obtain ⟨a, g⟩ := q
    refine Prod.ext (by simp) (funext fun ⟨i, hi⟩ => ?_)
    simp [(Finset.mem_erase.1 hi).1]

variable {D F : Fin n → Type} (other : ∀ j, j ≠ p → D j ≃ F j)

/-- Transport registers away from `p`. -/
def trS (s : Finset (Fin n)) (hp : p ∉ s) : SubBasis F s ≃ SubBasis D s :=
  Equiv.piCongrRight fun i => (other i.1 (fun h => hp (h ▸ i.2))).symm

def trR (S : Finset (Fin n)) (hp : p ∈ S) : Rest F S ≃ Rest D S :=
  Equiv.piCongrRight fun i => (other i.1 (fun h => i.2 (h ▸ hp))).symm

/-- Coordinates of the output basis, sharing the non-`p` factors with the input. -/
def eF (E : Type) (hp : p ∈ U) (hUC : Disjoint U C) :
    RegisterBasis F × E ≃ (F p × (SubBasis D (U.erase p) × E)) × (SubBasis D C × Rest D (U ∪ C)) :=
  (eG p U C F E hp hUC).trans (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (trS p other (U.erase p) (Finset.notMem_erase p U)) (Equiv.refl E)))
    (Equiv.prodCongr (trS p other C (Finset.disjoint_left.1 hUC hp))
      (trR p other (U ∪ C) (Finset.mem_union_left _ hp))))

variable {E : Type} (hp : p ∈ U) (hUC : Disjoint U C)

/-- Input basis vector with the non-`p` registers read off from `u`. -/
def xs (u : RegisterBasis F × E) (a : D p) : RegisterBasis D × E :=
  (eG p U C D E hp hUC).symm ((a, (eF p U C other E hp hUC u).1.2), (eF p U C other E hp hUC u).2)

lemma xs_p (u : RegisterBasis F × E) (a : D p) : (xs p U C other hp hUC u a).1 p = a := by
  simp [xs, eG]

lemma xs_other (u : RegisterBasis F × E) (a : D p) (j : Fin n) (hj : j ≠ p) :
    (xs p U C other hp hUC u a).1 j = (other j hj).symm (u.1 j) := by
  simp only [xs, eG, eF, Equiv.coe_fn_symm_mk, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, trS, trR, Equiv.piCongrRight_apply, hj, dite_false]
  split_ifs <;> rfl

lemma xs_cond (u : RegisterBasis F × E) (x : RegisterBasis D) :
    (∀ j (hj : j ≠ p), u.1 j = other j hj (x j)) ↔ ∃ a, x = (xs p U C other hp hUC u a).1 := by
  constructor
  · intro h
    refine ⟨x p, funext fun j => ?_⟩
    by_cases hj : j = p
    · subst hj; rw [xs_p]
    · rw [xs_other _ _ _ _ _ _ _ _ _ hj, h j hj, Equiv.symm_apply_apply]
  · rintro ⟨a, rfl⟩ j hj
    rw [xs_other _ _ _ _ _ _ _ _ _ hj, Equiv.apply_symm_apply]

lemma sum_cond [∀ i, Fintype (D i)] (u : RegisterBasis F × E) (g : RegisterBasis D → ℂ) :
    ∑ x, (if ∀ j (hj : j ≠ p), u.1 j = other j hj (x j) then g x else 0) =
      ∑ a, g (xs p U C other hp hUC u a).1 := by
  have hinj : ∀ a b, (xs p U C other hp hUC u a).1 = (xs p U C other hp hUC u b).1 → a = b := by
    intro a b h
    rw [← xs_p p U C other hp hUC u a, ← xs_p p U C other hp hUC u b, h]
  symm
  calc ∑ a, g (xs p U C other hp hUC u a).1
      = ∑ a, ∑ x, if x = (xs p U C other hp hUC u a).1 then g x else 0 := by
        simp
    _ = ∑ x, ∑ a, if x = (xs p U C other hp hUC u a).1 then g x else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : ∃ a, x = (xs p U C other hp hUC u a).1
        · obtain ⟨a, ha⟩ := hx
          rw [if_pos ((xs_cond p U C other hp hUC u x).2 ⟨a, ha⟩), Finset.sum_eq_single a]
          · simp [ha]
          · intro b _ hb; rw [if_neg]; intro h; exact hb (hinj _ _ (h.symm.trans ha))
          · simp
        · rw [if_neg (fun h => hx ((xs_cond p U C other hp hUC u x).1 h))]
          exact Finset.sum_eq_zero fun a _ => if_neg fun h => hx ⟨a, h⟩

lemma kraus_single {A B : Type} [Fintype A] {N : ℕ} (K : Fin N → Matrix B A ℂ)
    (a b : A) (c d : B) :
    krausApply K (Matrix.single a b 1) c d = ∑ k, K k c a * conj (K k d b) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.single_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single b, Finset.sum_eq_single a]
  · simp
  · intro i _ hi; simp [Ne.symm hi]
  · simp
  · intro j _ hj; rw [Finset.sum_eq_zero]; · simp
    intro i _; simp [Ne.symm hj]
  · simp

lemma la_eq [∀ i, Fintype (D i)] [Fintype E] {N : ℕ} (K : Fin N → Matrix (F p) (D p) ℂ)
    (Φ : Superop (D p) (F p)) (hΦ : ∀ ρ, Φ ρ = krausApply K ρ)
    (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) :
    localAction p other Φ r = (X4DPI.act K (r.submatrix (eG p U C D E hp hUC).symm
      (eG p U C D E hp hUC).symm)).submatrix (eF p U C other E hp hUC) (eF p U C other E hp hUC) := by
  funext u v
  simp only [localAction, submatrix_apply, forall_and, ite_and]
  have h1 : ∀ x : RegisterBasis D, (∑ y : RegisterBasis D, if ∀ j (hj : j ≠ p), u.1 j = other j hj (x j) then
      (if ∀ j (hj : j ≠ p), v.1 j = other j hj (y j) then
        r (x, u.2) (y, v.2) * Φ (Matrix.single (x p) (y p) 1) (u.1 p) (v.1 p) else 0) else 0) =
      if ∀ j (hj : j ≠ p), u.1 j = other j hj (x j) then (∑ y : RegisterBasis D,
      (if ∀ j (hj : j ≠ p), v.1 j = other j hj (y j) then
        r (x, u.2) (y, v.2) * Φ (Matrix.single (x p) (y p) 1) (u.1 p) (v.1 p) else 0)) else 0 := by
    intro x; split_ifs <;> simp
  simp_rw [h1]
  rw [sum_cond p U C other hp hUC u]
  simp_rw [sum_cond p U C other hp hUC v]
  simp only [X4DPI.act, submatrix_apply, xs_p, hΦ]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [kraus_single, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have ha : (eF p U C other E hp hUC u).1.1 = u.1 p := rfl
  have hb : (eF p U C other E hp hUC v).1.1 = v.1 p := rfl
  rw [ha, hb]
  have hx : ((xs p U C other hp hUC u a).1, u.2) = (eG p U C D E hp hUC).symm
      ((a, (eF p U C other E hp hUC u).1.2), (eF p U C other E hp hUC u).2) := rfl
  have hy : ((xs p U C other hp hUC v b).1, v.2) = (eG p U C D E hp hUC).symm
      ((b, (eF p U C other E hp hUC v).1.2), (eF p U C other E hp hUC v).2) := rfl
  rw [hx, hy]
  ring

lemma rm_sub {X T K F : Type*} [Fintype X] [Fintype T] (M : Matrix X X ℂ) (e : X ≃ T)
    (k : T → K) (f : T → F) :
    redistributionMarginal (M.submatrix e.symm e.symm) k f = redistributionMarginal M (k ∘ e) (f ∘ e) := by
  funext a b
  simp only [redistributionMarginal, submatrix_apply, Function.comp]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← e.sum_comp]
  simp

lemma dens_sub {X T : Type} [Fintype X] [Fintype T] {M : Matrix X X ℂ} (e : T ≃ X)
    (hM : IsDensityMatrix M) : IsDensityMatrix (M.submatrix e e) := by
  refine ⟨hM.1.submatrix _, ?_⟩
  rw [← hM.2]
  simp only [Matrix.trace, Matrix.diag, submatrix_apply]
  exact e.sum_comp (fun i => M i i)

lemma ent_sub {G : Fin n → Type} [∀ i, Fintype (G i)] {E : Type} [Fintype E] {T K F : Type}
    [Fintype T] [Fintype K] (X : Matrix (RegisterBasis G × E) (RegisterBasis G × E) ℂ)
    (hX : IsDensityMatrix X) (s : Finset (Fin n)) (e : RegisterBasis G × E ≃ T) (k : T → K) (f : T → F)
    (g : SubBasis G s × E ≃ K) (hk : ∀ x, k (e x) = g (X4C1.restr s x.1, x.2))
    (hf : ∀ x y, X4C1.restrC s x.1 = X4C1.restrC s y.1 ↔ f (e x) = f (e y)) (d : DecidableEq K) :
    @vnEntropy K _ d (redistributionMarginal (X.submatrix e.symm e.symm) k f) = entropyAt X s := by
  rw [rm_sub]
  exact X4C1.ent_id X hX s (k ∘ e) (f ∘ e) g hk hf d


def gU (G : Fin n → Type) (E : Type) :
    SubBasis G U × E ≃ G p × (SubBasis G (U.erase p) × E) :=
  ((splitS p G U hp).prodCongr (Equiv.refl E)).trans (Equiv.prodAssoc _ _ _)

def rearr (P Q R : Type) : (P × Q) × R ≃ (P × R) × Q :=
  (Equiv.prodAssoc _ _ _).trans (((Equiv.refl _).prodCongr (Equiv.prodComm _ _)).trans
    (Equiv.prodAssoc _ _ _).symm)

def gV (G : Fin n → Type) (E : Type) :
    SubBasis G (U ∪ C) × E ≃ (G p × (SubBasis G (U.erase p) × E)) × SubBasis G C :=
  (((X4C1.uE U C hUC).prodCongr (Equiv.refl E)).trans (rearr _ _ _)).trans
    ((gU p U hp G E).prodCongr (Equiv.refl _))

lemma hfG (G : Fin n → Type) (E : Type) (x y : RegisterBasis G × E) :
    X4C1.restrC U x.1 = X4C1.restrC U y.1 ↔ (eG p U C G E hp hUC x).2 = (eG p U C G E hp hUC y).2 := by
  simp only [X4C1.restrC, eG, Equiv.coe_fn_mk, Prod.mk.injEq, funext_iff, Subtype.forall]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Finset.disjoint_right.1 hUC ha), fun a ha => h a (fun h' => ha (Finset.mem_union_left _ h'))⟩
  · rintro ⟨h1, h2⟩ a ha
    by_cases hc : a ∈ C
    · exact h1 a hc
    · exact h2 a (by simp [ha, hc])

def gUF (E : Type) : SubBasis F U × E ≃ F p × (SubBasis D (U.erase p) × E) :=
  (gU p U hp F E).trans ((Equiv.refl _).prodCongr
    ((trS p other (U.erase p) (Finset.notMem_erase p U)).prodCongr (Equiv.refl E)))

def gVF (E : Type) : SubBasis F (U ∪ C) × E ≃ (F p × (SubBasis D (U.erase p) × E)) × SubBasis D C :=
  (gV p U C hp hUC F E).trans (((Equiv.refl _).prodCongr
    ((trS p other (U.erase p) (Finset.notMem_erase p U)).prodCongr (Equiv.refl E))).prodCongr
    (trS p other C (Finset.disjoint_left.1 hUC hp)))

include hp hUC in
theorem key [∀ i, Fintype (D i)] [∀ i, Fintype (F i)] [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    [Fintype E] [Nonempty E] (Φ : Superop (D p) (F p)) (hΦ : IsChannel Φ)
    (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) (hr : IsDensityMatrix r) :
    entropyAt (localAction p other Φ r) U - entropyAt (localAction p other Φ r) (U ∪ C) ≤
      entropyAt r U - entropyAt r (U ∪ C) := by
  obtain ⟨N, K, hK, hΦK⟩ := hΦ
  set eD := eG p U C D E hp hUC
  set eF' := eF p U C other E hp hUC
  have hρG : IsDensityMatrix (r.submatrix eD.symm eD.symm) := dens_sub _ hr
  have hla := la_eq p U C other hp hUC K Φ hΦK r
  have hσG := X4DPI.act_density K hK hρG
  have hσ : IsDensityMatrix (localAction p other Φ r) := by rw [hla]; exact dens_sub _ hσG
  have hA : X4DPI.act K (r.submatrix eD.symm eD.symm) = (localAction p other Φ r).submatrix eF'.symm eF'.symm := by
    rw [hla]; ext a b; simp [eD, eF']
  have hd := X4DPI.dpi K hK hρG
  rw [X4DPI.M1_rm, X4DPI.M2_rm, X4DPI.M1_rm, X4DPI.M2_rm, hA] at hd
  have hfF : ∀ x y : RegisterBasis F × E, X4C1.restrC U x.1 = X4C1.restrC U y.1 ↔ (eF' x).2 = (eF' y).2 := by
    intro x y
    rw [hfG p U C hp hUC F E x y]
    exact ((Equiv.prodCongr (trS p other C (Finset.disjoint_left.1 hUC hp))
      (trR p other (U ∪ C) (Finset.mem_union_left _ hp))).apply_eq_iff_eq).symm
  have hfF2 : ∀ x y : RegisterBasis F × E, X4C1.restrC (U ∪ C) x.1 = X4C1.restrC (U ∪ C) y.1 ↔
      (eF' x).2.2 = (eF' y).2.2 := by
    intro x y
    exact ((trR p other (U ∪ C) (Finset.mem_union_left _ hp)).apply_eq_iff_eq).symm
  rw [ent_sub r hr U eD (fun x => x.1) (fun x => x.2) (gU p U hp D E) (fun x => rfl) (hfG p U C hp hUC D E) _,
    ent_sub r hr (U ∪ C) eD (fun x => (x.1, x.2.1)) (fun x => x.2.2) (gV p U C hp hUC D E) (fun x => rfl) (fun x y => Iff.rfl) _,
    ent_sub _ hσ U eF' (fun x => x.1) (fun x => x.2) (gUF p U other hp E) (fun x => rfl) hfF _,
    ent_sub _ hσ (U ∪ C) eF' (fun x => (x.1, x.2.1)) (fun x => x.2.2) (gVF p U C other hp hUC E) (fun x => rfl) hfF2 _] at hd
  exact hd

lemma hfI (G : Fin n → Type) (E : Type) (s : Finset (Fin n)) (hs : p ∉ s) (x y : RegisterBasis G × E) :
    X4C1.restrC s x.1 = X4C1.restrC s y.1 ↔
      (((eG p {p} s G E (Finset.mem_singleton_self p) (Finset.disjoint_singleton_left.2 hs) x).1.2.1,
        (eG p {p} s G E (Finset.mem_singleton_self p) (Finset.disjoint_singleton_left.2 hs) x).2.2),
        (eG p {p} s G E (Finset.mem_singleton_self p) (Finset.disjoint_singleton_left.2 hs) x).1.1) =
      (((eG p {p} s G E (Finset.mem_singleton_self p) (Finset.disjoint_singleton_left.2 hs) y).1.2.1,
        (eG p {p} s G E (Finset.mem_singleton_self p) (Finset.disjoint_singleton_left.2 hs) y).2.2),
        (eG p {p} s G E (Finset.mem_singleton_self p) (Finset.disjoint_singleton_left.2 hs) y).1.1) := by
  simp only [X4C1.restrC, eG, Equiv.coe_fn_mk, Prod.mk.injEq, funext_iff, Subtype.forall,
    Finset.mem_erase, Finset.mem_singleton, Finset.mem_union, not_or]
  constructor
  · intro h
    exact ⟨⟨fun a ha => absurd ha.2 ha.1, fun a ha => h a ha.2⟩, h p hs⟩
  · rintro ⟨⟨-, h2⟩, h3⟩ a ha
    by_cases hap : a = p
    · subst hap; exact h3
    · exact h2 a ⟨hap, ha⟩

theorem inv [∀ i, Fintype (D i)] [∀ i, Fintype (F i)] [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    [Fintype E] [Nonempty E] (Φ : Superop (D p) (F p)) (hΦ : IsChannel Φ)
    (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) (hr : IsDensityMatrix r)
    (s : Finset (Fin n)) (hs : p ∉ s) :
    entropyAt (localAction p other Φ r) s = entropyAt r s := by
  obtain ⟨N, K, hK, hΦK⟩ := hΦ
  have hp1 : p ∈ ({p} : Finset (Fin n)) := Finset.mem_singleton_self p
  have hd : Disjoint {p} s := Finset.disjoint_singleton_left.2 hs
  set eD := eG p {p} s D E hp1 hd
  set eF' := eF p {p} s other E hp1 hd
  have hρG : IsDensityMatrix (r.submatrix eD.symm eD.symm) := dens_sub _ hr
  have hla := la_eq p {p} s other hp1 hd K Φ hΦK r
  have hσG := X4DPI.act_density K hK hρG
  have hσ : IsDensityMatrix (localAction p other Φ r) := by rw [hla]; exact dens_sub _ hσG
  have hA : X4DPI.act K (r.submatrix eD.symm eD.symm) =
      (localAction p other Φ r).submatrix eF'.symm eF'.symm := by
    rw [hla]; ext a b; simp only [submatrix_apply, Equiv.apply_symm_apply, eF', eD]
  let κ0 : (SubBasis D (({p} : Finset (Fin n)).erase p) × E) × (SubBasis D s × Rest D ({p} ∪ s)) →
      SubBasis D s × E := fun q => (q.2.1, q.1.2)
  let φ0 : (SubBasis D (({p} : Finset (Fin n)).erase p) × E) × (SubBasis D s × Rest D ({p} ∪ s)) →
      SubBasis D (({p} : Finset (Fin n)).erase p) × Rest D ({p} ∪ s) := fun q => (q.1.1, q.2.2)
  have c1 : ∀ {B : Type} [Fintype B] (X : Matrix ((B × (SubBasis D (({p} : Finset (Fin n)).erase p) × E)) ×
      (SubBasis D s × Rest D ({p} ∪ s))) ((B × (SubBasis D (({p} : Finset (Fin n)).erase p) × E)) ×
      (SubBasis D s × Rest D ({p} ∪ s))) ℂ),
      redistributionMarginal X (fun x => κ0 (x.1.2, x.2)) (fun x => (φ0 (x.1.2, x.2), x.1.1)) =
        redistributionMarginal (X4DPI.M0 X) κ0 φ0 := by
    intro B _ X
    rw [X4DPI.M0_rm, X4C1.rm_comp]
    rfl
  have e1 := ent_sub _ hσ s eF' (fun x => κ0 (x.1.2, x.2)) (fun x => (φ0 (x.1.2, x.2), x.1.1))
    ((trS p other s hs).prodCongr (Equiv.refl E)) (fun x => rfl) (fun x y => by
      rw [hfI p F E s hs x y]
      exact ((((trS p other _ (Finset.notMem_erase p {p})).prodCongr
        (trR p other ({p} ∪ s) (Finset.mem_union_left _ hp1))).prodCongr (Equiv.refl _)).apply_eq_iff_eq).symm)
    (Classical.decEq _)
  have e2 := ent_sub r hr s eD (fun x => κ0 (x.1.2, x.2)) (fun x => (φ0 (x.1.2, x.2), x.1.1))
    (Equiv.refl _) (fun x => rfl) (hfI p D E s hs) (Classical.decEq _)
  rw [← hA, c1, X4DPI.act_M0 K hK] at e1
  rw [c1] at e2
  rw [← e1, ← e2]

end X4P2

end

-- ===== P2Sol =====

noncomputable section

namespace X4P2
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

theorem part2 (m : ℕ) (D F : Fin m → Type) [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (E : Type) [Fintype E] [Nonempty E] (p : Fin m)
    (other : ∀ j, j ≠ p → D j ≃ F j) (Phi : Superop (D p) (F p))
    (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (hΦ : IsChannel Phi) (hr : IsDensityMatrix r) (kind : InformationKind) :
    conditionalMultipartiteInformation kind (localAction p other Phi r) (singleParties m) ∅ ≤
      conditionalMultipartiteInformation kind r (singleParties m) ∅ := by
  have hinv := fun s hs => inv p other Phi hΦ r hr s hs
  have hkey := fun U C hp hUC => key p U C other hp hUC Phi hΦ r hr
  have hall : allParties (singleParties m) = Finset.univ := by
    ext j; simp [allParties, singleParties]
  have hb : ∀ i : Fin m, (Finset.univ.erase i).biUnion (singleParties m) = Finset.univ.erase i := by
    intro i; ext j; simp [singleParties]
  have h0 := hinv ∅ (Finset.notMem_empty p)
  cases kind with
  | total =>
    simp only [conditionalMultipartiteInformation, hall, Finset.union_empty, singleParties]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hs : ∑ i ∈ Finset.univ.erase p, entropyAt (localAction p other Phi r) {i} =
        ∑ i ∈ Finset.univ.erase p, entropyAt r {i} :=
      Finset.sum_congr rfl fun i hi => hinv _ (by
        simpa [eq_comm] using (Finset.mem_erase.1 hi).1)
    have hk := hkey {p} (Finset.univ.erase p) (Finset.mem_singleton_self p)
      (Finset.disjoint_singleton_left.2 (Finset.notMem_erase p _))
    have hu : ({p} : Finset (Fin m)) ∪ Finset.univ.erase p = Finset.univ := by
      ext j; by_cases h : j = p <;> simp [h]
    rw [hu] at hk
    rw [hs, h0]
    linarith
  | dual =>
    simp only [conditionalMultipartiteInformation, hall, Finset.union_empty, hb]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hc : ((m - 1 : ℕ) : ℝ) = ((Finset.univ.erase p).card : ℝ) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
    have hle : ∑ i ∈ Finset.univ.erase p, (entropyAt (localAction p other Phi r) (Finset.univ.erase i) -
        entropyAt (localAction p other Phi r) Finset.univ) ≤
        ∑ i ∈ Finset.univ.erase p, (entropyAt r (Finset.univ.erase i) - entropyAt r Finset.univ) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hip : p ≠ i := fun h => (Finset.mem_erase.1 hi).1 h.symm
      have hk := hkey (Finset.univ.erase i) {i} (Finset.mem_erase.2 ⟨hip, Finset.mem_univ _⟩)
        (Finset.disjoint_singleton_right.2 (Finset.notMem_erase i _))
      have hu : Finset.univ.erase i ∪ {i} = (Finset.univ : Finset (Fin m)) := by
        ext j; by_cases h : j = i <;> simp [h]
      rwa [hu] at hk
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul] at hle
    rw [hc, h0, hinv _ (Finset.notMem_erase p _)]
    linarith

end X4P2

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {n k : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (a : Fin (k+2) → Finset (Fin n))
    (x : Finset (Fin n)) (hdis : DisjointRegisters a x) :
    (∀ kind : InformationKind, info kind rho a x ≤
      info kind rho (attachFirst a x) ∅) ∧
    (∀ (m : ℕ) (D F : Fin m → Type) [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
      [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
      (E : Type) [Fintype E] [Nonempty E] (p : Fin m)
      (other : ∀ j, j ≠ p → D j ≃ F j) (Phi : Superop (D p) (F p))
      (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ),
      2 ≤ m → IsChannel Phi → IsDensityMatrix r → ∀ kind : InformationKind,
      conditionalMultipartiteInformation kind (localAction p other Phi r) (singleParties m) ∅ ≤
        conditionalMultipartiteInformation kind r (singleParties m) ∅) :=
  ⟨X4P2.part1 rho hrho a x hdis, fun m D F _ _ _ _ E _ _ p other Phi r _ hΦ hr kind =>
    X4P2.part2 m D F E p other Phi r hΦ hr kind⟩

