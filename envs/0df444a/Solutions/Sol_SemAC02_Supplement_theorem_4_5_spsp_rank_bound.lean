-- Prove2me | solution 1 for SemAC02.Supplement.theorem_4_5_spsp_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T08:30:18.341197+00:00
-- url     : https://prove2.me/submissions/39cfe5a4-0dd4-4d03-ad89-14b5cd76e4f5

import Mathlib
import Definitions.Def_SemAC02_nDivision
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_AC02Frege_PC
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsPseudoRed
import Theorems.Thm_SemAC02_lemma_4_9_product_approximation
import Definitions.Def_SemAC02_Supplement_IsSemPCRef

open _root_.SemAC02 _root_.SemAC02.Supplement _root_.SemAC02.Supplement.ACirc
open _root_.AC02Frege
namespace P2MSPSPRankBoundProof
section
-- Inlined Solutions.P2MLinearMapFactorThrough

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace P2MProofComplexity.P2MLinearMapFactorThrough

/-- A map that kills every relation killed by f extends to a linear map on f's codomain. -/
theorem exists_factor {K A W Z : Type} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
    (f : A →ₗ[K] W) (g : A →ₗ[K] Z) (h : f.ker ≤ g.ker) :
    ∃ H : W →ₗ[K] Z, H.comp f = g := by
  let L := (f.ker.liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨H,hH⟩ := LinearMap.exists_extend L
  refine ⟨H,?_⟩
  ext x
  calc
    H (f x) = L (f.rangeRestrict x) := by
      have he : f.range.subtype (f.rangeRestrict x) = f x := rfl
      have hh := LinearMap.congr_fun hH (f.rangeRestrict x)
      rw [LinearMap.comp_apply,he] at hh
      exact hh
    _ = g x := by
      change (f.ker.liftQ g h) (f.quotKerEquivRange.symm ⟨f x,?_⟩) = g x
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      rfl

end P2MProofComplexity.P2MLinearMapFactorThrough
end

section
-- Inlined Solutions.P2MLinearMapCommonKernelWitness

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MLinearMapCommonKernelWitness

open Module

theorem exists_nonzero_image {K X W I : Type} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup W] [Module K W] [Module.Finite K X] [Fintype I]
    (Y : I → Type) [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)] [∀ i, Module.Finite K (Y i)]
    (R : X →ₗ[K] W) (f : ∀ i, X →ₗ[K] Y i)
    (hrank : (∑ i, finrank K (Y i))<finrank K (LinearMap.range R)) :
    ∃ x : X, R x≠0 ∧ ∀ i, f i x=0 := by
  classical
  by_contra hn
  let C := LinearMap.pi f
  have hker : LinearMap.ker C≤LinearMap.ker R := by
    intro x hx
    change R x=0
    by_contra hR
    apply hn
    refine ⟨x,hR,?_⟩
    intro i
    exact congrFun (show C x=0 from hx) i
  obtain ⟨H,hH⟩ := P2MLinearMapFactorThrough.exists_factor C R hker
  have hrange : R.range≤H.range := by
    rw [←hH]
    exact LinearMap.range_comp_le_range _ _
  have hdim : finrank K R.range≤finrank K ((i : I) → Y i) :=
    (Submodule.finrank_mono hrange).trans H.finrank_range_le
  rw [Module.finrank_pi_fintype] at hdim
  omega

end P2MProofComplexity.P2MLinearMapCommonKernelWitness
end

section
-- Inlined Solutions.ProductFunctionBasis

open Module
open scoped TensorProduct

namespace P2MProofComplexity

open PiTensorProduct

noncomputable def functionTensorEquiv
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] :
    (⨂[R] i, (X i → R)) ≃ₗ[R] (((i : ι) → X i) → R) := by
  classical
  exact (PiTensorProduct.congr (fun i => (Finsupp.linearEquivFunOnFinite R R (X i)).symm)) ≪≫ₗ
    (PiTensorProduct.ofFinsuppEquiv' (R := R) (κ := X)) ≪≫ₗ
    Finsupp.linearEquivFunOnFinite R R ((i : ι) → X i)

@[simp] theorem functionTensorEquiv_tprod
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] (f : (i : ι) → X i → R) (x : (i : ι) → X i) :
    functionTensorEquiv X (⨂ₜ[R] i, f i) x = ∏ i, f i (x i) := by
  classical
  simp [functionTensorEquiv]

noncomputable def productFunctionBasis
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) :
    Basis ((i : ι) → κ i) R (((i : ι) → X i) → R) :=
  (Basis.piTensorProduct b).map (functionTensorEquiv X)

@[simp] theorem productFunctionBasis_apply
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (k : (i : ι) → κ i) (x : (i : ι) → X i) :
    productFunctionBasis b k x = ∏ i, b i (k i) (x i) := by
  classical
  simp [productFunctionBasis]

theorem productFunctionBasis_repr
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (f : (i : ι) → X i → R)
    (k : (i : ι) → κ i) :
    (productFunctionBasis b).repr (fun x => ∏ i, f i (x i)) k =
      ∏ i, (b i).repr (f i) (k i) := by
  classical
  have hfun : (fun x => ∏ i, f i (x i)) = functionTensorEquiv X (⨂ₜ[R] i, f i) := by
    funext x
    exact (functionTensorEquiv_tprod X f x).symm
  rw [hfun]
  change (Basis.piTensorProduct b).repr
    ((functionTensorEquiv X).symm (functionTensorEquiv X (⨂ₜ[R] i, f i))) k = _
  rw [LinearEquiv.symm_apply_apply]
  exact Basis.piTensorProduct_repr_tprod_apply b f k

end P2MProofComplexity
end

section
-- Inlined Solutions.P2MDivisionBlockBasis

open Module

namespace SemAC02.P2MDivisionBlockBasis

noncomputable def valueEquiv (h : ℕ) :
    (Option (Fin h) → ZMod 2) ≃ₗ[ZMod 2] (Option (Fin h) → ZMod 2) where
  toFun c x := match x with | none => c none | some j => c none + c (some j)
  invFun c x := match x with | none => c none | some j => c none + c (some j)
  left_inv c := by
    funext x
    cases x with
    | none => rfl
    | some j => simp only [← add_assoc,CharTwo.add_self_eq_zero,zero_add]
  right_inv c := by
    funext x
    cases x with
    | none => rfl
    | some j => simp only [← add_assoc,CharTwo.add_self_eq_zero,zero_add]
  map_add' c d := by
    funext x
    cases x with
    | none => rfl
    | some j => change (c none+d none)+(c (some j)+d (some j)) = (c none+c (some j))+(d none+d (some j)); ring
  map_smul' a c := by
    funext x
    cases x with
    | none => rfl
    | some j =>
      change a • c none + a • c (some j) = a • (c none+c (some j))
      exact (smul_add a (c none) (c (some j))).symm

noncomputable def blockBasis (h : ℕ) :
    Basis (Option (Fin h)) (ZMod 2) (Option (Fin h) → ZMod 2) :=
  (Pi.basisFun (ZMod 2) (Option (Fin h))).map (valueEquiv h)

@[simp] theorem blockBasis_none (h : ℕ) (x : Option (Fin h)) : blockBasis h none x = 1 := by
  classical
  rw [blockBasis,Basis.map_apply]
  cases x <;> simp [valueEquiv,Pi.basisFun_apply]

@[simp] theorem blockBasis_some (h : ℕ) (j : Fin h) (x : Option (Fin h)) :
    blockBasis h (some j) x = if x = some j then 1 else 0 := by
  classical
  rw [blockBasis,Basis.map_apply]
  cases x with
  | none => simp [valueEquiv,Pi.basisFun_apply]
  | some k => simp [valueEquiv,Pi.basisFun_apply,Pi.single_apply,eq_comm]

end SemAC02.P2MDivisionBlockBasis
end

section
-- Inlined Solutions.P2MDivisionPoints

namespace SemAC02.P2MDivisionPoints

noncomputable def encode (n h : ℕ) (S : Fin n → Option (Fin h)) : nDivOmega n h := by
  classical
  refine ⟨fun v => decide (S v.1 = some v.2),?_⟩
  intro i j j' hj hj'
  simp only [decide_eq_true_eq] at hj hj'
  exact Option.some.inj (hj.symm.trans hj')

noncomputable def decode (n h : ℕ) (X : nDivOmega n h) (i : Fin n) : Option (Fin h) := by
  classical
  exact if hx : ∃ j, X.1 (i,j) = true then some (Classical.choose hx) else none

theorem decode_eq_some (n h : ℕ) (X : nDivOmega n h) (i : Fin n) (j : Fin h) :
    decode n h X i = some j ↔ X.1 (i,j) = true := by
  classical
  unfold decode
  split_ifs with hx
  · constructor
    · intro he
      have hj := Option.some.inj he
      rw [← hj]
      exact Classical.choose_spec hx
    · intro hj
      exact congrArg some (X.2 i (Classical.choose hx) j (Classical.choose_spec hx) hj)
  · simp only [Option.noConfusion, false_iff]
    exact fun hj => hx ⟨j,hj⟩

noncomputable def pointEquiv (n h : ℕ) : (Fin n → Option (Fin h)) ≃ nDivOmega n h where
  toFun := encode n h
  invFun := decode n h
  left_inv S := by
    classical
    funext i
    cases hs : S i with
    | none =>
      cases hd : decode n h (encode n h S) i with
      | none => rfl
      | some j =>
        have hb := (decode_eq_some n h (encode n h S) i j).mp hd
        simp [encode,hs] at hb
    | some j =>
      apply (decode_eq_some n h (encode n h S) i j).mpr
      simp [encode,hs]
  right_inv X := by
    classical
    apply Subtype.ext
    funext v
    apply Bool.eq_iff_iff.mpr
    simp only [encode,decide_eq_true_eq,decode_eq_some]

end SemAC02.P2MDivisionPoints
end

section
-- Inlined Solutions.P2MBooleanAlgebra

open MvPolynomial AC02Frege
namespace AC02Frege.P2MBooleanAlgebra

theorem ml_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2) :
    ML (monomial s c) = monomial (sqfree s) c := by
  have h := (basisMonomials V (ZMod 2)).constr_basis (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) s
  have hc : monomial s c = c • monomial s (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c • ((basisMonomials V (ZMod 2)).constr (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) (monomial s 1)) = _
  rw [show monomial s (1 : ZMod 2) = basisMonomials V (ZMod 2) s by rfl]
  rw [h]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem ml_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (ML p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial]
    intro t ht v
    have ht' : t = sqfree s := (Finset.mem_singleton.mp (support_monomial_subset ht))
    subst t
    simp [sqfree, Finsupp.mapRange_apply]
  | add p q hp hq =>
    rw [map_add]
    intro s hs v
    rcases Finset.mem_union.mp (support_add hs) with hs | hs
    · exact hp s hs v
    · exact hq s hs v


theorem sqfree_support {V : Type*} (s : V →₀ ℕ) : (sqfree s).support = s.support := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, sqfree, Finsupp.mapRange_apply]
  omega

theorem sqfree_eq_self {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) : sqfree s = s := by
  ext i
  simp only [sqfree, Finsupp.mapRange_apply, min_eq_left (hs i)]

theorem ml_of_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : ML p = p := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  conv_rhs => rw [p.as_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [sqfree_eq_self s (hp s hs)]

theorem ml_idempotent {V : Type*} (p : MvPolynomial V (ZMod 2)) : ML (ML p) = ML p :=
  ml_of_multilinear _ (ml_multilinear p)

theorem eval_ml {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (ML p) = eval x p := by
  classical
  have hpow (a : ZMod 2) (k : ℕ) : a ^ min k 1 = a ^ k := by
    fin_cases a
    · change (0 : ZMod 2) ^ min k 1 = (0 : ZMod 2) ^ k
      cases k <;> simp
    · change (1 : ZMod 2) ^ min k 1 = (1 : ZMod 2) ^ k
      simp
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial, eval_monomial, eval_monomial]
    congr 1
    simp only [Finsupp.prod, sqfree_support]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [sqfree, Finsupp.mapRange_apply] using hpow (x i) (s i)
  | add p q hp hq => simp only [map_add, hp, hq]

theorem multilinear_ext {V : Type} [Finite V]
    {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (h : ∀ x : V → ZMod 2, eval x p = eval x q) : p = q := by
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_eq_zero V (ZMod 2) (p - q)
  · intro x; simp only [map_sub, h x, sub_self]
  · have hp' : p ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V p 1).mpr hp
    have hq' : q ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V q 1).mpr hq
    simpa only [ZMod.card, Nat.reduceSub] using (restrictDegree V (ZMod 2) 1).sub_mem hp' hq'

theorem ml_mul_left {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (ML p * q) = ML (p * q) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [eval_ml, map_mul]

theorem ml_mul_right {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (p * ML q) = ML (p * q) := by
  rw [mul_comm p (ML q), ml_mul_left, mul_comm]

theorem xMon_eq_monomial {V : Type*} (S : Finset V) :
    xMon S = monomial (Finsupp.indicator S (fun _ _ => 1)) (1 : ZMod 2) := by
  classical
  simpa only [xMon, pow_one] using (prod_X_pow (R := ZMod 2) (fun _ : V => 1) S)

theorem indicator_support {V : Type*} (S : Finset V) :
    (Finsupp.indicator S (fun _ _ => (1 : ℕ))).support = S := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, Finsupp.indicator_apply]
  split_ifs <;> simp_all

theorem xMon_multilinear {V : Type*} (S : Finset V) : IsMultilinear (xMon S) := by
  classical
  rw [xMon_eq_monomial]
  intro s hs i
  have heq := Finset.mem_singleton.mp (support_monomial_subset hs)
  subst s
  simp only [Finsupp.indicator_apply]
  split_ifs <;> omega

theorem xMon_eval {V : Type*} (S : Finset V) (x : V → ZMod 2) :
    eval x (xMon S) = ∏ i ∈ S, x i := by
  simp only [xMon, map_prod, eval_X]

theorem xMon_totalDegree {V : Type*} (S : Finset V) : (xMon S).totalDegree = S.card := by
  classical
  rw [xMon_eq_monomial, totalDegree_monomial _ (one_ne_zero : (1 : ZMod 2) ≠ 0)]
  simp only [Finsupp.sum, indicator_support]
  have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finsupp.indicator_apply, hi]
  rw [heq]
  simp

theorem xMon_linearIndependent {V : Type*} :
    LinearIndependent (ZMod 2) (fun S : Finset V => xMon S) := by
  classical
  have hinj : Function.Injective (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) := by
    intro S T h
    have := congrArg Finsupp.support h
    simpa only [indicator_support] using this
  have h := (basisMonomials V (ZMod 2)).linearIndependent.comp
    (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) hinj
  simpa only [Function.comp_def, coe_basisMonomials, xMon_eq_monomial] using h

end AC02Frege.P2MBooleanAlgebra
end

section
-- Inlined Solutions.P2MMajorityFoundation

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace AC02Frege.P2MMajorityFoundation

open Classical

noncomputable def pointPoly {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) : MvPolynomial V (ZMod 2) :=
  ∏ i : V, if i ∈ S then X i else 1 + X i

theorem pointPoly_indicator {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = MvPolynomial.indicator (fun i : V => if i ∈ S then (1 : ZMod 2) else 0) := by
  classical
  unfold pointPoly MvPolynomial.indicator
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp only [hi, ↓reduceIte, ZMod.card, Nat.reduceSub, pow_one]
  · simp only [map_one, CharTwo.sub_eq_add]
    calc
      X i = X i + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + (X i + 1) := by abel
  · simp [CharTwo.sub_eq_add]

theorem pointPoly_multilinear {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    IsMultilinear (pointPoly S) := by
  rw [pointPoly_indicator]
  apply (mem_restrictDegree V _ 1).mp
  simpa only [ZMod.card, Nat.reduceSub] using indicator_mem_restrictDegree
    (fun i : V => if i ∈ S then (1 : ZMod 2) else 0)

theorem pointPoly_eval {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (x : V → ZMod 2) :
    eval x (pointPoly S) =
      if x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) then 1 else 0 := by
  classical
  rw [pointPoly_indicator]
  split_ifs with h
  · subst x; exact eval_indicator_apply_eq_one _
  · exact eval_indicator_apply_eq_zero _ _ h

theorem multilinear_sum {V ι : Type} (S : Finset ι) (f : ι → MvPolynomial V (ZMod 2))
    (hf : ∀ i ∈ S, IsMultilinear (f i)) : IsMultilinear (∑ i ∈ S, f i) := by
  apply (mem_restrictDegree V _ 1).mp
  exact Submodule.sum_mem _ (fun i hi => (mem_restrictDegree V (f i) 1).mpr (hf i hi))

theorem majOne_multilinear (ℓ : ℕ) : IsMultilinear (majOne ℓ) := by
  unfold majOne
  apply multilinear_sum
  intro S _
  simpa only [pointPoly] using pointPoly_multilinear S

theorem eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem point_of_ones {V : Type} [Fintype V] [DecidableEq V] (x : V → ZMod 2) :
    (fun i => if i ∈ Finset.univ.filter (fun i => x i = 1) then (1 : ZMod 2) else 0) = x := by
  classical
  funext i
  rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]

theorem ones_of_point {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    Finset.univ.filter (fun i => (if i ∈ S then (1 : ZMod 2) else 0) = 1) = S := by
  classical
  ext i
  simp

theorem majOne_eval (ℓ : ℕ) (x : Fin ℓ → ZMod 2) :
    eval x (majOne ℓ) = if ℓ / 2 < (Finset.univ.filter (fun i => x i = 1)).card
      then 1 else 0 := by
  classical
  unfold majOne
  simp only [map_sum]
  have hev (S : Finset (Fin ℓ)) := pointPoly_eval S x
  simp only [pointPoly] at hev
  simp only [hev]
  have heq (S : Finset (Fin ℓ)) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro hx; rw [hx, ones_of_point]
    · intro hS; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp

theorem heavy_monomial_absorbs_majority (ℓ : ℕ) (S : Finset (Fin ℓ))
    (hS : ℓ / 2 < S.card) : ML (xMon S * majOne ℓ) = xMon S := by
  apply multilinear_ext (ml_multilinear _) (xMon_multilinear S)
  intro x
  simp only [eval_ml, map_mul]
  by_cases hx : eval x (xMon S) = 0
  · rw [hx, zero_mul]
  · have hsub : S ⊆ Finset.univ.filter (fun i => x i = 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hxi : x i ≠ 0 := by
        intro hz
        apply hx
        rw [xMon_eval]
        exact Finset.prod_eq_zero hi hz
      rcases eq_zero_or_one (x i) with hz | ho
      · exact False.elim (hxi hz)
      · exact ho
    have hcard := Finset.card_le_card hsub
    rw [majOne_eval, if_pos (by omega), mul_one]

theorem pointPoly_factor {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = xMon S * ∏ i ∈ Finset.univ.filter (fun i : V => i ∉ S),
      (1 + X i : MvPolynomial V (ZMod 2)) := by
  simp only [pointPoly, Finset.prod_ite]
  congr 1
  rw [xMon]
  apply Finset.prod_congr
  · ext i; simp
  · intro i _; rfl

theorem support_mul_xMon_degree {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (p : MvPolynomial V (ZMod 2))
    (s : V →₀ ℕ) (hs : s ∈ (xMon S * p).support) : S.card ≤ s.sum (fun _ e => e) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (support_mul (xMon S) p hs)
  have haeq : a = Finsupp.indicator S (fun _ _ => (1 : ℕ)) := by
    rw [xMon_eq_monomial] at ha
    exact Finset.mem_singleton.mp (support_monomial_subset ha)
  subst a
  have hsum : (Finsupp.indicator S (fun _ _ => (1 : ℕ))).sum (fun _ e => e) = S.card := by
    simp only [Finsupp.sum, indicator_support]
    have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finsupp.indicator_apply, hi]
    rw [heq]; simp
  rw [← hab]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hsum]
  omega

theorem majOne_support_heavy (ℓ : ℕ) (s : Fin ℓ →₀ ℕ)
    (hs : s ∈ (majOne ℓ).support) : ℓ / 2 < s.sum (fun _ e => e) := by
  classical
  unfold majOne at hs
  obtain ⟨S, hS, hsS⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have hheavy := (Finset.mem_filter.mp hS).2
  change s ∈ (pointPoly S).support at hsS
  rw [pointPoly_factor] at hsS
  exact lt_of_lt_of_le hheavy (support_mul_xMon_degree S _ s hsS)

end AC02Frege.P2MMajorityFoundation
end

section
-- Inlined Solutions.P2MBooleanBasis

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation

namespace AC02Frege.P2MBooleanBasis

theorem squarefree_eq_indicator {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s = Finsupp.indicator s.support (fun _ _ => 1) := by
  classical
  ext i
  by_cases hi : i ∈ s.support
  · simp only [Finsupp.indicator_apply, dif_pos hi]
    have hpos := Finsupp.mem_support_iff.mp hi
    exact Nat.le_antisymm (hs i) (by omega)
  · simpa only [Finsupp.indicator_apply, dif_neg hi] using (by simpa only [Finsupp.mem_support_iff, not_not] using hi : s i = 0)

theorem squarefree_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2)
    (hs : ∀ i, s i ≤ 1) : monomial s c = c • xMon s.support := by
  rw [xMon_eq_monomial, smul_monomial, smul_eq_mul, mul_one,
    ← squarefree_eq_indicator s hs]

theorem squarefree_sum {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s.sum (fun _ e => e) = s.support.card := by
  have heq := squarefree_monomial s (1 : ZMod 2) hs
  have hd := congrArg MvPolynomial.totalDegree heq
  simpa only [totalDegree_monomial _ one_ne_zero, one_smul, xMon_totalDegree] using hd

noncomputable def monomialSpan {V : Type*} (P : Finset V → Prop) :
    Submodule (ZMod 2) (MvPolynomial V (ZMod 2)) :=
  Submodule.span (ZMod 2) {p | ∃ S : Finset V, P S ∧ p = xMon S}

theorem mem_monomialSpan_iff {V : Type*} (P : Finset V → Prop)
    (p : MvPolynomial V (ZMod 2)) : p ∈ monomialSpan P ↔
      IsMultilinear p ∧ ∀ s ∈ p.support, P s.support := by
  classical
  let M := restrictSupport (ZMod 2) {s : V →₀ ℕ | (∀ i, s i ≤ 1) ∧ P s.support}
  have heq : monomialSpan P = M := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro q ⟨S, hS, rfl⟩
      rw [xMon_eq_monomial]
      apply (monomial_mem_restrictSupport (ZMod 2)).mpr
      left
      refine ⟨?_, ?_⟩
      · intro i
        simp only [Finsupp.indicator_apply]
        split_ifs <;> omega
      · simpa only [indicator_support] using hS
    · intro q hq
      have hq' : ∀ s ∈ q.support, (∀ i, s i ≤ 1) ∧ P s.support := hq
      rw [q.as_sum]
      apply Submodule.sum_mem
      intro s hs
      obtain ⟨hml, hP⟩ := hq' s hs
      rw [squarefree_monomial s _ hml]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s.support, hP, rfl⟩)
  rw [heq, mem_restrictSupport_iff (ZMod 2)]
  constructor
  · intro hp
    exact ⟨fun s hs i => (hp hs).1 i, fun s hs => (hp hs).2⟩
  · rintro ⟨hml, hP⟩ s hs
    exact ⟨hml s hs, hP s hs⟩

theorem mem_light_iff {V : Type*} (m : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ monomialSpan (fun S : Finset V => S.card ≤ m) ↔
      IsMultilinear p ∧ p.totalDegree ≤ m := by
  rw [mem_monomialSpan_iff]
  constructor
  · rintro ⟨hp, hP⟩
    refine ⟨hp, Finset.sup_le fun s hs => ?_⟩
    rw [squarefree_sum s (hp s hs)]
    exact hP s hs
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun s hs => ?_⟩
    rw [← squarefree_sum s (hp s hs)]
    exact (le_totalDegree hs).trans hd

theorem point_interpolation {V : Type} [Fintype V] [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) :
    p = ∑ S : Finset V, eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p • pointPoly S := by
  apply multilinear_ext hp
    (multilinear_sum _ _ (fun S _ =>
      (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).smul_mem _
        ((mem_restrictDegree V _ 1).mpr (pointPoly_multilinear S)))))
  intro x
  simp only [map_sum, smul_eval, pointPoly_eval]
  have heq (S : Finset V) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro h; rw [h, ones_of_point]
    · intro h; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp
  have hx : (fun i => if x i = 1 then (1 : ZMod 2) else 0) = x := by
    funext i
    rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]
  rw [hx]

end AC02Frege.P2MBooleanBasis
end

section
-- Inlined Solutions.P2MBooleanFlip

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation AC02Frege.P2MBooleanBasis

namespace AC02Frege.P2MBooleanFlip

theorem ml_totalDegree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (ML p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_monomial_le _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  simp only [Finsupp.sum, sqfree_support]
  apply Finset.sum_le_sum
  intro i _
  simp only [sqfree, Finsupp.mapRange_apply]
  exact min_le_left _ _

theorem bind_linear_totalDegree_le {V W : Type*} (f : V → MvPolynomial W (ZMod 2))
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial V (ZMod 2)) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, bind₁_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply le_trans (totalDegree_mul _ _)
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

noncomputable def flip {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    MvPolynomial V (ZMod 2) := ML (bind₁ (fun i => 1 + X i) p)

theorem flip_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (flip p) := ml_multilinear _

theorem flip_degree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (flip p).totalDegree ≤ p.totalDegree := by
  apply (ml_totalDegree_le _).trans
  apply bind_linear_totalDegree_le
  intro i
  exact (totalDegree_add _ _).trans (by simp)

theorem flip_eval {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (flip p) = eval (fun i => 1 + x i) p := by
  rw [flip, eval_ml]
  simp only [eval, eval₂Hom_bind₁, map_add, map_one, eval₂Hom_X']

theorem flip_involution {V : Type} [Finite V] (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : flip (flip p) = p := by
  apply multilinear_ext (flip_multilinear _) hp
  intro x
  simp only [flip_eval, CharTwo.add_cancel_left]

end AC02Frege.P2MBooleanFlip
end

section
-- Inlined Solutions.P2MBooleanRestrictions

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation
open AC02Frege.P2MBooleanBasis AC02Frege.P2MBooleanFlip

namespace AC02Frege.P2MBooleanRestrictions

theorem xMon_eval_point {V : Type*} [DecidableEq V] (S T : Finset V) :
    eval (fun i => if i ∈ T then (1 : ZMod 2) else 0) (xMon S) =
      if S ⊆ T then 1 else 0 := by
  classical
  rw [xMon_eval]
  by_cases h : S ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h hi]
  · rw [if_neg h]
    obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (by simp [hit])

theorem multilinear_exponent_ext {V : Type*} (s t : V →₀ ℕ)
    (hs : ∀ i, s i ≤ 1) (ht : ∀ i, t i ≤ 1) (hst : s.support = t.support) : s = t := by
  rw [squarefree_eq_indicator s hs, squarefree_eq_indicator t ht, hst]

theorem eq_zero_of_support_point_eval_zero {V : Type} [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p)
    (hv : ∀ s ∈ p.support,
      eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  classical
  by_contra hne
  obtain ⟨s, hs, hmin⟩ := p.support.exists_min_image
    (fun t => t.support.card) (support_nonempty.mpr hne)
  have heval : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = p.coeff s := by
    have hsum : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p =
        ∑ t ∈ p.support, p.coeff t * (if t.support ⊆ s.support then (1 : ZMod 2) else 0) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [squarefree_monomial t _ (hp t ht), smul_eval, xMon_eval_point]
    rw [hsum, Finset.sum_eq_single s]
    · simp
    · intro t ht hts
      have hnot : ¬ t.support ⊆ s.support := by
        intro hsub
        have heq : t.support = s.support := Finset.eq_of_subset_of_card_le hsub (hmin t ht)
        exact hts (multilinear_exponent_ext t s (hp t ht) (hp s hs) heq)
      rw [if_neg hnot, mul_zero]
    · intro hnot
      exact False.elim (hnot hs)
  have hz := hv s hs
  rw [heval] at hz
  exact (mem_support_iff.mp hs) hz

theorem eval_injective_on_monomialSpan {V : Type} [DecidableEq V]
    (P : Finset V → Prop) (p : MvPolynomial V (ZMod 2))
    (hp : p ∈ monomialSpan P)
    (hv : ∀ S : Finset V, P S →
      eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  obtain ⟨hml, hP⟩ := (mem_monomialSpan_iff P p).mp hp
  exact eq_zero_of_support_point_eval_zero p hml (fun s hs => hv s.support (hP s hs))

theorem ml_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (ML p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨s, hs, his⟩ := (mem_vars_iff_mem_support i).mp hi
  have hexp : ML p = ∑ t ∈ p.support, monomial (sqfree t) (p.coeff t) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, ml_monomial]
  rw [hexp] at hs
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have heq := Finset.mem_singleton.mp (support_monomial_subset hst)
  subst s
  rw [sqfree_support] at his
  exact (mem_vars_iff_mem_support i).mpr ⟨t, ht, his⟩

theorem flip_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (P2MBooleanFlip.flip p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp
    (vars_bind₁ (fun j => 1 + X j) p (ml_vars_subset _ hi))
  have hsub : (1 + X j : MvPolynomial V (ZMod 2)).vars ⊆ {j} := by
    simpa using vars_add_subset (1 : MvPolynomial V (ZMod 2)) (X j)
  have heq := Finset.mem_singleton.mp (hsub hij)
  simpa only [heq] using hj

noncomputable def complementMap {V : Type} :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) where
  toFun := P2MBooleanFlip.flip
  map_add' p q := by simp only [P2MBooleanFlip.flip, map_add]
  map_smul' c p := by simp only [P2MBooleanFlip.flip, map_smul, RingHom.id_apply]

theorem flip_mem_monomialSpan {V : Type} (P : Finset V → Prop)
    (hP : ∀ S T, T ⊆ S → P S → P T)
    (p : MvPolynomial V (ZMod 2)) (hp : p ∈ monomialSpan P) :
    P2MBooleanFlip.flip p ∈ monomialSpan P := by
  classical
  have hle : monomialSpan P ≤ (monomialSpan P).comap complementMap := by
    apply Submodule.span_le.mpr
    rintro q ⟨S, hS, rfl⟩
    apply (mem_monomialSpan_iff P _).mpr
    refine ⟨flip_multilinear _, ?_⟩
    intro s hs
    have hsub : s.support ⊆ S := by
      apply (support_subset_vars_of_mem_support hs).trans
      apply (flip_vars_subset _).trans
      rw [xMon_eq_monomial, vars_monomial one_ne_zero, indicator_support]
    exact hP S s.support hsub hS
  exact hle hp

theorem monomialSpan_span_range {V : Type} (P : Finset V → Prop) :
    monomialSpan P = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset V // P S} => xMon S.1)) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨⟨S, hS⟩, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S.1, S.2, rfl⟩

end AC02Frege.P2MBooleanRestrictions
end

section
-- Inlined Solutions.P2MCommonBasis

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation
open AC02Frege.P2MBooleanBasis AC02Frege.P2MBooleanFlip AC02Frege.P2MBooleanRestrictions

namespace SemAC02.P2MCommonBasis

def ones {m : ℕ} (X : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => X i = true)

theorem indicator_ones {m : ℕ} (X : Fin m → Bool) : indicatorVec (ones X) = X := by
  funext i
  cases h : X i <;> simp [indicatorVec, ones, h]

theorem ones_indicator {m : ℕ} (S : Finset (Fin m)) : ones (indicatorVec S) = S := by
  ext i
  simp [indicatorVec, ones]

theorem toF2_indicator {m : ℕ} (S : Finset (Fin m)) :
    toF2 (indicatorVec S) = fun i => if i ∈ S then (1 : ZMod 2) else 0 := by
  funext i
  simp [toF2, indicatorVec]

theorem flip_eval_bool {m : ℕ} (p : MvPolynomial (Fin m) (ZMod 2)) (X : Fin m → Bool) :
    eval (toF2 X) (P2MBooleanFlip.flip p) = eval (toF2 (fun i => !X i)) p := by
  rw [flip_eval]
  have heq : (fun i => 1 + toF2 X i) = toF2 (fun i => !X i) := by
    funext i
    cases h : X i <;> simp [toF2, h, CharTwo.add_self_eq_zero]
  rw [heq]

noncomputable def supportEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {S : Finset (Fin m) // g (indicatorVec S) = true} ≃
      {X : Fin m → Bool // g X = true} where
  toFun S := ⟨indicatorVec S.1, S.2⟩
  invFun X := ⟨ones X.1, by simpa only [indicator_ones] using X.2⟩
  left_inv S := Subtype.ext (ones_indicator S.1)
  right_inv X := Subtype.ext (indicator_ones X.1)

def complementEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {X : Fin m → Bool // g X = true} ≃
      {X : Fin m → Bool // g (fun i => !X i) = true} where
  toFun X := ⟨fun i => !X.1 i, by simpa only [Bool.not_not] using X.2⟩
  invFun X := ⟨fun i => !X.1 i, X.2⟩
  left_inv X := Subtype.ext (by funext i; simp)
  right_inv X := Subtype.ext (by funext i; simp)

noncomputable def restriction {m : ℕ} (Ω : Set (Fin m → Bool)) :
    MvPolynomial (Fin m) (ZMod 2) →ₗ[ZMod 2] (Ω → ZMod 2) where
  toFun p X := eval (toF2 X.1) p
  map_add' p q := by ext X; simp
  map_smul' c p := by ext X; simp

theorem downclosed {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) :
    ∀ S T : Finset (Fin m), T ⊆ S → g (indicatorVec S) = true →
      g (indicatorVec T) = true := by
  intro S T hTS hS
  have hle : indicatorVec T ≤ indicatorVec S := by
    intro i
    by_cases hi : i ∈ T
    · simp [indicatorVec, hi, hTS hi]
    · simp [indicatorVec, hi]
  have h := hg hle
  rw [hS] at h
  exact Bool.eq_true_of_true_le h

theorem restriction_zero (m : ℕ) (g : (Fin m → Bool) → Bool)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g X = true} p = 0) : p = 0 := by
  apply eval_injective_on_monomialSpan _ p hp
  intro S hS
  have h := congrFun hv ⟨indicatorVec S, hS⟩
  change eval (toF2 (indicatorVec S)) p = 0 at h
  simpa only [toF2_indicator] using h

theorem restriction_complement_zero (m : ℕ) (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g (fun i => !X i) = true} p = 0) : p = 0 := by
  have hf : P2MBooleanFlip.flip p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true) :=
    flip_mem_monomialSpan _ (downclosed g hg) p hp
  have hvan : restriction {X : Fin m → Bool | g X = true} (P2MBooleanFlip.flip p) = 0 := by
    funext X
    change eval (toF2 X.1) (P2MBooleanFlip.flip p) = 0
    rw [flip_eval_bool]
    have h := congrFun hv ⟨fun i => !X.1 i, by simpa only [Set.mem_ofPred_eq, Bool.not_not] using X.2⟩
    exact h
  have hz := restriction_zero m g _ hf hvan
  have hml := ((mem_monomialSpan_iff _ _).mp hp).1
  calc
    p = P2MBooleanFlip.flip (P2MBooleanFlip.flip p) := (flip_involution p hml).symm
    _ = P2MBooleanFlip.flip 0 := congrArg (P2MBooleanFlip.flip (V := Fin m)) hz
    _ = 0 := by simp [P2MBooleanFlip.flip]

theorem restriction_independent (m : ℕ) (P : Finset (Fin m) → Prop) (Ω : Set (Fin m → Bool))
    (hinj : ∀ p : MvPolynomial (Fin m) (ZMod 2), p ∈ monomialSpan P → restriction Ω p = 0 → p = 0) :
    LinearIndependent (ZMod 2) (fun S : {S : Finset (Fin m) // P S} => restriction Ω (xMon S.1)) := by
  apply (xMon_linearIndependent.comp Subtype.val Subtype.val_injective).map_injOn
  intro v hv w hw heq
  have hv' : v ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  have hw' : w ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  apply sub_eq_zero.mp
  apply hinj (v - w) (Submodule.sub_mem _ hv' hw')
  rw [map_sub, heq, sub_self]

end SemAC02.P2MCommonBasis
end

section
-- Inlined Theorems.Thm_SemAC02_lemma_8_5_common_basis


open MvPolynomial AC02Frege SemAC02 SemAC02.P2MCommonBasis


/-- **Lemma 8.5 (Common monomial basis)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.5, p.64): with
`L = {S ⊆ [m] : g₀(1_S) = 1}`, `Ω₀ = {X : g₀(X) = 1}` and `Ω₁ = {X : g₁(X) = 1}`,
`g₁(X) = g₀(X̄)`, the monomials `x_S = ∏_{j∈S} x_j`, `S ∈ L`, give a basis of both `𝔽₂^{Ω₀}`
and `𝔽₂^{Ω₁}`.

**Formalization Note** Stated for every antitone Boolean function `g₀` on `{0,1}^m` (the
paper's `g₀ = g` from §8.1 is one). "Basis" is linear independence of the restrictions of the
`x_S` to `Ω_b` together with spanning all functions `Ω_b → 𝔽₂`. -/
theorem SemAC02.lemma_8_5_common_basis {m : ℕ} (g₀ : (Fin m → Bool) → Bool) (hg₀ : Antitone g₀) :
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) ∧
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) := by
  classical
  let P : Finset (Fin m) → Prop := fun S => g₀ (indicatorVec S) = true
  let Ω₀ : Set (Fin m → Bool) := {X | g₀ X = true}
  let Ω₁ : Set (Fin m → Bool) := {X | g₀ (fun i => !X i) = true}
  have hli0 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₀ (xMon S.1)) :=
    restriction_independent m P Ω₀ (restriction_zero m g₀)
  have hli1 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₁ (xMon S.1)) :=
    restriction_independent m P Ω₁ (restriction_complement_zero m g₀ hg₀)
  have hspan0 := hli0.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr (supportEquiv m g₀))
  have hspan1 := hli1.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr ((supportEquiv m g₀).trans (complementEquiv m g₀)))
  exact ⟨⟨hli0, hspan0⟩, ⟨hli1, hspan1⟩⟩

end

section
-- Inlined Solutions.SemanticFibreBasis

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MFibreBasis

abbrev BlockIndex {m : ℕ} (g : (Fin m → Bool) → Bool) :=
  {S : Finset (Fin m) // g (indicatorVec S) = true}

abbrev BlockFibre {m : ℕ} (g : (Fin m → Bool) → Bool) (b : Bool) :=
  {X : Fin m → Bool // if b then g (fun j => !X j) = true else g X = true}

noncomputable def blockBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) (b : Bool) :
    Basis (BlockIndex g) (ZMod 2) (BlockFibre g b → ZMod 2) := by
  have h := lemma_8_5_common_basis g hg
  cases b with
  | false => exact Basis.mk h.1.1 h.1.2.ge
  | true => exact Basis.mk h.2.1 h.2.2.ge

@[simp] theorem blockBasis_apply {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (b : Bool) (S : BlockIndex g) (X : BlockFibre g b) :
    blockBasis g hg b S X = eval (toF2 X.1) (xMon S.1) := by
  cases b <;> simp [blockBasis, Basis.mk_apply]

abbrev GlobalIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n : ℕ) :=
  {A : Finset (Fin n × Fin m) // IsLnSupport g A}

def assemble {n m : ℕ} {g : (Fin m → Bool) → Bool} (S : Fin n → BlockIndex g) :
    Finset (Fin n × Fin m) := Finset.univ.filter (fun v => v.2 ∈ (S v.1).1)

@[simp] theorem section_assemble {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (S : Fin n → BlockIndex g) (i : Fin n) : blockSection (assemble S) i = (S i).1 := by
  ext j
  simp [blockSection, assemble]

def sections {n m : ℕ} {g : (Fin m → Bool) → Bool} (A : GlobalIndex g n) (i : Fin n) :
    BlockIndex g := ⟨blockSection A.1 i, A.2 i⟩

@[simp] theorem assemble_sections {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (A : GlobalIndex g n) : assemble (sections A) = A.1 := by
  ext v
  simp [assemble, sections, blockSection]

def indexEquiv (n : ℕ) {m : ℕ} (g : (Fin m → Bool) → Bool) :
    (Fin n → BlockIndex g) ≃ GlobalIndex g n where
  toFun S := ⟨assemble S, by
    intro i
    rw [section_assemble]
    exact (S i).2⟩
  invFun A := sections A
  left_inv S := by funext i; apply Subtype.ext; exact section_assemble S i
  right_inv A := Subtype.ext (assemble_sections A)

abbrev Fibre {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :=
  {X : Fin n × Fin m → Bool // InFiber g z X}

def curryEquiv {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :
    Fibre g z ≃ ((i : Fin n) → BlockFibre g (z i)) where
  toFun X i := ⟨fun j => X.1 (i, j), X.2 i⟩
  invFun X := ⟨fun v => (X v.1).1 v.2, fun i => (X i).2⟩
  left_inv X := Subtype.ext (by funext v; rfl)
  right_inv X := by funext i; apply Subtype.ext; rfl

noncomputable def fibreBasis {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) : Basis (GlobalIndex g n) (ZMod 2) (Fibre g z → ZMod 2) :=
  ((P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).reindex
    (indexEquiv n g)).map (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))

theorem xMon_eval_blocks {n m : ℕ} (A : Finset (Fin n × Fin m))
    (X : Fin n × Fin m → Bool) : eval (toF2 X) (xMon A) =
      ∏ i : Fin n, eval (toF2 (fun j => X (i, j))) (xMon (blockSection A i)) := by
  classical
  simp only [xMon_eval, blockSection, Finset.prod_filter, toF2]
  rw [← Finset.prod_product']
  simp only [Finset.univ_product_univ]
  rw [← Finset.prod_filter]
  simp

@[simp] theorem fibreBasis_apply {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) (A : GlobalIndex g n) (X : Fibre g z) :
    fibreBasis g hg z A X = eval (toF2 X.1) (xMon A.1) := by
  classical
  rw [fibreBasis, Basis.map_apply, Basis.reindex_apply]
  change P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))
    (sections A) (curryEquiv g z X) = _
  rw [P2MProofComplexity.productFunctionBasis_apply, xMon_eval_blocks]
  apply Finset.prod_congr rfl
  intro i _
  rw [blockBasis_apply]
  rfl

end SemAC02.P2MFibreBasis
end

section
-- Inlined Solutions.P2MDivisionMonomialBasis

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MDivisionMonomialBasis

noncomputable def divisionBasis (n h : ℕ) :
    Basis (Fin n → Option (Fin h)) (ZMod 2) (nDivOmega n h → ZMod 2) :=
  (P2MProofComplexity.productFunctionBasis (fun _i : Fin n => P2MDivisionBlockBasis.blockBasis h)).map
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (P2MDivisionPoints.pointEquiv n h).symm)

noncomputable def assemble {n h : ℕ} (S : Fin n → Option (Fin h)) : Finset (Fin n × Fin h) := by
  classical
  exact Finset.univ.filter (fun v => S v.1 = some v.2)

theorem section_assemble {n h : ℕ} (S : Fin n → Option (Fin h)) (i : Fin n) :
    blockSection (assemble S) i = match S i with | none => ∅ | some j => {j} := by
  classical
  ext j
  cases hs : S i <;> simp [blockSection,assemble,hs,eq_comm]

@[simp] theorem divisionBasis_apply (n h : ℕ) (S : Fin n → Option (Fin h)) (X : nDivOmega n h) :
    divisionBasis n h S X = eval (toF2 X.1) (xMon (assemble S)) := by
  classical
  rw [divisionBasis,Basis.map_apply]
  change P2MProofComplexity.productFunctionBasis (fun _i : Fin n => P2MDivisionBlockBasis.blockBasis h) S
    ((P2MDivisionPoints.pointEquiv n h).symm X) = _
  rw [P2MProofComplexity.productFunctionBasis_apply,P2MFibreBasis.xMon_eval_blocks]
  apply Finset.prod_congr rfl
  intro i _
  rw [section_assemble]
  cases hs : S i with
  | none => simp only [P2MDivisionBlockBasis.blockBasis_none,xMon,Finset.prod_empty,map_one]
  | some j =>
    rw [P2MDivisionBlockBasis.blockBasis_some]
    change (if P2MDivisionPoints.decode n h X i = some j then 1 else 0) = _
    simp only [P2MDivisionPoints.decode_eq_some,xMon,Finset.prod_singleton,eval_X,toF2]

noncomputable def active {n h : ℕ} (S : Fin n → Option (Fin h)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => (S i).isSome)

theorem image_assemble {n h : ℕ} (S : Fin n → Option (Fin h)) :
    (assemble S).image Prod.fst = active S := by
  classical
  ext i
  constructor
  · rintro hi
    obtain ⟨⟨i',j⟩,hj,rfl⟩ := Finset.mem_image.mp hi
    have hs : S i' = some j := by simpa only [assemble,Finset.mem_filter,Finset.mem_univ,true_and] using hj
    simp only [active,Finset.mem_filter,Finset.mem_univ,true_and,hs,Option.isSome_some]
  · intro hi
    have hs : (S i).isSome := by simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    cases hSi : S i with
    | none => simp [hSi] at hs
    | some j => exact Finset.mem_image.mpr ⟨(i,j),by simp [assemble,hSi],rfl⟩

theorem assemble_card {n h : ℕ} (S : Fin n → Option (Fin h)) :
    (assemble S).card = (active S).card := by
  classical
  rw [← image_assemble S]
  apply (Finset.card_image_of_injOn ?_).symm
  rintro ⟨i,j⟩ h1 ⟨i',j'⟩ h2 he
  have hi : i = i' := he
  subst i'
  have hs1 : S i = some j := by simpa [assemble] using h1
  have hs2 : S i = some j' := by simpa [assemble] using h2
  exact Prod.ext rfl (Option.some.inj (hs1.symm.trans hs2))

theorem xMon_degree {n h : ℕ} (S : Fin n → Option (Fin h)) :
    (xMon (assemble S)).totalDegree = (active S).card :=
  (xMon_totalDegree _).trans (assemble_card S)

end SemAC02.P2MDivisionMonomialBasis
end

section
-- Inlined Solutions.P2MBooleanLocality

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MBooleanLocality

theorem multilinear_degree_le_card {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) : p.totalDegree ≤ Fintype.card V := by
  classical
  apply Finset.sup_le
  intro s hs
  rw [squarefree_sum s (hp s hs)]
  exact Finset.card_le_univ _

noncomputable def extendAssignment {V : Type} (J : Finset V) (x : J → ZMod 2) : V → Bool := by
  classical
  exact fun i => if hi : i ∈ J then decide (x ⟨i, hi⟩ = 1) else false

theorem represents_local_function {V : Type} [Fintype V] (J : Finset V)
    (f : (V → Bool) → ZMod 2)
    (hf : ∀ z z' : V → Bool, (∀ i ∈ J, z i = z' i) → f z = f z') :
    ∃ r : MvPolynomial V (ZMod 2), r.totalDegree ≤ J.card ∧
      ∀ z : V → Bool, eval (toF2 z) r = f z := by
  classical
  let η : (J → ZMod 2) → ZMod 2 := fun x => f (extendAssignment J x)
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.mp (MvPolynomial.range_evalᵢ J (ZMod 2)) η
  let p' : restrictDegree J (ZMod 2) (Fintype.card (ZMod 2) - 1) := p
  have hml : IsMultilinear p'.1 := by
    apply (mem_restrictDegree J _ 1).mp
    simpa only [ZMod.card, Nat.reduceSub] using p'.2
  refine ⟨rename Subtype.val p'.1, ?_, ?_⟩
  · apply (totalDegree_rename_le _ _).trans
    simpa only [Fintype.card_coe] using multilinear_degree_le_card p'.1 hml
  · intro z
    rw [eval_rename]
    have he := congrFun hp (fun j : J => toF2 z j.1)
    change eval (fun j : J => toF2 z j.1) p'.1 = f (extendAssignment J (fun j : J => toF2 z j.1)) at he
    change eval (fun j : J => toF2 z j.1) p'.1 = f z
    rw [he]
    apply hf
    intro i hi
    simp only [extendAssignment, dif_pos hi]
    cases h : z i <;> simp [toF2, h]

end SemAC02.P2MBooleanLocality
end

section
-- Inlined Solutions.SemanticFibreCoordinates

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis

namespace SemAC02.P2MFibreCoordinates

noncomputable def coordinates {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) : ZMod 2 :=
  (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) p) S

theorem coordinates_expansion {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) (X : Fibre g z) :
    eval (toF2 X.1) p = ∑ S : GlobalIndex g n, coordinates g hg p S z *
      eval (toF2 X.1) (xMon S.1) := by
  classical
  have h := congrFun ((fibreBasis g hg z).equivFun.symm_apply_apply (fun X => eval (toF2 X.1) p)) X
  rw [Basis.equivFun_symm_apply] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply, coordinates] using h.symm

theorem coordinates_unique {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (c : GlobalIndex g n → (Fin n → Bool) → ZMod 2)
    (hc : ∀ (z : Fin n → Bool) (X : Fin n × Fin m → Bool), InFiber g z X →
      eval (toF2 X) p = ∑ S, c S z * eval (toF2 X) (xMon S.1)) :
    ∀ S z, c S z = coordinates g hg p S z := by
  classical
  intro S z
  have he : (fun X : Fibre g z => eval (toF2 X.1) p) =
      (fibreBasis g hg z).equivFun.symm (fun S => c S z) := by
    rw [Basis.equivFun_symm_apply]
    funext X
    rw [hc z X.1 X.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply]
  have h := congrArg (fibreBasis g hg z).equivFun he
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrFun h S).symm

theorem coordinates_add {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p q : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p + q) S z = coordinates g hg p S z + coordinates g hg q S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p + q)) =
      (fun X => eval (toF2 X.1) p) + (fun X => eval (toF2 X.1) q) := by
    funext X
    exact map_add _ _ _
  unfold coordinates
  rw [he, map_add]
  rfl

theorem coordinates_smul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (a : ZMod 2) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (a • p) S z = a * coordinates g hg p S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (a • p)) =
      a • (fun X => eval (toF2 X.1) p) := by
    funext X
    simp only [smul_eval, Pi.smul_apply, smul_eq_mul]
  unfold coordinates
  rw [he, map_smul]
  rfl

end SemAC02.P2MFibreCoordinates
end

section
-- Inlined Solutions.SemanticProductCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates

namespace SemAC02.P2MProductCoordinates

noncomputable def blockCoefficient {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (U : Finset (Fin m)) (b : Bool) : ZMod 2 :=
  (blockBasis g hg b).repr (fun X => eval (toF2 X.1) (xMon T.1 * xMon U)) S

theorem blockCoefficient_empty {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (b : Bool) :
    blockCoefficient g hg S T ∅ b = if S = T then 1 else 0 := by
  classical
  have he : (fun X : BlockFibre g b => eval (toF2 X.1) (xMon T.1 * xMon ∅)) =
      blockBasis g hg b T := by
    funext X
    simp only [xMon, Finset.prod_empty, mul_one, blockBasis_apply]
  unfold blockCoefficient
  rw [he, Basis.repr_self]
  by_cases hST : S = T
  · subst S
    rw [Finsupp.single_eq_same, if_pos rfl]
  · rw [Finsupp.single_eq_of_ne hST, if_neg hST]

theorem coordinates_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) (z : Fin n → Bool) :
    coordinates g hg (xMon T.1 * xMon U) S z =
      ∏ i : Fin n, blockCoefficient g hg (sections S i) (sections T i) (blockSection U i) (z i) := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon U)) =
      (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))
        (fun X : (i : Fin n) → BlockFibre g (z i) =>
          ∏ i : Fin n, eval (toF2 (X i).1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) := by
    funext X
    change eval (toF2 X.1) (xMon T.1 * xMon U) =
      ∏ i : Fin n, eval (toF2 (fun j => X.1 (i, j)))
        (xMon (blockSection T.1 i) * xMon (blockSection U i))
    simp only [map_mul, xMon_eval_blocks, Finset.prod_mul_distrib]
  unfold coordinates
  rw [he]
  change (P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).repr
    ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)).symm
      ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)) _)) ((indexEquiv n g).symm S) = _
  rw [LinearEquiv.symm_apply_apply]
  exact P2MProofComplexity.productFunctionBasis_repr (fun i : Fin n => blockBasis g hg (z i))
    (fun i X => eval (toF2 X.1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) (sections S)

theorem blockSection_empty {n m : ℕ} (U : Finset (Fin n × Fin m)) (i : Fin n)
    (hi : i ∉ U.image Prod.fst) : blockSection U i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  apply hi
  have hij : (i, j) ∈ U := (Finset.mem_filter.mp hj).2
  exact Finset.mem_image.mpr ⟨(i, j), hij, rfl⟩

theorem coordinates_product_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m))
    (z z' : Fin n → Bool) (hz : ∀ i ∈ U.image Prod.fst, z i = z' i) :
    coordinates g hg (xMon T.1 * xMon U) S z = coordinates g hg (xMon T.1 * xMon U) S z' := by
  classical
  rw [coordinates_product, coordinates_product]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ U.image Prod.fst
  · rw [hz i hi]
  · rw [blockSection_empty U i hi, blockCoefficient_empty, blockCoefficient_empty]

end SemAC02.P2MProductCoordinates
end

section
-- Inlined Solutions.SemanticCoordinateSpaces

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates

namespace SemAC02.P2MCoordinateSpaces

noncomputable def booleanEvaluation (n : ℕ) :
    MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p z := eval (toF2 z) p
  map_add' p q := by funext z; exact map_add _ _ _
  map_smul' a p := by funext z; simp only [smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

noncomputable def degreeSpace (n D : ℕ) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) :=
  (restrictTotalDegree (Fin n) (ZMod 2) D).map (booleanEvaluation n)

theorem mem_degreeSpace {n D : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    u ∈ degreeSpace n D ↔ ∃ r : MvPolynomial (Fin n) (ZMod 2), r.totalDegree ≤ D ∧
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  constructor
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mp hr, fun z => congrFun heq z⟩
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mpr hr, funext heq⟩

def localSpace {n : ℕ} (J : Finset (Fin n)) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) where
  carrier := {u | ∀ z z', (∀ i ∈ J, z i = z' i) → u z = u z'}
  zero_mem' := by intro z z' hz; rfl
  add_mem' := by intro f h hf hh z z' hz; exact congrArg₂ (· + ·) (hf z z' hz) (hh z z' hz)
  smul_mem' := by intro a f hf z z' hz; exact congrArg (fun x => a • x) (hf z z' hz)

theorem localSpace_mono {n : ℕ} {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    localSpace I ≤ localSpace J := by
  intro f hf z z' hz
  exact hf z z' (fun i hi => hz i (hIJ hi))

noncomputable def coordinateMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p := coordinates g hg p S
  map_add' p q := by funext z; exact coordinates_add g hg p q S z
  map_smul' a p := by
    funext z
    simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using coordinates_smul g hg a p S z

end SemAC02.P2MCoordinateSpaces
end

section
-- Inlined Solutions.P2MBooleanFunctionPolynomials

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MBooleanFunctionPolynomials

theorem toF2_surjective {V : Type} (x : V → ZMod 2) : ∃ X : V → Bool, toF2 X = x := by
  refine ⟨fun v => decide (x v = 1), ?_⟩
  funext v
  have h : x v = 0 ∨ x v = 1 := by
    have h01 := AC02Frege.P2MMajorityFoundation.eq_zero_or_one (x v)
    exact h01
  rcases h with h | h <;> simp [toF2, h]

theorem multilinear_ext_bool {V : Type} [Finite V] {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (he : ∀ X : V → Bool, eval (toF2 X) p = eval (toF2 X) q) : p = q := by
  apply multilinear_ext hp hq
  intro x
  obtain ⟨X, rfl⟩ := toF2_surjective x
  exact he X

theorem exists_polynomial (n : ℕ) (u : (Fin n → Bool) → ZMod 2) :
    ∃ r : MvPolynomial (Fin n) (ZMod 2),
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  classical
  obtain ⟨r, _, hr⟩ := P2MBooleanLocality.represents_local_function Finset.univ u
    (fun z z' h => congrArg u (funext (fun i => h i (Finset.mem_univ i))))
  exact ⟨r, hr⟩

noncomputable def polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    MvPolynomial (Fin n) (ZMod 2) := ML (Classical.choose (exists_polynomial n u))

theorem polynomial_multilinear {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    IsMultilinear (polynomial u) := ml_multilinear _

@[simp] theorem eval_polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) (z : Fin n → Bool) :
    eval (toF2 z) (polynomial u) = u z := by
  rw [polynomial, eval_ml]
  exact Classical.choose_spec (exists_polynomial n u) z

theorem polynomial_eq {n : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (r : MvPolynomial (Fin n) (ZMod 2))
    (hr : ∀ z : Fin n → Bool, eval (toF2 z) r = u z) : polynomial u = ML r := by
  apply multilinear_ext_bool
    (polynomial_multilinear u) (ml_multilinear r)
  intro z
  rw [eval_polynomial, eval_ml, hr]

noncomputable def polynomialMap (n : ℕ) :
    ((Fin n → Bool) → ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) where
  toFun := polynomial
  map_add' u v := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.add_mem _ ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u))
          ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear v)))
    · intro z
      simp only [eval_polynomial, map_add, Pi.add_apply]
  map_smul' a u := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.smul_mem _ a ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u)))
    · intro z
      simp only [eval_polynomial, smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem polynomial_degree {n D : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (hu : u ∈ SemAC02.P2MCoordinateSpaces.degreeSpace n D) : (polynomial u).totalDegree ≤ D := by
  obtain ⟨r, hr, he⟩ := SemAC02.P2MCoordinateSpaces.mem_degreeSpace u |>.mp hu
  rw [polynomial_eq u r he]
  exact (ml_totalDegree_le r).trans hr

end SemAC02.P2MBooleanFunctionPolynomials
end

section
-- Inlined Solutions.PCOperations

open MvPolynomial

namespace AC02Frege.P2MSupport

theorem derivation_append {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K))
    {π ρ : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π)
    (hρ : PCNonBool.IsDerivation red P ρ) :
    PCNonBool.IsDerivation red P (π ++ ρ) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left
      simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    have hk' : k < ρ.length := by simp only [List.length_append] at hk; omega
    have hget (t : ℕ) (ht : t < ρ.length) :
        (π ++ ρ)[π.length + t]'(by simp only [List.length_append]; omega) = ρ[t] := by
      rw [List.getElem_append_right (Nat.le_add_right π.length t)]
      simp only [Nat.add_sub_cancel_left]
    rcases hρ k hk' with ha | hc | hm
    · left
      obtain ⟨a, ha, c, hac⟩ := ha
      exact ⟨a, ha, c, (hget k hk').trans hac⟩
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨π.length + i, π.length + j, by omega, by omega, a, b, ?_⟩
      rw [hget k hk', hget i (hi.trans hk'), hget j (hj.trans hk')]
      exact hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨π.length + i, by omega, v, ?_⟩
      rw [hget k hk', hget i (hi.trans hk')]
      exact hiv

theorem derivation_snoc {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K)) {π : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π) (p : MvPolynomial σ K)
    (hp :
      (∃ a ∈ P, ∃ c : K, p = c • red a) ∨
      (∃ (i j : ℕ) (hi : i < π.length) (hj : j < π.length) (a b : K),
        p = a • π[i] + b • π[j]) ∨
      (∃ (i : ℕ) (hi : i < π.length) (v : σ), p = red (X v * π[i]))) :
    PCNonBool.IsDerivation red P (π ++ [p]) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left; simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · have heq : k = π.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    have hlast : (π ++ [p])[π.length] = p := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    rcases hp with ha | hc | hm
    · left; simpa only [hlast] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [hlast, List.getElem_append_left hi, List.getElem_append_left hj] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [hlast, List.getElem_append_left hi] using hiv

theorem pc_zero {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    PCDerivable F D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {F : LiftSAParity.CNF (Fin n)} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) (c : ZMod 2) :
    PCDerivable F D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero F D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : PCDerivable F D p) (hq : PCDerivable F D q) :
    PCDerivable F D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show PCDerivable F D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    PCDerivable F D (p * X v) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [zero_mul]; exact pc_zero F D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [p * X v], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by simp only [hpi, LinearMap.id_apply, mul_comm]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = p * X v := List.mem_singleton.mp hq
      subst q
      exact (totalDegree_mul p (X v)).trans (by simpa only [totalDegree_X] using hdeg)

theorem pc_axiom {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ pcAxioms F)
    (hdeg : p.totalDegree ≤ D) : PCDerivable F D p := by
  refine Or.inr ⟨[p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

end AC02Frege.P2MSupport
end

section
-- Inlined Solutions.P2MBooleanPC

open MvPolynomial AC02Frege
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MBooleanPC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q.totalDegree ≤ D) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Derivable P D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) (c : ZMod 2) :
    Derivable P D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero P D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : Derivable P D p) (hq : Derivable P D q) :
    Derivable P D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show Derivable P D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    Derivable P D (ML (X v * p)) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [mul_zero, map_zero]; exact pc_zero P D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = ML (X v * p) := List.mem_singleton.mp hq
      subst q
      exact (ml_totalDegree_le _).trans ((totalDegree_mul (X v) p).trans (by simpa only [totalDegree_X, Nat.add_comm] using hdeg))

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P)
    (hdeg : (ML p).totalDegree ≤ D) : Derivable P D (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

theorem pc_mono {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D E : ℕ}
    (hDE : D ≤ E) {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) :
    Derivable P E p := by
  rcases hp with h | ⟨π, hπ, hdeg, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨π, hπ, fun q hq => (hdeg q hq).trans hDE, hp⟩

noncomputable def consequenceSpace {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) where
  carrier := {p | Derivable P D p}
  zero_mem' := pc_zero P D
  add_mem' := pc_add P D
  smul_mem' := fun a _ hp => pc_smul P D hp a

end SemAC02.P2MBooleanPC
end

section
-- Inlined Solutions.P2MRelativePC

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q ∈ U) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) : Derivable P U 0 := Or.inl rfl

theorem pc_mem {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))}
    {U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) : p ∈ U := by
  rcases hp with rfl | ⟨π,_,hmem,hp⟩
  · exact U.zero_mem
  · exact hmem p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (c : ZMod 2) :
    Derivable P U (c • p) := by
  rcases hp with rfl | ⟨π,hπ,hmem,hp⟩
  · simp only [smul_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; left
    exact ⟨i,i,hi,hi,c,0,by simp only [hpi,zero_smul,add_zero]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmem q hq
    · have he : q = c • p := List.mem_singleton.mp hq
      rw [he]
      exact U.smul_mem c (hmem p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p q : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (hq : Derivable P U q) :
    Derivable P U (p+q) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ,hρ,hρmem,hq⟩
  · simpa only [add_zero] using (show Derivable P U p from Or.inr ⟨π,hπ,hπmem,hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j,hj,hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p+q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i,j,hi,hj,1,1,by simp only [hpi,hqj,one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπmem r hr
      · exact hρmem r hr
    · have he : r = p+q := List.mem_singleton.mp hr
      rw [he]
      exact U.add_mem (hπmem p hp) (hρmem q hq)

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (v : Fin n)
    (hmem : ML (X v * p) ∈ U) : Derivable P U (ML (X v * p)) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simp only [mul_zero,map_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i,hi,v,by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπmem q hq
    · rwa [List.mem_singleton.mp hq]

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P) (hmem : ML p ∈ U) :
    Derivable P U (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hmem, by simp⟩
  intro k hk
  have he : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p,hp,1,by simp⟩

end SemAC02.P2MRelativePC
end

section
-- Inlined Solutions.RelativePCPolynomialMultiplication

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePC

theorem pc_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : Derivable P U u) (huml : IsMultilinear u)
    (hmem : ∀ w : MvPolynomial (Fin n) (ZMod 2), w.totalDegree ≤ v.totalDegree → ML (u*w) ∈ U) :
    Derivable P U (ML (u*v)) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    have he : u * C c = c • u := by rw [smul_eq_C_mul, mul_comm]
    rw [he, map_smul, ml_of_multilinear u huml]
    exact pc_smul P U hu c
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := by
      apply disjoint_support_monomial
      · exact hnot
      · exact hc
    have hsupp : (monomial s c + p).support = (monomial s c).support ∪ p.support := by
      exact Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_left
    have hdp : p.totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_right
    rw [mul_add, map_add]
    exact pc_add P U (ihm (fun w hw => hmem w (hw.trans hdm)))
      (ihp (fun w hw => hmem w (hw.trans hdp)))
  | mul_X p i ih =>
    have hle : p.totalDegree ≤ (p * X i).totalDegree := by
      by_cases hp : p = 0
      · simp [hp]
      · rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
        omega
    have hi := ih (fun w hw => hmem w (hw.trans hle))
    have he : ML (u * (p * X i)) = ML (X i * ML (u*p)) := by
      rw [ml_mul_right]
      congr 1
      ring
    rw [he]
    apply pc_mul_X P U hi i
    rw [← he]
    exact hmem _ le_rfl

end SemAC02.P2MRelativePC
end

section
-- Inlined Solutions.SemanticMonomialLocality

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates
open SemAC02.P2MProductCoordinates SemAC02.P2MCoordinateSpaces SemAC02.P2MBooleanLocality

namespace SemAC02.P2MMonomialLocality

theorem eval_monomial_squarefree {V : Type} (s : V →₀ ℕ) (a : ZMod 2) (x : V → ZMod 2) :
    eval x (monomial s a) = a * eval x (xMon s.support) := by
  calc
    eval x (monomial s a) = eval x (ML (monomial s a)) := (eval_ml _ _).symm
    _ = a * eval x (xMon s.support) := by
      rw [ml_monomial, squarefree_monomial (sqfree s) a (fun i => by simp [sqfree, Finsupp.mapRange_apply]),
        sqfree_support, smul_eval]

theorem coordinate_monomial {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) =
      a • coordinateMap g hg S (xMon T.1 * xMon s.support) := by
  funext z
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * monomial s a)) =
      a • (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon s.support)) := by
    funext X
    simp only [map_mul, eval_monomial_squarefree, Pi.smul_apply, smul_eq_mul]
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (xMon T.1 * monomial s a)) S = _
  rw [he, map_smul]
  rfl

theorem support_card_le_sum {V : Type} (s : V →₀ ℕ) : s.support.card ≤ s.sum (fun _ e => e) := by
  classical
  change s.support.card ≤ ∑ i ∈ s.support, s i
  calc
    s.support.card = ∑ _i ∈ s.support, 1 := by simp
    _ ≤ ∑ i ∈ s.support, s i := Finset.sum_le_sum (fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem degreeSpace_mono {n D E : ℕ} (hDE : D ≤ E) : degreeSpace n D ≤ degreeSpace n E := by
  intro u hu
  obtain ⟨r, hr, he⟩ := (mem_degreeSpace u).mp hu
  exact (mem_degreeSpace u).mpr ⟨r, hr.trans hDE, he⟩

theorem squarefree_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ localSpace (U.image Prod.fst) := by
  exact coordinates_product_local g hg S T U

theorem squarefree_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ degreeSpace n U.card := by
  have hl := squarefree_local g hg S T U
  obtain ⟨r, hr, he⟩ := represents_local_function (U.image Prod.fst)
    (coordinateMap g hg S (xMon T.1 * xMon U)) hl
  exact (mem_degreeSpace _).mpr ⟨r, hr.trans (Finset.card_image_le), he⟩

theorem monomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ localSpace (s.support.image Prod.fst) := by
  rw [coordinate_monomial]
  exact Submodule.smul_mem _ a (squarefree_local g hg S T s.support)

theorem monomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ degreeSpace n (s.sum (fun _ e => e)) := by
  rw [coordinate_monomial]
  apply Submodule.smul_mem
  exact degreeSpace_mono (support_card_le_sum s) (squarefree_degree g hg S T s.support)

end SemAC02.P2MMonomialLocality
end

section
-- Inlined Solutions.SemanticCoefficientControl

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates
open SemAC02.P2MCoordinateSpaces SemAC02.P2MMonomialLocality

namespace SemAC02.P2MCoefficientControl

theorem coordinate_polynomial_sum {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (f p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (f * p) = ∑ s ∈ p.support,
      coordinateMap g hg S (f * monomial s (p.coeff s)) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [Finset.mul_sum, map_sum]

theorem basis_polynomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (xMon T.1 * p) ∈ degreeSpace n p.totalDegree := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  exact degreeSpace_mono (le_totalDegree hs) (monomial_degree g hg S T s (p.coeff s))

theorem basis_polynomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) :
    coordinateMap g hg S (xMon T.1 * p) ∈ localSpace J := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  have hsub : s.support.image Prod.fst ⊆ J := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact hp v ((support_subset_vars_of_mem_support hs) hv)
  exact localSpace_mono hsub (monomial_local g hg S T s (p.coeff s))

theorem coefficient_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ degreeSpace n p.totalDegree := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (degreeSpace n p.totalDegree).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_degree g hg S ⟨T, hT⟩ p
  exact hle hf

theorem coefficient_locality {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ localSpace J := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (localSpace J).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_local g hg S ⟨T, hT⟩ p J hp
  exact hle hf

end SemAC02.P2MCoefficientControl
end

section
-- Inlined Solutions.SemanticCoefficientPolynomials

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip
open SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates SemAC02.P2MCoordinateSpaces
open SemAC02.P2MBooleanFunctionPolynomials SemAC02.P2MCoefficientControl

namespace SemAC02.P2MCoefficientPolynomials

noncomputable def coefficientMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) :=
  (polynomialMap n).comp (coordinateMap g hg S)

theorem coefficient_multilinear {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    IsMultilinear (coefficientMap g hg S p) := polynomial_multilinear _

@[simp] theorem eval_coefficient {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) :
    eval (toF2 z) (coefficientMap g hg S p) = coordinates g hg p S z := eval_polynomial _ _

theorem coefficient_congr {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p q : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (he : ∀ X : Fin n × Fin m → Bool, eval (toF2 X) p = eval (toF2 X) q) :
    coefficientMap g hg S p = coefficientMap g hg S q := by
  apply multilinear_ext_bool (coefficient_multilinear g hg S p) (coefficient_multilinear g hg S q)
  intro z
  simp only [eval_coefficient, coordinates]
  exact congrArg (fun u => (fibreBasis g hg z).equivFun u S)
    (funext (fun X : Fibre g z => he X.1))

@[simp] theorem coefficient_ml {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coefficientMap g hg S (ML p) = coefficientMap g hg S p :=
  coefficient_congr g hg S _ _ (fun _ => eval_ml _ _)

theorem coefficient_degree_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    (coefficientMap g hg S (f * p)).totalDegree ≤ p.totalDegree :=
  polynomial_degree _ (coefficient_degree g hg f hf p S)

theorem ble_degree {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) (hp : p ∈ Ble V D) :
    p.totalDegree ≤ D := by
  classical
  have hle : Ble V D ≤ restrictTotalDegree V (ZMod 2) D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    exact (mem_restrictTotalDegree V D _).mpr ((xMon_totalDegree A).trans_le hA)
  exact (mem_restrictTotalDegree V D p).mp (hle hp)

theorem coefficient_degree_multSpace {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (D : ℕ) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hp : p ∈ multSpace f D)
    (S : GlobalIndex g n) : (coefficientMap g hg S p).totalDegree ≤ D := by
  obtain ⟨q, hq, rfl⟩ := hp
  change (coefficientMap g hg S (ML (f * q))).totalDegree ≤ D
  rw [coefficient_ml]
  exact (coefficient_degree_product g hg f hf q S).trans (ble_degree D q hq)

theorem coordinates_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p * v) S z = ∑ T : GlobalIndex g n,
      coordinates g hg p T z * coordinates g hg (xMon T.1 * v) S z := by
  classical
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p * v)) =
      ∑ T : GlobalIndex g n, coordinates g hg p T z •
        (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * v)) := by
    funext X
    simp only [map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [coordinates_expansion g hg p z X, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T _
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (p * v)) S = _
  rw [he, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordinates]

theorem coefficient_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coefficientMap g hg S (p * v) = ∑ T : GlobalIndex g n,
      ML (coefficientMap g hg T p * coefficientMap g hg S (xMon T.1 * v)) := by
  classical
  refine multilinear_ext_bool (coefficient_multilinear g hg S _) ?_ ?_
  · exact (mem_restrictDegree (Fin n) _ 1).mp
      (Submodule.sum_mem _ (fun _ _ => (mem_restrictDegree (Fin n) _ 1).mpr (ml_multilinear _)))
  · intro z
    simp only [eval_coefficient, map_sum, eval_ml, map_mul]
    exact coordinates_mul g hg p v S z

end SemAC02.P2MCoefficientPolynomials
end

section
-- Inlined Solutions.P2MRelativeSpaceAlgebra

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MRelativeSpaceAlgebra

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
  rw [he, mem_light_iff]

theorem mem_multSpace_of_degree {V : Type} [Finite V]
    (f Q : MvPolynomial V (ZMod 2)) (D : ℕ) (hQ : Q.totalDegree ≤ D) :
    mulML f Q ∈ multSpace f D := by
  refine ⟨ML Q, (mem_Ble_iff D _).mpr ⟨ml_multilinear _, (ml_totalDegree_le _).trans hQ⟩, ?_⟩
  change ML (f * ML Q) = ML (f * Q)
  exact ml_mul_right f Q

theorem multSpace_multilinear {V : Type} (f p : MvPolynomial V (ZMod 2)) (D : ℕ)
    (hp : p ∈ multSpace f D) : IsMultilinear p := by
  obtain ⟨Q,_,rfl⟩ := hp
  exact ml_multilinear _

theorem multSpace_degree {V : Type} (f p : MvPolynomial V (ZMod 2)) (k D : ℕ)
    (hf : f ∈ Ble V k) (hp : p ∈ multSpace f D) : p.totalDegree ≤ k+D := by
  obtain ⟨Q,hQ,rfl⟩ := hp
  change (ML (f*Q)).totalDegree ≤ k+D
  exact (ml_totalDegree_le _).trans ((totalDegree_mul f Q).trans
    (Nat.add_le_add ((mem_Ble_iff k f).mp hf).2 ((mem_Ble_iff D Q).mp hQ).2))

theorem relative_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (f Q v : MvPolynomial (Fin n) (ZMod 2)) (D : ℕ)
    (hp : P2MRelativePC.Derivable P (multSpace f D) (mulML f Q))
    (hdeg : Q.totalDegree + v.totalDegree ≤ D) :
    P2MRelativePC.Derivable P (multSpace f D) (ML (mulML f Q * v)) := by
  apply P2MRelativePC.pc_polynomial_mul P (multSpace f D) (mulML f Q) v hp (ml_multilinear _)
  intro w hw
  have he : ML (mulML f Q * w) = mulML f (Q*w) := by
    change ML (ML (f*Q) * w) = ML (f*(Q*w))
    rw [ml_mul_left, mul_assoc]
  rw [he]
  apply mem_multSpace_of_degree
  exact (totalDegree_mul Q w).trans (by omega)

end SemAC02.P2MRelativeSpaceAlgebra
end

section
-- Inlined Solutions.P2MBooleanDimension

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanDimension

abbrev DegreeIndex (n D : ℕ) := {A : Finset (Fin n) // A.card ≤ D}

theorem span_degree_monomials (n D : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun A : DegreeIndex n D => xMon A.1)) = Ble (Fin n) D := by
  congr 1
  ext p
  constructor
  · rintro ⟨A,rfl⟩
    exact ⟨A.1,A.2,rfl⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨⟨A,hA⟩,rfl⟩

noncomputable def degreeBasis (n D : ℕ) : Basis (DegreeIndex n D) (ZMod 2) (Ble (Fin n) D) :=
  (Basis.span (xMon_linearIndependent.comp (fun A : DegreeIndex n D => A.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_degree_monomials n D))

instance finite_Ble (n D : ℕ) : Module.Finite (ZMod 2) (Ble (Fin n) D) :=
  Module.Finite.of_basis (degreeBasis n D)

def degreeIndexEquiv (n D : ℕ) : DegreeIndex n D ≃
    (j : Fin (min D n + 1)) × {A : Finset (Fin n) // A.card = j.1} where
  toFun A := ⟨⟨A.1.card, by
    have hcard := Finset.card_le_univ A.1
    simp only [Fintype.card_fin] at hcard
    omega⟩,A.1,rfl⟩
  invFun B := ⟨B.2.1,by have := B.1.2; have := B.2.2; omega⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv B := by
    rcases B with ⟨⟨j,hj⟩,A,hA⟩
    cases hA
    rfl

theorem finrank_Ble (n D : ℕ) : finrank (ZMod 2) (Ble (Fin n) D) = Hn n D := by
  classical
  rw [Module.finrank_eq_card_basis (degreeBasis n D), Fintype.card_congr (degreeIndexEquiv n D), Fintype.card_sigma]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range _ _

theorem Hn_pos (n D : ℕ) : 0 < Hn n D := by
  unfold Hn
  apply lt_of_lt_of_le (show 0 < n.choose 0 by simp)
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)

end SemAC02.P2MBooleanDimension
end

section
-- Inlined Solutions.P2MSingletonDivision

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip
open SemAC02.P2MBooleanFunctionPolynomials SemAC02.P2MRelativeSpaceAlgebra

namespace SemAC02.P2MSingletonDivision

def pointEquiv (n : ℕ) : (Fin n → Bool) ≃ nDivOmega n 1 where
  toFun z := ⟨fun v => z v.1, fun _ _ _ _ _ => Subsingleton.elim _ _⟩
  invFun X i := X.1 (i,0)
  left_inv z := rfl
  right_inv X := by
    apply Subtype.ext
    funext v
    exact congrArg X.1 (Prod.ext rfl (Subsingleton.elim _ _))

noncomputable def collapse (n : ℕ) :
    (nDivOmega n 1 → ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) :=
  (polynomialMap n).comp (LinearMap.pi (fun z => LinearMap.proj (pointEquiv n z)))

@[simp] theorem eval_collapse (n : ℕ) (u : nDivOmega n 1 → ZMod 2) (z : Fin n → Bool) :
    eval (toF2 z) (collapse n u) = u (pointEquiv n z) := eval_polynomial _ _

theorem collapse_multilinear (n : ℕ) (u : nDivOmega n 1 → ZMod 2) :
    IsMultilinear (collapse n u) := polynomial_multilinear _

theorem collapse_injective (n : ℕ) : Function.Injective (collapse n) := by
  intro u v huv
  funext X
  obtain ⟨z,rfl⟩ := (pointEquiv n).surjective X
  exact (eval_collapse n u z).symm.trans ((congrArg (eval (toF2 z)) huv).trans (eval_collapse n v z))

@[simp] theorem restrOmega_apply (n h : ℕ)
    (p : MvPolynomial (Fin n × Fin h) (ZMod 2)) (X : nDivOmega n h) :
    restrOmega n h p X = eval (toF2 X.1) p := by
  simp only [restrOmega, LinearMap.pi_apply]
  rfl

theorem collapse_restriction (n : ℕ) (p : MvPolynomial (Fin n × Fin 1) (ZMod 2)) :
    collapse n (restrOmega n 1 p) = ML (rename Prod.fst p) := by
  apply multilinear_ext_bool (collapse_multilinear n _) (ml_multilinear _)
  intro z
  rw [eval_collapse, restrOmega_apply, eval_ml, eval_rename]
  rfl

theorem collapse_mul (n : ℕ) (u v : nDivOmega n 1 → ZMod 2) :
    collapse n (u*v) = ML (collapse n u * collapse n v) := by
  apply multilinear_ext_bool (collapse_multilinear n _) (ml_multilinear _)
  intro z
  simp only [eval_collapse, eval_ml, map_mul, Pi.mul_apply]

theorem map_BleF0 (n k : ℕ) : (BleF0 n 1 k).map (collapse n) = Ble (Fin n) k := by
  apply le_antisymm
  · rintro p ⟨u,⟨q,hq,rfl⟩,rfl⟩
    rw [collapse_restriction]
    apply (mem_Ble_iff k _).mpr
    exact ⟨ml_multilinear _, (ml_totalDegree_le _).trans ((totalDegree_rename_le _ _).trans
      ((mem_restrictTotalDegree _ k q).mp hq))⟩
  · intro p hp
    let q := rename (fun i : Fin n => (i,(0 : Fin 1))) p
    have hq : q ∈ restrictTotalDegree (Fin n × Fin 1) (ZMod 2) k :=
      (mem_restrictTotalDegree _ k q).mpr ((totalDegree_rename_le _ p).trans ((mem_Ble_iff k p).mp hp).2)
    refine ⟨restrOmega n 1 q, ⟨q,hq,rfl⟩, ?_⟩
    rw [collapse_restriction]
    dsimp [q]
    rw [rename_rename]
    change ML (rename id p) = p
    rw [rename_id_apply]
    exact ml_of_multilinear p ((mem_Ble_iff k p).mp hp).1

theorem HF0_one (n k : ℕ) : HF0 n 1 k = Hn n k := by
  rw [← P2MBooleanDimension.finrank_Ble n k, ← map_BleF0 n k]
  exact (Submodule.equivMapOfInjective (collapse n) (collapse_injective n) _).finrank_eq

theorem map_error (n k : ℕ) (p : MvPolynomial (Fin n × Fin 1) (ZMod 2)) :
    ((BleF0 n 1 k).map (LinearMap.mulLeft (ZMod 2) (restrOmega n 1 p))).map (collapse n) =
      multSpace (rename Prod.fst p) k := by
  rw [← Submodule.map_comp]
  change (BleF0 n 1 k).map _ = (Ble (Fin n) k).map (mulML (rename Prod.fst p))
  rw [← map_BleF0 n k, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro u
  change collapse n (restrOmega n 1 p * u) = ML (rename Prod.fst p * collapse n u)
  rw [collapse_mul, collapse_restriction, ml_mul_left]

theorem finrank_error (n k : ℕ) (p : MvPolynomial (Fin n × Fin 1) (ZMod 2)) :
    finrank (ZMod 2) ((BleF0 n 1 k).map (LinearMap.mulLeft (ZMod 2) (restrOmega n 1 p))) =
      finrank (ZMod 2) (multSpace (rename Prod.fst p) k) := by
  rw [← map_error n k p]
  exact (Submodule.equivMapOfInjective (collapse n) (collapse_injective n) _).finrank_eq

end SemAC02.P2MSingletonDivision
end

section
-- Inlined Solutions.P2MDivisionSupports

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra
open SemAC02.P2MDivisionMonomialBasis

namespace SemAC02.P2MDivisionSupports

def Valid {n h : ℕ} (A : Finset (Fin n × Fin h)) : Prop :=
  ∀ i j j', (i,j) ∈ A → (i,j') ∈ A → j = j'

noncomputable def pointOfSupport {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : Valid A) : nDivOmega n h := by
  classical
  refine ⟨fun v => decide (v ∈ A),?_⟩
  intro i j j' hj hj'
  exact hA i j j' (by simpa only [decide_eq_true_eq] using hj) (by simpa only [decide_eq_true_eq] using hj')

noncomputable def sections {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : Valid A) : Fin n → Option (Fin h) :=
  P2MDivisionPoints.decode n h (pointOfSupport A hA)

theorem assemble_sections {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : Valid A) :
    assemble (sections A hA) = A := by
  classical
  ext v
  simp only [assemble,Finset.mem_filter,Finset.mem_univ,true_and,sections,P2MDivisionPoints.decode_eq_some,
    pointOfSupport,decide_eq_true_eq]

theorem valid_assemble {n h : ℕ} (S : Fin n → Option (Fin h)) : Valid (assemble S) := by
  classical
  intro i j j' hj hj'
  have h1 : S i = some j := by simpa [assemble] using hj
  have h2 : S i = some j' := by simpa [assemble] using hj'
  exact Option.some.inj (h1.symm.trans h2)

theorem xMon_invalid {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : ¬ Valid A) :
    restrOmega n h (xMon A) = 0 := by
  classical
  funext X
  rw [P2MSingletonDivision.restrOmega_apply]
  change eval (toF2 X.1) (xMon A) = 0
  by_contra hn
  rw [xMon_eval] at hn
  have hbit : ∀ v ∈ A, X.1 v = true := by
    intro v hv
    have hne := Finset.prod_ne_zero_iff.mp hn v hv
    cases he : X.1 v <;> simp [toF2,he] at hne ⊢
  exact hA (fun i j j' hj hj' => X.2 i j j' (hbit _ hj) (hbit _ hj'))

theorem monomial_restriction {n h : ℕ} (s : (Fin n × Fin h) →₀ ℕ) (c : ZMod 2) :
    restrOmega n h (monomial s c) = c • restrOmega n h (xMon s.support) := by
  funext X
  simp only [P2MSingletonDivision.restrOmega_apply,Pi.smul_apply,smul_eq_mul]
  exact P2MMonomialLocality.eval_monomial_squarefree s c (toF2 X.1)

end SemAC02.P2MDivisionSupports
end

section
-- Inlined Solutions.P2MDivisionDegreeBasis

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra
open SemAC02.P2MDivisionMonomialBasis SemAC02.P2MDivisionSupports

namespace SemAC02.P2MDivisionDegreeBasis

abbrev DegreeIndex (n h k : ℕ) := {S : Fin n → Option (Fin h) // (active S).card ≤ k}

noncomputable def degreeSpan (n h k : ℕ) : Submodule (ZMod 2) (nDivOmega n h → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun S : DegreeIndex n h k => divisionBasis n h S.1))

theorem BleF0_eq_span (n h k : ℕ) : BleF0 n h k = degreeSpan n h k := by
  classical
  apply le_antisymm
  · rintro f ⟨p,hp,rfl⟩
    have hpdeg := (mem_restrictTotalDegree _ k p).mp hp
    rw [p.as_sum,map_sum]
    apply Submodule.sum_mem
    intro s hs
    rw [monomial_restriction]
    apply Submodule.smul_mem
    by_cases hvalid : Valid s.support
    · let S := sections s.support hvalid
      have hScard : (active S).card ≤ k := by
        rw [← assemble_card S]
        change (assemble (sections s.support hvalid)).card ≤ k
        rw [assemble_sections]
        exact (P2MMonomialLocality.support_card_le_sum s).trans ((le_totalDegree hs).trans hpdeg)
      have he : restrOmega n h (xMon s.support) = divisionBasis n h S := by
        funext X
        rw [P2MSingletonDivision.restrOmega_apply,divisionBasis_apply]
        rw [show assemble S = s.support from assemble_sections _ _]
      rw [he]
      exact Submodule.subset_span ⟨⟨S,hScard⟩,rfl⟩
    · rw [xMon_invalid _ hvalid]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro f ⟨S,rfl⟩
    refine ⟨xMon (assemble S.1), (mem_restrictTotalDegree _ k _).mpr ((xMon_degree S.1).trans_le S.2), ?_⟩
    funext X
    exact (divisionBasis_apply n h S.1 X).symm

noncomputable def degreeBasis (n h k : ℕ) :
    Basis (DegreeIndex n h k) (ZMod 2) (BleF0 n h k) :=
  (Basis.span ((divisionBasis n h).linearIndependent.comp (fun S : DegreeIndex n h k => S.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (BleF0_eq_span n h k).symm)

instance finite_BleF0 (n h k : ℕ) : Module.Finite (ZMod 2) (BleF0 n h k) := by
  classical
  exact Module.Finite.of_basis (degreeBasis n h k)

theorem HF0_eq_card (n h k : ℕ) : HF0 n h k = Fintype.card (DegreeIndex n h k) := by
  classical
  exact Module.finrank_eq_card_basis (degreeBasis n h k)

end SemAC02.P2MDivisionDegreeBasis
end

section
-- Inlined Solutions.P2MDivisionFunctionAlgebra

open MvPolynomial

namespace SemAC02.P2MDivisionFunctionAlgebra

@[simp] theorem restriction_one (n h : ℕ) : restrOmega n h 1 = 1 := by
  funext X
  simp only [P2MSingletonDivision.restrOmega_apply,map_one,Pi.one_apply]

@[simp] theorem restriction_mul {n h : ℕ} (p q : MvPolynomial (Fin n × Fin h) (ZMod 2)) :
    restrOmega n h (p*q) = restrOmega n h p * restrOmega n h q := by
  funext X
  simp only [P2MSingletonDivision.restrOmega_apply,map_mul,Pi.mul_apply]

@[simp] theorem restriction_prod {n h : ℕ} {I : Type*} (E : Finset I)
    (p : I → MvPolynomial (Fin n × Fin h) (ZMod 2)) :
    restrOmega n h (∏ i ∈ E, p i) = ∏ i ∈ E, restrOmega n h (p i) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,restriction_one]
  | @insert i E hi ih => simp only [Finset.prod_insert hi,restriction_mul,ih]

theorem degree_mono {n h i j : ℕ} (hij : i ≤ j) : BleF0 n h i ≤ BleF0 n h j := by
  rintro f ⟨p,hp,rfl⟩
  refine ⟨p,(mem_restrictTotalDegree _ _ _).mpr ?_,rfl⟩
  exact ((mem_restrictTotalDegree _ _ _).mp hp).trans hij

theorem degree_mul {n h i j : ℕ} {f g : nDivOmega n h → ZMod 2}
    (hf : f ∈ BleF0 n h i) (hg : g ∈ BleF0 n h j) : f*g ∈ BleF0 n h (i+j) := by
  obtain ⟨p,hp,rfl⟩ := hf
  obtain ⟨q,hq,rfl⟩ := hg
  refine ⟨p*q,(mem_restrictTotalDegree _ _ _).mpr ?_,restriction_mul p q⟩
  exact (totalDegree_mul p q).trans (Nat.add_le_add ((mem_restrictTotalDegree _ _ _).mp hp)
    ((mem_restrictTotalDegree _ _ _).mp hq))

theorem span_one_add_degree {n h w : ℕ} {J : Type*}
    (gs : J → MvPolynomial (Fin n × Fin h) (ZMod 2)) (hgs : ∀ j, (gs j).totalDegree ≤ w) :
    Submodule.span (ZMod 2) (Set.range (fun j => 1+gs j)) ≤ restrictTotalDegree _ _ w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  apply (mem_restrictTotalDegree _ _ _).mpr
  exact (totalDegree_add 1 (gs j)).trans (max_le (by simp) (hgs j))

end SemAC02.P2MDivisionFunctionAlgebra
end

section
-- Inlined Solutions.P2MDivisionCommonMultiplierExistence

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDivisionCommonMultiplierExistence

open Module P2MDivisionFunctionAlgebra Classical

noncomputable def errorMap {n h k : ℕ} (e : nDivOmega n h → ZMod 2) :
    BleF0 n h k →ₗ[ZMod 2] (nDivOmega n h → ZMod 2) :=
  (LinearMap.mulLeft (ZMod 2) e).comp (BleF0 n h k).subtype

theorem error_range {n h k : ℕ} (e : nDivOmega n h → ZMod 2) :
    LinearMap.range (errorMap (k:=k) e)=(BleF0 n h k).map (LinearMap.mulLeft (ZMod 2) e) := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨p,p.2,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl⟩

theorem exists_multiplier {n h k d : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (E : Finset (nDivOmega n h → ZMod 2)) (a : E → (nDivOmega n h → ZMod 2))
    (ha : ∀ T, a T∈BleF0 n h d) (L : ℝ)
    (hL : ∀ T : E, (finrank (ZMod 2) ((BleF0 n h k).map
      (LinearMap.mulLeft (ZMod 2) (T.1+a T))) : ℝ) ≤ L)
    (R : BleF0 n h k →ₗ[ZMod 2] W)
    (hrank : (E.card : ℝ)*L < (finrank (ZMod 2) R.range : ℝ)) :
    ∃ f : BleF0 n h k, R f≠0 ∧ ∀ T : E,
      (f : nDivOmega n h → ZMod 2)*T.1∈BleF0 n h (k+d) := by
  let Y (T : E) : Type := ↥(LinearMap.range (errorMap (k:=k) (T.1+a T)))
  let maps (T : E) : BleF0 n h k →ₗ[ZMod 2] Y T := (errorMap (k:=k) (T.1+a T)).rangeRestrict
  have hdim : ((∑ T : E, finrank (ZMod 2) (Y T)) : ℝ) ≤ (E.card : ℝ)*L := by
    calc
      _ = ∑ T : E, (finrank (ZMod 2) (Y T) : ℝ) := by simp
      _ ≤ ∑ _T : E, L := by
        apply Finset.sum_le_sum
        intro T hT
        change (finrank (ZMod 2) (errorMap (k:=k) (T.1+a T)).range : ℝ) ≤ L
        rw [error_range]
        exact hL T
      _ = _ := by simp
  have hstrict : (∑ T : E, finrank (ZMod 2) (Y T)) < finrank (ZMod 2) R.range := by
    exact_mod_cast hdim.trans_lt hrank
  obtain ⟨f,hRf,hkill⟩ := P2MProofComplexity.P2MLinearMapCommonKernelWitness.exists_nonzero_image Y R maps hstrict
  refine ⟨f,hRf,?_⟩
  intro T
  have he : (T.1+a T)*(f : nDivOmega n h → ZMod 2)=0 := by
    exact congrArg Subtype.val (hkill T)
  have heq : (f : nDivOmega n h → ZMod 2)*T.1=f*a T := by
    funext x
    have hx := congrFun he x
    change (T.1 x+a T x)*(f : nDivOmega n h → ZMod 2) x=0 at hx
    rw [add_mul,CharTwo.add_eq_zero] at hx
    simpa only [Pi.mul_apply,mul_comm] using hx
  rw [heq]
  exact degree_mul f.2 (ha T)

end SemAC02.Supplement.P2MDivisionCommonMultiplierExistence
end

section
-- Inlined Solutions.P2MArithmeticCircuitBasics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MArithmeticCircuitBasics

open MvPolynomial ACirc

lemma toPoly_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) :
    toPoly (.sum ps) = (ps.map (fun p => C p.1*toPoly p.2)).sum := by
  rw [toPoly,List.attach_map_val (f := fun p : F × ACirc F V => C p.1*toPoly p.2)]

lemma toPoly_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) :
    toPoly (.prod cs) = (cs.map toPoly).prod := by
  rw [toPoly,List.attach_map_val]

lemma mem_fold_union {I : Type} [DecidableEq I] (a : I) (Ss : List (Finset I)) :
    a ∈ Ss.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ Ss, a ∈ S := by
  induction Ss with
  | nil => simp
  | cons S Ss ih => simp only [List.foldr_cons,Finset.mem_union,ih,List.mem_cons]; aesop

lemma mem_subterms_prod {F V : Type} (a : ACirc F V) (cs : List (ACirc F V)) :
    a ∈ subterms (.prod cs) ↔ a = .prod cs ∨ ∃ c ∈ cs, a ∈ subterms c := by
  classical
  rw [subterms,List.attach_map_val (f := fun c : ACirc F V => subterms c),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma mem_subterms_sum {F V : Type} (a : ACirc F V) (ps : List (F × ACirc F V)) :
    a ∈ subterms (.sum ps) ↔ a = .sum ps ∨ ∃ p ∈ ps, a ∈ subterms p.2 := by
  classical
  rw [subterms,List.attach_map_val (f := fun p : F × ACirc F V => subterms p.2),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma self_mem_subterms {F V : Type} (c : ACirc F V) : c ∈ subterms c := by
  cases c with
  | var i => simp [subterms]
  | const a => simp [subterms]
  | sum ps => exact (mem_subterms_sum _ _).mpr (Or.inl rfl)
  | prod cs => exact (mem_subterms_prod _ _).mpr (Or.inl rfl)

lemma cval_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) (x : V → Bool) :
    cval (.sum ps) x = (ps.map (fun p => p.1*cval p.2 x)).sum := by
  simp only [cval,polyFn,toPoly_sum,map_list_sum,List.map_map,Function.comp_def,map_mul,eval_C]

lemma cval_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) (x : V → Bool) :
    cval (.prod cs) x = (cs.map (fun c => cval c x)).prod := by
  simp only [cval,polyFn,toPoly_prod,map_list_prod,List.map_map,Function.comp_def]

end SemAC02.Supplement.P2MArithmeticCircuitBasics
end

section
-- Inlined Solutions.P2MArithmeticCircuitDegreeBounds

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MArithmeticCircuitDegreeBounds

open MvPolynomial ACirc P2MArithmeticCircuitBasics

lemma sum_degree {V : Type} (D : ℕ) (ps : List (MvPolynomial V (ZMod 2)))
    (h : ∀ p∈ps, p.totalDegree ≤ D) : ps.sum.totalDegree ≤ D := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    exact (totalDegree_add _ _).trans (max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq]))))

lemma prod_degree {V : Type} (ps : List (MvPolynomial V (ZMod 2))) :
    ps.prod.totalDegree ≤ (ps.map MvPolynomial.totalDegree).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simpa only [List.prod_cons,List.map_cons,List.sum_cons] using
      (totalDegree_mul p ps.prod).trans (Nat.add_le_add_left ih p.totalDegree)

lemma leaf_degree {V : Type} (c : ACirc (ZMod 2) V) (hc : IsLeaf c) : c.toPoly.totalDegree ≤ 1 := by
  cases c with
  | var i => simp [toPoly]
  | const a => simp [toPoly]
  | sum ps => exact hc.elim
  | prod cs => exact hc.elim

theorem monomial_degree {V : Type} (w : ℕ) (c : ACirc (ZMod 2) V) (hc : IsMonGate (w : ℕ∞) c) :
    c.toPoly.totalDegree ≤ w := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | sum ps => exact hc.elim
  | prod cs =>
    have hlen : cs.length ≤ w := by exact_mod_cast hc.1
    rw [toPoly_prod]
    apply (prod_degree (cs.map toPoly)).trans
    have hh : (cs.map (fun c => c.toPoly.totalDegree)).sum ≤ cs.length := by
      induction cs with
      | nil => simp
      | cons c cs ih =>
        have hleaf := leaf_degree c (hc.2 c (by simp))
        have htail : IsMonGate (w : ℕ∞) (ACirc.prod cs) := by
          constructor
          · exact_mod_cast (show cs.length ≤ w by simp only [List.length_cons] at hlen; omega)
          · intro z hz
            exact hc.2 z (by simp [hz])
        have hrest := ih htail (by simp only [List.length_cons] at hlen; omega)
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        omega
    simpa only [List.map_map,Function.comp_def] using hh.trans hlen

theorem bottom_degree {V : Type} (w : ℕ) (c : ACirc (ZMod 2) V)
    (hc : IsSumOf (IsMonGate (w : ℕ∞)) c) : c.toPoly.totalDegree ≤ w := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    rw [toPoly_sum]
    apply sum_degree
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact (totalDegree_mul _ _).trans (by simpa using monomial_degree w p.2 (hc p hp))

theorem factors_product {V : Type} (cs : List (ACirc (ZMod 2) V)) :
    (∏ i : Fin cs.length, cs[i].toPoly)=(ACirc.prod cs).toPoly := by
  rw [toPoly_prod,←List.prod_ofFn]
  exact congrArg List.prod (List.ofFn_getElem_eq_map cs toPoly)

end SemAC02.Supplement.P2MArithmeticCircuitDegreeBounds
end

section
-- Inlined Solutions.P2MDivisionCircuitFunctions

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDivisionCircuitFunctions

open MvPolynomial ACirc P2MDivisionFunctionAlgebra P2MArithmeticCircuitBasics

noncomputable def value {n h : ℕ} (c : ACirc (ZMod 2) (Fin n×Fin h)) : nDivOmega n h → ZMod 2 :=
  fun x => cval c x.1

theorem value_eq_restriction {n h : ℕ} (c : ACirc (ZMod 2) (Fin n×Fin h)) :
    value c=restrOmega n h c.toPoly := by
  funext x
  simp only [value,P2MSingletonDivision.restrOmega_apply,cval,polyFn]
  rfl

theorem sum_value {n h : ℕ} (ps : List (ZMod 2×ACirc (ZMod 2) (Fin n×Fin h))) :
    value (.sum ps)=(ps.map (fun p => p.1 • value p.2)).sum := by
  funext x
  simp only [value,cval_sum]
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simpa only [List.map_cons,List.sum_cons,Pi.add_apply,Pi.smul_apply,smul_eq_mul,value] using
      (congrArg (fun z => p.1*cval p.2 x.1+z) ih)

end SemAC02.Supplement.P2MDivisionCircuitFunctions
end

section
-- Inlined Solutions.P2MTruncatedIdealMultiplication

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MTruncatedIdealMultiplication

open MvPolynomial

theorem multiply {V : Type} (D : ℕ) (Z : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (hX : ∀ p∈Z, ∀ i : V, p.totalDegree+1 ≤ D → p*X i∈Z)
    (u v : MvPolynomial V (ZMod 2)) (hu : u∈Z)
    (hdeg : u.totalDegree+v.totalDegree ≤ D) : u*v∈Z := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    simpa only [mul_comm u (C c),←smul_eq_C_mul] using Z.smul_mem c hu
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := disjoint_support_monomial hnot hc
    have hsupp : (monomial s c+p).support=(monomial s c).support∪p.support := Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c+p).totalDegree :=
      totalDegree_le_of_support_subset (by rw [hsupp]; exact Finset.subset_union_left)
    have hdp : p.totalDegree ≤ (monomial s c+p).totalDegree :=
      totalDegree_le_of_support_subset (by rw [hsupp]; exact Finset.subset_union_right)
    rw [mul_add]
    exact Z.add_mem (ihm (by omega)) (ihp (by omega))
  | mul_X p i ih =>
    by_cases hp : p=0
    · simp only [hp,zero_mul,mul_zero]
      exact Z.zero_mem
    have hdp : (p*X i).totalDegree=p.totalDegree+1 := by
      rw [totalDegree_mul_of_isDomain hp (X_ne_zero i),totalDegree_X]
    have hmul : (u*p).totalDegree+1 ≤ D := by have hh := totalDegree_mul u p; omega
    simpa only [mul_assoc] using hX (u*p) (ih (by omega)) i hmul

end P2MProofComplexity.P2MTruncatedIdealMultiplication
end

section
-- Inlined Solutions.P2MDivisionPseudoReductionKernel

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDivisionPseudoReductionKernel

open MvPolynomial P2MDivisionFunctionAlgebra

lemma restriction_mem {n h B : ℕ} (p : MvPolynomial (Fin n×Fin h) (ZMod 2)) (hp : p.totalDegree ≤ B) :
    restrOmega n h p∈BleF0 n h B := ⟨p,(mem_restrictTotalDegree _ _ _).mpr hp,rfl⟩

noncomputable def restrictionMap (n h B : ℕ) :
    restrictTotalDegree (Fin n×Fin h) (ZMod 2) B →ₗ[ZMod 2] BleF0 n h B :=
  LinearMap.codRestrict (BleF0 n h B) ((restrOmega n h).comp
    (restrictTotalDegree (Fin n×Fin h) (ZMod 2) B).subtype) (fun p => ⟨p,p.2,rfl⟩)

noncomputable def zeroSpace {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : BleF0 n h B →ₗ[ZMod 2] W) : Submodule (ZMod 2) (MvPolynomial (Fin n×Fin h) (ZMod 2)) :=
  (LinearMap.ker (R.comp (restrictionMap n h B))).map
    (restrictTotalDegree (Fin n×Fin h) (ZMod 2) B).subtype

lemma of_zero {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : BleF0 n h B →ₗ[ZMod 2] W) (p : MvPolynomial (Fin n×Fin h) (ZMod 2))
    (hp : p.totalDegree ≤ B) (hRp : R ⟨restrOmega n h p,restriction_mem p hp⟩=0) : p∈zeroSpace R :=
  ⟨⟨p,(mem_restrictTotalDegree _ _ _).mpr hp⟩,hRp,rfl⟩

lemma zero_of_mem {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : BleF0 n h B →ₗ[ZMod 2] W) (p : MvPolynomial (Fin n×Fin h) (ZMod 2))
    (hp : p∈zeroSpace R) (hb : restrOmega n h p∈BleF0 n h B) : R ⟨restrOmega n h p,hb⟩=0 := by
  obtain ⟨q,hq,rfl⟩ := hp
  exact hq

lemma multiply_variable {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2))) (R : BleF0 n h B →ₗ[ZMod 2] W)
    (hR : IsPseudoRedF0 F R) (p : MvPolynomial (Fin n×Fin h) (ZMod 2))
    (hp : p∈zeroSpace R) (v : Fin n×Fin h) (hdeg : p.totalDegree+1 ≤ B) : p*X v∈zeroSpace R := by
  have hdp : p.totalDegree ≤ B := by omega
  have hdprod : (p*X v).totalDegree ≤ B := (totalDegree_mul _ _).trans (by simp only [totalDegree_X]; omega)
  have hb := restriction_mem p hdp
  have hbprod := restriction_mem (p*X v) hdprod
  have he : (fun x : nDivOmega n h => toF2 x.1 v*restrOmega n h p x)=restrOmega n h (p*X v) := by
    funext x
    rw [restriction_mul]
    simp only [Pi.mul_apply,P2MSingletonDivision.restrOmega_apply,eval_X]
    ring
  have hv : (fun x : nDivOmega n h => toF2 x.1 v*restrOmega n h p x)∈BleF0 n h B := he.symm ▸ hbprod
  have hz := hR.2 ⟨restrOmega n h p,hb⟩ v hv (zero_of_mem R p hp hb)
  have hsub : (⟨(fun x : nDivOmega n h => toF2 x.1 v*restrOmega n h p x),hv⟩ : BleF0 n h B)=
      ⟨restrOmega n h (p*X v),hbprod⟩ := Subtype.ext he
  rw [hsub] at hz
  exact of_zero R (p*X v) hdprod hz

theorem polynomial_product {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2))) (R : BleF0 n h B →ₗ[ZMod 2] W)
    (hR : IsPseudoRedF0 F R) (p q : MvPolynomial (Fin n×Fin h) (ZMod 2))
    (hdeg : p.totalDegree+q.totalDegree ≤ B)
    (hp : restrOmega n h p∈BleF0 n h B) (hRp : R ⟨restrOmega n h p,hp⟩=0)
    (hpq : restrOmega n h (p*q)∈BleF0 n h B) : R ⟨restrOmega n h (p*q),hpq⟩=0 := by
  have hz : p∈zeroSpace R := of_zero R p (by omega) hRp
  have hpqz := P2MProofComplexity.P2MTruncatedIdealMultiplication.multiply B (zeroSpace R)
    (fun p hp v hv => multiply_variable F R hR p hp v hv) p q hz hdeg
  exact zero_of_mem R (p*q) hpqz hpq

end SemAC02.Supplement.P2MDivisionPseudoReductionKernel
end

section
-- Inlined Solutions.P2MSPSPTermApproximation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSPSPTermApproximation

open MvPolynomial ACirc P2MDivisionFunctionAlgebra P2MDivisionCircuitFunctions

noncomputable def errorBound (n h w k r : ℕ) : ℝ :=
  2*(n.choose k : ℝ)*(h : ℝ)^k / Real.exp ((r : ℝ)/4*((k : ℝ)/(2*((n : ℝ)*h)))^w)

theorem term {n h w k r : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) (hw : 1 ≤ w)
    (hwk : 2*w ≤ k) (hkn : k ≤ n) (h3k : 3*k ≤ n)
    (t : ACirc (ZMod 2) (Fin n×Fin h)) (ht : IsProdOf (IsSumOf (IsMonGate (w : ℕ∞))) t) :
    ∃ a : nDivOmega n h → ZMod 2, a∈BleF0 n h (r*w) ∧
      (Module.finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2) (value t+a))) : ℝ) ≤
        errorBound n h w k r := by
  classical
  cases t with
  | var i => exact ht.elim
  | const z => exact ht.elim
  | sum ps => exact ht.elim
  | prod cs =>
    let gs : Fin cs.length → MvPolynomial (Fin n×Fin h) (ZMod 2) := fun i => cs[i].toPoly
    have hgs : ∀ i, (gs i).totalDegree ≤ w := fun i =>
      P2MArithmeticCircuitDegreeBounds.bottom_degree w cs[i] (ht cs[i] (List.getElem_mem i.2))
    obtain ⟨q,hq,hdeg,hprod,hfirst,hsecond⟩ :=
      SemAC02.lemma_4_9_product_approximation n h hn hh w k r hw (by omega) hkn gs hgs
    refine ⟨restrOmega n h (∏ l, (1+q l)),P2MDivisionPseudoReductionKernel.restriction_mem _ hdeg,?_⟩
    have he : restrOmega n h ((∏ j, gs j)+∏ l, (1+q l))=
        value (ACirc.prod cs)+restrOmega n h (∏ l, (1+q l)) := by
      rw [map_add]
      congr 1
      rw [value_eq_restriction]
      exact congrArg (restrOmega n h) (P2MArithmeticCircuitDegreeBounds.factors_product cs)
    have h := hsecond hwk h3k
    rw [he] at h
    simpa only [errorBound,Nat.cast_mul] using h

end SemAC02.Supplement.P2MSPSPTermApproximation
end

section
-- Inlined Solutions.P2MSPSPTopFunctions

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSPSPTopFunctions

open MvPolynomial ACirc P2MDivisionCircuitFunctions Classical

noncomputable def pool {n h : ℕ} (π : List (ACirc (ZMod 2) (Fin n×Fin h))) :
    Finset (nDivOmega n h → ZMod 2) :=
  ((π.flatMap topTerms).map value).toFinset.filter (fun p => p≠0)

theorem mem_pool {n h : ℕ} (π : List (ACirc (ZMod 2) (Fin n×Fin h))) (p : nDivOmega n h → ZMod 2) :
    p∈pool π ↔ p≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, value t=p := by
  constructor
  · intro hp
    have hn := (Finset.mem_filter.mp hp).2
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
    obtain ⟨c,hc,ht⟩ := List.mem_flatMap.mp ht
    exact ⟨hn,c,hc,t,ht,he⟩
  · rintro ⟨hn,c,hc,t,ht,he⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨t,List.mem_flatMap.mpr ⟨c,hc,ht⟩,he⟩),hn⟩

theorem card_eq_topS {n h : ℕ} (π : List (ACirc (ZMod 2) (Fin n×Fin h))) :
    (pool π).card=topS (nDivOmega n h) π := by
  have he : {g : nDivOmega n h → ZMod 2 | g≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, g=fun x => cval t x.1}=
      (↑(pool π) : Set (nDivOmega n h → ZMod 2)) := by
    ext g
    rw [Finset.mem_coe,mem_pool]
    constructor
    · rintro ⟨hn,c,hc,t,ht,he⟩
      exact ⟨hn,c,hc,t,ht,he.symm⟩
    · rintro ⟨hn,c,hc,t,ht,he⟩
      exact ⟨hn,c,hc,t,ht,he.symm⟩
  unfold topS
  rw [he,Set.ncard_coe_finset]

theorem top_term_layer {V : Type} (w : ℕ) (c t : ACirc (ZMod 2) V)
    (hc : IsSPSP (w : ℕ∞) c) (ht : t∈topTerms c) : IsProdOf (IsSumOf (IsMonGate (w : ℕ∞))) t := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ht
    exact hc p hp

theorem approximation_exists {n h w k r : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) (hw : 1 ≤ w)
    (hwk : 2*w ≤ k) (hkn : k ≤ n) (h3k : 3*k ≤ n)
    (π : List (ACirc (ZMod 2) (Fin n×Fin h))) (hπ : ∀ c∈π, IsSPSP (w : ℕ∞) c)
    (T : pool π) : ∃ a : nDivOmega n h → ZMod 2, a∈BleF0 n h (r*w) ∧
      (Module.finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2) (T.1+a))) : ℝ) ≤
        P2MSPSPTermApproximation.errorBound n h w k r := by
  obtain ⟨hnz,c,hc,t,ht,he⟩ := (mem_pool π T.1).mp T.2
  rw [←he]
  exact P2MSPSPTermApproximation.term hn hh hw hwk hkn h3k t (top_term_layer w c t (hπ c hc) ht)

end SemAC02.Supplement.P2MSPSPTopFunctions
end

section
-- Inlined Solutions.P2MSPSPLineMultiplierDegree

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSPSPLineMultiplierDegree

open MvPolynomial ACirc P2MDivisionFunctionAlgebra P2MDivisionCircuitFunctions

lemma expansion {n h : ℕ} (f : nDivOmega n h → ZMod 2)
    (ps : List (ZMod 2×ACirc (ZMod 2) (Fin n×Fin h))) :
    f*value (.sum ps)=(ps.map (fun p => p.1 • (f*value p.2))).sum := by
  rw [sum_value]
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,mul_add]
    rw [ih,mul_smul_comm]

lemma sum_mem {n h : ℕ} (D : ℕ) (ps : List (nDivOmega n h → ZMod 2))
    (hps : ∀ p∈ps, p∈BleF0 n h D) : ps.sum∈BleF0 n h D := by
  induction ps with
  | nil => exact (BleF0 n h D).zero_mem
  | cons p ps ih =>
    exact (BleF0 n h D).add_mem (hps p (by simp)) (ih (fun q hq => hps q (by simp [hq])))

lemma line_degree {n h w : ℕ} (f : nDivOmega n h → ZMod 2) (D : ℕ)
    (c : ACirc (ZMod 2) (Fin n×Fin h)) (hc : IsSPSP (w : ℕ∞) c)
    (ht : ∀ t∈topTerms c, f*value t∈BleF0 n h D) : f*value c∈BleF0 n h D := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    rw [expansion]
    apply sum_mem
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact (BleF0 n h D).smul_mem p.1 (ht p.2 (List.mem_map.mpr ⟨p,hp,rfl⟩))

theorem proof_degree {n h w k d : ℕ} (π : List (ACirc (ZMod 2) (Fin n×Fin h)))
    (hπ : ∀ c∈π, IsSPSP (w : ℕ∞) c) (f : BleF0 n h k)
    (hkill : ∀ T : P2MSPSPTopFunctions.pool π,
      (f : nDivOmega n h → ZMod 2)*T.1∈BleF0 n h (k+d)) :
    ∀ c∈π, (f : nDivOmega n h → ZMod 2)*value c∈BleF0 n h (k+d) := by
  intro c hc
  apply line_degree f (k+d) c (hπ c hc)
  intro t ht
  by_cases hz : value t=0
  · simp only [hz,mul_zero]
    exact (BleF0 n h (k+d)).zero_mem
  · have hp : value t∈P2MSPSPTopFunctions.pool π :=
      (P2MSPSPTopFunctions.mem_pool π _).mpr ⟨hz,c,hc,t,ht,rfl⟩
    exact hkill ⟨value t,hp⟩

end SemAC02.Supplement.P2MSPSPLineMultiplierDegree
end

section
-- Inlined Solutions.P2MDivisionPseudoReductionProducts

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDivisionPseudoReductionProducts

open MvPolynomial P2MDivisionFunctionAlgebra P2MDivisionPseudoReductionKernel

theorem function_product {n h B a b : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2))) (R : BleF0 n h B →ₗ[ZMod 2] W)
    (hR : IsPseudoRedF0 F R) (u v : nDivOmega n h → ZMod 2)
    (hu : u∈BleF0 n h a) (hv : v∈BleF0 n h b) (hbudget : a+b ≤ B)
    (huB : u∈BleF0 n h B) (hRu : R ⟨u,huB⟩=0) (hprod : u*v∈BleF0 n h B) :
    R ⟨u*v,hprod⟩=0 := by
  obtain ⟨p,hp,hpe⟩ := hu
  obtain ⟨q,hq,hqe⟩ := hv
  have hdp := (mem_restrictTotalDegree _ _ _).mp hp
  have hdq := (mem_restrictTotalDegree _ _ _).mp hq
  have hpB := restriction_mem p (by omega : p.totalDegree ≤ B)
  have hprodB := restriction_mem (p*q) ((totalDegree_mul p q).trans (show p.totalDegree+q.totalDegree ≤ B by omega))
  have hRp : R ⟨restrOmega n h p,hpB⟩=0 := by
    have he : (⟨restrOmega n h p,hpB⟩ : BleF0 n h B)=⟨u,huB⟩ := Subtype.ext hpe
    rwa [he]
  have hz := polynomial_product F R hR p q (by omega) hpB hRp hprodB
  have he : (⟨restrOmega n h (p*q),hprodB⟩ : BleF0 n h B)=⟨u*v,hprod⟩ := by
    apply Subtype.ext
    change restrOmega n h (p*q)=u*v
    rw [restriction_mul,hpe,hqe]
  rwa [he] at hz

lemma one_mem (n h d : ℕ) : (1 : nDivOmega n h → ZMod 2)∈BleF0 n h d := by
  simpa only [restriction_one] using restriction_mem (1 : MvPolynomial (Fin n×Fin h) (ZMod 2))
    (by simp : (1 : MvPolynomial (Fin n×Fin h) (ZMod 2)).totalDegree ≤ d)

lemma zero_or_one (a : ZMod 2) : a=0 ∨ a=1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem semantic_binary {n h B d : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2))) (R : BleF0 n h B →ₗ[ZMod 2] W)
    (hR : IsPseudoRedF0 F R) (hB : 3*d ≤ B)
    (p q g : nDivOmega n h → ZMod 2)
    (hp : p∈BleF0 n h d) (hq : q∈BleF0 n h d) (hg : g∈BleF0 n h d)
    (hpB : p∈BleF0 n h B) (hqB : q∈BleF0 n h B) (hgB : g∈BleF0 n h B)
    (hRp : R ⟨p,hpB⟩=0) (hRq : R ⟨q,hqB⟩=0)
    (hsem : ∀ x, p x=0 → q x=0 → g x=0) : R ⟨g,hgB⟩=0 := by
  have hq1 : 1+q∈BleF0 n h d := (BleF0 n h d).add_mem (one_mem n h d) hq
  have hgp : g*(1+q)∈BleF0 n h (2*d) := by simpa only [two_mul] using degree_mul hg hq1
  have hfirst : p*(g*(1+q))∈BleF0 n h B :=
    degree_mono (by omega : d+2*d ≤ B) (degree_mul hp hgp)
  have hsecond : q*g∈BleF0 n h B := degree_mono (by omega : d+d ≤ B) (degree_mul hq hg)
  have hRfirst := function_product F R hR p (g*(1+q)) hp hgp (by omega) hpB hRp hfirst
  have hRsecond := function_product F R hR q g hq hg (by omega) hqB hRq hsecond
  have hid : g=p*(g*(1+q))+q*g := by
    funext x
    simp only [Pi.add_apply,Pi.mul_apply,Pi.one_apply]
    rcases zero_or_one (p x) with hp | hp <;> rcases zero_or_one (q x) with hq | hq
    · simp [hp,hq,hsem x hp hq]
    all_goals simp [hp,hq,CharTwo.add_self_eq_zero]
  have hsub : (⟨g,hgB⟩ : BleF0 n h B)=⟨p*(g*(1+q)),hfirst⟩+⟨q*g,hsecond⟩ := Subtype.ext hid
  rw [hsub,map_add,hRfirst,hRsecond,add_zero]

end SemAC02.Supplement.P2MDivisionPseudoReductionProducts
end

section
-- Inlined Solutions.P2MDivisionCommonMultiplierSoundness

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDivisionCommonMultiplierSoundness

open MvPolynomial ACirc P2MDivisionFunctionAlgebra P2MDivisionCircuitFunctions P2MDivisionPseudoReductionProducts

theorem no_annihilator {n h B D k d₀ : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2)))
    (hF : ∀ a∈F, restrOmega n h a∈BleF0 n h d₀)
    (R : BleF0 n h B →ₗ[ZMod 2] W) (hR : IsPseudoRedF0 F R)
    (hB : 3*D ≤ B) (hbudget : k+d₀ ≤ D)
    (f : nDivOmega n h → ZMod 2) (hf : f∈BleF0 n h k)
    (hfB : f∈BleF0 n h B) (hRf : R ⟨f,hfB⟩≠0)
    (Cl : ACirc (ZMod 2) (Fin n×Fin h) → Prop)
    (π : List (ACirc (ZMod 2) (Fin n×Fin h)))
    (hπ : IsSemPCRef Cl (nDivOmega n h) (polyAx F) π)
    (hdegree : ∀ c∈π, f*value c∈BleF0 n h D) : False := by
  have hDB : D ≤ B := by omega
  have hFB : ∀ a∈F, restrOmega n h a∈BleF0 n h B := by
    intro a ha
    exact degree_mono (by omega : d₀ ≤ B) (hF a ha)
  have hBle : ∀ c∈π, f*value c∈BleF0 n h B := by
    intro c hc
    exact degree_mono hDB (hdegree c hc)
  have hz : ∀ i (hi : i < π.length), R ⟨f*value π[i],hBle _ (List.getElem_mem hi)⟩=0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      rcases hπ.2.1 i hi with ⟨a,ha,he⟩ | he | ⟨j,l,hj,hl,he⟩
      · obtain ⟨a,ha,rfl⟩ := ha
        have hp : restrOmega n h a*f∈BleF0 n h B :=
          degree_mono (by omega : d₀+k ≤ B) (degree_mul (hF a ha) hf)
        have heq : f*value π[i]=restrOmega n h a*f := by
          funext x
          change f x*cval π[i] x.1=restrOmega n h a x*f x
          rw [he x.1 x.2]
          rw [P2MSingletonDivision.restrOmega_apply]
          exact mul_comm _ _
        have hsub : (⟨f*value π[i],hBle _ (List.getElem_mem hi)⟩ : BleF0 n h B)=⟨restrOmega n h a*f,hp⟩ :=
          Subtype.ext heq
        rw [hsub]
        exact function_product F R hR _ f (hF a ha) hf (by omega) (hFB a ha)
          (hR.1 a ha (hFB a ha)) hp
      · have heq : f*value π[i]=0 := by
          funext x
          change f x*cval π[i] x.1=0
          rw [he x.1 x.2,mul_zero]
        have hsub : (⟨f*value π[i],hBle _ (List.getElem_mem hi)⟩ : BleF0 n h B)=0 := Subtype.ext heq
        rw [hsub,map_zero]
      · apply semantic_binary F R hR hB (f*value π[j]) (f*value π[l]) (f*value π[i])
          (hdegree _ (List.getElem_mem (hj.trans hi))) (hdegree _ (List.getElem_mem (hl.trans hi)))
          (hdegree _ (List.getElem_mem hi))
          (hBle _ (List.getElem_mem (hj.trans hi))) (hBle _ (List.getElem_mem (hl.trans hi)))
          (hBle _ (List.getElem_mem hi)) (ih j hj (hj.trans hi)) (ih l hl (hl.trans hi))
        intro x h₁ h₂
        rcases zero_or_one (f x) with hf | hf
        · change f x*cval π[i] x.1=0
          rw [hf,zero_mul]
        · have hp : cval π[j] x.1=0 := by simpa only [Pi.mul_apply,value,hf,one_mul] using h₁
          have hq : cval π[l] x.1=0 := by simpa only [Pi.mul_apply,value,hf,one_mul] using h₂
          change f x*cval π[i] x.1=0
          rw [hf,one_mul]
          exact he x.1 x.2 hp hq
  obtain ⟨c,hc,hval⟩ := hπ.2.2
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (List.mem_of_getLast? hc)
  have heq : f*value π[i]=f := by
    funext x
    change f x*cval π[i] x.1=f x
    rw [he,hval x.1 x.2,mul_one]
  have hsub : (⟨f*value π[i],hBle _ (List.getElem_mem hi)⟩ : BleF0 n h B)=⟨f,hfB⟩ := Subtype.ext heq
  have hh := hz i hi
  rw [hsub] at hh
  exact hRf hh

end SemAC02.Supplement.P2MDivisionCommonMultiplierSoundness
end

section
-- Inlined Solutions.P2MDivisionPseudoReductionRestriction

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDivisionPseudoReductionRestriction

open P2MDivisionFunctionAlgebra

noncomputable def restricted {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : BleF0 n h B →ₗ[ZMod 2] W) (k : ℕ) (hk : k ≤ B) : BleF0 n h k →ₗ[ZMod 2] W :=
  R.comp (Submodule.inclusion (degree_mono hk))

theorem range_eq {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : BleF0 n h B →ₗ[ZMod 2] W) (k : ℕ) (hk : k ≤ B) :
    LinearMap.range (restricted R k hk)=((Submodule.comap (BleF0 n h B).subtype (BleF0 n h k)).map R) := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨Submodule.inclusion (degree_mono hk) p,p.2,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl⟩

theorem rank_eq {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : BleF0 n h B →ₗ[ZMod 2] W) (k : ℕ) (hk : k ≤ B) :
    Module.finrank (ZMod 2) (LinearMap.range (restricted R k hk))=rankLeF0 R k := by
  rw [range_eq]
  rfl

end SemAC02.Supplement.P2MDivisionPseudoReductionRestriction
end

section
-- Inlined Solutions.P2MSPSPRankBound

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSPSPRankBound

open MvPolynomial ACirc P2MDivisionFunctionAlgebra P2MDivisionCircuitFunctions P2MSPSPTermApproximation

theorem rank_bound {n h : ℕ} (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2)))
    (hdiv : ∀ (i : Fin n) (j j' : Fin h), j≠j' → X (i,j)*X (i,j')∈F)
    (d₀ : ℕ) (hdeg : ∀ f∈F, restrOmega n h f∈BleF0 n h d₀)
    (w k r : ℕ) (hw : 1 ≤ w) (hwk : 2*w ≤ k) (hkn : k ≤ n)
    (hB : 3*(k+max d₀ (r*w)) ≤ n)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : BleF0 n h (3*(k+max d₀ (r*w))) →ₗ[ZMod 2] W) (hR : IsPseudoRedF0 F R)
    (π : List (ACirc (ZMod 2) (Fin n×Fin h)))
    (hπ : IsSemPCRef (IsSPSP (w : ℕ∞)) (nDivOmega n h) (polyAx F) π) :
    (rankLeF0 R k : ℝ)/(2*(n.choose k : ℝ)*(h : ℝ)^k)*
      Real.exp ((r : ℝ)/4*((k : ℝ)/(2*((n : ℝ)*h)))^w) ≤ topS (nDivOmega n h) π := by
  classical
  have hk : 1 ≤ k := by omega
  by_cases hh : h=0
  · simp only [hh,Nat.cast_zero,zero_pow (by omega : k≠0),mul_zero,div_zero,zero_mul]
    positivity
  have hh : 1 ≤ h := by omega
  have hn : 1 ≤ n := by omega
  let D := k+max d₀ (r*w)
  have hkB : k ≤ 3*D := by dsimp [D]; omega
  have h3k : 3*k ≤ n := by dsimp [D] at *; omega
  have hden : (0 : ℝ) < 2*(n.choose k : ℝ)*(h : ℝ)^k := by
    exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast Nat.choose_pos hkn))
      (pow_pos (by exact_mod_cast hh) _)
  let e : ℝ := Real.exp ((r : ℝ)/4*((k : ℝ)/(2*((n : ℝ)*h)))^w)
  have he : 0 < e := Real.exp_pos _
  by_contra hnot
  have hstrict : (topS (nDivOmega n h) π : ℝ)*errorBound n h w k r < (rankLeF0 R k : ℝ) := by
    have hlt := lt_of_not_ge hnot
    change (topS (nDivOmega n h) π : ℝ) < (rankLeF0 R k : ℝ)/(2*(n.choose k : ℝ)*(h : ℝ)^k)*e at hlt
    have hd := (div_lt_iff₀ he).mpr hlt
    have hx := (lt_div_iff₀ hden).mp hd
    change (topS (nDivOmega n h) π : ℝ)*(2*(n.choose k : ℝ)*(h : ℝ)^k/e) < _
    simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hx
  let E := P2MSPSPTopFunctions.pool π
  have hex : ∀ T : E, ∃ a : nDivOmega n h → ZMod 2, a∈BleF0 n h (r*w) ∧
      (Module.finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2) (T.1+a))) : ℝ) ≤
        errorBound n h w k r :=
    P2MSPSPTopFunctions.approximation_exists hn hh hw hwk hkn h3k π hπ.1
  choose a ha herror using hex
  let Rk := P2MDivisionPseudoReductionRestriction.restricted R k hkB
  have hrank : (E.card : ℝ)*errorBound n h w k r < (Module.finrank (ZMod 2) Rk.range : ℝ) := by
    rw [P2MDivisionPseudoReductionRestriction.rank_eq]
    simpa only [E,P2MSPSPTopFunctions.card_eq_topS] using hstrict
  obtain ⟨f,hfR,hkill⟩ := P2MDivisionCommonMultiplierExistence.exists_multiplier E a ha _ herror Rk hrank
  have hfB : (f : nDivOmega n h → ZMod 2)∈BleF0 n h (3*D) := degree_mono hkB f.2
  have hfR' : R ⟨(f : nDivOmega n h → ZMod 2),hfB⟩≠0 := hfR
  have hdegree := P2MSPSPLineMultiplierDegree.proof_degree π hπ.1 f hkill
  apply P2MDivisionCommonMultiplierSoundness.no_annihilator F hdeg R hR (by omega : 3*D ≤ 3*D)
    (by dsimp [D]; omega) f f.2 hfB hfR' (IsSPSP (w : ℕ∞)) π hπ
  intro c hc
  exact degree_mono (by dsimp [D]; omega : k+r*w ≤ D) (hdegree c hc)

end SemAC02.Supplement.P2MSPSPRankBound
end

end P2MSPSPRankBoundProof
open SemAC02.Supplement SemAC02.Supplement.ACirc MvPolynomial

theorem solution {n h : ℕ} (F : Set (MvPolynomial (Fin n × Fin h) (ZMod 2)))
    (hdiv : ∀ (i : Fin n) (j j' : Fin h), j ≠ j' → X (i, j) * X (i, j') ∈ F)
    (d₀ : ℕ) (hdeg : ∀ f ∈ F, restrOmega n h f ∈ BleF0 n h d₀)
    (w k r : ℕ) (hw : 1 ≤ w) (hwk : 2 * w ≤ k) (hkn : k ≤ n)
    (hB : 3 * (k + max d₀ (r * w)) ≤ n)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : BleF0 n h (3 * (k + max d₀ (r * w))) →ₗ[ZMod 2] W) (hR : IsPseudoRedF0 F R)
    (π : List (ACirc (ZMod 2) (Fin n × Fin h)))
    (hπ : IsSemPCRef (IsSPSP (w : ℕ∞)) (nDivOmega n h) (polyAx F) π) :
    (rankLeF0 R k : ℝ) / (2 * (n.choose k : ℝ) * (h : ℝ) ^ k) *
        Real.exp ((r : ℝ) / 4 * ((k : ℝ) / (2 * ((n : ℝ) * h))) ^ w) ≤
      topS (nDivOmega n h) π  := by
  exact P2MSPSPRankBoundProof.SemAC02.Supplement.P2MSPSPRankBound.rank_bound F hdiv d₀ hdeg w k r hw hwk hkn hB R hR π hπ
