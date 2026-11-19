-- Prove2me | solution 1 for SemAC02.Supplement.theorem_3_2_bphp_sps
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T15:14:40.818064+00:00
-- url     : https://prove2.me/submissions/95dfe1ce-4b15-47b0-bb84-2627e8dfc2e1

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Supplement_ResXor
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_AC02Frege_PC
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_bphp
import Mathlib.Order.PiLex
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_SemAC02_Supplement_IsPseudoRed
import Theorems.Thm_SemAC02_Supplement_theorem_4_4_sps_size_bound

open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MBitPHPSPSProof
section
-- Inlined Solutions.P2MBooleanAddressPatterns

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MBooleanAddressPatterns

variable {I : Type} [Fintype I] [DecidableEq I]

abbrev Pattern (s : Finset I) (b : I → Bool) := {a : I → Bool // ∀ i ∈ s, a i = b i}

noncomputable def freeEquiv (s : Finset I) (b : I → Bool) : Pattern s b ≃ ({i : I // i ∉ s} → Bool) where
  toFun a i := a.val i.val
  invFun f := ⟨fun i => if h : i ∈ s then b i else f ⟨i,h⟩,
    by intro i hi; simp only [dif_pos hi]⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp only [dif_pos hi]
      exact (a.property i hi).symm
    · simp only [dif_neg hi]
  right_inv f := by
    funext i
    simp only [dif_neg i.property]

theorem card (s : Finset I) (b : I → Bool) : Fintype.card (Pattern s b) = 2^(Fintype.card I-s.card) := by
  classical
  rw [Fintype.card_congr (freeEquiv s b), Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_coe]

/-- Outside a reserved pair of coordinates, at least one full pair of
addresses remains available after fewer than 2^(|I|-2) addresses are forbidden. -/
theorem fresh_pair (t s : I) (hst : s ≠ t) (used : Finset (I → Bool))
    (hused : used.card < 2^(Fintype.card I-2)) :
    ∃ a : I → Bool, a t = false ∧ a s = true ∧
      ∀ β : Bool, Function.update a t β ∉ used := by
  classical
  let b : I → Bool := fun i => if i = t then false else true
  let C : Finset (I → Bool) := Finset.univ.filter (fun a => ∀ i ∈ ({t,s} : Finset I), a i = b i)
  have hcard : C.card = 2^(Fintype.card I-2) := by
    have hh := card ({t,s} : Finset I) b
    rw [Fintype.card_subtype] at hh
    simpa only [C, Finset.card_pair hst.symm] using hh
  let forbidden := used.image (fun a => Function.update a t false)
  have hsmall : forbidden.card < C.card := by
    rw [hcard]
    exact (Finset.card_image_le).trans_lt hused
  obtain ⟨a,ha,haNot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hpat : ∀ i ∈ ({t,s} : Finset I), a i = b i := (Finset.mem_filter.mp ha).2
  have hat : a t = false := by simpa [b] using hpat t (by simp)
  have has : a s = true := by simpa [b,hst] using hpat s (by simp)
  refine ⟨a,hat,has,?_⟩
  intro β hβ
  apply haNot
  have he : Function.update (Function.update a t β) t false = a := by
    funext i
    by_cases hi : i = t <;> simp [Function.update_apply,hi,hat]
  exact Finset.mem_image.mpr ⟨Function.update a t β,hβ,he⟩

end P2MProofComplexity.P2MBooleanAddressPatterns
end

section
-- Inlined Solutions.P2MDisjointBooleanAddressPairs

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MDisjointBooleanAddressPairs

variable {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]

theorem choose (A : Finset J) (t s : J → I) (hne : ∀ j ∈ A, s j ≠ t j)
    (hbudget : 2*A.card < 2^(Fintype.card I-2)) :
    ∃ f : J → I → Bool,
      (∀ j ∈ A, f j (t j) = false ∧ f j (s j) = true) ∧
      ∀ j ∈ A, ∀ k ∈ A, j ≠ k → ∀ β γ : Bool,
        Function.update (f j) (t j) β ≠ Function.update (f k) (t k) γ := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨fun _ _ => false, by simp, by simp⟩
  | @insert j A hj ih =>
    have hbudgetA : 2*A.card < 2^(Fintype.card I-2) := by
      rw [Finset.card_insert_of_notMem hj] at hbudget
      omega
    obtain ⟨f,hf,hdis⟩ := ih (fun k hk => hne k (Finset.mem_insert_of_mem hk)) hbudgetA
    let used := A.biUnion (fun k => {Function.update (f k) (t k) false, Function.update (f k) (t k) true})
    have hused : used.card ≤ 2*A.card := by
      calc
        _ ≤ ∑ k ∈ A, ({Function.update (f k) (t k) false, Function.update (f k) (t k) true} : Finset (I → Bool)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ k ∈ A, 2 := Finset.sum_le_sum (fun k hk => by
          simpa only [Finset.card_singleton, Nat.reduceAdd] using
            Finset.card_insert_le (Function.update (f k) (t k) false) {Function.update (f k) (t k) true})
        _ = 2*A.card := by simp [Nat.mul_comm]
    obtain ⟨a,hat,has,hfresh⟩ := P2MBooleanAddressPatterns.fresh_pair (t j) (s j)
      (hne j (Finset.mem_insert_self _ _)) used (hused.trans_lt hbudgetA)
    let g := Function.update f j a
    have hg (k : J) (hk : k ∈ A) : g k = f k := by
      have hkj : k ≠ j := by intro he; subst k; exact hj hk
      exact Function.update_of_ne hkj _ _
    have hgj : g j = a := Function.update_self _ _ _
    have husedMem (k : J) (hk : k ∈ A) (β : Bool) : Function.update (f k) (t k) β ∈ used := by
      apply Finset.mem_biUnion.mpr
      refine ⟨k,hk,?_⟩
      cases β <;> simp
    refine ⟨g, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · simpa only [hgj] using And.intro hat has
      · simpa only [hg k hk] using hf k hk
    · intro k hk l hl hkl β γ
      by_cases hkj : k = j
      · subst k
        have hlA : l ∈ A := (Finset.mem_insert.mp hl).resolve_left hkl.symm
        rw [hgj, hg l hlA]
        intro he
        exact hfresh β (he.symm ▸ husedMem l hlA γ)
      · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left hkj
        by_cases hlj : l = j
        · subst l
          rw [hg k hkA, hgj]
          intro he
          exact hfresh γ (he ▸ husedMem k hkA β)
        · have hlA : l ∈ A := (Finset.mem_insert.mp hl).resolve_left hlj
          rw [hg k hkA, hg l hlA]
          exact hdis k hkA l hlA hkl β γ

end P2MProofComplexity.P2MDisjointBooleanAddressPairs
end

section
-- Inlined Solutions.P2MBitPHPAddressPairData

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MBitPHPAddressPairData

variable {m ℓ : ℕ}

def reserved (t : Fin (ℓ+2)) : Fin (ℓ+2) := if t = 0 then 1 else 0

theorem reserved_lt (t : Fin (ℓ+2)) : (reserved t).val < 2 := by
  unfold reserved
  split_ifs <;> norm_num

theorem reserved_ne (t : Fin (ℓ+2)) : reserved t ≠ t := by
  unfold reserved
  split_ifs with h
  · subst t
    simp
  · intro he
    exact h he.symm

structure Data (S : Finset (Fin m × Fin (ℓ+2))) where
  base : S → Fin (ℓ+2) → Bool
  base_true : ∀ v : S, base v (reserved v.val.2) = true
  disjoint : ∀ v w : S, v ≠ w → ∀ β γ : Bool,
    Function.update (base v) v.val.2 β ≠ Function.update (base w) w.val.2 γ

theorem exists_data (S : Finset (Fin m × Fin (ℓ+2))) (hbudget : 2*S.card < 2^ℓ) :
    Nonempty (Data S) := by
  classical
  obtain ⟨f,hf,hdis⟩ := P2MDisjointBooleanAddressPairs.choose (Finset.univ : Finset S)
    (fun v => v.val.2) (fun v => reserved v.val.2) (fun v _ => reserved_ne v.val.2)
    (by simpa only [Finset.card_univ, Fintype.card_coe, Fintype.card_fin, Nat.add_sub_cancel] using hbudget)
  exact ⟨⟨f,fun v => (hf v (Finset.mem_univ _)).2,
    fun v w hvw β γ => hdis v (Finset.mem_univ _) w (Finset.mem_univ _) hvw β γ⟩⟩

def Data.address {S : Finset (Fin m × Fin (ℓ+2))} (a : Data S) (β : S → Bool) (v : S) : Fin (ℓ+2) → Bool :=
  Function.update (a.base v) v.val.2 (β v)

theorem address_selected {S : Finset (Fin m × Fin (ℓ+2))} (a : Data S) (β : S → Bool) (v : S) :
    a.address β v v.val.2 = β v := Function.update_self _ _ _

theorem address_reserved {S : Finset (Fin m × Fin (ℓ+2))} (a : Data S) (β : S → Bool) (v : S) :
    a.address β v (reserved v.val.2) = true := by
  rw [Data.address, Function.update_of_ne (reserved_ne v.val.2)]
  exact a.base_true v

theorem address_ne {S : Finset (Fin m × Fin (ℓ+2))} (a : Data S) (β : S → Bool) (v w : S)
    (hvw : v ≠ w) : a.address β v ≠ a.address β w := a.disjoint v w hvw _ _

end P2MProofComplexity.P2MBitPHPAddressPairData
end

section
-- Inlined Solutions.P2MBooleanCubeCancellation

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MBooleanCubeCancellation

variable {I A : Type} [Fintype I] [DecidableEq I] [CommRing A] [CharP A 2]

def toggle (i : I) (β : I → Bool) : I → Bool := Function.update β i (!(β i))

theorem toggle_involutive (i : I) (β : I → Bool) : toggle i (toggle i β) = β := by
  funext j
  by_cases h : j = i <;> simp [toggle, Function.update_apply, h]

theorem toggle_ne (i : I) (β : I → Bool) : toggle i β ≠ β := by
  intro h
  have hh := congrFun h i
  simp only [toggle, Function.update_self] at hh
  cases hβ : β i <;> simp_all

theorem sum_eq_zero (i : I) (f : (I → Bool) → A)
    (hf : ∀ β, f (toggle i β) = f β) : ∑ β, f β = 0 := by
  apply Finset.sum_ninvolution (toggle i)
  · intro β
    rw [hf β]
    exact CharTwo.add_self_eq_zero _
  · intro β _
    exact toggle_ne i β
  · intro β
    exact Finset.mem_univ _
  · exact toggle_involutive i

theorem sum_full_product : (∑ β : I → Bool, ∏ i, (if β i then (1 : A) else 0)) = 1 := by
  classical
  have hprod (β : I → Bool) : (∏ i, (if β i then (1 : A) else 0)) =
      if β = (fun _ => true) then 1 else 0 := by
    by_cases he : β = fun _ => true
    · simp [he]
    · rw [if_neg he]
      obtain ⟨i, hi⟩ : ∃ i, β i = false := by
        by_contra h
        push_neg at h
        apply he
        funext i
        cases hβ : β i <;> simp_all
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  simp only [hprod]
  simp

end P2MProofComplexity.P2MBooleanCubeCancellation
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
-- Inlined Solutions.P2MAffineBooleanForms

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MAffineBooleanForms

open ACirc P2MArithmeticCircuitBasics MvPolynomial

lemma zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

noncomputable def evalMap {V : Type} [Fintype V] (x : V → Bool) :
    (Option V → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := v none+∑ i, v (some i)*(if x i then 1 else 0)
  map_add' v w := by simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]; ring
  map_smul' a v := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_add,Finset.mul_sum,mul_assoc] <;> ring

def equationVector {V : Type} (e : LinEq V) : Option V → ZMod 2
  | none => e.2+1
  | some i => e.1 i

lemma vector_nonzero_iff {V : Type} [Fintype V] (e : LinEq V) (x : V → Bool) :
    evalMap x (equationVector e) ≠ 0 ↔ e.Sat x := by
  change e.2+1+(∑ i, e.1 i*(if x i then 1 else 0)) ≠ 0 ↔
    (∑ i, e.1 i*(if x i then 1 else 0)) = e.2
  let l := ∑ i, e.1 i*(if x i then (1 : ZMod 2) else 0)
  change e.2+1+l ≠ 0 ↔ l = e.2
  rw [show e.2+1+l = 1+(l+e.2) by ring,← CharTwo.add_eq_zero]
  rcases zero_or_one (l+e.2) with h | h
  · norm_num [h]
  · simp only [h,CharTwo.add_self_eq_zero,ne_eq,not_true_eq_false,one_ne_zero]

noncomputable def affineCircuit {V : Type} [Fintype V] (v : Option V → ZMod 2) : ACirc (ZMod 2) V :=
  .sum ((v none+1,.const 1)::(Finset.univ.toList.map (fun i => (v (some i),.var i))))

lemma cval_affine {V : Type} [Fintype V] (v : Option V → ZMod 2) (x : V → Bool) :
    cval (affineCircuit v) x = 1+evalMap x v := by
  rw [affineCircuit,cval_sum]
  simp only [List.map_cons,List.sum_cons,List.map_map,Function.comp_def,cval,polyFn,toPoly,
    eval_C,eval_X,mul_one]
  rw [Finset.sum_map_toList]
  change v none+1+(∑ i, v (some i)*(if x i then 1 else 0)) =
    1+(v none+∑ i, v (some i)*(if x i then 1 else 0))
  ring

lemma affine_layer {V : Type} [Fintype V] (v : Option V → ZMod 2) :
    IsSumOf IsLeaf (affineCircuit v) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · trivial
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    trivial

lemma subterms_affine {V : Type} [Fintype V] (v : Option V → ZMod 2) (c : ACirc (ZMod 2) V)
    (hc : c ∈ subterms (affineCircuit v)) :
    c = affineCircuit v ∨ c = .const 1 ∨ ∃ i : V, c = .var i := by
  classical
  rcases (mem_subterms_sum c _).mp hc with he | ⟨q,hq,hc⟩
  · exact Or.inl he
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inl (by simpa only [subterms,Finset.mem_singleton] using hc))
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      exact Or.inr (Or.inr ⟨i,by simpa only [subterms,Finset.mem_singleton] using hc⟩)

end SemAC02.Supplement.P2MAffineBooleanForms
end

section
-- Inlined Solutions.P2MBooleanMonomialExtraction

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MBooleanMonomialExtraction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

variable {V A : Type} [DecidableEq V] [CommRing A] [CharP A 2]

theorem monomial (S T : Finset V) (hcard : T.card ≤ S.card)
    (g : (S → Bool) → V → A)
    (hselected : ∀ β (v : S), g β v.val = if β v then 1 else 0)
    (houtside : ∀ v, v ∉ S → ∀ β γ, g β v = g γ v) :
    (∑ β : S → Bool, ∏ v ∈ T, g β v) = if T = S then 1 else 0 := by
  classical
  by_cases he : T = S
  · subst T
    rw [if_pos rfl]
    have hprod (β : S → Bool) : (∏ v ∈ S, g β v) = ∏ v : S, (if β v then (1 : A) else 0) := by
      rw [← Finset.prod_attach]
      simp only [Finset.attach_eq_univ]
      exact Finset.prod_congr rfl (fun v _ => hselected β v)
    simp only [hprod]
    exact P2MBooleanCubeCancellation.sum_full_product
  · rw [if_neg he]
    have hnot : ¬ S ⊆ T := by
      intro hsub
      exact he (Finset.eq_of_subset_of_card_le hsub hcard).symm
    obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hnot
    apply P2MBooleanCubeCancellation.sum_eq_zero (⟨i, hiS⟩ : S)
    intro β
    apply Finset.prod_congr rfl
    intro v hv
    by_cases hvS : v ∈ S
    · rw [hselected _ ⟨v, hvS⟩, hselected _ ⟨v, hvS⟩]
      have hne : (⟨v, hvS⟩ : S) ≠ ⟨i, hiS⟩ := by
        intro hh
        have hvI := congrArg Subtype.val hh
        change v = i at hvI
        exact hiT (by rwa [← hvI])
      simp only [P2MBooleanCubeCancellation.toggle, Function.update_of_ne hne]
    · exact houtside v hvS _ _

/-- Summing all assignments to a monomial of maximum degree extracts its
coefficient; variables outside that monomial may be restricted arbitrarily,
provided those restrictions do not depend on the selected assignment. -/
theorem polynomial {W : Type} (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p)
    (d : V →₀ ℕ) (hd : d ∈ p.support)
    (hmax : ∀ e ∈ p.support, e.support.card ≤ d.support.card)
    (g : (d.support → Bool) → V → MvPolynomial W (ZMod 2))
    (hselected : ∀ β (v : d.support), g β v.val = if β v then 1 else 0)
    (houtside : ∀ v, v ∉ d.support → ∀ β γ, g β v = g γ v) :
    (∑ β : d.support → Bool, bind₁ (g β) p) = 1 := by
  classical
  have hcoeff : p.coeff d = 1 := by
    have hnonzero := mem_support_iff.mp hd
    rcases SemAC02.Supplement.P2MAffineBooleanForms.zero_or_one (p.coeff d) with hz | ho
    · exact (hnonzero hz).elim
    · exact ho
  have hexpand (β : d.support → Bool) : bind₁ (g β) p =
      ∑ e ∈ p.support, p.coeff e • ∏ v ∈ e.support, g β v := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [P2MBooleanBasis.squarefree_monomial e _ (hp e he), map_smul]
    simp only [xMon, map_prod, bind₁_X_right]
  simp only [hexpand]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum]
  have hmon (e : V →₀ ℕ) (he : e ∈ p.support) :
      (∑ β : d.support → Bool, ∏ v ∈ e.support, g β v) = if e = d then 1 else 0 := by
    rw [monomial d.support e.support (hmax e he) g hselected houtside]
    have heq : e.support = d.support ↔ e = d := by
      constructor
      · exact P2MBooleanRestrictions.multilinear_exponent_ext e d (hp e he) (hp d hd)
      · exact fun h => congrArg Finsupp.support h
    simp only [heq]
  rw [Finset.sum_eq_single d]
  · rw [hmon d hd, if_pos rfl, hcoeff, one_smul]
  · intro e he hne
    rw [hmon e he, if_neg hne, smul_zero]
  · intro hnot
    exact (hnot hd).elim

end P2MProofComplexity.P2MBooleanMonomialExtraction
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
-- Inlined Solutions.P2MRelativePCFinite

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePCFinite

def Derivable {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (p : MvPolynomial V (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial V (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q ∈ U) ∧ p ∈ π

theorem pc_zero {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) : Derivable P U 0 := Or.inl rfl

theorem pc_mem {V : Type} {P : Set (MvPolynomial V (ZMod 2))}
    {U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))}
    {p : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) : p ∈ U := by
  rcases hp with rfl | ⟨π,_,hmem,hp⟩
  · exact U.zero_mem
  · exact hmem p hp

theorem pc_smul {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    {p : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) (c : ZMod 2) :
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

theorem pc_add {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    {p q : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) (hq : Derivable P U q) :
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

theorem pc_mul_X {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    {p : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) (v : V)
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

theorem pc_axiom {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (p : MvPolynomial V (ZMod 2)) (hp : p ∈ P) (hmem : ML p ∈ U) :
    Derivable P U (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hmem, by simp⟩
  intro k hk
  have he : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p,hp,1,by simp⟩

end SemAC02.P2MRelativePCFinite
end

section
-- Inlined Solutions.P2MBooleanDegreeSpaces

open MvPolynomial AC02Frege AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MBooleanDegreeSpaces

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
  rw [he,mem_light_iff]

end SemAC02.P2MBooleanDegreeSpaces
end

section
-- Inlined Solutions.P2MRelativePCRenaming

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MRelativePCRenaming

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces

variable {V W : Type} [Finite V] [Finite W]

/-- Renaming followed by reduction is a homomorphism of Boolean polynomial algebras. -/
noncomputable def transport (f : V → W) :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial W (ZMod 2) :=
  ML.comp (rename f).toLinearMap

theorem transport_ml (f : V → W) (p : MvPolynomial V (ZMod 2)) :
    transport f (ML p) = transport f p := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [transport, LinearMap.comp_apply, AlgHom.toLinearMap_apply, eval_ml, eval_rename]

theorem transport_mul_X (f : V → W) (v : V) (p : MvPolynomial V (ZMod 2)) :
    transport f (ML (X v*p)) = ML (X (f v)*transport f p) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [transport, LinearMap.comp_apply, AlgHom.toLinearMap_apply, eval_ml,
    eval_rename, map_mul, eval_X, Function.comp_apply]

theorem transport_degree (f : V → W) (p : MvPolynomial V (ZMod 2)) :
    (transport f p).totalDegree ≤ p.totalDegree :=
  (P2MBooleanFlip.ml_totalDegree_le _).trans (totalDegree_rename_le f p)

theorem transport_mem (f : V → W) (B : ℕ) (p : MvPolynomial V (ZMod 2))
    (hp : p.totalDegree ≤ B) : transport f p ∈ Ble W B :=
  (mem_Ble_iff B _).mpr ⟨ml_multilinear _, (transport_degree f p).trans hp⟩

/-- Each substituted axiom may have an independent bounded-degree derivation. These
certificates extend line by line to every derivation from the substituted axioms. -/
theorem derivation (f : V → W) (P : Set (MvPolynomial V (ZMod 2)))
    (Q : Set (MvPolynomial W (ZMod 2))) (B : ℕ)
    (haxiom : ∀ p ∈ P, P2MRelativePCFinite.Derivable Q (Ble W B) (transport f p))
    (π : List (MvPolynomial V (ZMod 2))) (hπ : PCNonBool.IsDerivation ML P π)
    (hdegree : ∀ p ∈ π, p.totalDegree ≤ B) :
    ∀ p ∈ π, P2MRelativePCFinite.Derivable Q (Ble W B) (transport f p) := by
  have hall : ∀ k (hk : k < π.length),
      P2MRelativePCFinite.Derivable Q (Ble W B) (transport f π[k]) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ k hk with ⟨p, hp, a, he⟩ | ⟨i, j, hi, hj, a, b, he⟩ | ⟨i, hi, v, he⟩
      · rw [he, map_smul, transport_ml]
        exact P2MRelativePCFinite.pc_smul Q (Ble W B) (haxiom p hp) a
      · rw [he, map_add, map_smul, map_smul]
        exact P2MRelativePCFinite.pc_add Q (Ble W B)
          (P2MRelativePCFinite.pc_smul Q _ (ih i hi (hi.trans hk)) a)
          (P2MRelativePCFinite.pc_smul Q _ (ih j hj (hj.trans hk)) b)
      · rw [he, transport_mul_X]
        apply P2MRelativePCFinite.pc_mul_X Q (Ble W B) (ih i hi (hi.trans hk)) (f v)
        rw [← transport_mul_X, ← he]
        exact transport_mem f B π[k] (hdegree _ (List.getElem_mem hk))
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
  exact hall k hk

end SemAC02.Supplement.P2MRelativePCRenaming
end

section
-- Inlined Solutions.P2MRelativePCRestriction

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MRelativePCRestriction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces

variable {V W : Type} [Finite V] [Finite W]

/-- Each variable is retained as a target variable or assigned a field constant. -/
noncomputable def leaf (ρ : V → W ⊕ ZMod 2) (v : V) : MvPolynomial W (ZMod 2) :=
  Sum.elim X C (ρ v)

noncomputable def transport (ρ : V → W ⊕ ZMod 2) :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial W (ZMod 2) :=
  ML.comp (bind₁ (leaf ρ)).toLinearMap

theorem transport_multilinear (ρ : V → W ⊕ ZMod 2) (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (transport ρ p) := ml_multilinear _

theorem evaluation (ρ : V → W ⊕ ZMod 2) (p : MvPolynomial V (ZMod 2)) (x : W → ZMod 2) :
    eval x (transport ρ p) = eval (fun v => eval x (leaf ρ v)) p := by
  change eval x (ML (bind₁ (leaf ρ) p)) = _
  rw [eval_ml]
  exact eval₂Hom_bind₁ _ _ _ _

theorem transport_ml (ρ : V → W ⊕ ZMod 2) (p : MvPolynomial V (ZMod 2)) :
    transport ρ (ML p) = transport ρ p := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  change eval x (transport ρ (ML p)) = eval x (transport ρ p)
  rw [evaluation, evaluation, eval_ml]

theorem transport_mul_X (ρ : V → W ⊕ ZMod 2) (v : V) (p : MvPolynomial V (ZMod 2)) :
    transport ρ (ML (X v*p)) = ML (leaf ρ v*transport ρ p) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  change eval x (transport ρ (ML (X v*p))) = eval x (ML (leaf ρ v*transport ρ p))
  rw [evaluation, eval_ml, map_mul, eval_X, eval_ml, map_mul, evaluation]

theorem transport_degree (ρ : V → W ⊕ ZMod 2) (p : MvPolynomial V (ZMod 2)) :
    (transport ρ p).totalDegree ≤ p.totalDegree := by
  apply (P2MBooleanFlip.ml_totalDegree_le _).trans
  apply P2MBooleanFlip.bind_linear_totalDegree_le
  intro v
  unfold leaf
  cases ρ v <;> simp

theorem transport_mem (ρ : V → W ⊕ ZMod 2) (B : ℕ) (p : MvPolynomial V (ZMod 2))
    (hp : p.totalDegree ≤ B) : transport ρ p ∈ Ble W B :=
  (mem_Ble_iff B _).mpr ⟨ml_multilinear _, (transport_degree ρ p).trans hp⟩

theorem transport_one (ρ : V → W ⊕ ZMod 2) : transport ρ 1 = 1 := by
  change ML (bind₁ (leaf ρ) 1) = 1
  rw [map_one, ml_of_multilinear _ (by simp [IsMultilinear])]

theorem derivation (ρ : V → W ⊕ ZMod 2) (P : Set (MvPolynomial V (ZMod 2)))
    (Q : Set (MvPolynomial W (ZMod 2))) (B : ℕ)
    (haxiom : ∀ p ∈ P, P2MRelativePCFinite.Derivable Q (Ble W B) (transport ρ p))
    (π : List (MvPolynomial V (ZMod 2))) (hπ : PCNonBool.IsDerivation ML P π)
    (hdegree : ∀ p ∈ π, p.totalDegree ≤ B) :
    ∀ p ∈ π, P2MRelativePCFinite.Derivable Q (Ble W B) (transport ρ p) := by
  have hall : ∀ k (hk : k < π.length),
      P2MRelativePCFinite.Derivable Q (Ble W B) (transport ρ π[k]) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ k hk with ⟨p, hp, a, he⟩ | ⟨i, j, hi, hj, a, b, he⟩ | ⟨i, hi, v, he⟩
      · rw [he, map_smul, transport_ml]
        exact P2MRelativePCFinite.pc_smul Q (Ble W B) (haxiom p hp) a
      · rw [he, map_add, map_smul, map_smul]
        exact P2MRelativePCFinite.pc_add Q (Ble W B)
          (P2MRelativePCFinite.pc_smul Q _ (ih i hi (hi.trans hk)) a)
          (P2MRelativePCFinite.pc_smul Q _ (ih j hj (hj.trans hk)) b)
      · have hmem := transport_mem ρ B π[k] (hdegree _ (List.getElem_mem hk))
        rw [he, transport_mul_X] at hmem ⊢
        cases hleaf : ρ v with
        | inl w =>
          simp only [leaf, hleaf, Sum.elim_inl] at hmem ⊢
          exact P2MRelativePCFinite.pc_mul_X Q _ (ih i hi (hi.trans hk)) w hmem
        | inr c =>
          simp only [leaf, hleaf, Sum.elim_inr] at hmem ⊢
          rw [← smul_eq_C_mul, map_smul, ml_of_multilinear _ (transport_multilinear ρ _)]
          exact P2MRelativePCFinite.pc_smul Q _ (ih i hi (hi.trans hk)) c
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
  exact hall k hk

end SemAC02.Supplement.P2MRelativePCRestriction
end

section
-- Inlined Solutions.P2MBooleanRestrictionExtraction

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MBooleanRestrictionExtraction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

variable {U V W : Type} [Finite U] [Finite V] [Finite W] [DecidableEq V]

theorem renamed (f : U → V) (ρ : V → W ⊕ ZMod 2) (p : MvPolynomial U (ZMod 2)) :
    P2MRelativePCRestriction.transport ρ (P2MRelativePCRenaming.transport f p) =
      P2MRelativePCRestriction.transport (ρ ∘ f) p := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  change eval x (P2MRelativePCRestriction.transport ρ (P2MRelativePCRenaming.transport f p)) =
    eval x (P2MRelativePCRestriction.transport (ρ ∘ f) p)
  rw [P2MRelativePCRestriction.evaluation, P2MRelativePCRestriction.evaluation]
  change eval (fun v => eval x (P2MRelativePCRestriction.leaf ρ v)) (ML (rename f p)) = _
  rw [eval_ml, eval_rename]
  rfl

theorem sum_eq_one (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p)
    (d : V →₀ ℕ) (hd : d ∈ p.support)
    (hmax : ∀ e ∈ p.support, e.support.card ≤ d.support.card)
    (ρ : (d.support → Bool) → V → W ⊕ ZMod 2)
    (hselected : ∀ β (v : d.support), P2MRelativePCRestriction.leaf (ρ β) v.val = if β v then 1 else 0)
    (houtside : ∀ v, v ∉ d.support → ∀ β γ,
      P2MRelativePCRestriction.leaf (ρ β) v = P2MRelativePCRestriction.leaf (ρ γ) v) :
    (∑ β : d.support → Bool, P2MRelativePCRestriction.transport (ρ β) p) = 1 := by
  have hraw := P2MProofComplexity.P2MBooleanMonomialExtraction.polynomial p hp d hd hmax
    (fun β => P2MRelativePCRestriction.leaf (ρ β)) hselected houtside
  change (∑ β : d.support → Bool, ML (bind₁ (P2MRelativePCRestriction.leaf (ρ β)) p)) = 1
  rw [← map_sum, hraw]
  exact ml_of_multilinear _ (by simp [IsMultilinear])

end SemAC02.Supplement.P2MBooleanRestrictionExtraction
end

section
-- Inlined Solutions.P2MBitPHPRestriction

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MBitPHPRestriction

open MvPolynomial AC02Frege SemAC02.Supplement
open P2MBitPHPAddressPairData

variable {m ℓ : ℕ}

def tail (t : Fin ℓ) : Fin (ℓ+2) := ⟨t.val+2,by omega⟩

def lower (t : Fin (ℓ+2)) (ht : 2 ≤ t.val) : Fin ℓ := ⟨t.val-2,by omega⟩

theorem tail_lower (t : Fin (ℓ+2)) (ht : 2 ≤ t.val) : tail (lower t ht) = t := by
  apply Fin.ext
  simp only [tail,lower]
  omega

theorem lower_tail (t : Fin ℓ) : lower (tail t) (by simp [tail]) = t := by
  apply Fin.ext
  simp [lower,tail]

def HasRow (S : Finset (Fin m × Fin (ℓ+2))) (u : Fin m) : Prop := ∃ v : S, v.val.1 = u

noncomputable def restriction (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (β : S → Bool) (e : Fin m × Fin (ℓ+2)) : (Fin m × Fin ℓ) ⊕ ZMod 2 :=
  open Classical in if h : HasRow S e.1 then
    Sum.inr (if a.address β (Classical.choose h) e.2 then 1 else 0)
  else if ht : 2 ≤ e.2.val then Sum.inl (e.1,lower e.2 ht) else Sum.inr 0

theorem hasRow (S : Finset (Fin m × Fin (ℓ+2))) (v : S) : HasRow S v.val.1 := ⟨v,rfl⟩

theorem chosen (S : Finset (Fin m × Fin (ℓ+2)))
    (hrows : Set.InjOn Prod.fst (S : Set (Fin m × Fin (ℓ+2))))
    (v : S) (h : HasRow S v.val.1) : Classical.choose h = v := by
  apply Subtype.ext
  exact hrows (Classical.choose h).property v.property (Classical.choose_spec h)

theorem selected_row (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (hrows : Set.InjOn Prod.fst (S : Set (Fin m × Fin (ℓ+2))))
    (β : S → Bool) (v : S) (t : Fin (ℓ+2)) :
    restriction S a β (v.val.1,t) = Sum.inr (if a.address β v t then 1 else 0) := by
  have h := hasRow S v
  simp only [restriction,dif_pos h,chosen S hrows v h]

theorem unselected_row (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (β : S → Bool) (u : Fin m) (hu : ¬ HasRow S u) (t : Fin (ℓ+2)) :
    restriction S a β (u,t) = if ht : 2 ≤ t.val then Sum.inl (u,lower t ht) else Sum.inr 0 := by
  simp only [restriction,dif_neg hu]

theorem selected_leaf (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (hrows : Set.InjOn Prod.fst (S : Set (Fin m × Fin (ℓ+2))))
    (β : S → Bool) (v : S) : P2MRelativePCRestriction.leaf (restriction S a β) v.val = if β v then 1 else 0 := by
  have hv : v.val = (v.val.1,v.val.2) := rfl
  rw [hv,P2MRelativePCRestriction.leaf,selected_row S a hrows β v v.val.2]
  simp only [Sum.elim_inr,address_selected]
  cases β v <;> simp

theorem outside_independent (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (hrows : Set.InjOn Prod.fst (S : Set (Fin m × Fin (ℓ+2))))
    (e : Fin m × Fin (ℓ+2)) (he : e ∉ S) (β γ : S → Bool) :
    restriction S a β e = restriction S a γ e := by
  classical
  by_cases hr : HasRow S e.1
  · let v : S := Classical.choose hr
    have hv : v.val.1 = e.1 := Classical.choose_spec hr
    have ht : e.2 ≠ v.val.2 := by
      intro hh
      exact he (by have heq : e = v.val := Prod.ext hv.symm hh; rw [heq]; exact v.property)
    have hEq : a.address β (Classical.choose hr) e.2 = a.address γ (Classical.choose hr) e.2 := by
      change Function.update (a.base v) v.val.2 (β v) e.2 = Function.update (a.base v) v.val.2 (γ v) e.2
      rw [Function.update_of_ne ht,Function.update_of_ne ht]
    simp only [restriction,dif_pos hr,hEq]
  · simp only [restriction,dif_neg hr]

theorem extraction (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (hrows : Set.InjOn Prod.fst (S : Set (Fin m × Fin (ℓ+2))))
    (p : MvPolynomial (Fin m × Fin (ℓ+2)) (ZMod 2)) (hp : IsMultilinear p)
    (d : (Fin m × Fin (ℓ+2)) →₀ ℕ) (hd : d ∈ p.support) (hS : d.support = S)
    (hmax : ∀ e ∈ p.support, e.support.card ≤ d.support.card) :
    (∑ β : S → Bool, P2MRelativePCRestriction.transport (restriction S a β) p) = 1 := by
  subst S
  apply P2MBooleanRestrictionExtraction.sum_eq_one p hp d hd hmax
  · exact selected_leaf d.support a hrows
  · intro v hv β γ
    exact congrArg (Sum.elim X C) (outside_independent d.support a hrows v hv β γ)

end P2MProofComplexity.P2MBitPHPRestriction
end

section
-- Inlined Solutions.P2MMatchingPolynomialFunctions

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MMatchingPolynomialFunctions

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- A set of edges is a partial matching when no two distinct edges share an endpoint. -/
def IsMatching (A : Finset (L×R)) : Prop :=
  ∀ e ∈ A, ∀ f ∈ A, e.1 = f.1 ∨ e.2 = f.2 → e = f

abbrev Placements (L R : Type) := {A : Finset (L×R) // IsMatching A}

theorem matching_mono {A B : Finset (L×R)} (hAB : A ⊆ B) (hB : IsMatching B) : IsMatching A :=
  fun e he f hf hshare => hB e (hAB he) f (hAB hf) hshare

theorem matching_empty : IsMatching (∅ : Finset (L×R)) := by simp [IsMatching]

theorem matching_singleton (e : L×R) : IsMatching ({e} : Finset (L×R)) := by
  intro f hf g hg _
  exact (Finset.mem_singleton.mp hf).trans (Finset.mem_singleton.mp hg).symm

noncomputable def assignment (B : Placements L R) (e : L×R) : ZMod 2 := if e ∈ B.val then 1 else 0

noncomputable def evaluation : MvPolynomial (L×R) (ZMod 2) →ₗ[ZMod 2] (Placements L R → ZMod 2) where
  toFun p B := eval (assignment B) p
  map_add' p q := by
    funext B
    change eval (assignment B) (p+q) = eval (assignment B) p+eval (assignment B) q
    exact map_add (eval (assignment B)) p q
  map_smul' a p := by
    funext B
    change eval (assignment B) (a • p) = a • eval (assignment B) p
    exact smul_eval (assignment B) p a

noncomputable def monomial (A : Finset (L×R)) : Placements L R → ZMod 2 := evaluation (xMon A)

theorem monomial_value (A : Finset (L×R)) (B : Placements L R) :
    monomial A B = if A ⊆ B.val then 1 else 0 := P2MBooleanRestrictions.xMon_eval_point A B.val

theorem monomial_zero (A : Finset (L×R)) (hA : ¬ IsMatching A) : monomial A = 0 := by
  funext B
  have hnot : ¬ A ⊆ B.val := fun hh => hA (matching_mono hh B.property)
  simp only [monomial_value, if_neg hnot, Pi.zero_apply]

theorem monomial_mul (A B : Finset (L×R)) : monomial A*monomial B = monomial (A ∪ B) := by
  funext T
  simp only [Pi.mul_apply, monomial_value, Finset.union_subset_iff]
  by_cases hA : A ⊆ T.val <;> by_cases hB : B ⊆ T.val <;> simp [hA, hB]

theorem monomial_empty : monomial (∅ : Finset (L×R)) = 1 := by
  funext B
  simp only [monomial_value, Finset.empty_subset, if_true, Pi.one_apply]

theorem evaluation_injective (p q : MvPolynomial (L×R) (ZMod 2))
    (hp : p ∈ monomialSpan IsMatching) (hq : q ∈ monomialSpan IsMatching)
    (he : evaluation p = evaluation q) : p = q := by
  apply sub_eq_zero.mp
  apply P2MBooleanRestrictions.eval_injective_on_monomialSpan IsMatching (p-q)
    ((monomialSpan IsMatching).sub_mem hp hq)
  intro A hA
  have hh := congrFun he (⟨A, hA⟩ : Placements L R)
  rw [map_sub]
  exact sub_eq_zero.mpr hh

noncomputable def space (d : ℕ) : Submodule (ZMod 2) (Placements L R → ZMod 2) :=
  Submodule.span (ZMod 2) {p | ∃ A : Finset (L×R), IsMatching A ∧ A.card ≤ d ∧ p = monomial A}

theorem monomial_mem (A : Finset (L×R)) (hA : IsMatching A) (d : ℕ) (hd : A.card ≤ d) :
    monomial A ∈ space (L:=L) (R:=R) d := Submodule.subset_span ⟨A, hA, hd, rfl⟩

theorem one_mem (d : ℕ) : (1 : Placements L R → ZMod 2) ∈ space d := by
  rw [← monomial_empty]
  exact monomial_mem ∅ matching_empty d (by simp)

theorem space_mono {d e : ℕ} (hde : d ≤ e) : space (L:=L) (R:=R) d ≤ space e := by
  apply Submodule.span_le.mpr
  rintro p ⟨A, hA, hd, rfl⟩
  exact monomial_mem A hA e (hd.trans hde)

theorem mul_mem {d e : ℕ} {p q : Placements L R → ZMod 2} (hp : p ∈ space d) (hq : q ∈ space e) :
    p*q ∈ space (d+e) := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨A, hA, hd, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨B, hB, he, rfl⟩ := hq
      rw [monomial_mul]
      by_cases hAB : IsMatching (A ∪ B)
      · exact monomial_mem _ hAB _ ((Finset.card_union_le _ _).trans (Nat.add_le_add hd he))
      · rw [monomial_zero _ hAB]
        exact (space _).zero_mem
    | zero => simpa only [mul_zero] using (space (L:=L) (R:=R) (d+e)).zero_mem
    | add q r hq hr ihq ihr => simpa only [mul_add] using (space _).add_mem ihq ihr
    | smul a q hq ih => simpa only [mul_smul_comm] using (space _).smul_mem a ih
  | zero => simpa only [zero_mul] using (space (L:=L) (R:=R) (d+e)).zero_mem
  | add p r hp hr ihp ihr => simpa only [add_mul] using (space _).add_mem ihp ihr
  | smul a p hp ih => simpa only [smul_mul_assoc] using (space _).smul_mem a ih

end P2MProofComplexity.P2MMatchingPolynomialFunctions
end

section
-- Inlined Solutions.P2MMatchingSubstitutionDegree

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MMatchingSubstitutionDegree

open MvPolynomial P2MMatchingPolynomialFunctions

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem pow_mem {p : Placements L R → ZMod 2} {d : ℕ} (hp : p ∈ space d) (k : ℕ) :
    p^k ∈ space (d*k) := by
  induction k with
  | zero => simpa only [pow_zero, Nat.mul_zero] using (one_mem 0 (L:=L) (R:=R))
  | succ k ih =>
    simpa only [pow_succ, Nat.mul_succ, Nat.add_comm] using mul_mem ih hp

theorem prod_mem {I : Type*} (s : Finset I) (p : I → Placements L R → ZMod 2) (d : I → ℕ)
    (h : ∀ i ∈ s, p i ∈ space (d i)) : (∏ i ∈ s, p i) ∈ space (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using (one_mem 0 (L:=L) (R:=R))
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem aeval_mem {V : Type} (x : V → Placements L R → ZMod 2)
    (hx : ∀ v, x v ∈ space 1) (p : MvPolynomial V (ZMod 2)) :
    aeval x p ∈ space p.totalDegree := by
  classical
  have he : aeval x p = ∑ s ∈ p.support, aeval x (MvPolynomial.monomial s (coeff s p)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he]
  apply (space p.totalDegree).sum_mem
  intro s hs
  rw [aeval_monomial]
  have hprod : (s.prod fun v k => x v^k) ∈ space (s.sum fun _ k => k) := by
    unfold Finsupp.prod Finsupp.sum
    apply prod_mem
    intro v hv
    simpa only [Nat.one_mul] using pow_mem (hx v) (s v)
  have hscaled := (space (L:=L) (R:=R) (s.sum fun _ k => k)).smul_mem (coeff s p) hprod
  apply space_mono (le_totalDegree hs)
  simpa only [Algebra.smul_def] using hscaled

end P2MProofComplexity.P2MMatchingSubstitutionDegree
end

section
-- Inlined Solutions.P2MMatchingRowEquations

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MMatchingRowEquations

open P2MMatchingPolynomialFunctions

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

noncomputable def coordinate (e : L×R) : Placements L R → ZMod 2 := monomial {e}
noncomputable def equation (u : L) : Placements L R → ZMod 2 := 1-∑ v : R, coordinate (u, v)

theorem coordinate_value (e : L×R) (B : Placements L R) : coordinate e B = if e ∈ B.val then 1 else 0 := by
  simp only [coordinate, monomial_value, Finset.singleton_subset_iff]

theorem coordinate_mem (e : L×R) : coordinate e ∈ space (L:=L) (R:=R) 1 :=
  monomial_mem {e} (matching_singleton e) 1 (by simp)

theorem equation_mem (u : L) : equation (R:=R) u ∈ space (L:=L) (R:=R) 1 := by
  apply (space 1).sub_mem (one_mem 1)
  exact (space 1).sum_mem (fun v _ => coordinate_mem (u, v))

theorem row_sum_occupied (u : L) (B : Placements L R) (v : R) (hv : (u, v) ∈ B.val) :
    (∑ w : R, coordinate (u, w) B) = 1 := by
  classical
  rw [Finset.sum_eq_single v]
  · simp only [coordinate_value, if_pos hv]
  · intro w hw hwv
    have hnot : (u, w) ∉ B.val := by
      intro hh
      exact hwv (congrArg Prod.snd (B.property (u, w) hh (u, v) hv (Or.inl rfl)))
    simp only [coordinate_value, if_neg hnot]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem equation_value (u : L) (B : Placements L R) :
    equation u B = if ∃ v, (u, v) ∈ B.val then 0 else 1 := by
  classical
  change (1 : ZMod 2)-(∑ v : R, coordinate (u, v)) B = _
  simp only [Finset.sum_apply]
  by_cases h : ∃ v, (u, v) ∈ B.val
  · obtain ⟨v, hv⟩ := h
    rw [if_pos ⟨v, hv⟩, row_sum_occupied u B v hv, sub_self]
  · rw [if_neg h]
    have hz : (∑ v : R, coordinate (u, v) B) = 0 := Finset.sum_eq_zero (fun v _ => by
      have hv : (u, v) ∉ B.val := fun hv => h ⟨v, hv⟩
      simp only [coordinate_value, if_neg hv])
    rw [hz, sub_zero]

theorem equation_idempotent (u : L) : equation (R:=R) u*equation u = equation u := by
  funext B
  simp only [Pi.mul_apply, equation_value]
  split_ifs <;> simp

theorem monomial_mul_equation_zero (A : Finset (L×R)) (u : L)
    (hrow : ∃ e ∈ A, e.1 = u) : monomial A*equation u = 0 := by
  funext B
  simp only [Pi.mul_apply, Pi.zero_apply, monomial_value, equation_value]
  by_cases hAB : A ⊆ B.val
  · obtain ⟨e, he, heu⟩ := hrow
    have hoccupied : ∃ v, (u, v) ∈ B.val := by
      refine ⟨e.2, ?_⟩
      have he' := hAB he
      simpa only [← heu, Prod.mk.eta] using he'
    rw [if_pos hAB, if_pos hoccupied, mul_zero]
  · rw [if_neg hAB, zero_mul]

end P2MProofComplexity.P2MMatchingRowEquations
end

section
-- Inlined Solutions.P2MPigeonDanceStep

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MPigeonDanceStep

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

abbrev State (L : Type) (n : ℕ) := L → Option (Fin (n+1))

/-- The distinguished value zero represents a row equation. Positive holes are unique. -/
def Valid (a : State L n) : Prop :=
  ∀ u v j, j ≠ 0 → a u = some j → a v = some j → u = v

noncomputable def available (a : State L n) (old : Fin (n+1)) : Finset (Fin (n+1)) :=
  open Classical in Finset.univ.filter (fun j => old < j ∧ ∀ u, a u ≠ some j)

noncomputable def advance (a : State L n) (i : L) (j : Fin (n+1)) : State L n :=
  Function.update a i (some j)

noncomputable def greedy (a : State L n) (i : L) : Option (State L n) :=
  match a i with
  | none => some a
  | some old => if h : (available a old).Nonempty then some (advance a i ((available a old).min' h)) else none

theorem mem_available (a : State L n) (old j : Fin (n+1)) :
    j ∈ available a old ↔ old < j ∧ ∀ u, a u ≠ some j := by
  classical
  simp [available]

theorem advance_valid (a : State L n) (ha : Valid a) (i : L) (old j : Fin (n+1))
    (hj : j ∈ available a old) : Valid (advance a i j) := by
  intro u v k hk hu hv
  obtain ⟨hgreater, hfree⟩ := (mem_available a old j).mp hj
  by_cases hui : u = i
  · subst u
    by_cases hvi : v = i
    · exact hvi.symm
    · have hjk : j = k := Option.some.inj (by simpa only [advance, Function.update_self] using hu)
      have hv' : a v = some j := by
        simpa only [advance, Function.update_of_ne hvi, ← hjk] using hv
      exact (hfree v hv').elim
  · by_cases hvi : v = i
    · subst v
      have hjk : j = k := Option.some.inj (by simpa only [advance, Function.update_self] using hv)
      have hu' : a u = some j := by
        simpa only [advance, Function.update_of_ne hui, ← hjk] using hu
      exact (hfree u hu').elim
    · exact ha u v k hk (by simpa only [advance, Function.update_of_ne hui] using hu)
        (by simpa only [advance, Function.update_of_ne hvi] using hv)

theorem old_available (a b : State L n) (hb : Valid b) (i : L) (old new : Fin (n+1))
    (hai : a i = some old) (hbi : b i = some new) (hlt : old < new)
    (hothers : ∀ u, u ≠ i → a u = b u) : new ∈ available a old := by
  apply (mem_available a old new).mpr
  refine ⟨hlt, ?_⟩
  intro u hu
  by_cases hui : u = i
  · subst u
    have he := Option.some.inj (hai.symm.trans hu)
    exact (ne_of_lt hlt) he
  · have hnew : new ≠ 0 := by
      intro hz
      rw [hz] at hlt
      exact (not_lt_of_ge (Fin.zero_le old)) hlt
    have hu' : b u = some new := (hothers u hui).symm.trans hu
    exact hui (hb u i new hnew hu' hbi)

theorem advance_injective (a b : State L n) (ha : Valid a) (hb : Valid b) (i : L)
    (old new : Fin (n+1)) (hai : a i = some old) (hbi : b i = some new)
    (hA : (available a old).Nonempty) (hB : (available b new).Nonempty)
    (he : advance a i ((available a old).min' hA) = advance b i ((available b new).min' hB)) : a = b := by
  have hothers : ∀ u, u ≠ i → a u = b u := by
    intro u hu
    simpa only [advance, Function.update_of_ne hu] using congrFun he u
  have hmin : (available a old).min' hA = (available b new).min' hB :=
    Option.some.inj (by simpa only [advance, Function.update_self] using congrFun he i)
  have hold : old = new := by
    rcases lt_trichotomy old new with hlt | heq | hgt
    · have hav := old_available a b hb i old new hai hbi hlt hothers
      have hle := Finset.min'_le (available a old) new hav
      have hgreater := ((mem_available b new _).mp (Finset.min'_mem _ hB)).1
      rw [hmin] at hle
      exact (not_lt_of_ge hle hgreater).elim
    · exact heq
    · have hav := old_available b a ha i new old hbi hai hgt (fun u hu => (hothers u hu).symm)
      have hle := Finset.min'_le (available b new) old hav
      have hgreater := ((mem_available a old _).mp (Finset.min'_mem _ hA)).1
      rw [← hmin] at hle
      exact (not_lt_of_ge hle hgreater).elim
  funext u
  by_cases hui : u = i
  · subst u
    rw [hai, hbi, hold]
  · exact hothers u hui

theorem greedy_valid (a : State L n) (ha : Valid a) (i : L) (b : State L n)
    (he : greedy a i = some b) : Valid b := by
  classical
  cases hai : a i with
  | none =>
    have hab : a = b := Option.some.inj (by simpa only [greedy, hai] using he)
    rwa [← hab]
  | some old =>
    by_cases hA : (available a old).Nonempty
    · have hab : advance a i ((available a old).min' hA) = b :=
        Option.some.inj (by simpa only [greedy, hai, dif_pos hA] using he)
      rw [← hab]
      exact advance_valid a ha i old _ (Finset.min'_mem _ hA)
    · simp only [greedy, hai, dif_neg hA] at he
      cases he

theorem greedy_injective (a b : State L n) (ha : Valid a) (hb : Valid b) (i : L) (c : State L n)
    (heA : greedy a i = some c) (heB : greedy b i = some c) : a = b := by
  classical
  cases hai : a i with
  | none =>
    have hac : a = c := Option.some.inj (by simpa only [greedy, hai] using heA)
    cases hbi : b i with
    | none =>
      have hbc : b = c := Option.some.inj (by simpa only [greedy, hbi] using heB)
      exact hac.trans hbc.symm
    | some old =>
      by_cases hB : (available b old).Nonempty
      · have hbc : advance b i ((available b old).min' hB) = c :=
          Option.some.inj (by simpa only [greedy, hbi, dif_pos hB] using heB)
        have hi := congrFun hbc i
        rw [← hac, hai] at hi
        simp only [advance, Function.update_self] at hi
        cases hi
      · simp only [greedy, hbi, dif_neg hB] at heB
        cases heB
  | some old =>
    by_cases hA : (available a old).Nonempty
    · have hac : advance a i ((available a old).min' hA) = c :=
        Option.some.inj (by simpa only [greedy, hai, dif_pos hA] using heA)
      cases hbi : b i with
      | none =>
        have hbc : b = c := Option.some.inj (by simpa only [greedy, hbi] using heB)
        have hi := congrFun hac i
        rw [← hbc, hbi] at hi
        simp only [advance, Function.update_self] at hi
        cases hi
      | some new =>
        by_cases hB : (available b new).Nonempty
        · have hbc : advance b i ((available b new).min' hB) = c :=
            Option.some.inj (by simpa only [greedy, hbi, dif_pos hB] using heB)
          exact advance_injective a b ha hb i old new hai hbi hA hB (hac.trans hbc.symm)
        · simp only [greedy, hbi, dif_neg hB] at heB
          cases heB
    · simp only [greedy, hai, dif_neg hA] at heA
      cases heA

noncomputable def run : List L → State L n → Option (State L n)
  | [], a => some a
  | i::is, a => (greedy a i).bind (run is)

theorem run_valid (is : List L) (a b : State L n) (ha : Valid a) (he : run is a = some b) : Valid b := by
  induction is generalizing a b with
  | nil =>
    have hab := Option.some.inj he
    rwa [← hab]
  | cons i is ih =>
    cases hstep : greedy a i with
    | none => simp only [run, hstep, Option.bind_none] at he; cases he
    | some c =>
      apply ih c b (greedy_valid a ha i c hstep)
      simpa only [run, hstep, Option.bind_some] using he

theorem run_injective (is : List L) (a b c : State L n) (ha : Valid a) (hb : Valid b)
    (heA : run is a = some c) (heB : run is b = some c) : a = b := by
  induction is generalizing a b c with
  | nil => exact (Option.some.inj heA).trans (Option.some.inj heB).symm
  | cons i is ih =>
    cases hA : greedy a i with
    | none => simp only [run, hA, Option.bind_none] at heA; cases heA
    | some a' =>
      cases hB : greedy b i with
      | none => simp only [run, hB, Option.bind_none] at heB; cases heB
      | some b' =>
        have heA' : run is a' = some c := by simpa only [run, hA, Option.bind_some] using heA
        have heB' : run is b' = some c := by simpa only [run, hB, Option.bind_some] using heB
        have hab := ih a' b' c (greedy_valid a ha i a' hA) (greedy_valid b hb i b' hB) heA' heB'
        exact greedy_injective a b ha hb i a' hA (by rwa [hab])

end P2MProofComplexity.P2MPigeonDanceStep
end

section
-- Inlined Solutions.P2MPigeonDanceDomain

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MPigeonDanceDomain

open P2MPigeonDanceStep

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

noncomputable def domain (a : State L n) : Finset L :=
  open Classical in Finset.univ.filter (fun u => ∃ j, a u = some j)

theorem mem_domain (a : State L n) (u : L) : u ∈ domain a ↔ ∃ j, a u = some j := by
  classical
  simp [domain]

theorem advance_domain (a : State L n) (i : L) (old j : Fin (n+1)) (hai : a i = some old) :
    domain (advance a i j) = domain a := by
  classical
  ext u
  rw [mem_domain, mem_domain]
  by_cases hui : u = i
  · subst u
    simp only [advance, Function.update_self, hai, Option.some.injEq, exists_eq']
  · simp only [advance, Function.update_of_ne hui]

theorem greedy_domain (a : State L n) (i : L) (b : State L n) (he : greedy a i = some b) :
    domain b = domain a := by
  classical
  cases hai : a i with
  | none =>
    have hab : a = b := Option.some.inj (by simpa only [greedy, hai] using he)
    rw [← hab]
  | some old =>
    by_cases hA : (available a old).Nonempty
    · have hab : advance a i ((available a old).min' hA) = b :=
        Option.some.inj (by simpa only [greedy, hai, dif_pos hA] using he)
      rw [← hab]
      exact advance_domain a i old _ hai
    · simp only [greedy, hai, dif_neg hA] at he
      cases he

theorem greedy_other (a : State L n) (i : L) (b : State L n) (he : greedy a i = some b)
    (u : L) (hui : u ≠ i) : b u = a u := by
  classical
  cases hai : a i with
  | none =>
    have hab : a = b := Option.some.inj (by simpa only [greedy, hai] using he)
    rw [← hab]
  | some old =>
    by_cases hA : (available a old).Nonempty
    · have hab : advance a i ((available a old).min' hA) = b :=
        Option.some.inj (by simpa only [greedy, hai, dif_pos hA] using he)
      rw [← hab]
      exact Function.update_of_ne hui _ _
    · simp only [greedy, hai, dif_neg hA] at he
      cases he

theorem greedy_no_zero (a : State L n) (i : L) (b : State L n) (he : greedy a i = some b) : b i ≠ some 0 := by
  classical
  cases hai : a i with
  | none =>
    have hab : a = b := Option.some.inj (by simpa only [greedy, hai] using he)
    rw [← hab, hai]
    intro h
    cases h
  | some old =>
    by_cases hA : (available a old).Nonempty
    · have hab : advance a i ((available a old).min' hA) = b :=
        Option.some.inj (by simpa only [greedy, hai, dif_pos hA] using he)
      have hgreater := ((mem_available a old _).mp (Finset.min'_mem _ hA)).1
      intro hz
      rw [← hab] at hz
      have hj0 : (available a old).min' hA = 0 :=
        Option.some.inj (by simpa only [advance, Function.update_self] using hz)
      rw [hj0] at hgreater
      exact (not_lt_of_ge (Fin.zero_le old)) hgreater
    · simp only [greedy, hai, dif_neg hA] at he
      cases he

theorem run_domain (is : List L) (a b : State L n) (he : run is a = some b) : domain b = domain a := by
  induction is generalizing a b with
  | nil => rw [← Option.some.inj he]
  | cons i is ih =>
    cases hstep : greedy a i with
    | none => simp only [run, hstep, Option.bind_none] at he; cases he
    | some c =>
      have hr : run is c = some b := by simpa only [run, hstep, Option.bind_some] using he
      exact (ih c b hr).trans (greedy_domain a i c hstep)

theorem run_other (is : List L) (a b : State L n) (he : run is a = some b)
    (u : L) (hu : u ∉ is) : b u = a u := by
  induction is generalizing a b with
  | nil => rw [← Option.some.inj he]
  | cons i is ih =>
    have hui : u ≠ i := fun h => hu (List.mem_cons.mpr (Or.inl h))
    have hu' : u ∉ is := fun h => hu (List.mem_cons.mpr (Or.inr h))
    cases hstep : greedy a i with
    | none => simp only [run, hstep, Option.bind_none] at he; cases he
    | some c =>
      have hr : run is c = some b := by simpa only [run, hstep, Option.bind_some] using he
      exact (ih c b hr hu').trans (greedy_other a i c hstep u hui)

theorem run_no_zero (is : List L) (a b : State L n) (he : run is a = some b)
    (u : L) (hu : u ∈ is) : b u ≠ some 0 := by
  induction is generalizing a b with
  | nil => simp only [List.not_mem_nil] at hu
  | cons i is ih =>
    cases hstep : greedy a i with
    | none => simp only [run, hstep, Option.bind_none] at he; cases he
    | some c =>
      have hr : run is c = some b := by simpa only [run, hstep, Option.bind_some] using he
      rcases List.mem_cons.mp hu with rfl | hu
      · by_cases hi : u ∈ is
        · exact ih c b hr hi
        · rw [run_other is c b hr u hi]
          exact greedy_no_zero a u c hstep
      · exact ih c b hr hu

end P2MProofComplexity.P2MPigeonDanceDomain
end

section
-- Inlined Solutions.P2MPigeonDancePolynomials

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MPigeonDancePolynomials

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MMatchingPolynomialFunctions P2MMatchingRowEquations

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

abbrev Positive (n : ℕ) := {j : Fin (n+1) // j ≠ 0}

noncomputable def edges (a : State L n) : Finset (L×Positive n) :=
  open Classical in Finset.univ.filter (fun e => a e.1 = some e.2.val)

noncomputable def zeros (a : State L n) : Finset L :=
  open Classical in Finset.univ.filter (fun u => a u = some 0)

theorem mem_edges (a : State L n) (e : L×Positive n) : e ∈ edges a ↔ a e.1 = some e.2.val := by
  classical
  simp [edges]

theorem mem_zeros (a : State L n) (u : L) : u ∈ zeros a ↔ a u = some 0 := by
  classical
  simp [zeros]

theorem matching_edges (a : State L n) (ha : Valid a) : IsMatching (edges a) := by
  intro e he f hf hshare
  have he' := (mem_edges a e).mp he
  have hf' := (mem_edges a f).mp hf
  rcases hshare with hrow | hhole
  · have hv : e.2.val = f.2.val := Option.some.inj (he'.symm.trans (hrow ▸ hf'))
    exact Prod.ext hrow (Subtype.ext hv)
  · have hu : e.1 = f.1 := ha e.1 f.1 e.2.val e.2.property he' (by simpa only [hhole] using hf')
    exact Prod.ext hu hhole

theorem rows_edges (a : State L n) (u : L) :
    u ∈ (edges a).image Prod.fst ↔ ∃ j, a u = some j ∧ j ≠ 0 := by
  constructor
  · intro h
    obtain ⟨e, he, heu⟩ := Finset.mem_image.mp h
    exact ⟨e.2.val, by simpa only [heu] using (mem_edges a e).mp he, e.2.property⟩
  · rintro ⟨j, haj, hj⟩
    exact Finset.mem_image.mpr ⟨(u, ⟨j, hj⟩), (mem_edges a _).mpr haj, rfl⟩

theorem domain_card (a : State L n) : (edges a).card+(zeros a).card = (domain a).card := by
  classical
  have hrowinj : Set.InjOn Prod.fst (edges a : Set (L×Positive n)) := by
    intro e he f hf hrow
    have hv : e.2.val = f.2.val := Option.some.inj
      (((mem_edges a e).mp he).symm.trans (hrow ▸ (mem_edges a f).mp hf))
    exact Prod.ext hrow (Subtype.ext hv)
  have hdis : Disjoint ((edges a).image Prod.fst) (zeros a) := by
    apply Finset.disjoint_left.mpr
    intro u hu hz
    obtain ⟨j, hj, hj0⟩ := (rows_edges a u).mp hu
    exact hj0 (Option.some.inj (hj.symm.trans ((mem_zeros a u).mp hz)))
  have hdom : domain a = (edges a).image Prod.fst ∪ zeros a := by
    ext u
    rw [mem_domain, Finset.mem_union, rows_edges, mem_zeros]
    constructor
    · rintro ⟨j, hj⟩
      by_cases hj0 : j = 0
      · exact Or.inr (by rwa [hj0] at hj)
      · exact Or.inl ⟨j, hj, hj0⟩
    · rintro (⟨j, hj, _⟩ | hj)
      · exact ⟨j, hj⟩
      · exact ⟨0, hj⟩
  rw [hdom, Finset.card_union_of_disjoint hdis, Finset.card_image_iff.mpr hrowinj]

noncomputable def polynomial (a : State L n) : Placements L (Positive n) → ZMod 2 :=
  monomial (edges a)*∏ u ∈ zeros a, equation u

theorem product_equations_mem (A : Finset L) :
    (∏ u ∈ A, equation (R:=Positive n) u) ∈ space (L:=L) (R:=Positive n) A.card := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.card_empty] using (one_mem 0 (L:=L) (R:=Positive n))
  | @insert u A hu ih =>
    rw [Finset.prod_insert hu, Finset.card_insert_of_notMem hu]
    simpa only [Nat.add_comm] using mul_mem (equation_mem (R:=Positive n) u) ih

theorem polynomial_mem (a : State L n) (ha : Valid a) : polynomial a ∈ space (L:=L) (R:=Positive n) (domain a).card := by
  have hh := mul_mem (monomial_mem (edges a) (matching_edges a ha) (edges a).card le_rfl)
    (product_equations_mem (n:=n) (zeros a))
  rw [domain_card] at hh
  exact hh

theorem zeros_eq_empty (a : State L n) (ha : ∀ u, a u ≠ some 0) : zeros a = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact ha u ((mem_zeros a u).mp hu)

theorem edges_injective_no_zero (a b : State L n) (ha : ∀ u, a u ≠ some 0) (hb : ∀ u, b u ≠ some 0)
    (he : edges a = edges b) : a = b := by
  funext u
  cases hai : a u with
  | none =>
    cases hbi : b u with
    | none => rfl
    | some j =>
      have hj : j ≠ 0 := fun hh => hb u (by rwa [hh] at hbi)
      have hedge : (u, (⟨j, hj⟩ : Positive n)) ∈ edges b := (mem_edges b _).mpr hbi
      rw [← he] at hedge
      have hh := (mem_edges a _).mp hedge
      rw [hai] at hh
      cases hh
  | some j =>
    have hj : j ≠ 0 := fun hh => ha u (by rwa [hh] at hai)
    have hedge : (u, (⟨j, hj⟩ : Positive n)) ∈ edges a := (mem_edges a _).mpr hai
    rw [he] at hedge
    exact ((mem_edges b _).mp hedge).symm

end P2MProofComplexity.P2MPigeonDancePolynomials
end

section
-- Inlined Solutions.P2MBitPHPMatchingDecoding

set_option maxHeartbeats 3500000

namespace P2MProofComplexity.P2MBitPHPMatchingDecoding

open MvPolynomial P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDancePolynomials
open SemAC02.Supplement

variable {m n ℓ : ℕ}

noncomputable def bit (addr : Positive n ≃ (Fin ℓ → Bool)) (e : Fin m × Fin ℓ) :
    Placements (Fin m) (Positive n) → ZMod 2 :=
  ∑ j : Positive n, if addr j e.2 then coordinate (e.1, j) else 0

theorem bit_mem (addr : Positive n ≃ (Fin ℓ → Bool)) (e : Fin m × Fin ℓ) :
    bit addr e ∈ space 1 := by
  apply (space 1).sum_mem
  intro j hj
  split_ifs
  · exact coordinate_mem _
  · exact (space 1).zero_mem

noncomputable def decoded (addr : Positive n ≃ (Fin ℓ → Bool))
    (B : Placements (Fin m) (Positive n)) : Fin m × Fin ℓ → Bool :=
  fun e => decide (bit addr e B = 1)

theorem decoded_point (addr : Positive n ≃ (Fin ℓ → Bool)) (B : Placements (Fin m) (Positive n)) :
    (boolPt (decoded addr B) : Fin m × Fin ℓ → ZMod 2) = fun e => bit addr e B := by
  funext e
  rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (bit addr e B) with h | h <;>
    simp [boolPt, decoded, h]

theorem polynomial_value (addr : Positive n ≃ (Fin ℓ → Bool))
    (p : MvPolynomial (Fin m × Fin ℓ) (ZMod 2)) :
    (fun B => polyFn p (decoded addr B)) = aeval (bit addr) p := by
  funext B
  have he := MvPolynomial.comp_aeval_apply (bit addr) (Pi.evalAlgHom (ZMod 2) (fun _ => ZMod 2) B) p
  change aeval (bit addr) p B = aeval (fun e => bit addr e B) p at he
  rw [he]
  change eval (boolPt (decoded addr B)) p = eval (fun e => bit addr e B) p
  rw [decoded_point]

theorem polynomial_mem (addr : Positive n ≃ (Fin ℓ → Bool))
    (p : MvPolynomial (Fin m × Fin ℓ) (ZMod 2)) :
    (fun B => polyFn p (decoded addr B)) ∈ space p.totalDegree := by
  rw [polynomial_value]
  exact P2MMatchingSubstitutionDegree.aeval_mem (bit addr) (bit_mem addr) p

theorem circuit_mem (addr : Positive n ≃ (Fin ℓ → Bool))
    (c : ACirc (ZMod 2) (Fin m × Fin ℓ)) :
    (fun B => cval c (decoded addr B)) ∈ space (fnDeg (cval c)) := by
  have hnonempty : {d : ℕ | ∃ p : MvPolynomial (Fin m × Fin ℓ) (ZMod 2),
      p.totalDegree ≤ d ∧ polyFn p = cval c}.Nonempty :=
    ⟨c.toPoly.totalDegree, c.toPoly, le_rfl, rfl⟩
  obtain ⟨p, hp, he⟩ := Nat.sInf_mem hnonempty
  have hmem := space_mono hp (polynomial_mem addr p)
  change (fun B => polyFn p (decoded addr B)) ∈ space (fnDeg (cval c)) at hmem
  simpa only [he] using hmem

theorem bit_occupied (addr : Positive n ≃ (Fin ℓ → Bool))
    (B : Placements (Fin m) (Positive n)) (u : Fin m) (j : Positive n) (hj : (u,j) ∈ B.val)
    (t : Fin ℓ) : bit addr (u,t) B = if addr j t then 1 else 0 := by
  classical
  simp only [bit, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · split_ifs <;> simp [coordinate_value, hj]
  · intro k hk hkj
    have hnot : (u,k) ∉ B.val := by
      intro hh
      exact hkj (congrArg Prod.snd (B.property (u,k) hh (u,j) hj (Or.inl rfl)))
    split_ifs <;> simp [coordinate_value, hnot]
  · simp

theorem decoded_occupied (addr : Positive n ≃ (Fin ℓ → Bool))
    (B : Placements (Fin m) (Positive n)) (u : Fin m) (j : Positive n) (hj : (u,j) ∈ B.val)
    (t : Fin ℓ) : decoded addr B (u,t) = addr j t := by
  simp only [decoded, bit_occupied addr B u j hj t]
  cases addr j t <;> simp

theorem decoded_absent (addr : Positive n ≃ (Fin ℓ → Bool))
    (B : Placements (Fin m) (Positive n)) (u : Fin m) (hu : ¬ ∃ j, (u,j) ∈ B.val)
    (t : Fin ℓ) : decoded addr B (u,t) = false := by
  have hbit : bit addr (u,t) B = 0 := by
    simp only [bit, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : (u,j) ∉ B.val := fun h => hu ⟨j,h⟩
    split_ifs <;> simp [coordinate_value, hnot]
  simp [decoded, hbit]

end P2MProofComplexity.P2MBitPHPMatchingDecoding
end

section
-- Inlined Solutions.P2MPigeonDanceRelation

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MPigeonDanceRelation

open P2MPigeonDanceStep P2MPigeonDanceDomain

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

def Step (a : State L n) (i : L) (b : State L n) : Prop :=
  (a i = none ∧ b = a) ∨
    ∃ old new, a i = some old ∧ new ∈ available a old ∧ b = advance a i new

inductive Dance : List L → State L n → State L n → Prop
  | nil (a) : Dance [] a a
  | cons {i is a b c} : Step a i b → Dance is b c → Dance (i::is) a c

theorem step_valid {a b : State L n} {i : L} (ha : Valid a) (h : Step a i b) : Valid b := by
  rcases h with ⟨_, rfl⟩ | ⟨old, new, _, hnew, rfl⟩
  · exact ha
  · exact advance_valid a ha i old new hnew

theorem step_other {a b : State L n} {i u : L} (h : Step a i b) (hui : u ≠ i) : b u = a u := by
  rcases h with ⟨_, rfl⟩ | ⟨old, new, _, _, rfl⟩
  · rfl
  · exact Function.update_of_ne hui _ _

theorem step_domain {a b : State L n} {i : L} (h : Step a i b) : domain b = domain a := by
  rcases h with ⟨_, rfl⟩ | ⟨old, new, hai, _, rfl⟩
  · rfl
  · exact advance_domain a i old new hai

theorem dance_valid {is : List L} {a b : State L n} (ha : Valid a) (h : Dance is a b) : Valid b := by
  induction h with
  | nil => exact ha
  | cons hstep hrest ih => exact ih (step_valid ha hstep)

theorem dance_other {is : List L} {a b : State L n} (h : Dance is a b) (u : L) (hu : u ∉ is) : b u = a u := by
  induction h with
  | nil => rfl
  | @cons i is a b c hstep hrest ih =>
    have hui : u ≠ i := fun hh => hu (List.mem_cons.mpr (Or.inl hh))
    have hu' : u ∉ is := fun hh => hu (List.mem_cons.mpr (Or.inr hh))
    exact (ih hu').trans (step_other hstep hui)

noncomputable def relabel (σ : Equiv.Perm (Fin (n+1))) (a : State L n) : State L n :=
  fun u => (a u).map σ

theorem relabel_inverse (σ : Equiv.Perm (Fin (n+1))) (a : State L n) : relabel σ.symm (relabel σ a) = a := by
  funext u
  cases h : a u <;> simp [relabel, h]

theorem relabel_some (σ : Equiv.Perm (Fin (n+1))) (a : State L n) (u : L) (j : Fin (n+1)) :
    relabel σ a u = some (σ j) ↔ a u = some j := by
  cases h : a u <;> simp [relabel, h]

theorem relabel_advance (σ : Equiv.Perm (Fin (n+1))) (a : State L n) (i : L) (j : Fin (n+1)) :
    relabel σ (advance a i j) = advance (relabel σ a) i (σ j) := by
  funext u
  by_cases hui : u = i <;> simp [relabel, advance, Function.update_apply, hui]

theorem relabel_valid (σ : Equiv.Perm (Fin (n+1))) (hσ : σ 0 = 0) (a : State L n) (ha : Valid a) :
    Valid (relabel σ a) := by
  intro u v j hj hu hv
  have hj' : σ.symm j ≠ 0 := by
    intro hh
    apply hj
    have he := congrArg σ hh
    simpa only [Equiv.apply_symm_apply, hσ] using he
  apply ha u v (σ.symm j) hj'
  · apply (relabel_some σ a u (σ.symm j)).mp
    simpa only [Equiv.apply_symm_apply] using hu
  · apply (relabel_some σ a v (σ.symm j)).mp
    simpa only [Equiv.apply_symm_apply] using hv

theorem step_relabel (σ : Equiv.Perm (Fin (n+1))) (a b : State L n) (i : L) (h : Step a i b)
    (horder : ∀ old new, a i = some old → new ∈ available a old → σ old < σ new) :
    Step (relabel σ a) i (relabel σ b) := by
  rcases h with ⟨hai, rfl⟩ | ⟨old, new, hai, hnew, rfl⟩
  · left
    exact ⟨by simp [relabel, hai], rfl⟩
  · right
    refine ⟨σ old, σ new, by simp [relabel, hai], ?_, relabel_advance σ a i new⟩
    apply (mem_available _ _ _).mpr
    refine ⟨horder old new hai hnew, ?_⟩
    intro u hu
    exact ((mem_available a old new).mp hnew).2 u ((relabel_some σ a u new).mp hu)

end P2MProofComplexity.P2MPigeonDanceRelation
end

section
-- Inlined Solutions.P2MPigeonDanceGreedyCompleteness

set_option maxHeartbeats 3500000

namespace P2MProofComplexity.P2MPigeonDanceGreedyCompleteness

open P2MPigeonDanceStep P2MPigeonDanceRelation

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

/-- A smaller first move can replace a larger move: swap the two holes in all
future states. No unprocessed pigeon initially occupies either hole. -/
theorem swap_future (is : List L) (hnd : is.Nodup) (a b : State L n)
    (anchor : L) (hanchor : anchor ∉ is) (j k : Fin (n+1)) (hjk : j ≤ k)
    (hak : a anchor = some k)
    (hfree : ∀ u ∈ is, a u ≠ some j ∧ a u ≠ some k)
    (hDance : Dance is a b) : Dance is (relabel (Equiv.swap j k) a) (relabel (Equiv.swap j k) b) := by
  induction is generalizing a b with
  | nil => cases hDance; exact Dance.nil _
  | cons i is ih =>
    obtain ⟨hinot, hnd'⟩ := List.nodup_cons.mp hnd
    cases hDance with
    | @cons _ _ _ c _ hstep hrest =>
      have hanchor_i : anchor ≠ i := fun hh => hanchor (List.mem_cons.mpr (Or.inl hh))
      have hanchor' : anchor ∉ is := fun hh => hanchor (List.mem_cons.mpr (Or.inr hh))
      have hiFree := hfree i List.mem_cons_self
      have horder : ∀ old new, a i = some old → new ∈ available a old →
          (Equiv.swap j k) old < (Equiv.swap j k) new := by
        intro old new hai hnew
        have holdj : old ≠ j := fun hh => hiFree.1 (by rwa [← hh])
        have holdk : old ≠ k := fun hh => hiFree.2 (by rwa [← hh])
        have hnewk : new ≠ k := by
          intro hh
          have hfreeNew := ((mem_available a old new).mp hnew).2
          exact hfreeNew anchor (by rwa [hh])
        have hOld : (Equiv.swap j k) old = old := by simp [Equiv.swap_apply_def, holdj, holdk]
        rw [hOld]
        by_cases hnewj : new = j
        · rw [hnewj, Equiv.swap_apply_left]
          have holdj' : old < j := by simpa only [hnewj] using ((mem_available a old new).mp hnew).1
          exact holdj'.trans_le hjk
        · simpa only [Equiv.swap_apply_def, if_neg hnewj, if_neg hnewk] using
            ((mem_available a old new).mp hnew).1
      apply Dance.cons (step_relabel (Equiv.swap j k) a c i hstep horder)
      apply ih hnd' c b hanchor' ?_ ?_ hrest
      · exact (step_other hstep hanchor_i).trans hak
      · intro u hu
        have hui : u ≠ i := by intro hh; exact hinot (hh ▸ hu)
        rw [step_other hstep hui]
        exact hfree u (List.mem_cons.mpr (Or.inr hu))

theorem relabel_free (a : State L n) (j k : Fin (n+1))
    (hj : ∀ u, a u ≠ some j) (hk : ∀ u, a u ≠ some k) : relabel (Equiv.swap j k) a = a := by
  funext u
  cases hai : a u with
  | none => simp [relabel, hai]
  | some old =>
    have holdj : old ≠ j := fun hh => hj u (by rwa [← hh])
    have holdk : old ≠ k := fun hh => hk u (by rwa [← hh])
    simp [relabel, hai, Equiv.swap_apply_def, holdj, holdk]

/-- If any legal sequence moves every pigeon in the list, the greedy sequence
also succeeds (the minimal pigeon-dance lemma). -/
theorem complete (is : List L) (hnd : is.Nodup) (a b : State L n) (hDance : Dance is a b) :
    ∃ c, run is a = some c := by
  classical
  induction is generalizing a b with
  | nil => exact ⟨a, rfl⟩
  | cons i is ih =>
    obtain ⟨hinot, hnd'⟩ := List.nodup_cons.mp hnd
    cases hDance with
    | @cons _ _ _ c _ hstep hrest =>
      rcases hstep with ⟨hai, rfl⟩ | ⟨old, k, hai, hk, rfl⟩
      · obtain ⟨b', hb'⟩ := ih hnd' c b hrest
        exact ⟨b', by simpa only [run, greedy, hai, Option.bind_some] using hb'⟩
      · have hA : (available a old).Nonempty := ⟨k, hk⟩
        let j := (available a old).min' hA
        have hj : j ∈ available a old := Finset.min'_mem _ hA
        have hjk : j ≤ k := Finset.min'_le _ k hk
        have haj : ∀ u, a u ≠ some j := ((mem_available a old j).mp hj).2
        have hak : ∀ u, a u ≠ some k := ((mem_available a old k).mp hk).2
        have hrel : relabel (Equiv.swap j k) (advance a i k) = advance a i j := by
          rw [relabel_advance, relabel_free a j k haj hak, Equiv.swap_apply_right]
        have hfree : ∀ u ∈ is, advance a i k u ≠ some j ∧ advance a i k u ≠ some k := by
          intro u hu
          have hui : u ≠ i := by intro hh; exact hinot (hh ▸ hu)
          simp only [advance, Function.update_of_ne hui]
          exact ⟨haj u, hak u⟩
        have hnewDance := swap_future is hnd' (advance a i k) b i hinot j k hjk
          (by simp only [advance, Function.update_self]) hfree hrest
        rw [hrel] at hnewDance
        obtain ⟨b', hb'⟩ := ih hnd' (advance a i j) (relabel (Equiv.swap j k) b) hnewDance
        refine ⟨b', ?_⟩
        simpa only [run, greedy, hai, dif_pos hA, Option.bind_some, j] using hb'

end P2MProofComplexity.P2MPigeonDanceGreedyCompleteness
end

section
-- Inlined Solutions.P2MMatchingFunctionBasis

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MMatchingFunctionBasis

open Module MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MMatchingPolynomialFunctions

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem independent : LinearIndependent (ZMod 2) (fun A : Placements L R => monomial A.val) := by
  let U := monomialSpan (IsMatching (L:=L) (R:=R))
  have hmem (A : Placements L R) : xMon A.val ∈ U := Submodule.subset_span ⟨A.val, A.property, rfl⟩
  let b (A : Placements L R) : U := ⟨xMon A.val, hmem A⟩
  have hb : LinearIndependent (ZMod 2) b := by
    apply LinearIndependent.of_comp U.subtype
    exact xMon_linearIndependent.comp Subtype.val Subtype.val_injective
  let E := (evaluation (L:=L) (R:=R)).comp U.subtype
  have hE : Function.Injective E := by
    intro p q he
    apply Subtype.ext
    exact evaluation_injective p.val q.val p.property q.property he
  exact hb.map' E (LinearMap.ker_eq_bot.mpr hE)

abbrev DegreeIndex (L R : Type) (d : ℕ) := {A : Placements L R // A.val.card ≤ d}

theorem span_degree (d : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun A : DegreeIndex L R d => monomial A.val.val)) =
      space (L:=L) (R:=R) d := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.val.val, A.val.property, A.property, rfl⟩
  · rintro ⟨A, hA, hd, rfl⟩
    exact ⟨⟨⟨A, hA⟩, hd⟩, rfl⟩

noncomputable def degreeBasis (d : ℕ) : Basis (DegreeIndex L R d) (ZMod 2) (space (L:=L) (R:=R) d) :=
  (Basis.span (independent.comp (fun A : DegreeIndex L R d => A.val) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_degree d))

instance finite_space (d : ℕ) : Module.Finite (ZMod 2) (space (L:=L) (R:=R) d) := by
  classical
  exact Module.Finite.of_basis (degreeBasis d)

theorem finrank_space (d : ℕ) : Module.finrank (ZMod 2) (space (L:=L) (R:=R) d) =
    Nat.card (DegreeIndex L R d) := by
  classical
  rw [Module.finrank_eq_card_basis (degreeBasis d), Nat.card_eq_fintype_card]

end P2MProofComplexity.P2MMatchingFunctionBasis
end

section
-- Inlined Solutions.P2MPigeonDanceCounting

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MPigeonDanceCounting

open P2MPigeonDanceStep P2MPigeonDanceRelation P2MPigeonDanceDomain P2MPigeonDancePolynomials P2MMatchingPolynomialFunctions

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

abbrev GoodState (is : List L) (d : ℕ) :=
  {a : State L n // Valid a ∧ (domain a).card ≤ d ∧ ∃ b, Dance is a b}

noncomputable def output (is : List L) (hnd : is.Nodup) (d : ℕ) (a : GoodState (n:=n) is d) : State L n :=
  Classical.choose (P2MPigeonDanceGreedyCompleteness.complete is hnd a.val
    (Classical.choose a.property.2.2) (Classical.choose_spec a.property.2.2))

theorem output_spec (is : List L) (hnd : is.Nodup) (d : ℕ) (a : GoodState (n:=n) is d) :
    run is a.val = some (output is hnd d a) :=
  Classical.choose_spec (P2MPigeonDanceGreedyCompleteness.complete is hnd a.val
    (Classical.choose a.property.2.2) (Classical.choose_spec a.property.2.2))

noncomputable def index (is : List L) (hnd : is.Nodup) (hcovers : ∀ u, u ∈ is) (d : ℕ)
    (a : GoodState (n:=n) is d) : P2MMatchingFunctionBasis.DegreeIndex L (Positive n) d := by
  let b := output is hnd d a
  have hrun : run is a.val = some b := output_spec is hnd d a
  have hvalid : Valid b := run_valid is a.val b a.property.1 hrun
  refine ⟨⟨edges b, matching_edges b hvalid⟩, ?_⟩
  change (edges b).card ≤ d
  have hh := domain_card b
  have hdom := run_domain is a.val b hrun
  have hbound := a.property.2.1
  rw [hdom] at hh
  omega

theorem index_injective (is : List L) (hnd : is.Nodup) (hcovers : ∀ u, u ∈ is) (d : ℕ) :
    Function.Injective (index (n:=n) is hnd hcovers d) := by
  intro a b he
  have hedges : edges (output is hnd d a) = edges (output is hnd d b) :=
    congrArg (fun A : P2MMatchingFunctionBasis.DegreeIndex L (Positive n) d => A.val.val) he
  have hout := edges_injective_no_zero (output is hnd d a) (output is hnd d b)
    (fun u => run_no_zero is a.val _ (output_spec is hnd d a) u (hcovers u))
    (fun u => run_no_zero is b.val _ (output_spec is hnd d b) u (hcovers u)) hedges
  apply Subtype.ext
  exact run_injective is a.val b.val (output is hnd d a) a.property.1 b.property.1
    (output_spec is hnd d a) (by rw [hout]; exact output_spec is hnd d b)

theorem count_le_dimension (is : List L) (hnd : is.Nodup) (hcovers : ∀ u, u ∈ is) (d : ℕ) :
    Nat.card (GoodState (n:=n) is d) ≤ Module.finrank (ZMod 2) (space (L:=L) (R:=Positive n) d) := by
  rw [P2MMatchingFunctionBasis.finrank_space]
  exact Nat.card_le_card_of_injective (index is hnd hcovers d) (index_injective is hnd hcovers d)

end P2MProofComplexity.P2MPigeonDanceCounting
end

section
-- Inlined Solutions.P2MPigeonDanceOneRowExtension

set_option maxHeartbeats 3500000

namespace P2MProofComplexity.P2MPigeonDanceOneRowExtension

open P2MPigeonDanceStep P2MPigeonDanceRelation

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

theorem step_absent {a b : State L n} {i k : L} (h : Step a k b) (hai : a i = none) : b i = none := by
  by_cases hik : i = k
  · subst k
    rcases h with ⟨_, rfl⟩ | ⟨old, new, hsome, _, _⟩
    · exact hai
    · rw [hai] at hsome
      cases hsome
  · exact (step_other h hik).trans hai

theorem dance_absent {is : List L} {a b : State L n} {i : L} (h : Dance is a b) (hai : a i = none) : b i = none := by
  induction h with
  | nil => exact hai
  | cons hstep hrest ih => exact ih (step_absent hstep hai)

theorem step_no_zero {a b : State L n} {i : L} (h : Step a i b) : b i ≠ some 0 := by
  rcases h with ⟨hai, rfl⟩ | ⟨old, new, hai, hnew, rfl⟩
  · rw [hai]
    intro hh
    cases hh
  · intro hh
    have hnew0 : new = 0 := Option.some.inj (by simpa only [advance, Function.update_self] using hh)
    have hgt := ((mem_available a old new).mp hnew).1
    rw [hnew0] at hgt
    exact (not_lt_of_ge (Fin.zero_le old)) hgt

theorem advance_commute (a : State L n) (i k : L) (j h : Fin (n+1)) (hik : i ≠ k) :
    advance (advance a i j) k h = advance (advance a k h) i j := by
  funext u
  by_cases hui : u = i <;> by_cases huk : u = k <;>
    simp_all [advance, Function.update_apply]

theorem step_add_fixed {a b : State L n} {i k : L} (j : Fin (n+1)) (hik : i ≠ k)
    (h : Step a k b) (hnew : b k ≠ some j) : Step (advance a i j) k (advance b i j) := by
  rcases h with ⟨hai, rfl⟩ | ⟨old, new, hai, hfree, rfl⟩
  · left
    exact ⟨by simpa only [advance, Function.update_of_ne hik.symm] using hai, rfl⟩
  · have hnej : new ≠ j := by
      intro hh
      apply hnew
      simp only [advance, Function.update_self, hh]
    right
    refine ⟨old, new, by simpa only [advance, Function.update_of_ne hik.symm] using hai, ?_, ?_⟩
    · apply (mem_available _ old new).mpr
      refine ⟨((mem_available a old new).mp hfree).1, ?_⟩
      intro u hu
      by_cases hui : u = i
      · subst u
        have hh : j = new := Option.some.inj (by simpa only [advance, Function.update_self] using hu)
        exact hnej hh.symm
      · exact ((mem_available a old new).mp hfree).2 u
          (by simpa only [advance, Function.update_of_ne hui] using hu)
    · exact (advance_commute a i k j new hik).symm

theorem free_next {is : List L} {a c b : State L n} {k : L} (hk : k ∉ is)
    (hstep : Step a k c) (hrest : Dance is c b) (h : Fin (n+1))
    (ha : ∀ u, a u ≠ some h) (hb : ∀ u, b u ≠ some h) : ∀ u, c u ≠ some h := by
  intro u
  by_cases huk : u = k
  · subst u
    rw [← dance_other hrest k hk]
    exact hb k
  · rw [step_other hstep huk]
    exact ha u

theorem anchor_move (a : State L n) (i : L) (h : Fin (n+1)) (hpos : h ≠ 0)
    (hfree : ∀ u, a u ≠ some h) : Step (advance a i 0) i (advance a i h) := by
  right
  refine ⟨0, h, by simp only [advance, Function.update_self], ?_, ?_⟩
  · apply (mem_available _ 0 h).mpr
    refine ⟨lt_of_le_of_ne (Fin.zero_le h) hpos.symm, ?_⟩
    intro u hu
    by_cases hui : u = i
    · subst u
      have hh : (0 : Fin (n+1)) = h := Option.some.inj (by simpa only [advance, Function.update_self] using hu)
      exact hpos hh.symm
    · exact hfree u (by simpa only [advance, Function.update_of_ne hui] using hu)
  · funext u
    by_cases hui : u = i <;> simp [advance, Function.update_apply, hui]

/-- Insert an absent row into a legal dance. It starts at zero and takes a
positive hole unused by the original initial and final states. -/
theorem extend (is : List L) (hnd : is.Nodup) (a b : State L n) (i : L) (hai : a i = none)
    (h : Fin (n+1)) (hpos : h ≠ 0) (hfreeA : ∀ u, a u ≠ some h) (hfreeB : ∀ u, b u ≠ some h)
    (hDance : Dance is a b) :
    Dance is (advance a i (if i ∈ is then 0 else h)) (advance b i h) := by
  classical
  induction is generalizing a b with
  | nil =>
    cases hDance
    simp only [List.not_mem_nil, if_false]
    exact Dance.nil _
  | cons k is ih =>
    obtain ⟨hknot, hnd'⟩ := List.nodup_cons.mp hnd
    cases hDance with
    | @cons _ _ _ c _ hstep hrest =>
      have hci := step_absent hstep hai
      have hfreeC := free_next hknot hstep hrest h hfreeA hfreeB
      by_cases hik : i = k
      · subst k
        have hca : c = a := by
          rcases hstep with ⟨_, hca⟩ | ⟨old, new, hsome, _, _⟩
          · exact hca
          · rw [hai] at hsome
            cases hsome
        subst c
        have hTail := ih hnd' a b hai hfreeA hfreeB hrest
        simp only [if_neg hknot] at hTail
        simp only [List.mem_cons_self, if_true]
        exact Dance.cons (anchor_move a i h hpos hfreeA) hTail
      · have hTail := ih hnd' c b hci hfreeC hfreeB hrest
        have hAllowed : c k ≠ some (if i ∈ is then 0 else h) := by
          split_ifs
          · exact step_no_zero hstep
          · exact hfreeC k
        have hHead := step_add_fixed (if i ∈ is then 0 else h) hik hstep hAllowed
        have hmem : (i ∈ k::is) ↔ i ∈ is := by simp only [List.mem_cons, hik, false_or]
        simp only [hmem]
        exact Dance.cons hHead hTail

end P2MProofComplexity.P2MPigeonDanceOneRowExtension
end

section
-- Inlined Solutions.P2MPigeonDanceUnusedHole

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MPigeonDanceUnusedHole

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDancePolynomials P2MPigeonDanceRelation

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

noncomputable def holes (a : State L n) : Finset (Positive n) :=
  open Classical in Finset.univ.filter (fun j => ∃ u, a u = some j.val)

theorem mem_holes (a : State L n) (j : Positive n) : j ∈ holes a ↔ ∃ u, a u = some j.val := by
  classical
  simp [holes]

theorem holes_card (a : State L n) : (holes a).card ≤ (domain a).card := by
  classical
  let u (j : holes a) : L := Classical.choose ((mem_holes a j.val).mp j.property)
  have hu (j : holes a) : a (u j) = some j.val.val := Classical.choose_spec ((mem_holes a j.val).mp j.property)
  let f : holes a → domain a := fun j => ⟨u j, (mem_domain a _).mpr ⟨j.val.val, hu j⟩⟩
  have hf : Function.Injective f := by
    intro j k he
    have heU : u j = u k := congrArg Subtype.val he
    have hh : some j.val.val = some k.val.val := (hu j).symm.trans (by rw [heU]; exact hu k)
    exact Subtype.ext (Subtype.ext (Option.some.inj hh))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem positive_card (n : ℕ) : Fintype.card (Positive n) = n := by
  let e : Positive n ≃ Fin n :=
    { toFun := fun j => j.val.pred j.property
      invFun := fun j => ⟨j.succ, Fin.succ_ne_zero j⟩
      left_inv := by intro j; exact Subtype.ext (Fin.succ_pred j.val j.property)
      right_inv := by intro j; exact Fin.pred_succ j }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem unused (a b : State L n) (hsmall : (domain a).card+(domain b).card < n) :
    ∃ h : Fin (n+1), h ≠ 0 ∧ (∀ u, a u ≠ some h) ∧ (∀ u, b u ≠ some h) := by
  classical
  have hcard : (holes a ∪ holes b).card < (Finset.univ : Finset (Positive n)).card := by
    rw [Finset.card_univ, positive_card]
    exact ((Finset.card_union_le _ _).trans (Nat.add_le_add (holes_card a) (holes_card b))).trans_lt hsmall
  obtain ⟨j, hj, hjnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨j.val, j.property, ?_, ?_⟩
  · intro u hu
    exact hjnot (Finset.mem_union_left _ ((mem_holes a j).mpr ⟨u, hu⟩))
  · intro u hu
    exact hjnot (Finset.mem_union_right _ ((mem_holes b j).mpr ⟨u, hu⟩))

theorem dance_domain {is : List L} {a b : State L n} (hDance : Dance is a b) : domain b = domain a := by
  induction hDance with
  | nil => rfl
  | cons hstep hrest ih => exact ih.trans (step_domain hstep)

/-- Adding a new row equation preserves the existence of a dance below half
the number of positive holes. Only one unused hole is needed. -/
theorem insert_zero (is : List L) (hnd : is.Nodup) (a b : State L n)
    (i : L) (hi : i ∈ is) (hai : a i = none)
    (hsmall : 2*((domain a).card+1) ≤ n) (hDance : Dance is a b) :
    ∃ c, Dance is (advance a i 0) c := by
  have hdomain := dance_domain hDance
  obtain ⟨h, hpos, hA, hB⟩ := unused a b (by rw [hdomain]; omega)
  have hExt := P2MPigeonDanceOneRowExtension.extend is hnd a b i hai h hpos hA hB hDance
  refine ⟨advance b i h, ?_⟩
  simpa only [if_pos hi] using hExt

end P2MProofComplexity.P2MPigeonDanceUnusedHole
end

section
-- Inlined Solutions.P2MPigeonDanceInsertZero

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MPigeonDanceInsertZero

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDancePolynomials P2MMatchingPolynomialFunctions P2MMatchingRowEquations

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

theorem valid (a : State L n) (ha : Valid a) (i : L) : Valid (advance a i 0) := by
  intro u v j hj hu hv
  by_cases hui : u = i
  · subst u
    have hz : (0 : Fin (n+1)) = j := Option.some.inj (by simpa only [advance, Function.update_self] using hu)
    exact (hj hz.symm).elim
  · by_cases hvi : v = i
    · subst v
      have hz : (0 : Fin (n+1)) = j := Option.some.inj (by simpa only [advance, Function.update_self] using hv)
      exact (hj hz.symm).elim
    · exact ha u v j hj (by simpa only [advance, Function.update_of_ne hui] using hu)
        (by simpa only [advance, Function.update_of_ne hvi] using hv)

theorem edges (a : State L n) (i : L) (hai : a i = none) :
    P2MPigeonDancePolynomials.edges (advance a i 0) = P2MPigeonDancePolynomials.edges a := by
  ext e
  rw [mem_edges, mem_edges]
  by_cases hei : e.1 = i
  · simp only [hei, advance, Function.update_self, hai, Option.some.injEq]
    constructor
    · intro hh
      exact (e.2.property hh.symm).elim
    · intro hh
      cases hh
  · simp only [advance, Function.update_of_ne hei]

theorem zeros (a : State L n) (i : L) : P2MPigeonDancePolynomials.zeros (advance a i 0) = insert i (P2MPigeonDancePolynomials.zeros a) := by
  ext u
  rw [mem_zeros, Finset.mem_insert, mem_zeros]
  by_cases hui : u = i <;> simp [advance, Function.update_apply, hui]

theorem not_mem_zeros (a : State L n) (i : L) (hai : a i = none) : i ∉ P2MPigeonDancePolynomials.zeros a := by
  rw [mem_zeros, hai]
  intro h
  cases h

theorem polynomial (a : State L n) (i : L) (hai : a i = none) :
    P2MPigeonDancePolynomials.polynomial (advance a i 0) = P2MPigeonDancePolynomials.polynomial a*equation i := by
  classical
  unfold P2MPigeonDancePolynomials.polynomial
  rw [edges a i hai, zeros, Finset.prod_insert (not_mem_zeros a i hai)]
  ring

end P2MProofComplexity.P2MPigeonDanceInsertZero
end

section
-- Inlined Solutions.P2MPigeonDanceRowMultiplication

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MPigeonDanceRowMultiplication

open P2MPigeonDanceStep P2MPigeonDancePolynomials P2MMatchingPolynomialFunctions P2MMatchingRowEquations

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

theorem positive_zero (a : State L n) (i : L) (j : Fin (n+1)) (hj : j ≠ 0) (hai : a i = some j) :
    polynomial a*equation i = 0 := by
  have hrow : ∃ e ∈ edges a, e.1 = i := ⟨(i, ⟨j, hj⟩), (mem_edges a _).mpr hai, rfl⟩
  have hz := monomial_mul_equation_zero (edges a) i hrow
  calc
    _ = (monomial (edges a)*equation i)*(∏ u ∈ zeros a, equation u) := by unfold polynomial; ring
    _ = 0 := by rw [hz, zero_mul]

theorem zero_self (a : State L n) (i : L) (hai : a i = some 0) : polynomial a*equation i = polynomial a := by
  classical
  have hi : i ∈ zeros a := (mem_zeros a i).mpr hai
  let p := monomial (edges a)*∏ u ∈ (zeros a).erase i, equation u
  have he : polynomial a = p*equation i := by
    unfold polynomial p
    rw [← Finset.mul_prod_erase (zeros a) (fun u => equation (R:=Positive n) u) hi]
    ring
  rw [he, mul_assoc, equation_idempotent]

end P2MProofComplexity.P2MPigeonDanceRowMultiplication
end

section
-- Inlined Solutions.P2MPigeonDanceGoodSpan

set_option maxHeartbeats 3500000

namespace P2MProofComplexity.P2MPigeonDanceGoodSpan

open P2MPigeonDanceStep P2MPigeonDanceRelation P2MPigeonDanceDomain P2MPigeonDancePolynomials
open P2MPigeonDanceCounting P2MMatchingPolynomialFunctions P2MMatchingRowEquations

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

noncomputable def span (is : List L) (d : ℕ) : Submodule (ZMod 2) (Placements L (Positive n) → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun a : GoodState (n:=n) is d => polynomial a.val))

theorem basis_mem (is : List L) (d : ℕ) (a : GoodState (n:=n) is d) : polynomial a.val ∈ span is d :=
  Submodule.subset_span ⟨a, rfl⟩

theorem span_le_degree (is : List L) (d : ℕ) : span (n:=n) is d ≤ space (L:=L) (R:=Positive n) d := by
  apply Submodule.span_le.mpr
  rintro p ⟨a, rfl⟩
  exact space_mono a.property.2.1 (polynomial_mem a.val a.property.1)

theorem span_mono (is : List L) {d e : ℕ} (hde : d ≤ e) : span (n:=n) is d ≤ span is e := by
  apply Submodule.span_le.mpr
  rintro p ⟨a, rfl⟩
  exact basis_mem is e ⟨a.val, a.property.1, a.property.2.1.trans hde, a.property.2.2⟩

theorem mul_equation (is : List L) (hnd : is.Nodup) (hcovers : ∀ u, u ∈ is)
    (d : ℕ) (hd : 1 ≤ d) (hbudget : 2*d ≤ n) (i : L)
    (p : Placements L (Positive n) → ZMod 2) (hp : p ∈ span is (d-1)) : p*equation i ∈ span is d := by
  classical
  have hle : span (n:=n) is (d-1) ≤ (span is d).comap (LinearMap.mulRight (ZMod 2) (equation i)) := by
    apply Submodule.span_le.mpr
    rintro q ⟨a, rfl⟩
    change polynomial a.val*equation i ∈ span is d
    cases hai : a.val i with
    | none =>
      have hcard : (domain (advance a.val i 0)).card = (domain a.val).card+1 := by
        have hh := domain_card (advance a.val i 0)
        rw [P2MPigeonDanceInsertZero.edges a.val i hai, P2MPigeonDanceInsertZero.zeros,
          Finset.card_insert_of_notMem (P2MPigeonDanceInsertZero.not_mem_zeros a.val i hai)] at hh
        have hh' := domain_card a.val
        omega
      obtain ⟨b, hDance⟩ := a.property.2.2
      have hsmall : 2*((domain a.val).card+1) ≤ n := by
        have hh := a.property.2.1
        omega
      obtain ⟨c, hc⟩ := P2MPigeonDanceUnusedHole.insert_zero is hnd a.val b i (hcovers i) hai hsmall hDance
      let a' : GoodState (n:=n) is d := ⟨advance a.val i 0,
        P2MPigeonDanceInsertZero.valid a.val a.property.1 i, by rw [hcard]; have hh := a.property.2.1; omega, ⟨c, hc⟩⟩
      rw [← P2MPigeonDanceInsertZero.polynomial a.val i hai]
      exact basis_mem is d a'
    | some j =>
      by_cases hj : j = 0
      · have hai0 : a.val i = some 0 := by rwa [hj] at hai
        rw [P2MPigeonDanceRowMultiplication.zero_self a.val i hai0]
        exact span_mono is (Nat.sub_le d 1) (basis_mem is (d-1) a)
      · rw [P2MPigeonDanceRowMultiplication.positive_zero a.val i j hj hai]
        exact (span is d).zero_mem
  exact hle hp

end P2MProofComplexity.P2MPigeonDanceGoodSpan
end

section
-- Inlined Solutions.P2MPigeonDanceFiniteOrder

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MPigeonDanceFiniteOrder

open P2MPigeonDanceStep

noncomputable def suffix (m k : ℕ) : List (Fin m) := (List.finRange m).drop k

theorem mem_suffix (m k : ℕ) (u : Fin m) : u ∈ suffix m k ↔ k ≤ u.val := by
  rw [suffix, List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨j, hj, he⟩
    have hv := congrArg Fin.val he
    simp only [List.getElem_finRange, Fin.coe_cast, Fin.val_mk] at hv
    omega
  · intro hu
    refine ⟨u.val-k, by simp only [List.length_finRange]; omega, ?_⟩
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.coe_cast, Fin.val_mk]
    omega

theorem suffix_cons (m k : ℕ) (hk : k < m) : suffix m k = ⟨k, hk⟩::suffix m (k+1) := by
  have hlen : k < (List.finRange m).length := by simpa only [List.length_finRange] using hk
  simpa only [List.getElem_finRange, suffix, Fin.cast_mk] using (List.getElem_cons_drop hlen).symm

theorem suffix_empty (m k : ℕ) (hk : m ≤ k) : suffix m k = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp only [suffix, List.length_drop, List.length_finRange, Nat.sub_eq_zero_of_le hk]

theorem suffix_nodup (m k : ℕ) : (suffix m k).Nodup := (List.nodup_finRange m).drop

theorem suffix_covers (m : ℕ) (u : Fin m) : u ∈ suffix m 0 := (mem_suffix m 0 u).mpr (Nat.zero_le _)

def code {m n : ℕ} (a : State (Fin m) n) : Fin m → Fin (n+2) := fun u => (a u).elim 0 Fin.succ

local instance indexWellFounded (m : ℕ) : WellFoundedGT (Fin m) := ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

def Before {m n : ℕ} (a b : State (Fin m) n) : Prop := toColex (code a) < toColex (code b)

theorem before_wellFounded (m n : ℕ) : WellFounded (Before (m:=m) (n:=n)) := by
  classical
  letI : Fintype (Colex (Fin m → Fin (n+2))) := Fintype.ofEquiv _ toColex
  have h : WellFounded ((· < ·) : Colex (Fin m → Fin (n+2)) → Colex (Fin m → Fin (n+2)) → Prop) :=
    Finite.wellFounded_of_trans_of_irrefl _
  exact InvImage.wf (fun a => toColex (code a)) h

theorem before_of_lower {m n : ℕ} (a b : State (Fin m) n) (i : Fin m) (j k : Fin (n+1))
    (hai : a i = some j) (hbi : b i = some k) (hjk : j < k)
    (hfuture : ∀ u, i < u → a u = b u) : Before a b := by
  change Pi.Lex (· > ·) (· < ·) (code a) (code b)
  refine ⟨i, ?_, ?_⟩
  · intro u hu
    simp only [code, hfuture u hu]
  · simpa only [code, hai, hbi, Option.elim_some] using (Fin.succ_lt_succ_iff.mpr hjk)

end P2MProofComplexity.P2MPigeonDanceFiniteOrder
end

section
-- Inlined Solutions.P2MPigeonDanceRowErasure

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MPigeonDanceRowErasure

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDancePolynomials P2MMatchingPolynomialFunctions P2MMatchingRowEquations

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

def Pure (a : State L n) : Prop := ∀ u, a u ≠ some 0

noncomputable def erase (a : State L n) (i : L) : State L n := Function.update a i none

theorem erase_pure (a : State L n) (ha : Pure a) (i : L) : Pure (erase a i) := by
  intro u
  by_cases hui : u = i
  · subst u
    simp [erase]
  · simpa only [erase, Function.update_of_ne hui] using ha u

theorem erase_valid (a : State L n) (ha : Valid a) (i : L) : Valid (erase a i) := by
  intro u v j hj hu hv
  have hui : u ≠ i := by intro hh; subst u; simpa [erase] using hu
  have hvi : v ≠ i := by intro hh; subst v; simpa [erase] using hv
  exact ha u v j hj (by simpa only [erase, Function.update_of_ne hui] using hu)
    (by simpa only [erase, Function.update_of_ne hvi] using hv)

theorem erase_value (a : State L n) (i : L) : erase a i i = none := Function.update_self _ _ _

theorem domain_erase (a : State L n) (i : L) : domain (erase a i) = (domain a).erase i := by
  classical
  ext u
  rw [mem_domain, Finset.mem_erase, mem_domain]
  by_cases hui : u = i
  · subst u
    simp [erase]
  · simp [erase, hui]

theorem restore (a : State L n) (i : L) (j : Fin (n+1)) (hai : a i = some j) : advance (erase a i) i j = a := by
  funext u
  by_cases hui : u = i <;> simp [advance, erase, Function.update_apply, hui, hai]

theorem edges_advance (a : State L n) (i : L) (j : Positive n) (hai : a i = none) :
    edges (advance a i j.val) = insert (i, j) (edges a) := by
  classical
  ext e
  rw [mem_edges, Finset.mem_insert, mem_edges]
  by_cases hei : e.1 = i
  · simp only [advance, hei, Function.update_self, hai, Option.some.injEq]
    constructor
    · intro hh
      exact Or.inl (Prod.ext hei (Subtype.ext hh.symm))
    · rintro (hh | hh)
      · exact congrArg (fun e : L×Positive n => e.2.val) hh.symm
      · cases hh
  · constructor
    · intro hh
      exact Or.inr (by simpa only [advance, Function.update_of_ne hei] using hh)
    · rintro (hh | hh)
      · exact (hei (congrArg Prod.fst hh)).elim
      · simpa only [advance, Function.update_of_ne hei] using hh

theorem advance_pure (a : State L n) (ha : Pure a) (i : L) (j : Positive n) : Pure (advance a i j.val) := by
  intro u
  by_cases hui : u = i
  · subst u
    simp only [advance, Function.update_self, ne_eq, Option.some.injEq]
    exact j.property
  · simpa only [advance, Function.update_of_ne hui] using ha u

theorem polynomial_pure (a : State L n) (ha : Pure a) : polynomial a = monomial (edges a) := by
  unfold polynomial
  rw [zeros_eq_empty a ha, Finset.prod_empty, mul_one]

theorem polynomial_advance (a : State L n) (ha : Pure a) (i : L) (j : Positive n) (hai : a i = none) :
    polynomial (advance a i j.val) = polynomial a*coordinate (i, j) := by
  rw [polynomial_pure _ (advance_pure a ha i j), polynomial_pure a ha, edges_advance a i j hai]
  change monomial (insert (i, j) (edges a)) = monomial (edges a)*monomial {(i, j)}
  rw [monomial_mul, Finset.union_singleton]

theorem polynomial_factor (a : State L n) (ha : Pure a) (i : L) (j : Positive n) (hai : a i = some j.val) :
    polynomial a = polynomial (erase a i)*coordinate (i, j) := by
  rw [← polynomial_advance (erase a i) (erase_pure a ha i) i j (erase_value a i), restore a i j.val hai]

theorem advance_erase (a : State L n) (i : L) (j : Fin (n+1)) : advance (erase a i) i j = advance a i j := by
  funext u
  by_cases hui : u = i <;> simp [advance, erase, Function.update_apply, hui]

theorem occupied_zero (a : State L n) (ha : Pure a) (i : L) (hai : a i = none) (j : Positive n)
    (hoccupied : ∃ u, a u = some j.val) : polynomial a*coordinate (i, j) = 0 := by
  classical
  obtain ⟨u, hu⟩ := hoccupied
  have hui : u ≠ i := by intro hh; subst u; rw [hai] at hu; cases hu
  have hnot : ¬ IsMatching (insert (i, j) (edges a)) := by
    intro hM
    have heq := hM (i, j) (Finset.mem_insert_self _ _) (u, j)
      (Finset.mem_insert_of_mem ((mem_edges a _).mpr hu)) (Or.inr rfl)
    exact hui (congrArg Prod.fst heq).symm
  rw [← polynomial_advance a ha i j hai, polynomial_pure _ (advance_pure a ha i j), edges_advance a i j hai,
    monomial_zero _ hnot]

theorem advance_valid (a : State L n) (ha : Valid a) (i : L) (j : Positive n)
    (hfree : ∀ u, a u ≠ some j.val) : Valid (advance a i j.val) := by
  apply P2MPigeonDanceStep.advance_valid a ha i 0 j.val
  exact (mem_available a 0 j.val).mpr ⟨lt_of_le_of_ne (Fin.zero_le j.val) j.property.symm, hfree⟩

theorem row_identity (p : Placements L (Positive n) → ZMod 2) (i : L) :
    p = p*equation i+∑ j : Positive n, p*coordinate (i, j) := by
  unfold equation
  rw [← Finset.mul_sum]
  ring

theorem isolate (p : Placements L (Positive n) → ZMod 2) (i : L) (j : Positive n) :
    p*coordinate (i, j) = p-p*equation i-∑ k ∈ (Finset.univ : Finset (Positive n)).erase j, p*coordinate (i, k) := by
  have hh := row_identity p i
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hh
  linear_combination -hh

end P2MProofComplexity.P2MPigeonDanceRowErasure
end

section
-- Inlined Solutions.P2MPigeonDanceSpanningRecursion

set_option maxHeartbeats 4500000

namespace P2MProofComplexity.P2MPigeonDanceSpanningRecursion

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceRowErasure P2MPigeonDanceFiniteOrder P2MMatchingPolynomialFunctions P2MMatchingRowEquations

theorem no_dance_mem {m n : ℕ} (D : ℕ) (seed : State (Fin m) n)
    (hSpace : space (L:=Fin m) (R:=Positive n) (D-1) ≤ P2MPigeonDanceGoodSpan.span (suffix m 0) D)
    (hQ : ∀ p ∈ space (L:=Fin m) (R:=Positive n) (D-1), ∀ i, p*equation i ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) D)
    (hBefore : ∀ a : State (Fin m) n, Valid a → Pure a → (domain a).card ≤ D → Before a seed →
      polynomial a ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) D)
    (k : ℕ) (b : State (Fin m) n) (hb : Valid b) (hPure : Pure b) (hcard : (domain b).card ≤ D)
    (hFuture : ∀ u : Fin m, k ≤ u.val → b u = seed u)
    (hBad : ∀ c, ¬ Dance (suffix m k) b c) :
    polynomial b ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) D := by
  classical
  by_cases hk : k < m
  · let i : Fin m := ⟨k, hk⟩
    have hsuffix : suffix m k = i::suffix m (k+1) := suffix_cons m k hk
    cases hbi : b i with
    | none =>
      have hBad' : ∀ c, ¬ Dance (suffix m (k+1)) b c := by
        intro c hc
        apply hBad c
        rw [hsuffix]
        exact Dance.cons (Or.inl ⟨hbi, rfl⟩) hc
      exact no_dance_mem D seed hSpace hQ hBefore (k+1) b hb hPure hcard
        (fun u hu => hFuture u (by omega)) hBad'
    | some old =>
      have hold : old ≠ 0 := fun hh => hPure i (by rwa [hh] at hbi)
      let j : Positive n := ⟨old, hold⟩
      let c := erase b i
      have hcValid : Valid c := erase_valid b hb i
      have hcPure : Pure c := erase_pure b hPure i
      have hci : c i = none := erase_value b i
      have himem : i ∈ domain b := (mem_domain b i).mpr ⟨old, hbi⟩
      have hcCard : (domain c).card = (domain b).card-1 := by
        rw [domain_erase, Finset.card_erase_of_mem himem]
      have hcDegree : polynomial c ∈ space (L:=Fin m) (R:=Positive n) (D-1) := by
        apply space_mono (Nat.sub_le_sub_right hcard 1)
        simpa only [hcCard] using polynomial_mem c hcValid
      have hrow : polynomial b = polynomial c-polynomial c*equation i-
          ∑ v ∈ (Finset.univ : Finset (Positive n)).erase j, polynomial c*coordinate (i, v) :=
        (polynomial_factor b hPure i j hbi).trans (isolate (polynomial c) i j)
      rw [hrow]
      apply (P2MPigeonDanceGoodSpan.span (suffix m 0) D).sub_mem
        ((P2MPigeonDanceGoodSpan.span (suffix m 0) D).sub_mem (hSpace hcDegree) (hQ _ hcDegree i))
      apply (P2MPigeonDanceGoodSpan.span (suffix m 0) D).sum_mem
      intro v hv
      have hvj : v ≠ j := (Finset.mem_erase.mp hv).1
      by_cases hOccupied : ∃ u, c u = some v.val
      · rw [occupied_zero c hcPure i hci v hOccupied]
        exact (P2MPigeonDanceGoodSpan.span (suffix m 0) D).zero_mem
      · have hfree : ∀ u, c u ≠ some v.val := fun u hu => hOccupied ⟨u, hu⟩
        let b' := advance c i v.val
        have hEq : b' = advance b i v.val := advance_erase b i v.val
        have hb' : Valid b' := P2MPigeonDanceRowErasure.advance_valid c hcValid i v hfree
        have hPure' : Pure b' := advance_pure c hcPure i v
        have hCard' : (domain b').card ≤ D := by
          rw [hEq, advance_domain b i old v.val hbi]
          exact hcard
        have hValue : b' i = some v.val := by simp only [b', advance, Function.update_self]
        have hSeed : seed i = some old := (hFuture i (by simp [i])).symm.trans hbi
        have hAfter : ∀ u : Fin m, i < u → b' u = seed u := by
          intro u hiu
          have hui : u ≠ i := (ne_of_gt hiu)
          rw [hEq]
          simp only [advance, Function.update_of_ne hui]
          exact hFuture u (by change k < u.val at hiu; omega)
        have hne : v.val ≠ old := by
          intro hh
          exact hvj (Subtype.ext hh)
        rw [← polynomial_advance c hcPure i v hci]
        change polynomial b' ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) D
        rcases lt_trichotomy v.val old with hlt | heq | hgt
        · exact hBefore b' hb' hPure' hCard' (before_of_lower b' seed i v.val old hValue hSeed hlt hAfter)
        · exact (hne heq).elim
        · have hfreeB : ∀ u, b u ≠ some v.val := by
            intro u hu
            by_cases hui : u = i
            · subst u
              exact hne (Option.some.inj (hu.symm.trans hbi))
            · apply hfree u
              simpa only [c, erase, Function.update_of_ne hui] using hu
          have hstep : Step b i b' := Or.inr ⟨old, v.val, hbi,
            (mem_available b old v.val).mpr ⟨hgt, hfreeB⟩, hEq⟩
          have hBad' : ∀ z, ¬ Dance (suffix m (k+1)) b' z := by
            intro z hz
            apply hBad z
            rw [hsuffix]
            exact Dance.cons hstep hz
          exact no_dance_mem D seed hSpace hQ hBefore (k+1) b' hb' hPure' hCard'
            (fun u hu => hAfter u (by change k < u.val; omega)) hBad'
  · exact (hBad b (by rw [suffix_empty m k (by omega)]; exact Dance.nil b)).elim
termination_by m-k
decreasing_by all_goals omega

end P2MProofComplexity.P2MPigeonDanceSpanningRecursion
end

section
-- Inlined Solutions.P2MPigeonDanceMatchingStates

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MPigeonDanceMatchingStates

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDancePolynomials P2MMatchingPolynomialFunctions

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

noncomputable def state (B : Placements L (Positive n)) : State L n :=
  fun u => if h : ∃ v : Positive n, (u, v) ∈ B.val then some (Classical.choose h).val else none

theorem value (B : Placements L (Positive n)) (u : L) (j : Fin (n+1)) :
    state B u = some j ↔ ∃ v : Positive n, v.val = j ∧ (u, v) ∈ B.val := by
  classical
  unfold state
  split_ifs with h
  · constructor
    · intro he
      exact ⟨Classical.choose h, Option.some.inj he, Classical.choose_spec h⟩
    · rintro ⟨v, hvj, hv⟩
      have he := B.property (u, Classical.choose h) (Classical.choose_spec h) (u, v) hv (Or.inl rfl)
      have hv' : (Classical.choose h).val = v.val := congrArg (fun e : L×Positive n => e.2.val) he
      exact congrArg Option.some (hv'.trans hvj)
  · constructor
    · intro he
      cases he
    · rintro ⟨v, _, hv⟩
      exact (h ⟨v, hv⟩).elim

theorem no_zero (B : Placements L (Positive n)) (u : L) : state B u ≠ some 0 := by
  intro hz
  obtain ⟨v, hv0, hv⟩ := (value B u 0).mp hz
  exact v.property hv0

theorem valid (B : Placements L (Positive n)) : Valid (state B) := by
  intro u v j hj hu hv
  obtain ⟨a, haj, ha⟩ := (value B u j).mp hu
  obtain ⟨b, hbj, hb⟩ := (value B v j).mp hv
  have hab : a = b := Subtype.ext (haj.trans hbj.symm)
  exact congrArg Prod.fst (B.property (u, a) ha (v, b) hb (Or.inr hab))

theorem edges (B : Placements L (Positive n)) : P2MPigeonDancePolynomials.edges (state B) = B.val := by
  ext e
  rw [mem_edges, value]
  constructor
  · rintro ⟨v, hve, hv⟩
    have he : v = e.2 := Subtype.ext hve
    simpa only [he, Prod.mk.eta] using hv
  · intro he
    exact ⟨e.2, rfl, he⟩

theorem zeros (B : Placements L (Positive n)) : P2MPigeonDancePolynomials.zeros (state B) = ∅ :=
  zeros_eq_empty (state B) (no_zero B)

theorem domain_card (B : Placements L (Positive n)) : (domain (state B)).card = B.val.card := by
  have hh := P2MPigeonDancePolynomials.domain_card (state B)
  rw [edges, zeros, Finset.card_empty, add_zero] at hh
  exact hh.symm

theorem polynomial (B : Placements L (Positive n)) : P2MPigeonDancePolynomials.polynomial (state B) = monomial B.val := by
  unfold P2MPigeonDancePolynomials.polynomial
  rw [edges, zeros, Finset.prod_empty, mul_one]

end P2MProofComplexity.P2MPigeonDanceMatchingStates
end

section
-- Inlined Solutions.P2MPigeonDanceSpanning

set_option maxHeartbeats 4000000

namespace P2MProofComplexity.P2MPigeonDanceSpanning

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceRowErasure P2MPigeonDanceFiniteOrder P2MMatchingPolynomialFunctions P2MPigeonDanceCounting

theorem none_dance {L : Type} [Fintype L] [DecidableEq L] {n : ℕ} (is : List L) (a : State L n)
    (ha : ∀ u, a u = none) : Dance is a a := by
  induction is with
  | nil => exact Dance.nil _
  | cons i is ih => exact Dance.cons (Or.inl ⟨ha i, rfl⟩) ih

theorem one_mem {L : Type} [Fintype L] [DecidableEq L] {n : ℕ} (is : List L) (d : ℕ) :
    (1 : Placements L (Positive n) → ZMod 2) ∈ P2MPigeonDanceGoodSpan.span is d := by
  classical
  let a : State L n := fun _ => none
  have hValid : Valid a := by simp [Valid, a]
  have hDomain : domain a = ∅ := by ext u; simp [mem_domain, a]
  have hEdges : edges a = ∅ := by ext e; simp [mem_edges, a]
  have hZeros : zeros a = ∅ := zeros_eq_empty a (by intro u; simp [a])
  let a' : GoodState (n:=n) is d := ⟨a, hValid, by rw [hDomain]; simp, ⟨a, none_dance is a (fun _ => rfl)⟩⟩
  have hPoly : polynomial a = 1 := by
    unfold polynomial
    rw [hEdges, hZeros, Finset.prod_empty, mul_one, monomial_empty]
  rw [← hPoly]
  exact P2MPigeonDanceGoodSpan.basis_mem is d a'

/-- The successful mixed-state polynomials span all partial-matching
polynomials through degree d, provided 2d does not exceed the number of holes. -/
theorem span_eq_space (m n d : ℕ) (hbudget : 2*d ≤ n) :
    P2MPigeonDanceGoodSpan.span (n:=n) (suffix m 0) d = space (L:=Fin m) (R:=Positive n) d := by
  classical
  induction d with
  | zero =>
    apply le_antisymm (P2MPigeonDanceGoodSpan.span_le_degree _ _) _
    apply Submodule.span_le.mpr
    rintro p ⟨A, hA, hCard, rfl⟩
    have hEmpty : A = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hEmpty, monomial_empty]
    exact one_mem (suffix m 0) 0
  | succ d ih =>
    have hIH := ih (by omega : 2*d ≤ n)
    have hSpace : space (L:=Fin m) (R:=Positive n) d ≤ P2MPigeonDanceGoodSpan.span (suffix m 0) (d+1) := by
      rw [← hIH]
      exact P2MPigeonDanceGoodSpan.span_mono _ (Nat.le_succ d)
    have hQ : ∀ p ∈ space (L:=Fin m) (R:=Positive n) d, ∀ i,
        p*P2MMatchingRowEquations.equation i ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d+1) := by
      intro p hp i
      have hp' : p ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) d := by rwa [hIH]
      exact P2MPigeonDanceGoodSpan.mul_equation (suffix m 0) (suffix_nodup m 0) (suffix_covers m)
        (d+1) (by omega) hbudget i p (by simpa only [Nat.add_sub_cancel] using hp')
    have hState : ∀ a : State (Fin m) n, Valid a → Pure a → (domain a).card ≤ d+1 →
        polynomial a ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d+1) := by
      intro a
      refine (before_wellFounded m n).induction (C := fun b => Valid b → Pure b →
        (domain b).card ≤ d+1 → polynomial b ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d+1)) a ?_
      intro b ihb hb hPure hCard
      by_cases hDance : ∃ c, Dance (suffix m 0) b c
      · exact P2MPigeonDanceGoodSpan.basis_mem _ _ ⟨b, hb, hCard, hDance⟩
      · exact P2MPigeonDanceSpanningRecursion.no_dance_mem (d+1) b hSpace hQ
          (fun c hc hcp hcc hbefore => ihb c hbefore hc hcp hcc)
          0 b hb hPure hCard (fun _ _ => rfl) (fun c hc => hDance ⟨c, hc⟩)
    apply le_antisymm (P2MPigeonDanceGoodSpan.span_le_degree _ _) _
    apply Submodule.span_le.mpr
    rintro p ⟨A, hA, hCard, rfl⟩
    let B : Placements (Fin m) (Positive n) := ⟨A, hA⟩
    have hRoot := hState (P2MPigeonDanceMatchingStates.state B) (P2MPigeonDanceMatchingStates.valid B)
      (P2MPigeonDanceMatchingStates.no_zero B) (by rw [P2MPigeonDanceMatchingStates.domain_card]; exact hCard)
    rw [P2MPigeonDanceMatchingStates.polynomial] at hRoot
    exact hRoot

end P2MProofComplexity.P2MPigeonDanceSpanning
end

section
-- Inlined Solutions.P2MPigeonDanceBasis

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MPigeonDanceBasis

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceCounting P2MPigeonDanceFiniteOrder P2MMatchingPolynomialFunctions

theorem independent (m n d : ℕ) (hbudget : 2*d ≤ n) :
    LinearIndependent (ZMod 2)
      (fun a : GoodState (n:=n) (suffix m 0) d => polynomial a.val) := by
  classical
  apply linearIndependent_iff_card_le_finrank_span.mpr
  change Fintype.card (GoodState (n:=n) (suffix m 0) d) ≤
    Module.finrank (ZMod 2) (P2MPigeonDanceGoodSpan.span (suffix m 0) d)
  rw [P2MPigeonDanceSpanning.span_eq_space m n d hbudget]
  simpa only [Nat.card_eq_fintype_card] using
    count_le_dimension (n:=n) (suffix m 0) (suffix_nodup m 0) (suffix_covers m) d

/-- Intersecting spans of subfamilies of an independent family intersects
the indexing sets. This is the degree-filtration step in the dance argument. -/
theorem span_image_inter {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    {v : I → V} (hv : LinearIndependent K v) (s t : Set I) :
    Submodule.span K (v '' (s ∩ t)) =
      Submodule.span K (v '' s) ⊓ Submodule.span K (v '' t) := by
  apply le_antisymm
  · exact le_inf (Submodule.span_mono (Set.image_mono Set.inter_subset_left))
      (Submodule.span_mono (Set.image_mono Set.inter_subset_right))
  · intro p hp
    obtain ⟨f, hf, hfp⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp hp.1
    obtain ⟨g, hg, hgp⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp hp.2
    have hfg : f = g := hv (hfp.trans hgp.symm)
    apply (Finsupp.mem_span_image_iff_linearCombination K).mpr
    refine ⟨f, ?_, hfp⟩
    intro i hi
    exact ⟨hf hi, hg (by simpa only [← hfg] using hi)⟩

end P2MProofComplexity.P2MPigeonDanceBasis
end

section
-- Inlined Solutions.P2MPigeonDanceEraseDance

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MPigeonDanceEraseDance

open P2MPigeonDanceStep P2MPigeonDanceRelation P2MPigeonDanceRowErasure P2MPigeonDancePolynomials

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

theorem erase_advance (a : State L n) (i k : L) (j : Fin (n+1)) (hki : k ≠ i) :
    erase (advance a k j) i = advance (erase a i) k j := by
  funext u
  by_cases hui : u = i <;> by_cases huk : u = k <;>
    simp_all [erase, advance, Function.update_apply]

theorem erase_advance_self (a : State L n) (i : L) (j : Fin (n+1)) :
    erase (advance a i j) i = erase a i := by
  funext u
  by_cases hui : u = i <;> simp [erase, advance, Function.update_apply, hui]

theorem step (a b : State L n) (k i : L) (h : Step a k b) :
    Step (erase a i) k (erase b i) := by
  rcases h with ⟨hak, rfl⟩ | ⟨old, new, hak, hnew, rfl⟩
  · left
    refine ⟨?_, rfl⟩
    by_cases hki : k = i <;> simp [erase, Function.update_apply, hki, hak]
  · by_cases hki : k = i
    · subst k
      exact Or.inl ⟨erase_value a i, erase_advance_self a i new⟩
    · right
      refine ⟨old, new, ?_, ?_, erase_advance a i k new hki⟩
      · simpa only [erase, Function.update_of_ne hki] using hak
      · apply (mem_available _ _ _).mpr
        obtain ⟨hlt, hfree⟩ := (mem_available a old new).mp hnew
        refine ⟨hlt, ?_⟩
        intro u hu
        by_cases hui : u = i
        · subst u
          simpa [erase] using hu
        · exact hfree u (by simpa only [erase, Function.update_of_ne hui] using hu)

theorem dance {is : List L} {a b : State L n} (h : Dance is a b) (i : L) :
    Dance is (erase a i) (erase b i) := by
  induction h with
  | nil => exact Dance.nil _
  | cons hs hr ih => exact Dance.cons (step _ _ _ i hs) ih

theorem polynomial_factor_zero (a : State L n) (i : L) (hai : a i = some 0) :
    polynomial a = polynomial (erase a i)*P2MMatchingRowEquations.equation i := by
  rw [← P2MPigeonDanceInsertZero.polynomial (erase a i) i (erase_value a i), restore a i 0 hai]

end P2MProofComplexity.P2MPigeonDanceEraseDance
end

section
-- Inlined Solutions.P2MPigeonDanceConsequences

set_option maxHeartbeats 3500000

namespace P2MProofComplexity.P2MPigeonDanceConsequences

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceCounting P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDanceFiniteOrder

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

noncomputable def span (is : List L) (d : ℕ) : Submodule (ZMod 2) (Placements L (Positive n) → ZMod 2) :=
  Submodule.span (ZMod 2)
    ((fun a : GoodState (n:=n) is d => polynomial a.val) '' {a | (zeros a.val).Nonempty})

theorem basis_mem (is : List L) (d : ℕ) (a : GoodState (n:=n) is d) (ha : (zeros a.val).Nonempty) :
    polynomial a.val ∈ span is d := Submodule.subset_span ⟨a, ha, rfl⟩

theorem span_le_good (is : List L) (d : ℕ) : span (n:=n) is d ≤ P2MPigeonDanceGoodSpan.span is d := by
  apply Submodule.span_le.mpr
  rintro p ⟨a, ha, rfl⟩
  exact P2MPigeonDanceGoodSpan.basis_mem is d a

theorem span_mono (is : List L) {d e : ℕ} (hde : d ≤ e) : span (n:=n) is d ≤ span is e := by
  apply Submodule.span_le.mpr
  rintro p ⟨a, ha, rfl⟩
  exact basis_mem is e ⟨a.val, a.property.1, a.property.2.1.trans hde, a.property.2.2⟩ ha

theorem mul_equation (is : List L) (hnd : is.Nodup) (hcovers : ∀ u, u ∈ is)
    (d : ℕ) (hd : 1 ≤ d) (hbudget : 2*d ≤ n) (i : L)
    (p : Placements L (Positive n) → ZMod 2) (hp : p ∈ P2MPigeonDanceGoodSpan.span is (d-1)) :
    p*equation i ∈ span is d := by
  classical
  have hle : P2MPigeonDanceGoodSpan.span (n:=n) is (d-1) ≤
      (span is d).comap (LinearMap.mulRight (ZMod 2) (equation i)) := by
    apply Submodule.span_le.mpr
    rintro q ⟨a, rfl⟩
    change polynomial a.val*equation i ∈ span is d
    cases hai : a.val i with
    | none =>
      have hcard : (domain (advance a.val i 0)).card = (domain a.val).card+1 := by
        have hh := domain_card (advance a.val i 0)
        rw [P2MPigeonDanceInsertZero.edges a.val i hai, P2MPigeonDanceInsertZero.zeros,
          Finset.card_insert_of_notMem (P2MPigeonDanceInsertZero.not_mem_zeros a.val i hai)] at hh
        have hh' := domain_card a.val
        omega
      obtain ⟨b, hDance⟩ := a.property.2.2
      have hsmall : 2*((domain a.val).card+1) ≤ n := by
        have hh := a.property.2.1
        omega
      obtain ⟨c, hc⟩ := P2MPigeonDanceUnusedHole.insert_zero is hnd a.val b i (hcovers i) hai hsmall hDance
      let a' : GoodState (n:=n) is d := ⟨advance a.val i 0,
        P2MPigeonDanceInsertZero.valid a.val a.property.1 i,
        by rw [hcard]; have hh := a.property.2.1; omega, ⟨c, hc⟩⟩
      rw [← P2MPigeonDanceInsertZero.polynomial a.val i hai]
      exact basis_mem is d a' ⟨i, (mem_zeros _ _).mpr (Function.update_self _ _ _)⟩
    | some j =>
      by_cases hj : j = 0
      · have hai0 : a.val i = some 0 := by rwa [hj] at hai
        rw [P2MPigeonDanceRowMultiplication.zero_self a.val i hai0]
        exact span_mono is (Nat.sub_le d 1)
          (basis_mem is (d-1) a ⟨i, (mem_zeros _ _).mpr hai0⟩)
      · rw [P2MPigeonDanceRowMultiplication.positive_zero a.val i j hj hai]
        exact (span is d).zero_mem
  exact hle hp

noncomputable def emptyGood (m n d : ℕ) : GoodState (n:=n) (suffix m 0) d := by
  classical
  let a : State (Fin m) n := fun _ => none
  have hvalid : Valid a := by simp [a, Valid]
  have hdom : domain a = ∅ := by ext u; simp [mem_domain, a]
  exact ⟨a, hvalid, by rw [hdom]; simp,
    ⟨a, P2MPigeonDanceSpanning.none_dance _ a (fun _ => rfl)⟩⟩

theorem emptyGood_polynomial (m n d : ℕ) : polynomial (emptyGood m n d).val = 1 := by
  classical
  have he : edges (emptyGood m n d).val = ∅ := by ext e; simp [mem_edges, emptyGood]
  have hz : zeros (emptyGood m n d).val = ∅ := by ext u; simp [mem_zeros, emptyGood]
  rw [polynomial, he, hz, Finset.prod_empty, mul_one, monomial_empty]

theorem one_not_mem (m n d : ℕ) (hbudget : 2*d ≤ n) :
    (1 : Placements (Fin m) (Positive n) → ZMod 2) ∉ span (suffix m 0) d := by
  classical
  rw [← emptyGood_polynomial m n d]
  apply (P2MPigeonDanceBasis.independent m n d hbudget).notMem_span_image
  change ¬ (zeros (emptyGood m n d).val).Nonempty
  simp [zeros, emptyGood]

end P2MProofComplexity.P2MPigeonDanceConsequences
end

section
-- Inlined Solutions.P2MBitPHPMatchingAxioms

set_option maxHeartbeats 4000000

namespace P2MProofComplexity.P2MBitPHPMatchingAxioms

open MvPolynomial P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDancePolynomials
open P2MPigeonDanceFiniteOrder SemAC02.Supplement P2MBitPHPMatchingDecoding

variable {m n ℓ : ℕ}

theorem delta_value (u : Fin m) (a : Fin ℓ → Bool) (x : Fin m × Fin ℓ → Bool) :
    polyFn (deltaA u a) x = if (fun t => x (u,t)) = a then 1 else 0 := by
  classical
  unfold polyFn deltaA
  rw [map_prod]
  by_cases h : (fun t => x (u,t)) = a
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro t ht
    have he : x (u,t) = a t := congrFun h t
    cases ha : a t <;> simp [ha, boolPt, he]
  · rw [if_neg h]
    obtain ⟨t, ht⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    cases ha : a t <;> cases hx : x (u,t) <;> simp_all [boolPt]

theorem delta_decoded (addr : Positive n ≃ (Fin ℓ → Bool)) (u : Fin m) (a : Fin ℓ → Bool) :
    (fun B => polyFn (deltaA u a) (decoded addr B)) =
      coordinate (u,addr.symm a)+(if a = (fun _ => false) then 1 else 0 : ZMod 2) • equation u := by
  classical
  funext B
  by_cases hu : ∃ j, (u,j) ∈ B.val
  · obtain ⟨j,hj⟩ := hu
    have hrow : (fun t => decoded addr B (u,t)) = addr j := funext (decoded_occupied addr B u j hj)
    have htarget : (u,addr.symm a) ∈ B.val ↔ addr j = a := by
      constructor
      · intro h
        have hj' : j = addr.symm a := congrArg Prod.snd (B.property (u,j) hj (u,addr.symm a) h (Or.inl rfl))
        rw [hj', addr.apply_symm_apply]
      · intro h
        have hj' : j = addr.symm a := addr.injective (h.trans (addr.apply_symm_apply a).symm)
        simpa only [← hj'] using hj
    simp only [delta_value, hrow, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      coordinate_value, equation_value, if_pos (show ∃ j, (u,j) ∈ B.val from ⟨j,hj⟩),
      mul_zero, add_zero]
    by_cases hja : addr j = a
    · simp only [if_pos hja, if_pos (htarget.mpr hja)]
    · simp only [if_neg hja, if_neg (mt htarget.mp hja)]
  · have hrow : (fun t => decoded addr B (u,t)) = (fun _ => false) :=
      funext (decoded_absent addr B u hu)
    have htarget : (u,addr.symm a) ∉ B.val := fun h => hu ⟨_,h⟩
    simp only [delta_value, hrow, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      coordinate_value, if_neg htarget, equation_value, if_neg hu, mul_one, zero_add]
    simp only [eq_comm]

theorem delta_mem (addr : Positive n ≃ (Fin ℓ → Bool)) (u : Fin m) (a : Fin ℓ → Bool) :
    (fun B => polyFn (deltaA u a) (decoded addr B)) ∈ space 1 := by
  rw [delta_decoded]
  exact (space 1).add_mem (coordinate_mem _) ((space 1).smul_mem _ (equation_mem _))

theorem collision_zero (u v : Fin m) (huv : u ≠ v) (j : Positive n) :
    coordinate (u,j)*coordinate (v,j) = 0 := by
  have hbad : ¬ IsMatching ({(u,j)} ∪ {(v,j)}) := by
    intro h
    have he := h (u,j) (by simp) (v,j) (by simp) (Or.inr rfl)
    exact huv (congrArg Prod.fst he)
  exact (monomial_mul {(u,j)} {(v,j)}).trans (monomial_zero _ hbad)

theorem axiom_mem (addr : Positive n ≃ (Fin ℓ → Bool)) (d : ℕ) (hd : 2 ≤ d) (hbudget : 2*d ≤ n)
    (u v : Fin m) (huv : u ≠ v) (a : Fin ℓ → Bool) :
    (fun B => polyFn (deltaA u a*deltaA v a) (decoded addr B)) ∈
      P2MPigeonDanceConsequences.span (suffix m 0) d := by
  classical
  let c : ZMod 2 := if a = (fun _ => false) then 1 else 0
  let du : Placements (Fin m) (Positive n) → ZMod 2 := fun B => polyFn (deltaA u a) (decoded addr B)
  let dv : Placements (Fin m) (Positive n) → ZMod 2 := fun B => polyFn (deltaA v a) (decoded addr B)
  let xu := coordinate (u,addr.symm a)
  let xv := coordinate (v,addr.symm a)
  have hdu : du = xu+c • equation u := delta_decoded addr u a
  have hdv : dv = xv+c • equation v := delta_decoded addr v a
  have hx : xu*xv = 0 := collision_zero u v huv _
  have hid : du*dv = c • (dv*equation u+xu*equation v) := by
    rw [hdu, hdv]
    simp only [Algebra.smul_def]
    linear_combination hx
  have hvGood : dv ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d-1) := by
    rw [P2MPigeonDanceSpanning.span_eq_space m n (d-1) (by omega)]
    exact space_mono (by omega : 1 ≤ d-1) (delta_mem addr v a)
  have hxGood : xu ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d-1) := by
    rw [P2MPigeonDanceSpanning.span_eq_space m n (d-1) (by omega)]
    exact space_mono (by omega : 1 ≤ d-1) (coordinate_mem _)
  have hQu := P2MPigeonDanceConsequences.mul_equation (suffix m 0) (suffix_nodup m 0) (suffix_covers m)
    d (by omega) hbudget u dv hvGood
  have hQv := P2MPigeonDanceConsequences.mul_equation (suffix m 0) (suffix_nodup m 0) (suffix_covers m)
    d (by omega) hbudget v xu hxGood
  have hout := (P2MPigeonDanceConsequences.span (suffix m 0) d).smul_mem c
    ((P2MPigeonDanceConsequences.span (suffix m 0) d).add_mem hQu hQv)
  rw [← hid] at hout
  have he : (fun B => polyFn (deltaA u a*deltaA v a) (decoded addr B)) = du*dv := by
    funext B
    exact map_mul (eval (boolPt (decoded addr B))) _ _
  rwa [he]

end P2MProofComplexity.P2MBitPHPMatchingAxioms
end

section
-- Inlined Solutions.P2MBitPHPPolynomialFacts

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MBitPHPPolynomialFacts

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

theorem polyFn_ext {V : Type} [Finite V] {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q) (he : polyFn p = polyFn q) : p = q := by
  apply multilinear_ext hp hq
  intro x
  let y : V → Bool := fun v => decide (x v = 1)
  have hy : (boolPt y : V → ZMod 2) = x := by
    funext v
    rcases P2MMajorityFoundation.eq_zero_or_one (x v) with h | h <;> simp [boolPt,y,h]
  have hh := congrFun he y
  simpa only [polyFn,hy] using hh

theorem delta_degree {m ℓ : ℕ} (u : Fin m) (a : Fin ℓ → Bool) : (deltaA u a).totalDegree ≤ ℓ := by
  classical
  unfold deltaA
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ t : Fin ℓ, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro t ht
      split_ifs
      · simp
      · exact (totalDegree_sub _ _).trans (by simp)
    _ = ℓ := by simp

theorem axiom_degree {m ℓ : ℕ} (p : MvPolynomial (Fin m × Fin ℓ) (ZMod 2)) (hp : p ∈ bphp m ℓ) :
    p.totalDegree ≤ 2*ℓ := by
  obtain ⟨u,v,a,huv,rfl⟩ := hp
  exact (totalDegree_mul _ _).trans (by have hu := delta_degree u a; have hv := delta_degree v a; omega)

noncomputable def normalAxioms (m ℓ : ℕ) : Set (MvPolynomial (Fin m × Fin ℓ) (ZMod 2)) := ML '' bphp m ℓ

theorem normal_degree {m ℓ : ℕ} (p : MvPolynomial (Fin m × Fin ℓ) (ZMod 2)) (hp : p ∈ normalAxioms m ℓ) :
    IsMultilinear p ∧ p.totalDegree ≤ 2*ℓ := by
  obtain ⟨q,hq,rfl⟩ := hp
  exact ⟨ml_multilinear _, (P2MBooleanFlip.ml_totalDegree_le _).trans (axiom_degree q hq)⟩

theorem normal_polyAx (m ℓ : ℕ) : polyAx (normalAxioms m ℓ) = polyAx (bphp m ℓ) := by
  ext f
  constructor
  · rintro ⟨p,⟨q,hq,rfl⟩,rfl⟩
    exact ⟨q,hq,by funext x; exact (eval_ml q (boolPt x)).symm⟩
  · rintro ⟨q,hq,rfl⟩
    exact ⟨ML q,⟨q,hq,rfl⟩,by funext x; exact eval_ml q (boolPt x)⟩

theorem normal_derivation {m ℓ : ℕ} (π : List (MvPolynomial (Fin m × Fin ℓ) (ZMod 2)))
    (hπ : PCNonBool.IsDerivation ML (normalAxioms m ℓ) π) : PCNonBool.IsDerivation ML (bphp m ℓ) π := by
  intro k hk
  rcases hπ k hk with ⟨p,⟨q,hq,rfl⟩,c,he⟩ | hcomb | hmul
  · left
    exact ⟨q,hq,c,by simpa only [ml_idempotent] using he⟩
  · exact Or.inr (Or.inl hcomb)
  · exact Or.inr (Or.inr hmul)

end SemAC02.Supplement.P2MBitPHPPolynomialFacts
end

section
-- Inlined Solutions.P2MBitPHPRestrictionSemantics

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MBitPHPRestrictionSemantics

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra SemAC02.Supplement
open P2MBitPHPAddressPairData P2MBitPHPRestriction

variable {m ℓ : ℕ}

noncomputable def lifted (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S) (β : S → Bool)
    (x : Fin m × Fin ℓ → Bool) (e : Fin m × Fin (ℓ+2)) : Bool :=
  Sum.elim x (fun c => decide (c=1)) (restriction S a β e)

theorem transport_value (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S) (β : S → Bool)
    (p : MvPolynomial (Fin m × Fin (ℓ+2)) (ZMod 2)) (x : Fin m × Fin ℓ → Bool) :
    polyFn (P2MRelativePCRestriction.transport (restriction S a β) p) x = polyFn p (lifted S a β x) := by
  unfold polyFn
  rw [P2MRelativePCRestriction.evaluation]
  have hx : (fun v => eval (boolPt x) (P2MRelativePCRestriction.leaf (restriction S a β) v)) =
      boolPt (lifted S a β x) := by
    funext e
    unfold P2MRelativePCRestriction.leaf lifted
    cases hr : restriction S a β e with
    | inl v => simp [boolPt,hr]
    | inr c =>
      rcases P2MMajorityFoundation.eq_zero_or_one c with hc | hc <;> simp [boolPt,hr,hc]
  rw [hx]

theorem selected (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (hrows : Set.InjOn Prod.fst (S : Set (Fin m × Fin (ℓ+2))))
    (β : S → Bool) (x : Fin m × Fin ℓ → Bool) (v : S) (t : Fin (ℓ+2)) :
    lifted S a β x (v.val.1,t) = a.address β v t := by
  rw [lifted,selected_row S a hrows β v t]
  cases a.address β v t <;> simp

theorem unselected (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (β : S → Bool) (x : Fin m × Fin ℓ → Bool) (u : Fin m) (hu : ¬ HasRow S u) (t : Fin (ℓ+2)) :
    lifted S a β x (u,t) = if ht : 2 ≤ t.val then x (u,lower t ht) else false := by
  rw [lifted,unselected_row S a β u hu t]
  split_ifs <;> simp

theorem different_rows (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (hrows : Set.InjOn Prod.fst (S : Set (Fin m × Fin (ℓ+2))))
    (β : S → Bool) (x : Fin m × Fin ℓ → Bool) (v : S) (u : Fin m) (huv : u ≠ v.val.1) :
    (fun t => lifted S a β x (v.val.1,t)) ≠ (fun t => lifted S a β x (u,t)) := by
  intro he
  classical
  by_cases hu : HasRow S u
  · obtain ⟨w,hw⟩ := hu
    have hvw : v ≠ w := by intro hh; subst w; exact huv hw.symm
    apply address_ne a β v w hvw
    funext t
    have hh := congrFun he t
    rw [selected S a hrows β x v t, ← hw, selected S a hrows β x w t] at hh
    exact hh
  · have hh := congrFun he (reserved v.val.2)
    rw [selected S a hrows β x v _, address_reserved,
      unselected S a β x u hu _, dif_neg (by have hh := reserved_lt v.val.2; omega)] at hh
    cases hh

theorem row_eq_iff (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (β : S → Bool) (x : Fin m × Fin ℓ → Bool) (u : Fin m) (hu : ¬ HasRow S u)
    (z : Fin (ℓ+2) → Bool) (hz : ∀ t, t.val < 2 → z t = false) :
    (fun t => lifted S a β x (u,t)) = z ↔ (fun t => x (u,t)) = (fun t => z (tail t)) := by
  constructor
  · intro he
    funext t
    have hh := congrFun he (tail t)
    simpa only [unselected S a β x u hu _, tail, dif_pos (by omega : 2 ≤ t.val+2), lower,
      Nat.add_sub_cancel] using hh
  · intro he
    funext t
    rw [unselected S a β x u hu t]
    split_ifs with ht
    · have hh := congrFun he (lower t ht)
      simpa only [tail_lower] using hh
    · exact (hz t (by omega)).symm

end P2MProofComplexity.P2MBitPHPRestrictionSemantics
end

section
-- Inlined Solutions.P2MBitPHPRestrictedAxioms

set_option maxHeartbeats 3500000

namespace P2MProofComplexity.P2MBitPHPRestrictedAxioms

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra SemAC02 SemAC02.Supplement
open P2MBitPHPAddressPairData P2MBitPHPRestriction P2MBitPHPRestrictionSemantics P2MBitPHPMatchingAxioms

variable {m ℓ : ℕ}

theorem selected_zero (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (hrows : Set.InjOn Prod.fst (S : Set (Fin m × Fin (ℓ+2))))
    (β : S → Bool) (v : S) (u : Fin m) (huv : u ≠ v.val.1) (z : Fin (ℓ+2) → Bool) :
    P2MRelativePCRestriction.transport (restriction S a β) (deltaA v.val.1 z*deltaA u z) = 0 := by
  apply P2MBitPHPPolynomialFacts.polyFn_ext (ml_multilinear _) (by simp [IsMultilinear])
  funext x
  change polyFn (P2MRelativePCRestriction.transport (restriction S a β) (deltaA v.val.1 z*deltaA u z)) x = polyFn 0 x
  rw [transport_value]
  simp only [polyFn,map_zero]
  change polyFn (deltaA v.val.1 z*deltaA u z) (lifted S a β x) = 0
  simp only [polyFn,map_mul]
  change polyFn (deltaA v.val.1 z) (lifted S a β x)*polyFn (deltaA u z) (lifted S a β x) = 0
  rw [delta_value,delta_value]
  by_cases hv : (fun t => lifted S a β x (v.val.1,t)) = z
  · have hu : (fun t => lifted S a β x (u,t)) ≠ z := by
      intro hu
      exact different_rows S a hrows β x v u huv (hv.trans hu.symm)
    simp only [if_pos hv,if_neg hu,mul_zero]
  · simp only [if_neg hv,zero_mul]

theorem unselected_image (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (β : S → Bool) (u v : Fin m) (hu : ¬ HasRow S u) (hv : ¬ HasRow S v)
    (z : Fin (ℓ+2) → Bool) :
    P2MRelativePCRestriction.transport (restriction S a β) (deltaA u z*deltaA v z) = 0 ∨
      P2MRelativePCRestriction.transport (restriction S a β) (deltaA u z*deltaA v z) =
        ML (deltaA u (fun t => z (tail t))*deltaA v (fun t => z (tail t))) := by
  classical
  by_cases hz : ∀ t, t.val < 2 → z t = false
  · right
    apply P2MBitPHPPolynomialFacts.polyFn_ext (ml_multilinear _) (ml_multilinear _)
    funext x
    change polyFn (P2MRelativePCRestriction.transport (restriction S a β) (deltaA u z*deltaA v z)) x =
      polyFn (ML (deltaA u (fun t => z (tail t))*deltaA v (fun t => z (tail t)))) x
    rw [transport_value]
    change polyFn (deltaA u z*deltaA v z) (lifted S a β x) =
      polyFn (ML (deltaA u (fun t => z (tail t))*deltaA v (fun t => z (tail t)))) x
    simp only [polyFn,eval_ml,map_mul]
    change polyFn (deltaA u z) (lifted S a β x)*polyFn (deltaA v z) (lifted S a β x) =
      polyFn (deltaA u (fun t => z (tail t))) x*polyFn (deltaA v (fun t => z (tail t))) x
    simp only [delta_value,row_eq_iff S a β x u hu z hz,row_eq_iff S a β x v hv z hz]
  · left
    obtain ⟨t,ht,hzt⟩ : ∃ t, t.val < 2 ∧ z t ≠ false := by
      push Not at hz
      exact hz
    apply P2MBitPHPPolynomialFacts.polyFn_ext (ml_multilinear _) (by simp [IsMultilinear])
    funext x
    change polyFn (P2MRelativePCRestriction.transport (restriction S a β) (deltaA u z*deltaA v z)) x = polyFn 0 x
    rw [transport_value]
    simp only [polyFn,map_zero]
    change polyFn (deltaA u z*deltaA v z) (lifted S a β x) = 0
    simp only [polyFn,map_mul]
    change polyFn (deltaA u z) (lifted S a β x)*polyFn (deltaA v z) (lifted S a β x) = 0
    have hrow : (fun t => lifted S a β x (u,t)) ≠ z := by
      intro he
      have hh := congrFun he t
      rw [unselected S a β x u hu t,dif_neg (by omega)] at hh
      exact hzt hh.symm
    rw [delta_value,if_neg hrow,zero_mul]

theorem axiom_spec (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (hrows : Set.InjOn Prod.fst (S : Set (Fin m × Fin (ℓ+2))))
    (β : S → Bool) (p : MvPolynomial (Fin m × Fin (ℓ+2)) (ZMod 2)) (hp : p ∈ bphp m (ℓ+2)) :
    P2MRelativePCRestriction.transport (restriction S a β) p = 0 ∨
      ∃ q ∈ bphp m ℓ, P2MRelativePCRestriction.transport (restriction S a β) p = ML q := by
  classical
  obtain ⟨u,v,z,huv,rfl⟩ := hp
  by_cases hu : HasRow S u
  · obtain ⟨w,hw⟩ := hu
    left
    rw [← hw]
    exact selected_zero S a hrows β w v (by simpa only [hw] using huv.symm) z
  · by_cases hv : HasRow S v
    · obtain ⟨w,hw⟩ := hv
      left
      rw [mul_comm,← hw]
      exact selected_zero S a hrows β w u (by simpa only [hw] using huv) z
    · rcases unselected_image S a β u v hu hv z with hzero | himage
      · exact Or.inl hzero
      · exact Or.inr ⟨_,⟨u,v,fun t => z (tail t),huv,rfl⟩,himage⟩

theorem axiom_derivable (S : Finset (Fin m × Fin (ℓ+2))) (a : Data S)
    (hrows : Set.InjOn Prod.fst (S : Set (Fin m × Fin (ℓ+2))))
    (β : S → Bool) (B : ℕ) (hB : 2*ℓ ≤ B)
    (p : MvPolynomial (Fin m × Fin (ℓ+2)) (ZMod 2)) (hp : p ∈ bphp m (ℓ+2)) :
    P2MRelativePCFinite.Derivable (bphp m ℓ) (Ble (Fin m × Fin ℓ) B)
      (P2MRelativePCRestriction.transport (restriction S a β) p) := by
  rcases axiom_spec S a hrows β p hp with hz | ⟨q,hq,he⟩
  · rw [hz]
    exact P2MRelativePCFinite.pc_zero _ _
  · rw [he]
    apply P2MRelativePCFinite.pc_axiom _ _ q hq
    exact (P2MBooleanDegreeSpaces.mem_Ble_iff B _).mpr ⟨ml_multilinear _,
      (P2MBooleanFlip.ml_totalDegree_le _).trans ((P2MBitPHPPolynomialFacts.axiom_degree q hq).trans hB)⟩

end P2MProofComplexity.P2MBitPHPRestrictedAxioms
end

section
-- Inlined Solutions.P2MPigeonDanceDegreeFiltration

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MPigeonDanceDegreeFiltration

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceCounting P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDanceFiniteOrder

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

theorem good_span_cut (is : List L) (d e : ℕ) (hed : e ≤ d) :
    P2MPigeonDanceGoodSpan.span (n:=n) is e = Submodule.span (ZMod 2)
      ((fun a : GoodState (n:=n) is d => polynomial a.val) '' {a | (domain a.val).card ≤ e}) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.val, a.property.1, a.property.2.1.trans hed, a.property.2.2⟩, a.property.2.1, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a.val, a.property.1, ha, a.property.2.2⟩, rfl⟩

theorem consequence_span_cut (is : List L) (d e : ℕ) (hed : e ≤ d) :
    P2MPigeonDanceConsequences.span (n:=n) is e = Submodule.span (ZMod 2)
      ((fun a : GoodState (n:=n) is d => polynomial a.val) ''
        {a | (zeros a.val).Nonempty ∧ (domain a.val).card ≤ e}) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a.val, a.property.1, a.property.2.1.trans hed, a.property.2.2⟩, ⟨ha, a.property.2.1⟩, rfl⟩
  · rintro ⟨a, ⟨ha, he⟩, rfl⟩
    exact ⟨⟨a.val, a.property.1, he, a.property.2.2⟩, ha, rfl⟩

theorem degree_cut (m n d e : ℕ) (hbudget : 2*d ≤ n) (hed : e ≤ d)
    (p : Placements (Fin m) (Positive n) → ZMod 2)
    (hp : p ∈ P2MPigeonDanceConsequences.span (suffix m 0) d)
    (hdegree : p ∈ space e) : p ∈ P2MPigeonDanceConsequences.span (suffix m 0) e := by
  have he : 2*e ≤ n := by omega
  have hlow : space (L:=Fin m) (R:=Positive n) e = Submodule.span (ZMod 2)
      ((fun a : GoodState (n:=n) (suffix m 0) d => polynomial a.val) ''
        {a | (domain a.val).card ≤ e}) := by
    rw [← P2MPigeonDanceSpanning.span_eq_space m n e he]
    exact good_span_cut _ d e hed
  rw [consequence_span_cut _ d e hed]
  have hIntersection := P2MPigeonDanceBasis.span_image_inter
    (P2MPigeonDanceBasis.independent m n d hbudget)
    {a | (zeros a.val).Nonempty} {a | (domain a.val).card ≤ e}
  change p ∈ Submodule.span (ZMod 2)
    ((fun a : GoodState (n:=n) (suffix m 0) d => polynomial a.val) ''
      ({a | (zeros a.val).Nonempty} ∩ {a | (domain a.val).card ≤ e}))
  rw [hIntersection]
  exact ⟨hp, by rwa [← hlow]⟩

end P2MProofComplexity.P2MPigeonDanceDegreeFiltration
end

section
-- Inlined Solutions.P2MPigeonDanceWeakClosure

set_option maxHeartbeats 3500000

namespace P2MProofComplexity.P2MPigeonDanceWeakClosure

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceCounting P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDanceFiniteOrder
open P2MPigeonDanceRowErasure

theorem coordinate (m n d : ℕ) (hd : 2 ≤ d) (hbudget : 2*d ≤ n)
    (p : Placements (Fin m) (Positive n) → ZMod 2)
    (hp : p ∈ P2MPigeonDanceConsequences.span (suffix m 0) d)
    (hdegree : p ∈ space (d-1)) (e : Fin m × Positive n) :
    p*P2MMatchingRowEquations.coordinate e ∈ P2MPigeonDanceConsequences.span (suffix m 0) d := by
  classical
  have hp' := P2MPigeonDanceDegreeFiltration.degree_cut m n d (d-1) hbudget (Nat.sub_le d 1) p hp hdegree
  have hle : P2MPigeonDanceConsequences.span (n:=n) (suffix m 0) (d-1) ≤
      (P2MPigeonDanceConsequences.span (suffix m 0) d).comap
        (LinearMap.mulRight (ZMod 2) (P2MMatchingRowEquations.coordinate e)) := by
    apply Submodule.span_le.mpr
    rintro q ⟨a, ha, rfl⟩
    change polynomial a.val*P2MMatchingRowEquations.coordinate e ∈ P2MPigeonDanceConsequences.span (suffix m 0) d
    obtain ⟨i, hi⟩ := ha
    have hai : a.val i = some 0 := (mem_zeros _ _).mp hi
    let c := erase a.val i
    have hcValid : Valid c := erase_valid a.val a.property.1 i
    have hiDomain : i ∈ domain a.val := (mem_domain _ _).mpr ⟨0, hai⟩
    have hcCard : (domain c).card ≤ d-2 := by
      have hh := a.property.2.1
      change (domain (erase a.val i)).card ≤ d-2
      rw [domain_erase, Finset.card_erase_of_mem hiDomain]
      omega
    have hcDegree : polynomial c ∈ space (d-2) := space_mono hcCard (polynomial_mem c hcValid)
    have hProduct : polynomial c*P2MMatchingRowEquations.coordinate e ∈ space (d-1) := by
      apply space_mono (show d-2+1 ≤ d-1 by omega)
      exact mul_mem hcDegree (coordinate_mem e)
    have hGood : polynomial c*P2MMatchingRowEquations.coordinate e ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d-1) := by
      rwa [P2MPigeonDanceSpanning.span_eq_space m n (d-1) (by omega)]
    have hOut := P2MPigeonDanceConsequences.mul_equation (suffix m 0) (suffix_nodup m 0) (suffix_covers m)
      d (by omega) hbudget i _ hGood
    rw [P2MPigeonDanceEraseDance.polynomial_factor_zero a.val i hai]
    convert hOut using 1 <;> ring
  exact hle hp'

theorem monomial (m n d : ℕ) (hd : 2 ≤ d) (hbudget : 2*d ≤ n)
    (p : Placements (Fin m) (Positive n) → ZMod 2)
    (hp : p ∈ P2MPigeonDanceConsequences.span (suffix m 0) d)
    (e : ℕ) (hdegree : p ∈ space e) (A : Finset (Fin m × Positive n))
    (hA : IsMatching A) (hbound : e+A.card ≤ d) :
    p*P2MMatchingPolynomialFunctions.monomial A ∈ P2MPigeonDanceConsequences.span (suffix m 0) d := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa only [monomial_empty, mul_one] using hp
  | @insert x A hx ih =>
    have hAM : IsMatching A := matching_mono (Finset.subset_insert _ _) hA
    have hcard : (insert x A).card = A.card+1 := Finset.card_insert_of_notMem hx
    have hmem := ih hAM (by rw [hcard] at hbound; omega)
    have hdeg : p*P2MMatchingPolynomialFunctions.monomial A ∈ space (d-1) := by
      apply space_mono (show e+A.card ≤ d-1 by rw [hcard] at hbound; omega)
      exact mul_mem hdegree (monomial_mem A hAM A.card le_rfl)
    have hout := coordinate m n d hd hbudget _ hmem hdeg x
    have hX : P2MMatchingRowEquations.coordinate x = P2MMatchingPolynomialFunctions.monomial {x} := rfl
    rw [hX, mul_assoc, monomial_mul, Finset.union_singleton] at hout
    exact hout

theorem mul (m n d : ℕ) (hd : 2 ≤ d) (hbudget : 2*d ≤ n)
    (p q : Placements (Fin m) (Positive n) → ZMod 2)
    (hp : p ∈ P2MPigeonDanceConsequences.span (suffix m 0) d)
    (e f : ℕ) (hdegree : p ∈ space e) (hq : q ∈ space f) (hbound : e+f ≤ d) :
    p*q ∈ P2MPigeonDanceConsequences.span (suffix m 0) d := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨A, hA, hcard, rfl⟩ := hq
    exact monomial m n d hd hbudget p hp e hdegree A hA (by omega)
  | zero => simpa only [mul_zero] using (P2MPigeonDanceConsequences.span (suffix m 0) d).zero_mem
  | add q r hq hr ihq ihr =>
    simpa only [mul_add] using (P2MPigeonDanceConsequences.span (suffix m 0) d).add_mem ihq ihr
  | smul c q hq ih =>
    simpa only [mul_smul_comm] using (P2MPigeonDanceConsequences.span (suffix m 0) d).smul_mem c ih

end P2MProofComplexity.P2MPigeonDanceWeakClosure
end

section
-- Inlined Solutions.P2MBitPHPPCObstruction

set_option maxHeartbeats 3500000

namespace P2MProofComplexity.P2MBitPHPPCObstruction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra SemAC02 SemAC02.Supplement
open P2MMatchingPolynomialFunctions P2MPigeonDancePolynomials P2MPigeonDanceFiniteOrder P2MBitPHPMatchingDecoding

theorem aeval_ml {m n ℓ : ℕ} (addr : Positive n ≃ (Fin ℓ → Bool))
    (p : MvPolynomial (Fin m × Fin ℓ) (ZMod 2)) : aeval (bit addr) (ML p) = aeval (bit addr) p := by
  rw [← polynomial_value, ← polynomial_value]
  funext B
  exact eval_ml p (boolPt (decoded addr B))

theorem derivation (m n ℓ B K : ℕ) (addr : Positive n ≃ (Fin ℓ → Bool))
    (hK : 2 ≤ K) (hBK : B+1 ≤ K) (hbudget : 2*K ≤ n)
    (π : List (MvPolynomial (Fin m × Fin ℓ) (ZMod 2)))
    (hπ : PCNonBool.IsDerivation ML (bphp m ℓ) π)
    (hdegree : ∀ p ∈ π, p.totalDegree ≤ B) :
    ∀ p ∈ π, aeval (bit addr) p ∈ P2MPigeonDanceConsequences.span (suffix m 0) K := by
  have hall : ∀ k (hk : k < π.length),
      aeval (bit addr) π[k] ∈ P2MPigeonDanceConsequences.span (suffix m 0) K := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ k hk with ⟨p,hp,c,he⟩ | ⟨i,j,hi,hj,a,b,he⟩ | ⟨i,hi,v,he⟩
      · rw [he, map_smul, aeval_ml]
        apply (P2MPigeonDanceConsequences.span (suffix m 0) K).smul_mem
        obtain ⟨u,v,a,huv,rfl⟩ := hp
        rw [← polynomial_value]
        exact P2MBitPHPMatchingAxioms.axiom_mem addr K hK hbudget u v huv a
      · rw [he, map_add, map_smul, map_smul]
        exact (P2MPigeonDanceConsequences.span (suffix m 0) K).add_mem
          ((P2MPigeonDanceConsequences.span (suffix m 0) K).smul_mem a (ih i hi (hi.trans hk)))
          ((P2MPigeonDanceConsequences.span (suffix m 0) K).smul_mem b (ih j hj (hj.trans hk)))
      · rw [he, aeval_ml, map_mul, aeval_X, mul_comm]
        exact P2MPigeonDanceWeakClosure.mul m n K hK hbudget _ _ (ih i hi (hi.trans hk)) B 1
          (space_mono (hdegree _ (List.getElem_mem (hi.trans hk)))
            (P2MMatchingSubstitutionDegree.aeval_mem (bit addr) (bit_mem addr) π[i]))
          (bit_mem addr v) hBK
  intro p hp
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hp
  exact hall k hk

theorem not_derivable_one (m n ℓ B K : ℕ) (addr : Positive n ≃ (Fin ℓ → Bool))
    (hK : 2 ≤ K) (hBK : B+1 ≤ K) (hbudget : 2*K ≤ n) :
    ¬ P2MRelativePCFinite.Derivable (bphp m ℓ) (Ble (Fin m × Fin ℓ) B) 1 := by
  rintro (hzero | ⟨π,hπ,hBle,hOne⟩)
  · exact one_ne_zero hzero
  · have hout := derivation m n ℓ B K addr hK hBK hbudget π hπ
      (fun p hp => ((P2MBooleanDegreeSpaces.mem_Ble_iff B p).mp (hBle p hp)).2) 1 hOne
    rw [map_one] at hout
    exact P2MPigeonDanceConsequences.one_not_mem m n K hbudget hout

end P2MProofComplexity.P2MBitPHPPCObstruction
end

section
-- Inlined Solutions.RelativePCFinitePolynomialMultiplication

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePCFinite

theorem pc_polynomial_mul {V : Type} [Finite V] (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (u v : MvPolynomial V (ZMod 2)) (hu : Derivable P U u) (huml : IsMultilinear u)
    (hmem : ∀ w : MvPolynomial V (ZMod 2), w.totalDegree ≤ v.totalDegree → ML (u*w) ∈ U) :
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

end SemAC02.P2MRelativePCFinite
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
-- Inlined Solutions.P2MLocalBooleanConsequence

set_option maxHeartbeats 3500000

namespace SemAC02.Supplement.P2MLocalBooleanConsequence

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis AC02Frege.P2MMajorityFoundation

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def assignment (S : Finset V) (B : Finset S) : V → ZMod 2 :=
  fun v => if h : v ∈ S then if (⟨v, h⟩ : S) ∈ B then 1 else 0 else 0

noncomputable def indicator (S : Finset V) (B : Finset S) : MvPolynomial V (ZMod 2) :=
  ML (rename Subtype.val (pointPoly B))

theorem indicator_multilinear (S : Finset V) (B : Finset S) : IsMultilinear (indicator S B) := by
  exact ml_multilinear _

theorem indicator_degree (S : Finset V) (B : Finset S) : (indicator S B).totalDegree ≤ S.card := by
  apply (P2MBooleanFlip.ml_totalDegree_le _).trans
  apply (totalDegree_rename_le _ _).trans
  simpa only [Fintype.card_coe] using P2MBooleanLocality.multilinear_degree_le_card (pointPoly B) (pointPoly_multilinear B)

theorem indicator_eval (S : Finset V) (B : Finset S) (x : V → ZMod 2) :
    eval x (indicator S B) = if (fun v : S => x v.val) = (fun v => if v ∈ B then 1 else 0) then 1 else 0 := by
  rw [indicator, eval_ml, eval_rename, pointPoly_eval]
  rfl

theorem eval_local (S : Finset V) (p : MvPolynomial V (ZMod 2)) (hp : p.vars ⊆ S)
    (x y : V → ZMod 2) (hxy : ∀ v ∈ S, x v = y v) : eval x p = eval y p := by
  apply eval₂Hom_congr' rfl _ rfl
  intro v hv hv'
  exact hxy v (hp hv)

theorem assignment_eq (S : Finset V) (B : Finset S) (x : V → ZMod 2)
    (hx : (fun v : S => x v.val) = (fun v => if v ∈ B then 1 else 0)) :
    ∀ v ∈ S, x v = assignment S B v := by
  intro v hv
  have hh := congrFun hx ⟨v, hv⟩
  simpa only [assignment, dif_pos hv] using hh

theorem interpolation (S : Finset V) (q : MvPolynomial V (ZMod 2)) (hml : IsMultilinear q)
    (hvars : q.vars ⊆ S) :
    q = ∑ B : Finset S, eval (assignment S B) q • indicator S B := by
  classical
  apply multilinear_ext hml
    (multilinear_sum _ _ (fun B _ => (mem_restrictDegree V _ 1).mp
      ((restrictDegree V (ZMod 2) 1).smul_mem _ ((mem_restrictDegree V _ 1).mpr (indicator_multilinear S B)))))
  intro x
  have heq (B : Finset S) :
      (fun v : S => x v.val) = (fun v => if v ∈ B then (1 : ZMod 2) else 0) ↔
      B = Finset.univ.filter (fun v : S => x v.val = 1) := by
    constructor
    · intro h
      have hh := congrArg (fun f : S → ZMod 2 => Finset.univ.filter (fun v => f v = 1)) h
      simp only [ones_of_point] at hh
      exact hh.symm
    · intro h
      subst B
      exact (point_of_ones (fun v : S => x v.val)).symm
  simp only [map_sum, smul_eval, indicator_eval, heq]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply eval_local S q hvars
  intro v hv
  dsimp [assignment]
  rw [dif_pos hv]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases eq_zero_or_one (x v) with he | he <;> simp [he]

theorem relative_sum (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) {I : Type} (E : Finset I)
    (f : I → MvPolynomial V (ZMod 2)) (hf : ∀ i ∈ E, P2MRelativePCFinite.Derivable P U (f i)) :
    P2MRelativePCFinite.Derivable P U (∑ i ∈ E, f i) := by
  classical
  induction E using Finset.induction_on with
  | empty => simpa using P2MRelativePCFinite.pc_zero P U
  | @insert i E hi ih =>
    rw [Finset.sum_insert hi]
    exact P2MRelativePCFinite.pc_add P U (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem complete (S : Finset V) (P : Set (MvPolynomial V (ZMod 2))) (a : ℕ)
    (hvars : ∀ p ∈ P, p.vars ⊆ S) (hdegree : ∀ p ∈ P, p.totalDegree ≤ a)
    (q : MvPolynomial V (ZMod 2)) (hml : IsMultilinear q) (hqvars : q.vars ⊆ S)
    (hconsequence : ∀ x : V → ZMod 2, (∀ p ∈ P, eval x p = 0) → eval x q = 0) :
    P2MRelativePCFinite.Derivable P (Ble V (a+S.card)) q := by
  classical
  have hpoint (B : Finset S) :
      P2MRelativePCFinite.Derivable P (Ble V (a+S.card))
        (eval (assignment S B) q • indicator S B) := by
    by_cases hzero : eval (assignment S B) q = 0
    · simpa only [hzero, zero_smul] using P2MRelativePCFinite.pc_zero P (Ble V (a+S.card))
    · have hfExists : ∃ f ∈ P, eval (assignment S B) f ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hzero (hconsequence _ hn)
      obtain ⟨f, hf, hfnz⟩ := hfExists
      have hfval : eval (assignment S B) f = 1 :=
        (eq_zero_or_one _).resolve_left hfnz
      have hFdeg : (ML f).totalDegree ≤ a := (P2MBooleanFlip.ml_totalDegree_le f).trans (hdegree f hf)
      have hFmem : ML f ∈ Ble V (a+S.card) :=
        (P2MBooleanDegreeSpaces.mem_Ble_iff _ _).mpr ⟨ml_multilinear _, hFdeg.trans (Nat.le_add_right _ _)⟩
      have hAx := P2MRelativePCFinite.pc_axiom P (Ble V (a+S.card)) f hf hFmem
      have hProd := P2MRelativePCFinite.pc_polynomial_mul P (Ble V (a+S.card))
        (ML f) (indicator S B) hAx (ml_multilinear _) (by
          intro w hw
          apply (P2MBooleanDegreeSpaces.mem_Ble_iff _ _).mpr
          refine ⟨ml_multilinear _, ?_⟩
          exact (P2MBooleanFlip.ml_totalDegree_le _).trans
            ((totalDegree_mul _ _).trans (Nat.add_le_add hFdeg (hw.trans (indicator_degree S B)))))
      have he : ML (ML f*indicator S B) = indicator S B := by
        apply multilinear_ext (ml_multilinear _) (indicator_multilinear S B)
        intro x
        simp only [eval_ml, map_mul, indicator_eval]
        split_ifs with hx
        · rw [eval_local S f (hvars f hf) x (assignment S B) (assignment_eq S B x hx), hfval]
          simp
        · simp
      rw [he] at hProd
      exact P2MRelativePCFinite.pc_smul P _ hProd _
  rw [interpolation S q hml hqvars]
  exact relative_sum P _ Finset.univ _ (fun B _ => hpoint B)

theorem mono_axioms (P Q : Set (MvPolynomial V (ZMod 2))) (hPQ : P ⊆ Q)
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) (q : MvPolynomial V (ZMod 2))
    (hq : P2MRelativePCFinite.Derivable P U q) : P2MRelativePCFinite.Derivable Q U q := by
  rcases hq with hq | ⟨π, hπ, hspace, hq⟩
  · exact Or.inl hq
  · refine Or.inr ⟨π, ?_, hspace, hq⟩
    intro k hk
    rcases hπ k hk with ⟨p, hp, a, he⟩ | hcomb | hmul
    · exact Or.inl ⟨p, hPQ hp, a, he⟩
    · exact Or.inr (Or.inl hcomb)
    · exact Or.inr (Or.inr hmul)

theorem mono_space (P : Set (MvPolynomial V (ZMod 2)))
    (U W : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) (hUW : U ≤ W)
    (q : MvPolynomial V (ZMod 2)) (hq : P2MRelativePCFinite.Derivable P U q) :
    P2MRelativePCFinite.Derivable P W q := by
  rcases hq with hq | ⟨π, hπ, hspace, hq⟩
  · exact Or.inl hq
  · exact Or.inr ⟨π, hπ, fun p hp => hUW (hspace p hp), hq⟩

end SemAC02.Supplement.P2MLocalBooleanConsequence
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
-- Inlined Solutions.P2MMultiplierSupportCount

set_option maxHeartbeats 1000000

open Module MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MMultiplierSupportCount

abbrev MultiplierIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :=
  {S : Finset (Fin n × Fin m) // S.card ≤ k ∧ IsLnSupport g S}

theorem multiplier_span {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun S : MultiplierIndex g n k => xMon S.1)) =
      multiplierSpace g n k := by
  unfold multiplierSpace
  congr 1
  ext p
  constructor
  · rintro ⟨S,rfl⟩
    exact ⟨S.1,S.2,rfl⟩
  · rintro ⟨S,hS,rfl⟩
    exact ⟨⟨S,hS⟩,rfl⟩

noncomputable def multiplierBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Basis (MultiplierIndex g n k) (ZMod 2) (multiplierSpace g n k) :=
  (Basis.span (xMon_linearIndependent.comp (fun S : MultiplierIndex g n k => S.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (multiplier_span g n k))

instance finite_multiplierSpace {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Module.Finite (ZMod 2) (multiplierSpace g n k) := Module.Finite.of_basis (multiplierBasis g n k)

theorem finrank_multiplier {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    finrank (ZMod 2) (multiplierSpace g n k) =
      (Finset.univ.filter (fun S : Finset (Fin n × Fin m) => S.card ≤ k ∧ IsLnSupport g S)).card := by
  rw [Module.finrank_eq_card_basis (multiplierBasis g n k)]
  exact Fintype.card_subtype _

abbrev LowIndex (V : Type) (k : ℕ) := {S : Finset V // S.card ≤ k}

def lowIndexEquiv (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    LowIndex V k ≃ (j : Fin (min k (Fintype.card V)+1)) × {S : Finset V // S.card = j.1} where
  toFun S := ⟨⟨S.1.card,by have := Finset.card_le_univ S.1; omega⟩,S.1,rfl⟩
  invFun T := ⟨T.2.1,by have := T.1.2; have := T.2.2; omega⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv T := by rcases T with ⟨⟨j,hj⟩,S,hS⟩; cases hS; rfl

theorem low_support_card (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    (Finset.univ.filter (fun S : Finset V => S.card ≤ k)).card = Hn (Fintype.card V) k := by
  rw [← Fintype.card_subtype,Fintype.card_congr (lowIndexEquiv V k),Fintype.card_sigma]
  simp only [Fintype.card_finset_len]
  exact Fin.sum_univ_eq_sum_range _ _

end SemAC02.P2MMultiplierSupportCount
end

section
-- Inlined Solutions.P2MBooleanDegreeBasis

open Module MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanDegreeBasis

abbrev DegreeIndex (V : Type) (K : ℕ) := {T : Finset V // T.card ≤ K}

theorem degree_span (V : Type) (K : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun T : DegreeIndex V K => xMon T.1)) = Ble V K := by
  unfold Ble
  congr 1
  ext p
  constructor
  · rintro ⟨T,rfl⟩; exact ⟨T.1,T.2,rfl⟩
  · rintro ⟨T,hT,rfl⟩; exact ⟨⟨T,hT⟩,rfl⟩

noncomputable def degreeBasis (V : Type) (K : ℕ) : Basis (DegreeIndex V K) (ZMod 2) (Ble V K) :=
  (Basis.span (xMon_linearIndependent.comp (fun T : DegreeIndex V K => T.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (degree_span V K))

instance finite_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) : Module.Finite (ZMod 2) (Ble V K) :=
  Module.Finite.of_basis (degreeBasis V K)

theorem finrank_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) :
    finrank (ZMod 2) (Ble V K) = Hn (Fintype.card V) K := by
  rw [Module.finrank_eq_card_basis (degreeBasis V K)]
  have he : Fintype.card (DegreeIndex V K) =
      (Finset.univ.filter (fun T : Finset V => T.card ≤ K)).card := Fintype.card_subtype _
  rw [he]
  exact P2MMultiplierSupportCount.low_support_card V K

end SemAC02.P2MBooleanDegreeBasis
end

section
-- Inlined Solutions.P2MBitPHPPigeonLinearSeparation

set_option maxHeartbeats 3500000

namespace SemAC02.Supplement.P2MBitPHPPigeonLinearSeparation

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis
open P2MProofComplexity P2MBitPHPAddressPairData P2MBitPHPRestriction

def Eligible {m b : ℕ} (k : ℕ) (S : Finset (Fin m × Fin b)) : Prop :=
  S.card ≤ k ∧ Set.InjOn Prod.fst (S : Set (Fin m × Fin b))

noncomputable def space (m b k : ℕ) : Submodule (ZMod 2) (MvPolynomial (Fin m × Fin b) (ZMod 2)) :=
  monomialSpan (Eligible (m:=m) (b:=b) k)

theorem space_le (m b k : ℕ) : space m b k ≤ Ble (Fin m × Fin b) k := by
  apply Submodule.span_le.mpr
  rintro p ⟨S,hS,rfl⟩
  exact Submodule.subset_span ⟨S,hS.1,rfl⟩

instance finite_space (m b k : ℕ) : Module.Finite (ZMod 2) (space m b k) :=
  Module.Finite.of_injective (Submodule.inclusion (space_le m b k)) (Submodule.inclusion_injective _)

theorem separation (m ℓ B k : ℕ) (hchoose : 2*k < 2^ℓ) (hB : 2*ℓ ≤ B)
    (hbudget : 2*(B+2) ≤ 2^ℓ)
    (p : MvPolynomial (Fin m × Fin (ℓ+2)) (ZMod 2)) (hp : p ∈ space m (ℓ+2) k)
    (hderive : P2MRelativePCFinite.Derivable (P2MBitPHPPolynomialFacts.normalAxioms m (ℓ+2))
      (Ble (Fin m × Fin (ℓ+2)) B) p) : p = 0 := by
  classical
  by_contra hnonzero
  obtain ⟨hml,hsupport⟩ := (mem_monomialSpan_iff (Eligible (m:=m) (b:=ℓ+2) k) p).mp hp
  obtain ⟨d,hd,hmax⟩ := p.support.exists_max_image (fun e => e.support.card) (support_nonempty.mpr hnonzero)
  obtain ⟨hdk,hrows⟩ := hsupport d hd
  obtain ⟨a⟩ := exists_data d.support (show 2*d.support.card < 2^ℓ by omega)
  have hRestricted (β : d.support → Bool) : P2MRelativePCFinite.Derivable (bphp m ℓ) (Ble (Fin m × Fin ℓ) B)
      (P2MRelativePCRestriction.transport (restriction d.support a β) p) := by
    rcases hderive with hzero | ⟨π,hπ,hdegree,hpπ⟩
    · exact (hnonzero hzero).elim
    · exact P2MRelativePCRestriction.derivation (restriction d.support a β) (bphp m (ℓ+2)) (bphp m ℓ) B
        (P2MBitPHPRestrictedAxioms.axiom_derivable d.support a hrows β B hB) π
        (P2MBitPHPPolynomialFacts.normal_derivation π hπ)
        (fun q hq => ((P2MBooleanDegreeSpaces.mem_Ble_iff B q).mp (hdegree q hq)).2) p hpπ
  have hSum := P2MLocalBooleanConsequence.relative_sum (bphp m ℓ) (Ble (Fin m × Fin ℓ) B) Finset.univ
    (fun β : d.support → Bool => P2MRelativePCRestriction.transport (restriction d.support a β) p)
    (fun β _ => hRestricted β)
  have hOne := extraction d.support a hrows p hml d hd rfl hmax
  rw [hOne] at hSum
  let addr : P2MPigeonDancePolynomials.Positive (2^ℓ) ≃ (Fin ℓ → Bool) :=
    Fintype.equivOfCardEq (by rw [P2MPigeonDanceUnusedHole.positive_card]; simp)
  exact P2MBitPHPPCObstruction.not_derivable_one m (2^ℓ) ℓ B (B+2) addr (by omega) (by omega) hbudget hSum

end SemAC02.Supplement.P2MBitPHPPigeonLinearSeparation
end

section
-- Inlined Solutions.P2MSeparatedSetCounting

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MSeparatedSetCounting

variable {V : Type} [Fintype V] [DecidableEq V]

def Good (B : V → Finset V) (A : Finset V) : Prop :=
  ∀ v ∈ A, ∀ w ∈ A, v ≠ w → w ∉ B v

noncomputable def sets (B : V → Finset V) (j : ℕ) : Finset (Finset V) :=
  open Classical in Finset.univ.filter (fun A => A.card = j ∧ Good B A)

noncomputable def available (B : V → Finset V) (A : Finset V) : Finset V :=
  Finset.univ \ A.biUnion B

theorem mem_sets (B : V → Finset V) (j : ℕ) (A : Finset V) :
    A ∈ sets B j ↔ A.card = j ∧ Good B A := by
  classical
  simp [sets]

theorem available_bound (B : V → Finset V) (b : ℕ) (hB : ∀ v, (B v).card ≤ b)
    (A : Finset V) : Fintype.card V - b * A.card ≤ (available B A).card := by
  have hcard : (A.biUnion B).card ≤ b * A.card := by
    calc
      _ ≤ ∑ v ∈ A, (B v).card := Finset.card_biUnion_le
      _ ≤ ∑ v ∈ A, b := Finset.sum_le_sum (fun v _ => hB v)
      _ = _ := by simp [Nat.mul_comm]
  dsimp only [available]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  omega

theorem available_not_mem (B : V → Finset V) (hself : ∀ v, v ∈ B v)
    (A : Finset V) (v : V) (hv : v ∈ available B A) : v ∉ A := by
  intro hvA
  exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr ⟨v, hvA, hself v⟩)

theorem good_insert (B : V → Finset V)
    (hsymm : ∀ v w, w ∈ B v → v ∈ B w) (A : Finset V) (hA : Good B A)
    (v : V) (hv : v ∈ available B A) : Good B (insert v A) := by
  intro x hx y hy hxy
  have hav (w : V) (hw : w ∈ A) : v ∉ B w := by
    intro hh
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr ⟨w, hw, hh⟩)
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    rcases Finset.mem_insert.mp hy with hy | hy
    · exact (hxy hy.symm).elim
    · exact fun hh => hav y hy (hsymm v y hh)
  · rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      exact hav x hx
    · exact hA x hx y hy hxy

theorem step (B : V → Finset V) (b : ℕ) (hB : ∀ v, (B v).card ≤ b)
    (hself : ∀ v, v ∈ B v) (hsymm : ∀ v w, w ∈ B v → v ∈ B w) (j : ℕ) :
    (Fintype.card V - b*j) * (sets B j).card ≤ (j+1) * (sets B (j+1)).card := by
  classical
  let D := (Σ A : sets B j, {v // v ∈ available B A.val})
  let T := (Σ A : sets B (j+1), A.val)
  have hnot (A : sets B j) (v : {v // v ∈ available B A.val}) : v.val ∉ A.val :=
    available_not_mem B hself A.val v.val v.property
  have hnew (A : sets B j) (v : {v // v ∈ available B A.val}) :
      insert v.val A.val ∈ sets B (j+1) := by
    apply (mem_sets B _ _).mpr
    obtain ⟨hcard, hgood⟩ := (mem_sets B _ _).mp A.property
    exact ⟨by rw [Finset.card_insert_of_notMem (hnot A v), hcard],
      good_insert B hsymm A.val hgood v.val v.property⟩
  let f : D → T := fun z =>
    ⟨⟨insert z.2.val z.1.val, hnew z.1 z.2⟩, ⟨z.2.val, Finset.mem_insert_self _ _⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨A, v⟩ ⟨A', v'⟩ he
    have hv : v.val = v'.val := congrArg (fun z : T => z.2.val) he
    have hset : insert v.val A.val = insert v'.val A'.val := congrArg (fun z : T => z.1.val) he
    have heA : A.val = A'.val := by
      have hh := congrArg (fun E => E.erase v.val) hset
      have hnot' : v.val ∉ A'.val := by rw [hv]; exact hnot A' v'
      rw [← hv, Finset.erase_insert (hnot A v), Finset.erase_insert hnot'] at hh
      exact hh
    have heA' : A = A' := Subtype.ext heA
    subst A'
    have hev : v = v' := Subtype.ext hv
    subst v'
    rfl
  have hT (A : sets B (j+1)) : Fintype.card A.val = j+1 := by
    rw [Fintype.card_coe]
    exact ((mem_sets B _ _).mp A.property).1
  calc
    _ = ∑ A : sets B j, (Fintype.card V - b*j) := by simp [Nat.mul_comm]
    _ ≤ ∑ A : sets B j, Fintype.card {v // v ∈ available B A.val} := by
      apply Finset.sum_le_sum
      intro A hA
      rw [Fintype.card_coe]
      have hh := available_bound B b hB A.val
      rwa [((mem_sets B _ _).mp A.property).1] at hh
    _ = Fintype.card D := (Fintype.card_sigma).symm
    _ ≤ Fintype.card T := Fintype.card_le_of_injective f hf
    _ = _ := by rw [Fintype.card_sigma]; simp [hT, Nat.mul_comm]

theorem product_count (B : V → Finset V) (b : ℕ) (hB : ∀ v, (B v).card ≤ b)
    (hself : ∀ v, v ∈ B v) (hsymm : ∀ v w, w ∈ B v → v ∈ B w) (k : ℕ) :
    (∏ i ∈ Finset.range k, (Fintype.card V-b*i)) ≤ k.factorial * (sets B k).card := by
  classical
  induction k with
  | zero =>
    have hempty : (∅ : Finset V) ∈ sets B 0 := by rw [mem_sets]; simp [Good]
    simpa using Finset.card_pos.mpr ⟨∅, hempty⟩
  | succ k ih =>
    rw [Finset.prod_range_succ]
    calc
      _ ≤ (k.factorial*(sets B k).card)*(Fintype.card V-b*k) := Nat.mul_le_mul_right _ ih
      _ = k.factorial*((Fintype.card V-b*k)*(sets B k).card) := by ring
      _ ≤ k.factorial*((k+1)*(sets B (k+1)).card) :=
        Nat.mul_le_mul_left _ (step B b hB hself hsymm k)
      _ = (k+1).factorial*(sets B (k+1)).card := by rw [Nat.factorial_succ]; ring

theorem count (B : V → Finset V) (b : ℕ) (hB : ∀ v, (B v).card ≤ b)
    (hself : ∀ v, v ∈ B v) (hsymm : ∀ v w, w ∈ B v → v ∈ B w) (k : ℕ) :
    (Fintype.card V - b*(k-1))^k ≤ k.factorial * (sets B k).card := by
  classical
  let q := Fintype.card V - b*(k-1)
  have hbase : sets B 0 = {∅} := by
    ext A
    rw [mem_sets, Finset.mem_singleton]
    constructor
    · exact fun h => Finset.card_eq_zero.mp h.1
    · intro he
      subst A
      simp [Good]
  have hi : ∀ j ≤ k, q^j ≤ j.factorial * (sets B j).card := by
    intro j
    induction j with
    | zero => simp [hbase]
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hstep := step B b hB hself hsymm j
      have hq : q ≤ Fintype.card V - b*j := by
        have hh := Nat.mul_le_mul_left b (show j ≤ k-1 by omega)
        dsimp [q]
        omega
      calc
        q^(j+1) = q^j*q := pow_succ _ _
        _ ≤ (j.factorial * (sets B j).card)*q := Nat.mul_le_mul_right _ hprev
        _ ≤ j.factorial * ((Fintype.card V-b*j)*(sets B j).card) := by
          have hh := Nat.mul_le_mul_left (j.factorial * (sets B j).card) hq
          nlinarith
        _ ≤ j.factorial * ((j+1)*(sets B (j+1)).card) := Nat.mul_le_mul_left _ hstep
        _ = (j+1).factorial * (sets B (j+1)).card := by rw [Nat.factorial_succ]; ring
  exact hi k le_rfl

end P2MProofComplexity.P2MSeparatedSetCounting
end

section
-- Inlined Solutions.P2MPseudoReductionRestriction

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPseudoReductionRestriction

open P2MBooleanDegreeSpaces

lemma ble_mono {V : Type} {k B : ℕ} (h : k≤B) : Ble V k≤Ble V B := by
  intro p hp
  exact (mem_Ble_iff B p).mpr ⟨((mem_Ble_iff k p).mp hp).1,((mem_Ble_iff k p).mp hp).2.trans h⟩

noncomputable def restricted {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) (hk : k≤B) : Ble V k →ₗ[ZMod 2] W :=
  R.comp (Submodule.inclusion (ble_mono hk))

theorem range_eq {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) (hk : k≤B) :
    LinearMap.range (restricted R k hk)=((Submodule.comap (Ble V B).subtype (Ble V k)).map R) := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨Submodule.inclusion (ble_mono hk) p,p.2,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl⟩

theorem rank_eq {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) (hk : k≤B) :
    Module.finrank (ZMod 2) (LinearMap.range (restricted R k hk))=rankLe R k := by
  rw [range_eq]
  rfl

end SemAC02.Supplement.P2MPseudoReductionRestriction
end

section
-- Inlined Solutions.P2MNaiveBooleanReduction

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MNaiveBooleanReduction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces

variable {V : Type} [Fintype V] [DecidableEq V]

def consequences (P : Set (MvPolynomial V (ZMod 2))) (B : ℕ) :
    Submodule (ZMod 2) (MvPolynomial V (ZMod 2)) where
  carrier := {p | P2MRelativePCFinite.Derivable P (Ble V B) p}
  zero_mem' := P2MRelativePCFinite.pc_zero _ _
  add_mem' := P2MRelativePCFinite.pc_add _ _
  smul_mem' := fun a _ hp => P2MRelativePCFinite.pc_smul _ _ hp a

noncomputable def reduction (P : Set (MvPolynomial V (ZMod 2))) (B : ℕ) :
    Ble V B →ₗ[ZMod 2] (Ble V B ⧸ (consequences P B).comap (Ble V B).subtype) :=
  ((consequences P B).comap (Ble V B).subtype).mkQ

theorem zero_iff (P : Set (MvPolynomial V (ZMod 2))) (B : ℕ) (p : Ble V B) :
    reduction P B p = 0 ↔ P2MRelativePCFinite.Derivable P (Ble V B) p.val :=
  Submodule.Quotient.mk_eq_zero _

theorem pseudo (P : Set (MvPolynomial V (ZMod 2))) (B : ℕ) : IsPseudoRed P (reduction P B) := by
  constructor
  · intro p hp hpB
    apply (zero_iff P B _).mpr
    have hml := ((mem_Ble_iff B p).mp hpB).1
    have hh := P2MRelativePCFinite.pc_axiom P (Ble V B) p hp (by rwa [ml_of_multilinear p hml])
    rwa [ml_of_multilinear p hml] at hh
  · intro p v hv hz
    exact (zero_iff P B _).mpr
      (P2MRelativePCFinite.pc_mul_X P (Ble V B) ((zero_iff P B p).mp hz) v hv)

theorem rank_lower (P : Set (MvPolynomial V (ZMod 2))) (B k : ℕ) (hkB : k ≤ B)
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) (hUk : U ≤ Ble V k)
    (hsep : ∀ p ∈ U, P2MRelativePCFinite.Derivable P (Ble V B) p → p = 0) :
    Module.finrank (ZMod 2) U ≤ rankLe (reduction P B) k := by
  let R := reduction P B
  let T := (Submodule.comap (Ble V B).subtype (Ble V k)).map R
  have hUB : U ≤ Ble V B := hUk.trans (P2MPseudoReductionRestriction.ble_mono hkB)
  let f : U →ₗ[ZMod 2] T :=
    { toFun := fun p => ⟨R ⟨p.val, hUB p.property⟩, ⟨⟨p.val, hUB p.property⟩, hUk p.property, rfl⟩⟩
      map_add' := by
        intro p q
        apply Subtype.ext
        change R ⟨p.val+q.val, _⟩ = R ⟨p.val, _⟩+R ⟨q.val, _⟩
        exact map_add R ⟨p.val, hUB p.property⟩ ⟨q.val, hUB q.property⟩
      map_smul' := by
        intro a p
        apply Subtype.ext
        change R ⟨a • p.val, _⟩ = a • R ⟨p.val, _⟩
        exact map_smul R a ⟨p.val, hUB p.property⟩ }
  have hf : Function.Injective f := by
    intro p q he
    have he' : R ⟨p.val, hUB p.property⟩ = R ⟨q.val, hUB q.property⟩ := congrArg Subtype.val he
    have hz : R (⟨p.val, hUB p.property⟩-⟨q.val, hUB q.property⟩) = 0 := by rw [map_sub, he', sub_self]
    have hderive := (zero_iff P B _).mp hz
    have hdiff := hsep (p.val-q.val) (U.sub_mem p.property q.property) hderive
    exact Subtype.ext (sub_eq_zero.mp hdiff)
  exact LinearMap.finrank_le_finrank_of_injective hf

end SemAC02.Supplement.P2MNaiveBooleanReduction
end

section
-- Inlined Solutions.P2MBitPHPPigeonLinearRank

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MBitPHPPigeonLinearRank

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MBitPHPPigeonLinearSeparation P2MProofComplexity

noncomputable def conflicts {m b : ℕ} (v : Fin m × Fin b) : Finset (Fin m × Fin b) :=
  Finset.univ.filter (fun w => w.1 = v.1)

theorem mem_conflicts {m b : ℕ} (v w : Fin m × Fin b) : w ∈ conflicts v ↔ w.1 = v.1 := by
  simp [conflicts]

theorem conflicts_card {m b : ℕ} (v : Fin m × Fin b) : (conflicts v).card = b := by
  have he : conflicts v = ({v.1} : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin b)) := by
    ext w
    rw [mem_conflicts,Finset.mem_product,Finset.mem_singleton]
    simp only [Finset.mem_univ,and_true]
  rw [he]
  simp

theorem good_iff {m b : ℕ} (S : Finset (Fin m × Fin b)) :
    P2MSeparatedSetCounting.Good conflicts S ↔ Set.InjOn Prod.fst (S : Set (Fin m × Fin b)) := by
  constructor
  · intro h v hv w hw he
    by_contra hn
    exact h v hv w hw hn ((mem_conflicts v w).mpr he.symm)
  · intro h v hv w hw hne hmem
    exact hne (h hv hw ((mem_conflicts v w).mp hmem).symm)

theorem count_le_dimension (m b k : ℕ) :
    (P2MSeparatedSetCounting.sets (conflicts (m:=m) (b:=b)) k).card ≤ Module.finrank (ZMod 2) (space m b k) := by
  classical
  let E := P2MSeparatedSetCounting.sets (conflicts (m:=m) (b:=b)) k
  have hmem (S : E) : xMon S.val ∈ space m b k := by
    obtain ⟨hcard,hgood⟩ := (P2MSeparatedSetCounting.mem_sets _ _ _).mp S.property
    exact Submodule.subset_span ⟨S.val,⟨hcard.le,(good_iff S.val).mp hgood⟩,rfl⟩
  let v (S : E) : space m b k := ⟨xMon S.val,hmem S⟩
  have hv : LinearIndependent (ZMod 2) v := by
    apply LinearIndependent.of_comp (space m b k).subtype
    exact xMon_linearIndependent.comp Subtype.val Subtype.val_injective
  simpa only [Fintype.card_coe] using hv.fintype_card_le_finrank

theorem power_dimension (m b k : ℕ) :
    (m*b-b*(k-1))^k ≤ k.factorial*Module.finrank (ZMod 2) (space m b k) := by
  have hcount := P2MSeparatedSetCounting.count (conflicts (m:=m) (b:=b)) b
    (fun v => (conflicts_card v).le) (fun v => (mem_conflicts v v).mpr rfl)
    (fun v w h => (mem_conflicts w v).mpr ((mem_conflicts v w).mp h).symm) k
  simp only [Fintype.card_prod,Fintype.card_fin] at hcount
  exact hcount.trans (Nat.mul_le_mul_left _ (count_le_dimension m b k))

theorem rank (m ℓ B k : ℕ) (hchoose : 2*k < 2^ℓ) (hB : 2*ℓ ≤ B)
    (hbudget : 2*(B+2) ≤ 2^ℓ) (hkB : k ≤ B) :
    (m*(ℓ+2)-(ℓ+2)*(k-1))^k ≤ k.factorial*
      rankLe (P2MNaiveBooleanReduction.reduction (P2MBitPHPPolynomialFacts.normalAxioms m (ℓ+2)) B) k := by
  have hRank := P2MNaiveBooleanReduction.rank_lower (P2MBitPHPPolynomialFacts.normalAxioms m (ℓ+2)) B k hkB
    (space m (ℓ+2) k) (space_le m (ℓ+2) k) (separation m ℓ B k hchoose hB hbudget)
  exact (power_dimension m (ℓ+2) k).trans (Nat.mul_le_mul_left _ hRank)

end SemAC02.Supplement.P2MBitPHPPigeonLinearRank
end

section
-- Inlined Solutions.P2MPigeonLinearRankRatio

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MPigeonLinearRankRatio

theorem power_exponential (n b k : ℕ) (hn : 1 ≤ n) (hbk : b*k ≤ n) :
    Real.exp ((b : ℝ)*(k : ℝ)^2/(2*n)) ≤ (1+(b : ℝ)*k/n)^k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let t : ℝ := (b : ℝ)*k/n
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hnR).mpr
    simpa only [one_mul,Nat.cast_mul] using (show ((b*k : ℕ) : ℝ) ≤ n by exact_mod_cast hbk)
  have hlog : t/2 ≤ Real.log (1+t) := by
    have hh := Real.le_log_one_add_of_nonneg ht0
    have hlow : t/2 ≤ 2*t/(t+2) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < t+2)).mpr
      nlinarith
    exact hlow.trans hh
  have he : Real.exp ((k : ℝ)*Real.log (1+t)) = (1+t)^k := by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity : (0 : ℝ) < 1+t)]
  rw [← he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have he' : (b : ℝ)*(k : ℝ)^2/(2*n) = (k : ℝ)*(t/2) := by dsimp [t]; field_simp <;> ring
  rwa [he']

theorem lower (n b k : ℕ) (hk : 1 ≤ k) (hbudget : 3*(k+2*b*k) ≤ n)
    (rank : ℝ) (hrank : ((n : ℝ)-(b : ℝ)*(k-1 : ℕ))^k/(k.factorial : ℝ) ≤ rank) :
    1/2*Real.exp ((b : ℝ)*(k : ℝ)^2/(2*n)) ≤ rank/(2*((n-2*b*k).choose k : ℝ)) := by
  let r := 2*b*k
  have hr : r ≤ n := by dsimp [r]; omega
  have hknr : k ≤ n-r := by dsimp [r]; omega
  have hn : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsub : ((n-r : ℕ) : ℝ) = (n : ℝ)-r := Nat.cast_sub hr
  have hrR : (r : ℝ) = 2*(b : ℝ)*k := by dsimp [r]; push_cast; rfl
  have hkSub : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by rw [Nat.cast_sub hk]; norm_num
  have hbase0 : 0 ≤ ((n-r : ℕ) : ℝ)*(1+(b : ℝ)*k/n) := by positivity
  have hbase : ((n-r : ℕ) : ℝ)*(1+(b : ℝ)*k/n) ≤ (n : ℝ)-(b : ℝ)*(k-1 : ℕ) := by
    have hsmall : ((n-r : ℕ) : ℝ)*((b : ℝ)*k/n) ≤ (b : ℝ)*k := by
      have hnr : ((n-r : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n r
      calc
        _ ≤ (n : ℝ)*((b : ℝ)*k/n) := mul_le_mul_of_nonneg_right hnr (by positivity)
        _ = _ := by field_simp
    rw [hsub,hkSub]
    rw [hsub] at hsmall
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    nlinarith [hrR]
  have hpow := pow_le_pow_left₀ hbase0 hbase k
  rw [mul_pow] at hpow
  have hchoose : ((n-r).choose k : ℝ) ≤ ((n-r : ℕ) : ℝ)^k/(k.factorial : ℝ) := Nat.choose_le_pow_div k (n-r)
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hcomb : ((n-r).choose k : ℝ)*(1+(b : ℝ)*k/n)^k ≤ rank := by
    calc
      _ ≤ (((n-r : ℕ) : ℝ)^k/(k.factorial : ℝ))*(1+(b : ℝ)*k/n)^k :=
        mul_le_mul_of_nonneg_right hchoose (by positivity)
      _ = (((n-r : ℕ) : ℝ)^k*(1+(b : ℝ)*k/n)^k)/(k.factorial : ℝ) := by ring
      _ ≤ ((n : ℝ)-(b : ℝ)*(k-1 : ℕ))^k/(k.factorial : ℝ) := div_le_div_of_nonneg_right hpow hfact.le
      _ ≤ rank := hrank
  have hbk : b*k ≤ n := calc
    b*k ≤ 2*(b*k) := by omega
    _ = r := by dsimp [r]; ring
    _ ≤ n := hr
  have hExp := power_exponential n b k hn hbk
  have hExpComb : ((n-r).choose k : ℝ)*Real.exp ((b : ℝ)*(k : ℝ)^2/(2*n)) ≤ rank :=
    (mul_le_mul_of_nonneg_left hExp (Nat.cast_nonneg _)).trans hcomb
  have hchoosePos : (0 : ℝ) < ((n-r).choose k : ℝ) := by exact_mod_cast Nat.choose_pos hknr
  change _ ≤ rank/(2*((n-r).choose k : ℝ))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*((n-r).choose k : ℝ))).mpr
  nlinarith

end SemAC02.Supplement.P2MPigeonLinearRankRatio
end

section
-- Inlined Solutions.P2MBooleanVariableEquivalence

set_option maxHeartbeats 2000000

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanVariableEquivalence

theorem multilinear_rename {V W : Type} (e : V ≃ W) {p : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) : IsMultilinear (rename e p) := by
  classical
  intro s hs w
  rw [support_rename_of_injective e.injective] at hs
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
  simpa only [Finsupp.mapDomain_equiv_apply] using hp t ht (e.symm w)

theorem ml_rename {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (p : MvPolynomial V (ZMod 2)) : rename e (ML p) = ML (rename e p) := by
  apply multilinear_ext (multilinear_rename e (ml_multilinear p)) (ml_multilinear _)
  intro x
  simp only [eval_rename,eval_ml]

theorem rename_mem_Ble {V W : Type} (e : V ≃ W) {k : ℕ} {p : MvPolynomial V (ZMod 2)}
    (hp : p ∈ Ble V k) : rename e p ∈ Ble W k := by
  rcases P2MBooleanDegreeSpaces.mem_Ble_iff k p |>.mp hp with ⟨hml,hdeg⟩
  exact (P2MBooleanDegreeSpaces.mem_Ble_iff k _).mpr
    ⟨multilinear_rename e hml,(totalDegree_rename_le e p).trans hdeg⟩

theorem map_Ble {V W : Type} (e : V ≃ W) (k : ℕ) :
    (Ble V k).map (rename e).toLinearMap = Ble W k := by
  apply le_antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact rename_mem_Ble e hp
  · intro p hp
    refine ⟨rename e.symm p,rename_mem_Ble e.symm hp,?_⟩
    exact (renameEquiv (ZMod 2) e).apply_symm_apply p

theorem mulML_rename {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f p : MvPolynomial V (ZMod 2)) : rename e (mulML f p) = mulML (rename e f) (rename e p) := by
  simp only [mulML,LinearMap.comp_apply,LinearMap.mulLeft_apply]
  rw [ml_rename,map_mul]

theorem rename_mem_multSpace {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) {p : MvPolynomial V (ZMod 2)}
    (hp : p ∈ multSpace f k) : rename e p ∈ multSpace (rename e f) k := by
  obtain ⟨q,hq,rfl⟩ := hp
  exact ⟨rename e q,rename_mem_Ble e hq,(mulML_rename e f q).symm⟩

theorem map_multSpace {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) :
    (multSpace f k).map (rename e).toLinearMap = multSpace (rename e f) k := by
  apply le_antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact rename_mem_multSpace e f k hp
  · intro p hp
    have hf : rename e.symm (rename e f) = f := (renameEquiv (ZMod 2) e).symm_apply_apply f
    refine ⟨rename e.symm p,?_,?_⟩
    · have hh := rename_mem_multSpace e.symm (rename e f) k hp
      rw [hf] at hh
      exact hh
    · exact (renameEquiv (ZMod 2) e).apply_symm_apply p

theorem finrank_map {V W : Type} (e : V ≃ W)
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) :
    Module.finrank (ZMod 2) (U.map (rename e).toLinearMap) = Module.finrank (ZMod 2) U := by
  exact (Submodule.equivMapOfInjective (rename e).toLinearMap
    (renameEquiv (ZMod 2) e).injective U).finrank_eq.symm

noncomputable def spaceEquiv {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) :
    multSpace f k ≃ₗ[ZMod 2] multSpace (rename e f) k where
  toFun u := ⟨rename e u.val,rename_mem_multSpace e f k u.property⟩
  invFun u := ⟨rename e.symm u.val,by
    have h := rename_mem_multSpace e.symm (rename e f) k u.property
    have hf : rename e.symm (rename e f) = f := (renameEquiv (ZMod 2) e).symm_apply_apply f
    rw [hf] at h
    exact h⟩
  left_inv u := Subtype.ext ((renameEquiv (ZMod 2) e).symm_apply_apply u.val)
  right_inv u := Subtype.ext ((renameEquiv (ZMod 2) e).apply_symm_apply u.val)
  map_add' u v := Subtype.ext (map_add (rename e) u.val v.val)
  map_smul' a u := Subtype.ext ((rename e).toLinearMap.map_smul a u.val)

@[simp] theorem spaceEquiv_val {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) (u : multSpace f k) :
    (spaceEquiv e f k u).val = rename e u.val := rfl

@[simp] theorem spaceEquiv_symm_val {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) (u : multSpace (rename e f) k) :
    ((spaceEquiv e f k).symm u).val = rename e.symm u.val := rfl

end SemAC02.P2MBooleanVariableEquivalence
end

section
-- Inlined Solutions.P2MBooleanPseudoReductionEquivalence

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MBooleanPseudoReductionEquivalence

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanVariableEquivalence

variable {V U W : Type} [Finite V] [Finite U] [AddCommGroup W] [Module (ZMod 2) W]

noncomputable def degreeEquiv (e : V ≃ U) (B : ℕ) : Ble V B ≃ₗ[ZMod 2] Ble U B where
  toFun p := ⟨rename e p.val, rename_mem_Ble e p.property⟩
  invFun p := ⟨rename e.symm p.val, rename_mem_Ble e.symm p.property⟩
  left_inv p := Subtype.ext ((renameEquiv (ZMod 2) e).symm_apply_apply p.val)
  right_inv p := Subtype.ext ((renameEquiv (ZMod 2) e).apply_symm_apply p.val)
  map_add' p q := Subtype.ext (map_add (rename e) p.val q.val)
  map_smul' a p := Subtype.ext ((rename e).toLinearMap.map_smul a p.val)

noncomputable def reduction (e : V ≃ U) {B : ℕ} (R : Ble V B →ₗ[ZMod 2] W) : Ble U B →ₗ[ZMod 2] W :=
  R.comp (degreeEquiv e B).symm.toLinearMap

theorem pseudo (e : V ≃ U) {B : ℕ} (F : Set (MvPolynomial V (ZMod 2)))
    (R : Ble V B →ₗ[ZMod 2] W) (hR : IsPseudoRed F R) :
    IsPseudoRed (rename e '' F) (reduction e R) := by
  constructor
  · rintro p ⟨q, hq, rfl⟩ hp
    have he : rename e.symm (rename e q) = q := (renameEquiv (ZMod 2) e).symm_apply_apply q
    have hqB := rename_mem_Ble e.symm hp
    rw [he] at hqB
    have hval : (degreeEquiv e B).symm ⟨rename e q, hp⟩ = ⟨q, hqB⟩ := Subtype.ext he
    change R ((degreeEquiv e B).symm _) = 0
    rw [hval]
    exact hR.1 q hq hqB
  · intro p v hmem hz
    have he : rename e.symm (ML (X v*p.val)) = ML (X (e.symm v)*rename e.symm p.val) := by
      rw [ml_rename, map_mul, rename_X]
    have hmem' := rename_mem_Ble e.symm hmem
    rw [he] at hmem'
    have hh := hR.2 ((degreeEquiv e B).symm p) (e.symm v) hmem' hz
    change R ((degreeEquiv e B).symm _) = 0
    convert hh using 1
    exact congrArg R (Subtype.ext he)

theorem rank_eq (e : V ≃ U) {B : ℕ} (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) :
    rankLe (reduction e R) k = rankLe R k := by
  have heq : (Submodule.comap (Ble U B).subtype (Ble U k)).map (reduction e R) =
      (Submodule.comap (Ble V B).subtype (Ble V k)).map R := by
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(degreeEquiv e B).symm p, rename_mem_Ble e.symm hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨degreeEquiv e B p, rename_mem_Ble e hp, ?_⟩
      change R ((degreeEquiv e B).symm (degreeEquiv e B p)) = R p
      rw [LinearEquiv.symm_apply_apply]
  unfold rankLe
  rw [heq]

end SemAC02.Supplement.P2MBooleanPseudoReductionEquivalence
end

section
-- Inlined Solutions.P2MProofTopFunctions

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MProofTopFunctions

open ACirc Classical

noncomputable def pool {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    Finset (Ω → F) :=
  ((π.flatMap topTerms).map (fun t => fun x : Ω => cval t x.1)).toFinset.filter (fun g => g≠0)

theorem mem_pool {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) (g : Ω → F) :
    g∈pool Ω π ↔ g≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, (fun x : Ω => cval t x.1)=g := by
  constructor
  · intro hp
    have hn := (Finset.mem_filter.mp hp).2
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
    obtain ⟨c,hc,ht⟩ := List.mem_flatMap.mp ht
    exact ⟨hn,c,hc,t,ht,he⟩
  · rintro ⟨hn,c,hc,t,ht,he⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨t,List.mem_flatMap.mpr ⟨c,hc,ht⟩,he⟩),hn⟩

theorem card_eq_topS {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    (pool Ω π).card=topS Ω π := by
  have he : {g : Ω → F | g≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, g=fun x => cval t x.1}=
      (↑(pool Ω π) : Set (Ω → F)) := by
    ext g
    rw [Finset.mem_coe,mem_pool]
    constructor
    · rintro ⟨hn,c,hc,t,ht,he⟩; exact ⟨hn,c,hc,t,ht,he.symm⟩
    · rintro ⟨hn,c,hc,t,ht,he⟩; exact ⟨hn,c,hc,t,ht,he.symm⟩
  unfold topS
  rw [he,Set.ncard_coe_finset]

theorem projection_bound {F V U : Type} [CommRing F]
    (η : (U → Bool) → (V → Bool)) (M τ : ACirc F V → ACirc F U)
    (π : List (ACirc F V))
    (hterms : ∀ c, topTerms (M c)=(topTerms c).map τ)
    (hval : ∀ c∈π, ∀ t∈topTerms c, ∀ y, cval (τ t) y=cval t (η y)) :
    topS Set.univ (π.map M) ≤ topS Set.univ π := by
  let pull (f : ↥(Set.univ : Set (V → Bool)) → F) : ↥(Set.univ : Set (U → Bool)) → F :=
    fun y => f ⟨η y.1,Set.mem_univ _⟩
  have hsub : pool Set.univ (π.map M)⊆(pool Set.univ π).image pull := by
    intro g hg
    obtain ⟨hn,c',hc',t',ht',he⟩ := (mem_pool Set.univ (π.map M) g).mp hg
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hc'
    rw [hterms c] at ht'
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ht'
    let f : ↥(Set.univ : Set (V → Bool)) → F := fun x => cval t x.1
    have hpull : pull f=g := by
      rw [←he]
      funext y
      exact (hval c hc t ht y.1).symm
    have hf : f≠0 := by
      intro hz
      apply hn
      rw [←hpull,hz]
      rfl
    exact Finset.mem_image.mpr ⟨f,(mem_pool Set.univ π f).mpr ⟨hf,c,hc,t,ht,rfl⟩,hpull⟩
  rw [←card_eq_topS,←card_eq_topS]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

end SemAC02.Supplement.P2MProofTopFunctions
end

section
-- Inlined Solutions.P2MArithmeticLeafSubstitution

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MArithmeticLeafSubstitution

open ACirc P2MArithmeticCircuitBasics

def liftPoint {V U : Type} (f : V → U ⊕ Bool) (y : U → Bool) : V → Bool :=
  fun i => (f i).elim y id


noncomputable def circuit {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) : ACirc F V → ACirc F U
  | .var i => (f i).elim ACirc.var (fun b => ACirc.const (if b then 1 else 0))
  | .const a => .const a
  | .sum ps => .sum (ps.attach.map (fun p => (p.1.1,circuit f p.1.2)))
  | .prod cs => .prod (cs.attach.map (fun c => circuit f c.1))
termination_by c => c
decreasing_by
  all_goals first
    | (obtain ⟨⟨a,b⟩,hp⟩ := p; have h := List.sizeOf_lt_of_mem hp; simp at h ⊢; omega)
    | (obtain ⟨c,hc⟩ := c; have h := List.sizeOf_lt_of_mem hc; simp at h ⊢; omega)

theorem circuit_sum {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (ps : List (F×ACirc F V)) :
    circuit f (.sum ps)=.sum (ps.map (fun p => (p.1,circuit f p.2))) := by
  rw [circuit,List.attach_map_val (f:=fun p : F×ACirc F V => (p.1,circuit f p.2))]

theorem circuit_prod {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (cs : List (ACirc F V)) :
    circuit f (.prod cs)=.prod (cs.map (circuit f)) := by
  rw [circuit,List.attach_map_val]

theorem value {F V U : Type} [CommRing F] (f : V → U ⊕ Bool) (c : ACirc F V) (y : U → Bool) :
    cval (circuit f c) y=cval c (liftPoint f y) := by
  cases c with
  | var i => cases hi : f i <;> simp [circuit,cval,polyFn,toPoly,boolPt,liftPoint,hi]
  | const a => simp [circuit,cval,polyFn,toPoly]
  | sum ps =>
    rw [circuit_sum,cval_sum,cval_sum,List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    dsimp only [Function.comp_def]
    rw [value f p.2 y]
  | prod cs =>
    rw [circuit_prod,cval_prod,cval_prod,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact value f c y
termination_by c
decreasing_by
  all_goals first
    | (obtain ⟨a,b⟩ := p; have h := List.sizeOf_lt_of_mem hp; simp at h ⊢; omega)
    | (have h := List.sizeOf_lt_of_mem hc; simp at h ⊢; omega)

theorem leaf {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (c : ACirc F V) (hc : IsLeaf c) : IsLeaf (circuit f c) := by
  cases c <;> simp_all [IsLeaf,circuit]
  case var i => cases f i <;> simp [IsLeaf]

theorem sum_of {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (P : ACirc F V → Prop) (Q : ACirc F U → Prop)
    (hPQ : ∀ c, P c → Q (circuit f c)) (c : ACirc F V) (hc : IsSumOf P c) : IsSumOf Q (circuit f c) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    rw [circuit_sum]
    rintro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hPQ q.2 (hc q hq)

theorem prod_of {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (P : ACirc F V → Prop) (Q : ACirc F U → Prop)
    (hPQ : ∀ c, P c → Q (circuit f c)) (c : ACirc F V) (hc : IsProdOf P c) : IsProdOf Q (circuit f c) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | sum ps => exact hc.elim
  | prod cs =>
    rw [circuit_prod]
    intro d hd
    obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hd
    exact hPQ c (hc c hc')

theorem monomial {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (w : ℕ∞) (c : ACirc F V) (hc : IsMonGate w c) :
    IsMonGate w (circuit f c) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | sum ps => exact hc.elim
  | prod cs =>
    rw [circuit_prod]
    constructor
    · simpa only [List.length_map] using hc.1
    · intro d hd
      obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hd
      exact leaf f c (hc.2 c hc')

theorem spsp {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (w : ℕ∞) (c : ACirc F V) (hc : IsSPSP w c) :
    IsSPSP w (circuit f c) :=
  sum_of f _ _ (prod_of f _ _ (sum_of f _ _ (monomial f w))) c hc

theorem top_terms {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (c : ACirc F V) :
    topTerms (circuit f c)=(topTerms c).map (circuit f) := by
  cases c <;> simp [circuit,circuit_sum,circuit_prod,topTerms,List.map_map,Function.comp_def]
  case var i => cases f i <;> rfl

theorem sps {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool)
    (c : ACirc F V) (hc : IsSPS c) : IsSPS (circuit f c) :=
  sum_of f _ _ (prod_of f _ _ (sum_of f _ _ (leaf f))) c hc

theorem top_bound {F V U : Type} [CommRing F] (f : V → U ⊕ Bool)
    (π : List (ACirc F V)) :
    topS Set.univ (π.map (circuit f)) ≤ topS Set.univ π := by
  apply P2MProofTopFunctions.projection_bound (liftPoint f) (circuit f) (circuit f) π (top_terms f)
  intro c hc t ht y
  exact value f t y

end SemAC02.Supplement.P2MArithmeticLeafSubstitution
end

section
-- Inlined Solutions.P2MSemanticLeafSubstitution

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSemanticLeafSubstitution

open ACirc P2MArithmeticLeafSubstitution

theorem refutation {F V U : Type} [Field F] (f : V → U ⊕ Bool)
    (A : Set ((V → Bool) → F)) (B : Set ((U → Bool) → F))
    (P : ACirc F V → Prop) (Q : ACirc F U → Prop)
    (hPQ : ∀ c, P c → Q (circuit f c))
    (hinput : ∀ a ∈ A, (∃ b ∈ B, ∀ y, b y = a (liftPoint f y)) ∨
      (∀ y, a (liftPoint f y) = 0))
    (π : List (ACirc F V)) (hπ : IsSemPCRef P Set.univ A π) :
    IsSemPCRef Q Set.univ B (π.map (circuit f)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact hPQ a (hπ.1 a ha)
  · intro i hi
    have hi' : i < π.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map]
    rcases hπ.2.1 i hi' with ⟨a, ha, he⟩ | he | ⟨j, l, hj, hl, he⟩
    · rcases hinput a ha with ⟨b, hb, hval⟩ | hzero
      · left
        refine ⟨b, hb, ?_⟩
        intro y hy
        rw [value, he _ (Set.mem_univ _), hval y]
      · right; left
        intro y hy
        rw [value, he _ (Set.mem_univ _), hzero y]
    · right; left
      intro y hy
      rw [value]
      exact he _ (Set.mem_univ _)
    · right; right
      refine ⟨j, l, hj, hl, ?_⟩
      intro y hy hp hq
      rw [value] at hp hq ⊢
      exact he _ (Set.mem_univ _) hp hq
  · obtain ⟨c, hc, hval⟩ := hπ.2.2
    refine ⟨circuit f c, ?_, ?_⟩
    · rw [List.getLast?_map, hc]; rfl
    · intro y hy
      rw [value]
      exact hval _ (Set.mem_univ _)

end SemAC02.Supplement.P2MSemanticLeafSubstitution
end

section
-- Inlined Solutions.P2MSPSFiniteSizeBound

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MSPSFiniteSizeBound

open MvPolynomial ACirc AC02Frege AC02Frege.P2MBooleanAlgebra

variable {V U : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem refutation (f : V → U) (F : Set (MvPolynomial V (ZMod 2)))
    (π : List (ACirc (ZMod 2) V)) (hπ : IsSemPCRef IsSPS Set.univ (polyAx F) π) :
    IsSemPCRef IsSPS Set.univ (polyAx (rename f '' F))
      (π.map (P2MArithmeticLeafSubstitution.circuit (fun v => Sum.inl (f v)))) := by
  apply P2MSemanticLeafSubstitution.refutation (fun v => Sum.inl (f v)) _ _ _ _
    (P2MArithmeticLeafSubstitution.sps _) _ π hπ
  rintro a ⟨p, hp, rfl⟩
  left
  refine ⟨polyFn (rename f p), ⟨rename f p, ⟨p, hp, rfl⟩, rfl⟩, ?_⟩
  intro y
  simp only [polyFn, eval_rename]
  rfl

theorem lower (F : Set (MvPolynomial V (ZMod 2))) (d₀ : ℕ)
    (hF : ∀ f ∈ F, IsMultilinear f ∧ f.totalDegree ≤ d₀)
    (k r : ℕ) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) (hr : 1 ≤ r) (hrn : r ≤ Fintype.card V)
    (hB : 3*(k+max d₀ r) ≤ Fintype.card V)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V (3*(k+max d₀ r)) →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (π : List (ACirc (ZMod 2) V)) (hπ : IsSemPCRef IsSPS Set.univ (polyAx F) π) :
    (rankLe R k : ℝ)/(2*((Fintype.card V-r).choose k : ℝ)) ≤ topS Set.univ π := by
  let e := Fintype.equivFin V
  let R' := P2MBooleanPseudoReductionEquivalence.reduction e R
  let π' := π.map (P2MArithmeticLeafSubstitution.circuit (fun v => Sum.inl (e v)))
  have hF' : ∀ p ∈ rename e '' F, IsMultilinear p ∧ p.totalDegree ≤ d₀ := by
    rintro p ⟨q, hq, rfl⟩
    exact ⟨P2MBooleanVariableEquivalence.multilinear_rename e (hF q hq).1,
      (totalDegree_rename_le e q).trans (hF q hq).2⟩
  have hh := theorem_4_4_sps_size_bound (rename e '' F) d₀ hF' k r hk hkn hr hrn hB R'
    (P2MBooleanPseudoReductionEquivalence.pseudo e F R hR) π' (refutation e F π hπ)
  rw [P2MBooleanPseudoReductionEquivalence.rank_eq] at hh
  exact hh.trans (by exact_mod_cast P2MArithmeticLeafSubstitution.top_bound (fun v => Sum.inl (e v)) π)

end SemAC02.Supplement.P2MSPSFiniteSizeBound
end

section
-- Inlined Solutions.P2MBitPHPFiniteSizeBound

set_option maxHeartbeats 3500000

namespace SemAC02.Supplement.P2MBitPHPFiniteSizeBound

open MvPolynomial ACirc AC02Frege

theorem lower (m ℓ k : ℕ) (hk : 1 ≤ k)
    (hchoose : 2*k < 2^ℓ)
    (hHoleBudget : 2*(3*(k+2*(ℓ+2)*k)+2) ≤ 2^ℓ)
    (hAmbientBudget : 3*(k+2*(ℓ+2)*k) ≤ m*(ℓ+2))
    (π : List (ACirc (ZMod 2) (Fin m × Fin (ℓ+2))))
    (hπ : IsSemPCRef IsSPS Set.univ (polyAx (bphp m (ℓ+2))) π) :
    1/2*Real.exp ((k : ℝ)^2/(2*m)) ≤ topS Set.univ π := by
  let b := ℓ+2
  let r := 2*b*k
  let B := 3*(k+max (2*b) r)
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hr : 1 ≤ r := by dsimp [r]; nlinarith
  have hd : 2*b ≤ r := by dsimp [r]; nlinarith
  have hmax : max (2*b) r = r := max_eq_right hd
  have hB : 2*ℓ ≤ B := by dsimp only [B]; rw [hmax]; dsimp [r,b]; nlinarith
  have hkB : k ≤ B := by dsimp [B]; omega
  let F := P2MBitPHPPolynomialFacts.normalAxioms m b
  let R := P2MNaiveBooleanReduction.reduction F B
  have hHoleB : 2*(B+2) ≤ 2^ℓ := by simpa only [B,hmax,r,b] using hHoleBudget
  have hRankNat := P2MBitPHPPigeonLinearRank.rank m ℓ B k hchoose hB hHoleB hkB
  have hbase : b*(k-1) ≤ m*b := by
    have hrN : r ≤ m*b := by change 3*(k+r) ≤ m*b at hAmbientBudget; omega
    have hh : b*(k-1) ≤ 2*b*k := by nlinarith [Nat.sub_le k 1]
    exact hh.trans hrN
  have hRank : ((m*b : ℕ) - b*(k-1) : ℕ)^k ≤ k.factorial*rankLe R k := hRankNat
  have hRankR : (((m*b : ℕ) : ℝ)-(b : ℝ)*(k-1 : ℕ))^k/(k.factorial : ℝ) ≤ (rankLe R k : ℝ) := by
    apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos k : (0 : ℝ) < k.factorial)).mpr
    have hh : (((m*b-b*(k-1) : ℕ)) : ℝ)^k ≤ (k.factorial : ℝ)*(rankLe R k : ℝ) := by exact_mod_cast hRank
    rw [Nat.cast_sub hbase,Nat.cast_mul,Nat.cast_mul] at hh
    simpa only [Nat.cast_mul,mul_comm] using hh
  have hRatio := P2MPigeonLinearRankRatio.lower (m*b) b k hk hAmbientBudget (rankLe R k) hRankR
  have hF : ∀ p ∈ F, IsMultilinear p ∧ p.totalDegree ≤ 2*b := P2MBitPHPPolynomialFacts.normal_degree
  have hπF : IsSemPCRef IsSPS Set.univ (polyAx F) π := by
    dsimp only [F]
    rwa [P2MBitPHPPolynomialFacts.normal_polyAx]
  have hSize := P2MSPSFiniteSizeBound.lower F (2*b) hF k r hk (by
      simp only [Fintype.card_prod,Fintype.card_fin]
      change 3*(k+r) ≤ m*b at hAmbientBudget
      omega) hr (by
      simp only [Fintype.card_prod,Fintype.card_fin]
      change 3*(k+r) ≤ m*b at hAmbientBudget
      omega) (by
      simp only [Fintype.card_prod,Fintype.card_fin,max_eq_right hd]
      exact hAmbientBudget)
      R (P2MNaiveBooleanReduction.pseudo F B) π hπF
  have hExp : (b : ℝ)*(k : ℝ)^2/(2*(m*b : ℕ)) = (k : ℝ)^2/(2*m) := by
    have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    push_cast
    field_simp
    <;> ring
  rw [hExp] at hRatio
  exact hRatio.trans (by simpa only [Fintype.card_prod,Fintype.card_fin] using hSize)

end SemAC02.Supplement.P2MBitPHPFiniteSizeBound
end

section
-- Inlined Solutions.P2MSPSMinimalSize

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MSPSMinimalSize

open ACirc P2MArithmeticCircuitBasics Module

noncomputable def value {V : Type} (c : ACirc (ZMod 2) V) : ↥(Set.univ : Set (V → Bool)) → ZMod 2 :=
  fun x => cval c x.val

noncomputable def span {V : Type} (π : List (ACirc (ZMod 2) V)) :
    Submodule (ZMod 2) (↥(Set.univ : Set (V → Bool)) → ZMod 2) :=
  Submodule.span (ZMod 2) (P2MProofTopFunctions.pool Set.univ π : Set _)

theorem line_mem {V : Type} (π : List (ACirc (ZMod 2) V)) (c : ACirc (ZMod 2) V)
    (hc : c ∈ π) (hSPS : IsSPS c) : value c ∈ span π := by
  classical
  cases c with
  | var v => exact hSPS.elim
  | const a => exact hSPS.elim
  | prod cs => exact hSPS.elim
  | sum ps =>
    have hval : value (.sum ps) = (ps.map (fun p => p.1 • value p.2)).sum := by
      funext x
      change cval (.sum ps) x.val =
        (Pi.evalRingHom (fun _ : ↥(Set.univ : Set (V → Bool)) => ZMod 2) x)
          ((ps.map (fun p => p.1 • value p.2)).sum)
      rw [map_list_sum]
      simp only [value,cval_sum,List.map_map,Function.comp_def,Pi.evalRingHom_apply,Pi.smul_apply,smul_eq_mul]
    rw [hval]
    apply (span π).list_sum_mem
    intro f hf
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hf
    apply (span π).smul_mem
    by_cases hz : value p.2 = 0
    · rw [hz]
      exact (span π).zero_mem
    · apply Submodule.subset_span
      exact (P2MProofTopFunctions.mem_pool Set.univ π (value p.2)).mpr
        ⟨hz,.sum ps,hc,p.2,List.mem_map.mpr ⟨p,hp,rfl⟩,rfl⟩

theorem constant_lines_of_small_size {V : Type} [Fintype V]
    (π : List (ACirc (ZMod 2) V)) (hSPS : ∀ c ∈ π, IsSPS c)
    (hsize : topS Set.univ π ≤ 1)
    (hLast : ∃ c ∈ π, ∀ x : V → Bool, cval c x = 1) :
    ∀ c ∈ π, ∃ a : ZMod 2, ∀ x : V → Bool, cval c x = a := by
  classical
  let E := P2MProofTopFunctions.pool Set.univ π
  let W := span π
  have hdim : finrank (ZMod 2) W ≤ 1 := by
    have hh := finrank_span_le_card (R:=ZMod 2) (↑E : Set (↥(Set.univ : Set (V → Bool)) → ZMod 2))
    have hc : E.card ≤ 1 := by rwa [P2MProofTopFunctions.card_eq_topS]
    have hE : (↑E : Set (↥(Set.univ : Set (V → Bool)) → ZMod 2)).toFinset = E := by ext f; simp
    rw [hE] at hh
    exact hh.trans hc
  obtain ⟨c,hc,hOne⟩ := hLast
  have hvalOne : value c = 1 := by funext x; exact hOne x.val
  have hOneW : (1 : ↥(Set.univ : Set (V → Bool)) → ZMod 2) ∈ W := by
    rw [← hvalOne]
    exact line_mem π c hc (hSPS c hc)
  have hnonzero : (1 : ↥(Set.univ : Set (V → Bool)) → ZMod 2) ≠ 0 := by
    intro he
    have hh := congrFun he ⟨fun _ => false,Set.mem_univ _⟩
    exact one_ne_zero hh
  have hpos : 0 < finrank (ZMod 2) W := Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨1,hOneW⟩,by intro he; exact hnonzero (congrArg Subtype.val he)⟩
  have hW : W = Submodule.span (ZMod 2) {1} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (by omega) hOneW hnonzero
  intro d hd
  have hmem : value d ∈ Submodule.span (ZMod 2) {1} := by rw [← hW]; exact line_mem π d hd (hSPS d hd)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨a,?_⟩
  intro x
  have hh := congrFun ha (⟨x,Set.mem_univ x⟩ : ↥(Set.univ : Set (V → Bool)))
  simpa only [value,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one] using hh.symm

end SemAC02.Supplement.P2MSPSMinimalSize
end

section
-- Inlined Solutions.P2MBitPHPSemanticObstruction

set_option maxHeartbeats 4000000

namespace P2MProofComplexity.P2MBitPHPSemanticObstruction

open P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDancePolynomials P2MPigeonDanceFiniteOrder
open SemAC02.Supplement P2MBitPHPMatchingDecoding

theorem semantic_step (m n ℓ D K : ℕ) (addr : Positive n ≃ (Fin ℓ → Bool))
    (hK : 2 ≤ K) (hbudget : 2*K ≤ n) (hDK : 3*D ≤ K)
    (f g h : ACirc (ZMod 2) (Fin m × Fin ℓ))
    (hfD : fnDeg (cval f) ≤ D) (hgD : fnDeg (cval g) ≤ D) (hhD : fnDeg (cval h) ≤ D)
    (hf : (fun B => cval f (decoded addr B)) ∈ P2MPigeonDanceConsequences.span (suffix m 0) K)
    (hg : (fun B => cval g (decoded addr B)) ∈ P2MPigeonDanceConsequences.span (suffix m 0) K)
    (hsem : ∀ x : Fin m × Fin ℓ → Bool, cval f x = 0 → cval g x = 0 → cval h x = 0) :
    (fun B => cval h (decoded addr B)) ∈ P2MPigeonDanceConsequences.span (suffix m 0) K := by
  let F : Placements (Fin m) (Positive n) → ZMod 2 := fun B => cval f (decoded addr B)
  let G : Placements (Fin m) (Positive n) → ZMod 2 := fun B => cval g (decoded addr B)
  let H : Placements (Fin m) (Positive n) → ZMod 2 := fun B => cval h (decoded addr B)
  have hF : F ∈ space D := space_mono hfD (circuit_mem addr f)
  have hG : G ∈ space D := space_mono hgD (circuit_mem addr g)
  have hH : H ∈ space D := space_mono hhD (circuit_mem addr h)
  have hOneG : 1+G ∈ space D := (space D).add_mem (one_mem D) hG
  have hCoeff : H*(1+G) ∈ space (2*D) := by
    simpa only [two_mul] using mul_mem hH hOneG
  have hProd1 := P2MPigeonDanceWeakClosure.mul m n K hK hbudget F (H*(1+G)) hf D (2*D) hF hCoeff (by omega)
  have hProd2 := P2MPigeonDanceWeakClosure.mul m n K hK hbudget G H hg D D hG hH (by omega)
  have hid : H = F*(H*(1+G))+G*H := by
    funext B
    change H B = F B*(H B*(1+G B))+G B*H B
    rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (F B) with hF | hF <;>
      rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (G B) with hG | hG
    · have hH : H B = 0 := hsem (decoded addr B) hF hG
      simp [hF, hG, hH]
    all_goals simp [hF, hG, CharTwo.add_self_eq_zero]
  change H ∈ P2MPigeonDanceConsequences.span (suffix m 0) K
  rw [hid]
  exact (P2MPigeonDanceConsequences.span (suffix m 0) K).add_mem hProd1 hProd2

theorem no_refutation (m n ℓ D : ℕ) (addr : Positive n ≃ (Fin ℓ → Bool))
    (hn : 4 ≤ n) (hdegree : 6*D ≤ n)
    (π : List (ACirc (ZMod 2) (Fin m × Fin ℓ)))
    (hπ : IsSemPCRef (fun _ => True) Set.univ (polyAx (bphp m ℓ)) π)
    (hD : ∀ c ∈ π, fnDeg (cval c) ≤ D) : False := by
  classical
  let K := max 2 (3*D)
  have hK : 2 ≤ K := le_max_left _ _
  have hDK : 3*D ≤ K := le_max_right _ _
  have hbudget : 2*K ≤ n := by dsimp [K]; omega
  have hall : ∀ k (hk : k < π.length),
      (fun B => cval π[k] (decoded addr B)) ∈ P2MPigeonDanceConsequences.span (suffix m 0) K := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ.2.1 k hk with ha | hz | hs
      · obtain ⟨a, ha, he⟩ := ha
        obtain ⟨p, hp, rfl⟩ := ha
        obtain ⟨u,v,a,huv,rfl⟩ := hp
        have hEq : (fun B => cval π[k] (decoded addr B)) =
            (fun B => polyFn (deltaA u a*deltaA v a) (decoded addr B)) := by
          funext B
          exact he _ (Set.mem_univ _)
        rw [hEq]
        exact P2MBitPHPMatchingAxioms.axiom_mem addr K hK hbudget u v huv a
      · have hEq : (fun B => cval π[k] (decoded addr B)) = 0 := by
          funext B
          exact hz _ (Set.mem_univ _)
        rw [hEq]
        exact (P2MPigeonDanceConsequences.span (suffix m 0) K).zero_mem
      · obtain ⟨i,j,hi,hj,hs⟩ := hs
        exact semantic_step m n ℓ D K addr hK hbudget hDK π[i] π[j] π[k]
          (hD _ (List.getElem_mem (hi.trans hk))) (hD _ (List.getElem_mem (hj.trans hk)))
          (hD _ (List.getElem_mem hk)) (ih i hi (hi.trans hk)) (ih j hj (hj.trans hk))
          (fun x => hs x (Set.mem_univ x))
  obtain ⟨c,hLast,hOne⟩ := hπ.2.2
  have hc : c ∈ π := List.mem_of_getLast? hLast
  obtain ⟨k,hk,hck⟩ := List.mem_iff_getElem.mp hc
  have hOut := hall k hk
  have hEq : (fun B => cval π[k] (decoded addr B)) = 1 := by
    funext B
    rw [hck]
    exact hOne _ (Set.mem_univ _)
  rw [hEq] at hOut
  exact P2MPigeonDanceConsequences.one_not_mem m n K hbudget hOut

end P2MProofComplexity.P2MBitPHPSemanticObstruction
end

section
-- Inlined Solutions.P2MBitPHPDegreeLowerBound

set_option maxHeartbeats 4000000

namespace SemAC02.Supplement.P2MBitPHPDegreeLowerBound

open P2MProofComplexity P2MProofComplexity.P2MPigeonDancePolynomials

noncomputable def addresses (ℓ : ℕ) : Positive (2^ℓ) ≃ (Fin ℓ → Bool) :=
  Fintype.equivOfCardEq (by rw [P2MPigeonDanceUnusedHole.positive_card]; simp)

theorem full :
    ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∀ m : ℕ, 2 ^ ℓ < m →
      ∀ π : List (ACirc (ZMod 2) (Fin m × Fin ℓ)),
        IsSemPCRef (fun _ => True) Set.univ (polyAx (bphp m ℓ)) π →
        ∃ c ∈ π, ((2 : ℝ) ^ ℓ) / 6 ≤ (fnDeg (cval c) : ℝ) := by
  classical
  refine ⟨2, ?_⟩
  intro ℓ hℓ m hm π hπ
  by_contra h
  push_neg at h
  obtain ⟨c,hLast,hOne⟩ := hπ.2.2
  have hc : c ∈ π := List.mem_of_getLast? hLast
  let D := π.toFinset.sup (fun c => fnDeg (cval c))
  have hD : ∀ c ∈ π, fnDeg (cval c) ≤ D := by
    intro c hc
    exact Finset.le_sup (f:=fun c => fnDeg (cval c)) (List.mem_toFinset.mpr hc)
  have hnonempty : π.toFinset.Nonempty := ⟨c,List.mem_toFinset.mpr hc⟩
  obtain ⟨c',hc',hDc⟩ := Finset.exists_mem_eq_sup π.toFinset hnonempty (fun c => fnDeg (cval c))
  have hReal : (D : ℝ) < (2:ℝ)^ℓ/6 := by
    change ((π.toFinset.sup (fun c => fnDeg (cval c)) : ℕ) : ℝ) < _
    rw [hDc]
    exact h c' (List.mem_toFinset.mp hc')
  have hbudget : 6*D ≤ 2^ℓ := by
    have hh : (6:ℝ)*D < (2:ℝ)^ℓ := by linarith
    have hhNat : 6*D < 2^ℓ := by exact_mod_cast hh
    omega
  have hn : 4 ≤ 2^ℓ := calc
    4 = 2^2 := by norm_num
    _ ≤ 2^ℓ := Nat.pow_le_pow_right (by omega) hℓ
  exact P2MBitPHPSemanticObstruction.no_refutation m (2^ℓ) ℓ D (addresses ℓ) hn hbudget π hπ hD

end SemAC02.Supplement.P2MBitPHPDegreeLowerBound
end

section
-- Inlined Solutions.P2MBitPHPMinimalSize

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MBitPHPMinimalSize

open MvPolynomial ACirc P2MProofComplexity

theorem constant_degree {V : Type} (f : (V → Bool) → ZMod 2) (a : ZMod 2)
    (he : ∀ x, f x = a) : fnDeg f ≤ 0 := by
  apply Nat.sInf_le
  refine ⟨C a,by simp,?_⟩
  funext x
  simpa only [polyFn,eval_C] using (he x).symm

theorem two_le (m b : ℕ) (hb : 2 ≤ b) (π : List (ACirc (ZMod 2) (Fin m × Fin b)))
    (hπ : IsSemPCRef IsSPS Set.univ (polyAx (bphp m b)) π) : 2 ≤ topS Set.univ π := by
  classical
  by_contra h
  have hsize : topS Set.univ π ≤ 1 := by omega
  obtain ⟨c,hLast,hOne⟩ := hπ.2.2
  have hconst := P2MSPSMinimalSize.constant_lines_of_small_size π hπ.1 hsize
    ⟨c,List.mem_of_getLast? hLast,fun x => hOne x (Set.mem_univ x)⟩
  have hD : ∀ c ∈ π, fnDeg (cval c) ≤ 0 := by
    intro c hc
    obtain ⟨a,ha⟩ := hconst c hc
    exact constant_degree (cval c) a ha
  have hn : 4 ≤ 2^b := calc
    4 = 2^2 := by norm_num
    _ ≤ 2^b := Nat.pow_le_pow_right (by omega) hb
  exact P2MBitPHPSemanticObstruction.no_refutation m (2^b) b 0 (P2MBitPHPDegreeLowerBound.addresses b) hn
    (by omega) π ⟨by intro c hc; trivial,hπ.2⟩ hD

end SemAC02.Supplement.P2MBitPHPMinimalSize
end

section
-- Inlined Solutions.P2MBitPHPSizeParameters

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MBitPHPSizeParameters

theorem exponential_large (b : ℕ) (hb : 32 ≤ b) : 2000*b ≤ 2^b := by
  have h : ∀ d : ℕ, 2000*(d+32) ≤ 2^(d+32) := by
    intro d
    induction d with
    | zero => norm_num
    | succ d ih =>
      have he : d+1+32 = (d+32)+1 := by omega
      rw [he,Nat.pow_succ]
      nlinarith
  simpa only [Nat.sub_add_cancel hb] using h (b-32)

theorem budgets (ℓ m : ℕ) (hℓ : 30 ≤ ℓ) (hm : 2^(ℓ+2) < m) :
    ∃ k : ℕ, 1 ≤ k ∧ 2*k < 2^ℓ ∧
      2*(3*(k+2*(ℓ+2)*k)+2) ≤ 2^ℓ ∧
      3*(k+2*(ℓ+2)*k) ≤ m*(ℓ+2) ∧
      ((2 : ℝ)^(ℓ+2))/(2000*(ℓ+2 : ℕ)) ≤ k := by
  let b := ℓ+2
  let n := 2^b
  let k := n/(1000*b)
  have hb : 32 ≤ b := by dsimp [b]; omega
  have hden : 0 < 1000*b := by positivity
  have hn : 2000*b ≤ n := exponential_large b hb
  have hk : 1 ≤ k := by
    apply (Nat.le_div_iff_mul_le hden).mpr
    nlinarith
  have hupper : 1000*b*k ≤ n := by
    have hh := Nat.div_mul_le_self n (1000*b)
    dsimp only [k]
    nlinarith
  have hnH : n = 4*2^ℓ := by dsimp [n,b]; rw [Nat.pow_add]; norm_num; ring
  have hH : 250*b*k ≤ 2^ℓ := by nlinarith [hupper,hnH]
  have hbk : k ≤ b*k := by nlinarith
  have hm' : n < m := hm
  have hmMul : m ≤ m*b := by nlinarith
  refine ⟨k,hk,by nlinarith,by dsimp only [b] at hH; nlinarith,
    by dsimp only [b] at hupper hbk; nlinarith,?_⟩
  have hrem := Nat.lt_mul_div_succ n hden
  have hlow : n ≤ 2000*b*k := by
    change n < 1000*b*(k+1) at hrem
    nlinarith
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hlowR : (n : ℝ) ≤ 2000*(b : ℝ)*k := by exact_mod_cast hlow
  have hnR : (n : ℝ) = (2:ℝ)^(ℓ+2) := by dsimp [n,b]; norm_cast
  have hbEq : (b : ℝ) = ((ℓ+2 : ℕ) : ℝ) := rfl
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2000*((ℓ+2 : ℕ) : ℝ))).mpr
  rw [← hnR,← hbEq]
  nlinarith

theorem absorb_factor_two (x S : ℝ) (hx : 0 ≤ x) (hS : 2 ≤ S)
    (hfinite : 1/2*Real.exp x ≤ S) : (2:ℝ)^(x/4) ≤ S := by
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsq : (Real.exp (Real.log 2*(x/4)))^2 ≤ Real.exp x := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hnonneg := Real.exp_pos (Real.log 2*(x/4))
  nlinarith

theorem exponent (m b k : ℕ) (hm : 0 < m) (hb : 0 < b)
    (hLower : (2:ℝ)^b/(2000*b) ≤ k) :
    (1/32000000 : ℝ)*((2:ℝ)^b)^2/((m:ℝ)*(b:ℝ)^2) ≤ (k:ℝ)^2/(8*m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlow := (div_le_iff₀ (by positivity : (0 : ℝ) < 2000*(b:ℝ))).mp hLower
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2:ℝ)^b) hlow 2
  have hsquare : ((2:ℝ)^b)^2 ≤ 4000000*(b:ℝ)^2*(k:ℝ)^2 := by nlinarith
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (m:ℝ)*(b:ℝ)^2)
    (by positivity : (0 : ℝ) < 8*(m:ℝ))).mpr
  nlinarith [mul_le_mul_of_nonneg_right hsquare hmR.le]

end SemAC02.Supplement.P2MBitPHPSizeParameters
end

section
-- Inlined Solutions.P2MBitPHPSPSLowerBound

set_option maxHeartbeats 4000000

namespace SemAC02.Supplement.P2MBitPHPSPSLowerBound

open ACirc

theorem full :
    ∃ c : ℝ, 0 < c ∧ ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∀ m : ℕ, 2 ^ ℓ < m →
      ∀ π : List (ACirc (ZMod 2) (Fin m × Fin ℓ)),
        IsSemPCRef IsSPS Set.univ (polyAx (bphp m ℓ)) π →
        (2 : ℝ) ^ (c * ((2 : ℝ) ^ ℓ) ^ 2 / ((m : ℝ) * (ℓ : ℝ) ^ 2)) ≤ topS Set.univ π := by
  refine ⟨1/32000000,by norm_num,32,?_⟩
  intro b hb m hm π hπ
  have hb2 : 2 ≤ b := by omega
  have he : b-2+2 = b := by omega
  obtain ⟨k,hk,hchoose,hHole,hAmbient,hLower⟩ := P2MBitPHPSizeParameters.budgets (b-2) m (by omega)
    (by simpa only [he] using hm)
  have hFinite' := P2MBitPHPFiniteSizeBound.lower m (b-2) k hk hchoose hHole hAmbient
  rw [he] at hFinite'
  have hFinite := hFinite' π hπ
  have hSize2 := P2MBitPHPMinimalSize.two_le m b hb2 π hπ
  have hSize2R : (2:ℝ) ≤ topS Set.univ π := by exact_mod_cast hSize2
  have hAbsorb := P2MBitPHPSizeParameters.absorb_factor_two ((k:ℝ)^2/(2*m)) (topS Set.univ π)
    (by positivity) hSize2R hFinite
  have hmpos : 0 < m := (pow_pos (by norm_num : 0 < (2:ℕ)) b).trans hm
  have hExp := P2MBitPHPSizeParameters.exponent m b k hmpos (by omega)
    (by simpa only [he,Nat.cast_add,Nat.cast_ofNat] using hLower)
  have hExp' : (1/32000000:ℝ)*((2:ℝ)^b)^2/((m:ℝ)*(b:ℝ)^2) ≤ ((k:ℝ)^2/(2*m))/4 := by
    convert hExp using 1 <;> ring
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hExp').trans hAbsorb

end SemAC02.Supplement.P2MBitPHPSPSLowerBound
end

end P2MBitPHPSPSProof
open SemAC02.Supplement MvPolynomial ACirc Filter Topology

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∀ m : ℕ, 2 ^ ℓ < m →
      ∀ π : List (ACirc (ZMod 2) (Fin m × Fin ℓ)),
        IsSemPCRef IsSPS Set.univ (polyAx (bphp m ℓ)) π →
        (2 : ℝ) ^ (c * ((2 : ℝ) ^ ℓ) ^ 2 / ((m : ℝ) * (ℓ : ℝ) ^ 2)) ≤ topS Set.univ π  := by
  exact P2MBitPHPSPSProof.SemAC02.Supplement.P2MBitPHPSPSLowerBound.full
