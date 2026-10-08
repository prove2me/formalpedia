-- Prove2me | solution 1 for ProximityTerminalDerivativeCoreV1.terminal_product_union
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-04T12:09:35.345419+00:00
-- url     : https://prove2.me/submissions/e296b819-8454-4f15-87cf-7b9344a96dc8

import Definitions.Def_ProximityTerminalDerivativeCoreV1
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.CharP.Basic

open scoped Classical BigOperators
open ProximityTerminalDerivativeCoreV1
set_option maxHeartbeats 500000

namespace ProximityTerminalDerivativeCoreProofV1
noncomputable section
variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem support_before_pderiv (i:Fin 4) (P:MvPolynomial (Fin 4) K) (d:Fin 4 →₀ ℕ)
   (hd:d∈(MvPolynomial.pderiv i P).support):
   d+Finsupp.single i 1∈P.support:=by
 apply MvPolynomial.mem_support_iff.mpr
 intro hzero
 have hne:=MvPolynomial.mem_support_iff.mp hd
 apply hne
 rw [MvPolynomial.coeff_pderiv,hzero,zero_mul]

theorem pderiv_degree_bound (i j:Fin 4) (P:MvPolynomial (Fin 4) K) (a:ℕ)
   (hP:P.degreeOf j ≤ a):(MvPolynomial.pderiv i P).degreeOf j ≤ a:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hh:=MvPolynomial.degreeOf_le_iff.mp hP
   (d+Finsupp.single i 1) (support_before_pderiv i P d hd)
 simp only [Finsupp.add_apply] at hh
 omega

theorem pderiv_same_degree_bound (i:Fin 4) (P:MvPolynomial (Fin 4) K) (a:ℕ)
   (hP:P.degreeOf i ≤ a):(MvPolynomial.pderiv i P).degreeOf i ≤ a-1:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hh:=MvPolynomial.degreeOf_le_iff.mp hP
   (d+Finsupp.single i 1) (support_before_pderiv i P d hd)
 simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
 omega

theorem pderiv_zero_of_degree_zero (i:Fin 4) (F:MvPolynomial (Fin 4) K)
   (hdegree:F.degreeOf i=0):MvPolynomial.pderiv i F=0:=by
 apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
 intro hmem
 exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hmem) hdegree

theorem pderiv_zero_iff_degree_zero_below_char
   (i:Fin 4) (F:MvPolynomial (Fin 4) K) (p:ℕ) [CharP K p]
   (hdegree:F.degreeOf i < p):
   MvPolynomial.pderiv i F=0 ↔ F.degreeOf i=0:=by
 classical
 constructor
 · intro hzero
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   by_contra hn
   have hpos:0 < d i:=by omega
   have hsmall:d i < p:=(MvPolynomial.monomial_le_degreeOf i hd).trans_lt hdegree
   let e:Fin 4 →₀ ℕ:=d-Finsupp.single i 1
   have he:e+Finsupp.single i 1=d:=
     Finsupp.sub_add_single_one_cancel (by omega:d i≠0)
   have hnat:e i+1=d i:=by
     have hh:=congrArg (fun f:Fin 4 →₀ ℕ => f i) he
     simpa only [Finsupp.add_apply,Finsupp.single_eq_same] using hh
   have hcast:(d i:K)≠0:=
     (CharP.cast_eq_zero_iff K p (d i)).not.mpr (Nat.not_dvd_of_pos_of_lt hpos hsmall)
   have hcoef:(e i:K)+1≠0:=by
     simpa only [←hnat,Nat.cast_add,Nat.cast_one] using hcast
   have hz:MvPolynomial.coeff e (MvPolynomial.pderiv i F)=0:=by
     rw [hzero,MvPolynomial.coeff_zero]
   rw [MvPolynomial.coeff_pderiv,he] at hz
   exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hcoef hz
 · exact pderiv_zero_of_degree_zero i F

theorem R_derivative_nonzero (F:MvPolynomial (Fin 4) K) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p):
   MvPolynomial.pderiv (2:Fin 4) F≠0:=by
 intro hzero
 have hd:=(pderiv_zero_iff_degree_zero_below_char (2:Fin 4) F p hsmall).mp hzero
 omega

@[simp] theorem dR_zero (F : MvPolynomial (Fin 4) K) : dR 0 F = F := rfl

theorem dR_succ (j : ℕ) (F : MvPolynomial (Fin 4) K) :
    dR (j + 1) F = MvPolynomial.pderiv (2 : Fin 4) (dR j F) := by
  unfold dR
  exact Function.iterate_succ_apply' _ _ _

theorem dR_R_degree_le (j : ℕ) (F : MvPolynomial (Fin 4) K) :
    (dR j F).degreeOf 2 ≤ F.degreeOf 2 - j := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [dR_succ]
      have h := pderiv_same_degree_bound (2 : Fin 4) (dR k F) (F.degreeOf 2 - k) ih
      omega

theorem exists_dR_R_degree_zero (F : MvPolynomial (Fin 4) K) :
    ∃ j, (dR j F).degreeOf 2 = 0 :=
  ⟨F.degreeOf 2, Nat.eq_zero_of_le_zero (by simpa using dR_R_degree_le (F.degreeOf 2) F)⟩

theorem chainLength_eq_find (F : MvPolynomial (Fin 4) K) :
    chainLength F = Nat.find (exists_dR_R_degree_zero F) := by
  unfold chainLength
  rw [dif_pos (exists_dR_R_degree_zero F)]

theorem chainLength_spec (F : MvPolynomial (Fin 4) K) :
    (dR (chainLength F) F).degreeOf 2 = 0 := by
  rw [chainLength_eq_find]
  exact Nat.find_spec (exists_dR_R_degree_zero F)

theorem chainLength_le (F : MvPolynomial (Fin 4) K) : chainLength F ≤ F.degreeOf 2 := by
  rw [chainLength_eq_find]
  exact Nat.find_min' (exists_dR_R_degree_zero F)
    (Nat.eq_zero_of_le_zero (by simpa using dR_R_degree_le (F.degreeOf 2) F))

theorem dR_R_degree_pos_of_lt_chainLength (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (hj : j < chainLength F) : 0 < (dR j F).degreeOf 2 := by
  rw [chainLength_eq_find] at hj
  exact Nat.pos_of_ne_zero (Nat.find_min (exists_dR_R_degree_zero F) hj)

theorem dR_ne_zero (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (p : ℕ) [CharP K p]
    (hsmall : F.degreeOf 2 < p) (j : ℕ) (hj : j ≤ chainLength F) : dR j F ≠ 0 := by
  induction j with
  | zero => simpa using hF
  | succ k ih =>
      rw [dR_succ]
      have hk : k < chainLength F := by omega
      have hpos := dR_R_degree_pos_of_lt_chainLength F k hk
      have hle : (dR k F).degreeOf 2 < p := by
        have := dR_R_degree_le k F
        omega
      exact R_derivative_nonzero (dR k F) p hpos hle


end
end ProximityTerminalDerivativeCoreProofV1

open ProximityTerminalDerivativeCoreProofV1

theorem solution {K : Type} [Field K] {A : Type*} [CommRing A] [IsDomain A] (s : Finset (MvPolynomial (Fin 4) K))
    (p : ℕ) [CharP K p]
    (hne : ∀ F ∈ s, F ≠ 0) (hsmall : ∀ F ∈ s, F.degreeOf 2 < p)
    (Gamma : Finset K) (ev : K → MvPolynomial (Fin 4) K →+* A) :
    (∏ F ∈ s, dR (chainLength F) F) ≠ 0 ∧
    (∏ F ∈ s, dR (chainLength F) F).degreeOf 2 = 0 ∧
    Gamma.filter (fun γ => ∃ F ∈ s, ev γ (dR (chainLength F) F) = 0) =
      Gamma.filter (fun γ => ev γ (∏ F ∈ s, dR (chainLength F) F) = 0) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun F hF =>
    dR_ne_zero F (hne F hF) p (hsmall F hF) (chainLength F) le_rfl), ?_, ?_⟩
  · apply Nat.eq_zero_of_le_zero
    calc
      _ ≤ ∑ F ∈ s, (dR (chainLength F) F).degreeOf 2 :=
        MvPolynomial.degreeOf_prod_le 2 s _
      _ = 0 := Finset.sum_eq_zero (fun F _ => chainLength_spec F)
  · apply Finset.filter_congr
    intro γ _
    rw [map_prod, Finset.prod_eq_zero_iff]


