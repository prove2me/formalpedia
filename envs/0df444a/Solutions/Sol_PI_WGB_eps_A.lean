-- Prove2me | solution 1 for PI.WGB.eps_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:10.192517+00:00
-- url     : https://prove2.me/submissions/b9a938aa-85e2-4e8c-b8e7-4c70b2b0a551

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FixedLineProofA
import Theorems.Thm_PI_WGB_eval_aeval_poly_A
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGB_eval_D_A
import Theorems.Thm_PI_WGB_mStarA_cc
import Theorems.Thm_PI_WGB_mStarA_cl
import Theorems.Thm_PI_WGB_mStarA_lc
import Theorems.Thm_PI_WGB_mStarA_ll
import Theorems.Thm_PI_WGB_mkPtA_D
import Theorems.Thm_PI_WGB_prod_mkPtA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] PI.WGB.mStarA_cc
attribute [local simp] PI.WGB.mStarA_cl
attribute [local simp] PI.WGB.mStarA_lc
attribute [local simp] PI.WGB.mStarA_ll



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) f ν)
    (hrow : ∀ m ∈ f.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (hR : RInvA (fun x => eval x f)) (hC : lhwline_CInv (fun x => eval x f))
    (hc : coeff (mStarA kap ν) f ≠ 0) (i i' : Fin n) (hii : i'.val = i.val + 1)
    (hle : kap i' ≤ ν (Fin.castSucc i')) : ν (Fin.castSucc i') ≤ kap i := by
  by_contra hlt
  push Not at hlt
  have hne : i ≠ i' := by
    intro e
    rw [e] at hii
    omega
  have hlt' : Fin.castSucc i < Fin.castSucc i' := by
    rw [Fin.castSucc_lt_castSucc_iff, Fin.lt_def]
    omega
  set νp := ν (Fin.castSucc i') with hνp
  let dv : ℂ → Fin n → ℂ := fun e a => if a = i then e else if a = i' then -1 / e else 1
  let zz : ℂ → Fin (n + 1) → ℂ := fun e s => if s = Fin.castSucc i' then -1 / e else 1
  let Y : Fin (n + 1) × Fin (n + 1) → Polynomial ℂ := fun v =>
    Fin.lastCases (if v.2 = Fin.castSucc i' then 0 else 1)
      (fun a => Fin.lastCases 0 (fun k => if a = i then (if k = i then Polynomial.X else if k = i' then 1 else 0)
        else if a = i' then (if k = i then 1 else 0) else (if k = a then 1 else 0)) v.2) v.1
  have hpt : ∀ e : ℂ, e ≠ 0 → (fun v => (Y v).eval e) =
      lhwline_rowOp (Fin.castSucc i) (Fin.castSucc i') (1 / e)
        (lhwline_colOp (Fin.castSucc i) (Fin.castSucc i') (1 / e) (mkPtA (dv e) (zz e))) := by
    intro e he
    funext v
    obtain ⟨ρ, s⟩ := v
    induction ρ using Fin.lastCases with
    | last =>
      induction s using Fin.lastCases with
      | last =>
        simp [Y, lhwline_rowOp, lhwline_colOp, mkPtA, zz, (Fin.castSucc_lt_last i').ne',
          (Fin.castSucc_lt_last i).ne']
      | cast k =>
        simp only [Y, lhwline_rowOp, lhwline_colOp, mkPtA, zz, Fin.lastCases_castSucc, Fin.lastCases_last,
          Fin.castSucc_inj, (Fin.castSucc_lt_last i').ne', if_false]
        by_cases hk : k = i'
        · subst hk
          simp [hne]
          ring
        · simp [hk]
    | cast a =>
      induction s using Fin.lastCases with
      | last =>
        simp [Y, lhwline_rowOp, lhwline_colOp, mkPtA, (Fin.castSucc_lt_last i').ne']
      | cast k =>
        simp only [Y, lhwline_rowOp, lhwline_colOp, mkPtA, dv, Fin.lastCases_castSucc, Fin.lastCases_last,
          Fin.castSucc_inj]
        by_cases ha : a = i
        · subst ha
          have hai : a ≠ i' := hne
          by_cases hk : k = a
          · subst hk
            simp [hai]
          · by_cases hk' : k = i'
            · subst hk'
              simp [hai, hk, Ne.symm hai, hne, Ne.symm hne]
              field_simp
            · simp [hai, hk, hk']
        · by_cases ha' : a = i'
          · subst ha'
            by_cases hk : k = i
            · subst hk
              simp [ha, hne, Ne.symm hne]
              field_simp
            · by_cases hk' : k = a
              · subst hk'
                simp [ha, hk, hne, Ne.symm hne]
                field_simp
                ring
              · simp [ha, hk, hk', Ne.symm hk']
          · by_cases hk : k = i
            · subst hk
              simp [ha, ha', Ne.symm ha, hne, Ne.symm hne]
            · by_cases hk' : k = i'
              · subst hk'
                simp [ha, ha', hk, Ne.symm ha', Ne.symm ha]
              · by_cases hka : k = a <;> simp [ha, ha', hk, hk', hka, Ne.symm ha, Ne.symm ha']
  have hval : ∀ e : ℂ, e ≠ 0 →
      (aeval Y f).eval e = coeff (mStarA kap ν) f * (e ^ kap i * (-1 / e) ^ νp) := by
    intro e he
    have e1 := hR (lhwline_colOp (Fin.castSucc i) (Fin.castSucc i') (1 / e) (mkPtA (dv e) (zz e)))
      (Fin.castSucc i) (Fin.castSucc i') (1 / e) hlt' (by simp)
    have e2 := hC (mkPtA (dv e) (zz e)) (Fin.castSucc i) (Fin.castSucc i') (1 / e) hlt'
    simp only at e1 e2
    rw [eval_aeval_poly_A, hpt e he, e1, e2, eval_D_A kap ν f hcol hrow _ (mkPtA_D _ _), prod_mkPtA]
    congr 1
    have h1 : ∏ a, dv e a ^ kap a = e ^ kap i * (-1 / e) ^ kap i' := by
      have : ∀ a, dv e a ^ kap a =
          (if a = i then e ^ kap i else 1) * (if a = i' then (-1 / e) ^ kap i' else 1) := by
        intro a
        by_cases h1 : a = i
        · subst h1
          simp [dv, hne]
        · by_cases h2 : a = i'
          · subst h2
            simp [dv, h1]
          · simp [dv, h1, h2]
      rw [Finset.prod_congr rfl (fun a _ => this a), Finset.prod_mul_distrib, Finset.prod_ite_eq',
        Finset.prod_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
    have h2 : ∏ k : Fin n, zz e (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k) = (-1 / e) ^ (νp - kap i') := by
      have : ∀ k : Fin n, zz e (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k) =
          if k = i' then (-1 / e) ^ (νp - kap i') else 1 := by
        intro k
        by_cases hk : k = i'
        · subst hk
          simp [zz, hνp]
        · simp [zz, hk]
      rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
    have h3 : zz e (Fin.last n) = 1 := by
      simp [zz, (Fin.castSucc_lt_last i').ne']
    rw [h1, h2, h3, one_pow, mul_one, mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
  set p := aeval Y f with hp
  set q : Polynomial ℂ := p * Polynomial.X ^ νp -
    Polynomial.C (coeff (mStarA kap ν) f * (-1) ^ νp) * Polynomial.X ^ (kap i) with hq
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro e he
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at he
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hq, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, hval e he]
    rw [div_pow]
    field_simp
    ring
  have hco := congrArg (fun r : Polynomial ℂ => r.coeff (kap i)) hq0
  simp only [hq, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow', Polynomial.coeff_C_mul_X_pow,
    if_neg (not_le.mpr hlt), if_pos rfl, Polynomial.coeff_zero, zero_sub, neg_eq_zero] at hco
  simp at hco
  rcases hco with h | h
  · exact hc h
  · exfalso
    rw [← Polynomial.C_1, ← Polynomial.C_neg, ← Polynomial.C_pow, Polynomial.coeff_C_zero] at h
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) h
end PI.WGB
