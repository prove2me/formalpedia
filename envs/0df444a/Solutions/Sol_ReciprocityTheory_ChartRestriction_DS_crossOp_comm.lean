-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.crossOp_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:15.767802+00:00
-- url     : https://prove2.me/submissions/a7a140ce-0e51-4e1e-89d6-b4cd2394d650

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_comm_of_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_commutator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_factorAd_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (k : ℕ) (i : Fin k) {a b : Fin n} (hab : ε a = ε b) :
    crossOp ε E k i * bAct E k a b = bAct E k a b * crossOp ε E k i := by
  classical
  have hmrel : ∀ a b c d : Fin n, mAct E k a b * mAct E k c d - mAct E k c d * mAct E k a b =
      (if b = c then mAct E k a d else 0) - (if d = a then mAct E k c b else 0) := by
    intro a b c d
    refine LinearMap.ext fun F => PiLp.ext fun κ => ?_
    have h := LinearMap.congr_fun (hE a b c d) (F κ)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, mAct_apply]
    rw [h]
    split_ifs <;> simp [mAct_apply]
  have hterm : ∀ c d : Fin n,
      (mAct E k a b + factorAd k i a b) * (factorAd k i c d * mAct E k d c) -
        (factorAd k i c d * mAct E k d c) * (mAct E k a b + factorAd k i a b) =
      factorAd k i c d * (mAct E k a b * mAct E k d c - mAct E k d c * mAct E k a b) +
        (factorAd k i a b * factorAd k i c d - factorAd k i c d * factorAd k i a b) * mAct E k d c := by
    intro c d
    have h1 := mAct_factorAd_comm (E := E) k i a b c d
    have h2 := mAct_factorAd_comm (E := E) k i d c a b
    calc _ = mAct E k a b * factorAd k i c d * mAct E k d c +
          factorAd k i a b * factorAd k i c d * mAct E k d c -
          factorAd k i c d * mAct E k d c * mAct E k a b -
          factorAd k i c d * (mAct E k d c * factorAd k i a b) := by noncomm_ring
      _ = _ := by
        rw [h1, h2]
        noncomm_ring
  have key : ∑ c, ∑ d ∈ univ.filter (fun d => ε d = ε c),
      (factorAd k i c d * ((if b = d then mAct E k a c else 0) - (if c = a then mAct E k d b else 0)) +
        ((if b = c then factorAd k i a d else 0) - (if d = a then factorAd k i c b else 0)) *
          mAct E k d c) = 0 := by
    simp [mul_sub, sub_mul, mul_ite, ite_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, hab]
  have hmain : (mAct E k a b + factorAd k i a b) * crossOp ε E k i -
      crossOp ε E k i * (mAct E k a b + factorAd k i a b) = 0 := by
    unfold crossOp
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    rw [← key]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hterm, hmrel, factorAd_commutator]
  have hother : ∀ j ∈ univ.erase i,
      factorAd (M := M) k j a b * crossOp ε E k i = crossOp ε E k i * factorAd k j a b := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    unfold crossOp
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← mul_assoc, factorAd_comm_of_ne k hji, mul_assoc, ← mAct_factorAd_comm (E := E) k j d c a b,
      ← mul_assoc]
  have hsum : (∑ j ∈ univ.erase i, factorAd (M := M) k j a b) * crossOp ε E k i =
      crossOp ε E k i * ∑ j ∈ univ.erase i, factorAd k j a b := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hother
  have hsplit : bAct E k a b =
      (mAct E k a b + factorAd k i a b) + ∑ j ∈ univ.erase i, factorAd (M := M) k j a b := by
    unfold bAct
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    abel
  rw [hsplit, mul_add, add_mul, ← hsum]
  have h := sub_eq_zero.1 hmain
  rw [h]
end ReciprocityTheory.ChartRestriction.DS
