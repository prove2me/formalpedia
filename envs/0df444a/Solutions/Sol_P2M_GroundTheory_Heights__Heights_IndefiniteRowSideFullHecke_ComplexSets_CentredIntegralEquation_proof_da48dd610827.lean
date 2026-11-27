-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_proof_da48dd610827
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:17.469381+00:00
-- url     : https://prove2.me/submissions/08b4f17a-ff96-4748-b3dd-1b1435096bf1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCentredIntegralEquation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_exists_monic_map_eq_X_pow_d6b90c590648
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_germEval_toGerm_44cc721d23db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_germEval_constGerm_b8db1706a27b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_germEval_pull_77ead29e3af0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_isUnit_of_germEval_ne_zero_b1c4a153b19d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_toGerm_monic_expr_1d2752f94b3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_coe_monic_expr_7f3f33f75757
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermPrimitivePresentation_pull_toGerm_8762c4c475dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermPrimitivePresentation_toGerm_mem_iff_9b3ec135511e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
open PrimeGermPrimitivePresentation
variable {σ : Type} [Fintype σ]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
theorem _root_.solution : CentredIntegralEquation.Statement := by
  classical
  intro σ _ w k p d A hp hcoord hpoly g hg
  set I := holGermIdeal w p
  let _ : Algebra (holGerms (A w)) (holGerms w ⧸ I) := ((Ideal.Quotient.mk I).comp (pull A w)).toAlgebra
  have halg : ∀ r, algebraMap (holGerms (A w)) (holGerms w ⧸ I) r = Ideal.Quotient.mk I (pull A w r) :=
    fun _ => rfl

  have hcl : ∀ (u : anFun w) (f : (σ → ℂ) → ℂ), u.1 = f →
      (Ideal.Quotient.mk I (toGerm w u) = 0 ↔ IsGermCombination w p f) := by
    rintro u f rfl
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact toGerm_mem_iff hp u

  have hev : ∀ (x : anFun w) (n : ℕ) (c : Fin n → anFun (A w)),
      aeval (Ideal.Quotient.mk I (toGerm w x)) (X ^ n + ∑ j : Fin n, C (toGerm (A w) (c j)) * X ^ (j : ℕ)) =
        Ideal.Quotient.mk I (toGerm w (x ^ n + ∑ j, compA A w (c j) * x ^ (j : ℕ))) := by
    intro x n c
    rw [toGerm_monic_expr]
    simp only [map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C, halg]
  set zc : σ → anFun w := fun i => mkA (fun z => z i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  set cz : σ → holGerms w ⧸ I := fun i => Ideal.Quotient.mk I (toGerm w (zc i))

  have hint : ∀ i, IsIntegral (holGerms (A w)) (cz i) := by
    intro i
    obtain ⟨n, b, hb, hcomb⟩ := hcoord i
    set c : Fin n → anFun (A w) := fun j => mkA (b j) (hb j)
    refine ⟨X ^ n + ∑ j : Fin n, C (toGerm (A w) (c j)) * X ^ (j : ℕ), ?_, ?_⟩
    · refine monic_X_pow_add (degree_sum_le _ _ |>.trans_lt ?_)
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun j _ => ?_
      exact (degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.2 j.2)
    · rw [← aeval_def, hev]
      exact (hcl _ _ (coe_monic_expr A w (zc i) n c)).2 hcomb

  have hadj : Algebra.adjoin (holGerms (A w)) (Set.range cz) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨u, rfl⟩ := toGerm_surjective w s
    obtain ⟨t, a, ha, hcomb⟩ := hpoly u.1 u.2
    set a' : (σ → ℕ) → (Fin d → ℂ) → ℂ := fun m => if m ∈ t then a m else 0
    have ha' : ∀ m, AnalyticAt ℂ (a' m) (A w) := by
      intro m
      by_cases hm : m ∈ t
      · simpa [a', hm] using ha m hm
      · simp only [a', hm, if_false]; exact analyticAt_const
    set v : anFun w := ∑ m ∈ t, compA A w (mkA (a' m) (ha' m)) * ∏ i, zc i ^ m i
    have hv : (u - v).1 = fun z => u.1 z - ∑ m ∈ t, a m (A z) * ∏ i, z i ^ m i := by
      funext z
      simp only [v, AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
        SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply,
        Finset.prod_apply, Pi.pow_apply]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      simp [compA, mkA, a', zc, hm]
    have h1 : Ideal.Quotient.mk I (toGerm w u) = Ideal.Quotient.mk I (toGerm w v) := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub]
      exact (hcl _ _ hv).2 hcomb
    rw [h1]
    simp only [v, map_sum, map_mul, map_prod, map_pow, ← pull_toGerm]
    refine Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ ?_ (Subalgebra.prod_mem _ fun i _ =>
      Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _)
    rw [← halg]
    exact Subalgebra.algebraMap_mem _ _
  have : Module.Finite (holGerms (A w)) (holGerms w ⧸ I) := by
    refine ⟨?_⟩
    rw [← Algebra.top_toSubmodule, ← hadj]
    exact fg_adjoin_of_finite (Set.finite_range _) (by rintro _ ⟨i, rfl⟩; exact hint i)

  set gA : anFun w := mkA g hg
  set gcl : holGerms w ⧸ I := Ideal.Quotient.mk I (toGerm w gA)
  set xB := gcl - algebraMap (holGerms (A w)) (holGerms w ⧸ I) (constGerm (A w) (g w))
  have hx : ∀ c : ℂ, c ≠ 0 → ∀ y : holGerms w ⧸ I,
      IsUnit (algebraMap (holGerms (A w)) (holGerms w ⧸ I) (constGerm (A w) c) + xB * y) := by
    intro c hc y
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    have e : algebraMap (holGerms (A w)) (holGerms w ⧸ I) (constGerm (A w) c) + xB * Ideal.Quotient.mk I t =
        Ideal.Quotient.mk I (pull A w (constGerm (A w) c) +
          (toGerm w gA - pull A w (constGerm (A w) (g w))) * t) := by
      simp only [xB, gcl, halg, map_add, map_mul, map_sub]
    rw [e]
    refine (isUnit_of_germEval_ne_zero _ ?_).map _
    simp only [map_add, map_mul, map_sub, germEval_pull, germEval_constGerm, germEval_toGerm]
    simpa [gA, mkA] using hc
  obtain ⟨Q, hQm, hQ0, hQmap⟩ :=
    exists_monic_map_eq_X_pow (germEval (A w)) (constGerm (A w)) (germEval_constGerm _) xB hx
  have : Nontrivial (holGerms (A w)) := (germEval (A w)).domain_nontrivial
  set F := Q.comp (X - C (constGerm (A w) (g w)))
  have hFm : F.Monic := hQm.comp (monic_X_sub_C _) (by rw [natDegree_X_sub_C]; omega)
  have hF0 : aeval gcl F = 0 := by
    rw [aeval_comp, map_sub, aeval_X, aeval_C]
    exact hQ0
  have hFmap : F.map (germEval (A w)) = (X - C (g w)) ^ Q.natDegree := by
    rw [Polynomial.map_comp, hQmap, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, germEval_constGerm,
      X_pow_comp]
  have hdeg : F.natDegree = Q.natDegree := by
    rw [← hFm.natDegree_map (germEval (A w)), hFmap, sub_eq_add_neg, ← C_neg, natDegree_pow_X_add_C]
  set n := F.natDegree
  have hrepv : ∀ c : holGerms (A w), (rep c).1 (A w) = germEval (A w) c := fun c => by
    rw [← germEval_toGerm, toGerm_rep]
  refine ⟨n, fun j => (rep (F.coeff j)).1, fun j => (rep (F.coeff j)).2, ?_, fun T => ?_⟩
  · refine (hcl _ _ (coe_monic_expr A w gA n fun j => rep (F.coeff j))).1 ?_
    rw [toGerm_monic_expr]
    simp only [toGerm_rep]
    rw [Fin.sum_univ_eq_sum_range (fun i => pull A w (F.coeff i) * toGerm w gA ^ i) n, ← hF0]
    conv_rhs => rw [hFm.as_sum]
    simp only [map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C, halg, gcl]
    rfl
  · simp only [hrepv]
    rw [Fin.sum_univ_eq_sum_range (fun i => germEval (A w) (F.coeff i) * T ^ i) n]
    have h := congrArg (eval T) hFmap
    conv_lhs at h => rw [hFm.as_sum]
    have hd : F.natDegree = Q.natDegree := hdeg
    simpa [Polynomial.map_sum, eval_finsetSum, hd, hdeg] using h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
