-- Prove2me | solution 1 for ProgHedging.Nonconvex.eq_6_4_local_opt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:36:40.223962+00:00
-- url     : https://prove2.me/submissions/2807360a-12d5-416e-80c8-d5a82547d3f3

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone
open scoped RealInnerProductSpace

namespace Aux_PH64
open ProgHedging.Convex

lemma ip_self {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) :
    pr.ip X X = ∑ s, pr.p s * ‖X s‖ ^ 2 := by
  unfold Problem.ip
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [real_inner_self_eq_norm_sq]

lemma ip_nonneg {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) :
    0 ≤ pr.ip X X := by
  rw [ip_self]
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (pr.p_pos s).le (sq_nonneg _))

lemma pnorm_sq {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) :
    pr.pnorm X ^ 2 = ∑ s, pr.p s * ‖X s‖ ^ 2 := by
  unfold Problem.pnorm
  rw [Real.sq_sqrt (ip_nonneg pr X), ip_self]

end Aux_PH64

open ProgHedging.Nonconvex in
theorem solution {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (X W : ℕ → ProgHedging.Convex.Policy S n) (hseq : pr.IsLocalPHSeq r δ X W) :
    (∀ Y Z : ProgHedging.Convex.Policy S n, pr.pnorm (Y - Z) ≤ pr.deltaPrime δ → ∀ s, ‖Y s - Z s‖ ≤ δ) ∧
    ∀ ν, X (ν + 1) ∈ pr.adm ∧ ∀ Y ∈ pr.adm, pr.pnorm (Y - X (ν + 1)) ≤ pr.deltaPrime δ →
      pr.Fnu r (pr.J (X ν)) (W ν) (X (ν + 1)) ≤ pr.Fnu r (pr.J (X ν)) (W ν) Y := by
  have part1 : ∀ Y Z : ProgHedging.Convex.Policy S n, pr.pnorm (Y - Z) ≤ pr.deltaPrime δ →
      ∀ s, ‖Y s - Z s‖ ≤ δ := by
    intro Y Z h s
    haveI : Nonempty S := ⟨s⟩
    have hbdd : BddBelow (Set.range fun s => Real.sqrt (pr.p s)) :=
      ⟨0, by rintro _ ⟨t, rfl⟩; exact Real.sqrt_nonneg _⟩
    have hinf_le : (⨅ s, Real.sqrt (pr.p s)) ≤ Real.sqrt (pr.p s) := ciInf_le hbdd s
    have hinf_nn : 0 ≤ ⨅ s, Real.sqrt (pr.p s) := le_ciInf (fun t => Real.sqrt_nonneg _)
    have hpn : 0 ≤ pr.pnorm (Y - Z) := Real.sqrt_nonneg _
    have hsq : pr.pnorm (Y - Z) ^ 2 ≤ (pr.deltaPrime δ) ^ 2 := pow_le_pow_left₀ hpn h 2
    rw [Aux_PH64.pnorm_sq] at hsq
    have hsingle : pr.p s * ‖(Y - Z) s‖ ^ 2 ≤ ∑ t, pr.p t * ‖(Y - Z) t‖ ^ 2 :=
      Finset.single_le_sum (f := fun t => pr.p t * ‖(Y - Z) t‖ ^ 2)
        (fun t _ => mul_nonneg (pr.p_pos t).le (sq_nonneg _)) (Finset.mem_univ s)
    have hdp : (pr.deltaPrime δ) ^ 2 ≤ δ ^ 2 * pr.p s := by
      unfold Problem.deltaPrime
      have h1 : (⨅ s, Real.sqrt (pr.p s)) ^ 2 ≤ Real.sqrt (pr.p s) ^ 2 :=
        pow_le_pow_left₀ hinf_nn hinf_le 2
      rw [Real.sq_sqrt (pr.p_pos s).le] at h1
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg δ)
    rw [Pi.sub_apply] at hsingle
    have hps := pr.p_pos s
    have : ‖Y s - Z s‖ ^ 2 ≤ δ ^ 2 := by
      by_contra hc
      push_neg at hc
      nlinarith
    nlinarith [norm_nonneg (Y s - Z s)]
  refine ⟨part1, fun ν => ?_⟩
  obtain ⟨-, -, hstep⟩ := hseq
  obtain ⟨hloc, -⟩ := hstep ν
  have hFnu : ∀ V Wv Xv : ProgHedging.Convex.Policy S n, pr.Fnu r V Wv Xv =
      ∑ s, pr.p s * pr.subObj s (V s) (Wv s) r (Xv s) := by
    intro V Wv Xv
    unfold Problem.Fnu
    rw [Aux_PH64.pnorm_sq]
    unfold ProgHedging.Convex.Problem.F ProgHedging.Convex.Problem.ip
      ProgHedging.Convex.Problem.subObj
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Pi.sub_apply]
    ring
  refine ⟨fun s => (hloc s).1, fun Y hY hball => ?_⟩
  rw [hFnu, hFnu]
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (pr.p_pos s).le
  exact (hloc s).2 (Y s) (hY s) (part1 Y (X (ν + 1)) hball s)
