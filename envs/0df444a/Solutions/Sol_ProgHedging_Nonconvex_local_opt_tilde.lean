-- Prove2me | solution 1 for ProgHedging.Nonconvex.local_opt_tilde
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:20:13.280354+00:00
-- url     : https://prove2.me/submissions/b97a2797-d7a0-4f9f-99d5-75d5933cf368

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone
import Theorems.Thm_ProgHedging_Nonconvex_eq_6_6
import Theorems.Thm_ProgHedging_Nonconvex_limit_mem_M_N

open Filter Topology
open scoped RealInnerProductSpace

namespace Aux_PH61L
open ProgHedging.Convex
open Classical

lemma pnorm_sq {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) :
    pr.pnorm X ^ 2 = ∑ s, pr.p s * ‖X s‖ ^ 2 := by
  have hip : pr.ip X X = ∑ s, pr.p s * ‖X s‖ ^ 2 := by
    unfold Problem.ip
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [real_inner_self_eq_norm_sq]
  have hnn : 0 ≤ pr.ip X X := by
    rw [hip]; exact Finset.sum_nonneg (fun s _ => mul_nonneg (pr.p_pos s).le (sq_nonneg _))
  unfold Problem.pnorm
  rw [Real.sq_sqrt hnn, hip]

lemma filt_eq {S : Type*} [Fintype S] (σ : Setoid S) (s s' : S) (h : σ.r s s') :
    Finset.univ.filter (fun s'' => σ.r s'' s) = Finset.univ.filter (fun s'' => σ.r s'' s') := by
  ext s''
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h1; exact σ.iseqv.trans h1 h
  · intro h1; exact σ.iseqv.trans h1 (σ.iseqv.symm h)

lemma den_pos {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (s : S) (j : Fin n) :
    0 < ∑ s' ∈ Finset.univ.filter (fun s' => (pr.bundle (pr.period j)).r s' s), pr.p s' := by
  apply Finset.sum_pos (fun s' _ => pr.p_pos s')
  exact ⟨s, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact
    (pr.bundle (pr.period j)).iseqv.refl s⟩

/-- `⟨Y, W⟩ = 0` for `Y ∈ 𝒩`, `W ∈ ℳ`. -/
lemma ip_N_M {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (Y W : Policy S n)
    (hY : Y ∈ pr.N) (hW : W ∈ pr.M) : pr.ip Y W = 0 := by
  unfold Problem.ip
  have hinner : ∀ s, ⟪Y s, W s⟫ = ∑ j, Y s j * W s j := by
    intro s
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [mul_comm]
  simp_rw [hinner, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  set σ := pr.bundle (pr.period j)
  set P : S → ℝ := fun s => ∑ s' ∈ Finset.univ.filter (fun s' => σ.r s' s), pr.p s'
  have hPpos : ∀ s, 0 < P s := fun s => den_pos pr s j
  -- numerator of J W vanishes
  have hJW : ∀ s, ∑ s' ∈ Finset.univ.filter (fun s' => σ.r s' s), pr.p s' * W s' j = 0 := by
    intro s
    have h := congrArg (fun V : Policy S n => V s j) hW
    simp only [Problem.J] at h
    change (∑ s' ∈ Finset.univ.filter (fun s' => σ.r s' s), pr.p s' * W s' j) / P s = 0 at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h (hPpos s).ne'
  have hYc : ∀ s s', σ.r s' s → Y s' j = Y s j := fun s s' h => hY j s' s h
  have hPc : ∀ s s', σ.r s' s → P s' = P s := by
    intro s s' h
    simp only [P]
    rw [filt_eq σ s' s h]
  calc ∑ s, pr.p s * (Y s j * W s j)
      = ∑ s, ∑ s' ∈ Finset.univ.filter (fun s' => σ.r s' s),
          pr.p s' * (pr.p s * (Y s j * W s j)) / P s := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [← Finset.sum_div, ← Finset.sum_mul]
        change _ = P s * _ / P s
        field_simp [(hPpos s).ne']
    _ = ∑ s, ∑ s', if σ.r s' s then pr.p s' * (pr.p s * (Y s j * W s j)) / P s else 0 := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ s', ∑ s, if σ.r s' s then pr.p s' * (pr.p s * (Y s j * W s j)) / P s else 0 :=
        Finset.sum_comm
    _ = ∑ s', (pr.p s' * Y s' j / P s') *
          ∑ s ∈ Finset.univ.filter (fun s => σ.r s s'), pr.p s * W s j := by
        refine Finset.sum_congr rfl (fun s' _ => ?_)
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        by_cases h : σ.r s' s
        · have h' : σ.r s s' := σ.iseqv.symm h
          rw [if_pos h, if_pos h', hYc s' s h', hPc s' s h']
          ring
        · have h' : ¬ σ.r s s' := fun h'' => h (σ.iseqv.symm h'')
          rw [if_neg h, if_neg h']
    _ = 0 := by
        refine Finset.sum_eq_zero (fun s' _ => ?_)
        rw [hJW s', mul_zero]

end Aux_PH61L

namespace ProgHedging.Nonconvex
end ProgHedging.Nonconvex

open ProgHedging.Nonconvex in
theorem solution {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (X W : ℕ → ProgHedging.Convex.Policy S n) (hseq : pr.IsLocalPHSeq r δ X W)
    (Xs Ws : ProgHedging.Convex.Policy S n) (hX : Tendsto X atTop (𝓝 Xs)) (hW : Tendsto W atTop (𝓝 Ws)) :
    (∀ Y ∈ pr.adm ∩ pr.N, pr.pnorm (Y - Xs) < pr.deltaPrime δ →
      pr.F Xs ≤ pr.F Y + r / 2 * pr.pnorm (Y - Xs) ^ 2) ∧
    ∀ Y : ProgHedging.Convex.Policy S n, pr.F Y + r / 2 * pr.pnorm (Y - Xs) ^ 2 = ∑ s, pr.p s * pr.fTilde r Xs s (Y s) := by
  obtain ⟨hWM, -, hXN⟩ := ProgHedging.Nonconvex.limit_mem_M_N pr hr hδ X W hseq Xs Ws hX hW
  obtain ⟨-, hloc⟩ := ProgHedging.Nonconvex.eq_6_6 pr hr hδ X W hseq Xs Ws hX hW
  refine ⟨fun Y hY hlt => ?_, fun Y => ?_⟩
  · have h := hloc Y hY.1 hlt
    rw [Aux_PH61L.ip_N_M pr Xs Ws hXN hWM, Aux_PH61L.ip_N_M pr Y Ws hY.2 hWM] at h
    linarith
  · rw [Aux_PH61L.pnorm_sq]
    unfold ProgHedging.Convex.Problem.F Problem.fTilde
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Pi.sub_apply]
    ring
