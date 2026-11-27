-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_proof_5a7acf548f6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:26.621738+00:00
-- url     : https://prove2.me/submissions/69aec26e-acf5-46db-8602-10d305fc2fef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_fiberPoly_monic_f4ae4bc91a77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_fiberPoly_eval_897e59951098
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_mem_roots_fiberPoly_501f147fc65c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_rootFactor_eval_eq_zero_75b168033e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_rootFactor_mul_not_057a89ea9b43
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_exists_ne_zero_of_open_c7e4de96daad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_extended_factor_edafc28f6428
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_eq_zero_of_dense_5cad5f3be74c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_analyticAt_monicEval_d05bf81c2488

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
open Polynomial Filter Topology Classical
open PolynomialRootPredicateFactor
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PolynomialRootPredicateFactor
theorem _root_.solution : PolynomialRootPredicateFactor.Statement := by
  intro d N B a δ P hBo hBc ha hδ ⟨t₁, ht₁B, ht₁⟩ hsep hbr
  have hdense := exists_ne_zero_of_open hBc hδ ht₁B ht₁
  obtain ⟨m, F, hF, hFe⟩ := extended_factor P hBo hBc ha hδ ht₁B ht₁ hsep hbr
  obtain ⟨n, G, hG, hGe⟩ := extended_factor (fun t τ => ¬ P t τ) hBo hBc ha hδ ht₁B ht₁ hsep
    fun t₀ h₀ hδ₀ τ₀ hτ₀ => by
      obtain ⟨O, r, h1, h2, h3, h4, h5⟩ := hbr t₀ h₀ hδ₀ τ₀ hτ₀
      exact ⟨O, r, h1, h2, h3, h4, fun s hs => ⟨(h5 s hs).1, not_congr (h5 s hs).2⟩⟩
  have hCe : ∀ t ∈ B, δ t ≠ 0 → ∀ T : ℂ,
      T ^ m + ∑ k ∈ Finset.range m, F k t * T ^ k = (rootFactor (fiberPoly a t) (P t)).eval T := by
    intro t ht hδt T
    rw [hFe t ht hδt]
    simp [eval_finsetSum]
  have hEe : ∀ t ∈ B, δ t ≠ 0 → ∀ T : ℂ, T ^ n + ∑ k ∈ Finset.range n, G k t * T ^ k =
      (rootFactor (fiberPoly a t) (fun τ => ¬ P t τ)).eval T := by
    intro t ht hδt T
    rw [hGe t ht hδt]
    simp [eval_finsetSum]
  refine ⟨fun t T => T ^ m + ∑ k ∈ Finset.range m, F k t * T ^ k,
    fun t T => T ^ n + ∑ k ∈ Finset.range n, G k t * T ^ k, fun t ht T =>
      ⟨analyticAt_monicEval F t T fun k => hF k t ht, analyticAt_monicEval G t T fun k => hG k t ht⟩, ?_, ?_⟩
  · intro t ht T
    beta_reduce
    have hpair : AnalyticAt ℂ (fun s : Fin d → ℂ => (s, T)) t := analyticAt_id.prod analyticAt_const
    have hCc : ContinuousAt (fun s => T ^ m + ∑ k ∈ Finset.range m, F k s * T ^ k) t :=
      ((analyticAt_monicEval F t T fun k => hF k t ht).comp_of_eq hpair rfl).continuousAt
    have hEc : ContinuousAt (fun s => T ^ n + ∑ k ∈ Finset.range n, G k s * T ^ k) t :=
      ((analyticAt_monicEval G t T fun k => hG k t ht).comp_of_eq hpair rfl).continuousAt
    have hpc : ContinuousAt (fun s => T ^ N + ∑ j, a j s * T ^ (j : ℕ)) t :=
      (analyticAt_const.fun_add (Finset.analyticAt_fun_sum _ fun j _ =>
          (ha j t ht).fun_mul analyticAt_const)).continuousAt
    have hcont : ContinuousAt (fun s => (T ^ m + ∑ k ∈ Finset.range m, F k s * T ^ k) *
        (T ^ n + ∑ k ∈ Finset.range n, G k s * T ^ k) - (T ^ N + ∑ j, a j s * T ^ (j : ℕ))) t :=
      (hCc.mul hEc).sub hpc
    refine sub_eq_zero.1 (eq_zero_of_dense hBo hdense ht hcont fun s hs hδs => ?_)
    rw [sub_eq_zero, hCe s hs hδs, hEe s hs hδs, ← eval_mul,
      rootFactor_mul_not _ (fiberPoly_monic a s), fiberPoly_eval]
  · intro t ht hδt τ hτ
    beta_reduce
    have hτr : τ ∈ (fiberPoly a t).roots := (mem_roots_fiberPoly a t τ).2 hτ
    rw [hCe t ht hδt, hEe t ht hδt, rootFactor_eval_eq_zero, rootFactor_eval_eq_zero]
    exact ⟨and_iff_right hτr, and_iff_right hτr⟩
end PolynomialRootPredicateFactor
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
