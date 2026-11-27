-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFormsAlt_proof_20f45a120250
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:58:26.464327+00:00
-- url     : https://prove2.me/submissions/7af5590d-c174-4fec-a7dd-4d4e0c7a7d7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExistsFormOfMemChartRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFormsAlt_mkF_chartMonomial_84ac4eaecbed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFormsAlt_exists_form_of_mem_chartRing_e51b8144b218
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open ChartFormsAlt
namespace GroundTheory.Heights₂.Heights
namespace ChartFormsAlt
theorem _root_.solution : ChartFormsAlt.Statement := by
  classical
  intro ι _ _ n P D
  have hrep : ∀ (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)),
      ∃ (F : MvPolynomial (Coord n) ℤ) (e : ι → ℕ), IsWeightedHomogeneous (coordDeg n) F e ∧
        (P.IsLive c → D.elt j / P.chartPow c D.deg * P.mkF (chartMonomial c e) = P.mkF F) := by
    intro c j
    by_cases hc : P.IsLive c
    · obtain ⟨F, e, hF, h⟩ := exists_form_of_mem_chartRing P c hc (D.chart_mem c hc j)
      exact ⟨F, e, hF, fun _ ↦ h⟩
    · exact ⟨0, 0, isWeightedHomogeneous_zero _ _ _, fun h ↦ absurd h hc⟩
  choose F e hF hFe using hrep
  refine ⟨fun k ↦ 1 + (∑ c, ∑ j, e c j k) + (-D.deg k).toNat, fun d hd ↦ ?_⟩
  have hle : ∀ c j k, e c j k ≤ ∑ c, ∑ j, e c j k := fun c j k ↦
    (Finset.single_le_sum (f := fun j ↦ e c j k) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun c ↦ ∑ j, e c j k) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c))
  have hdk : ∀ k, 1 + (∑ c, ∑ j, e c j k) + (-D.deg k).toNat ≤ d k := fun k ↦ hd k
  have ht : ∀ c j k, (e c j k : ℤ) ≤ d k + D.deg k := by
    intro c j k
    have h1 := hle c j k
    have h2 := hdk k
    omega
  have hnn : ∀ k, 0 ≤ (d k : ℤ) + D.deg k := by
    intro k
    have h2 := hdk k
    omega
  let t : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → ι → ℕ :=
    fun c j k ↦ ((d k : ℤ) + D.deg k - e c j k).toNat
  refine ⟨fun c j ↦ if P.IsLive c then F c j * chartMonomial c (t c j) else 0, ?_⟩
  refine ⟨fun k ↦ ?_, hnn, fun c j ↦ ?_, fun c hc j ↦ ?_, fun c hc j ↦ ?_⟩
  · have h2 := hdk k
    omega
  · refine ⟨fun k ↦ ((d k : ℤ) + D.deg k).toNat, ?_, fun k ↦ Int.toNat_of_nonneg (hnn k)⟩
    split_ifs with hc
    · have hd' : e c j + t c j = fun k ↦ ((d k : ℤ) + D.deg k).toNat := by
        funext k
        have h1 := ht c j k
        simp only [Pi.add_apply, t]
        omega
      rw [← hd']
      exact (hF c j).mul (isWeightedHomogeneous_chartMonomial c (t c j))
    · exact isWeightedHomogeneous_zero _ _ _
  · simp only [if_pos hc]
    have hy : ∀ k, P.mkF (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
    have hC : P.chartPow c D.deg ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hy k)
    have key : P.mkF (chartMonomial c (e c j)) * P.mkF (chartMonomial c (t c j)) =
        P.mkF (chartMonomial c d) * P.chartPow c D.deg := by
      rw [mkF_chartMonomial, mkF_chartMonomial, mkF_chartMonomial, ArithVariety.chartPow,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), ← zpow_add₀ (hy k)]
      congr 1
      have h1 := ht c j k
      simp only [t]
      omega
    rw [map_mul, ← hFe c j hc, mul_assoc, key]
    field_simp
  · simp [if_neg hc]
end ChartFormsAlt
end GroundTheory.Heights₂.Heights
