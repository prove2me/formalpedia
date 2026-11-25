-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_locDens_lincomb_le_7cc29db62577
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:53:13.528358+00:00
-- url     : https://prove2.me/submissions/65b387f4-dddb-4c1c-92d5-000c11ab2c4d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_EnergySum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_mdisc_sum_le_df9fc20e43da
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_hessC_finset_sum_8ccaf9ba300e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_lincomb___d6eca3b5a7b8
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_posSemidef
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open MeasureTheory
open scoped ContDiff ComplexOrder
open ReciprocityTheory.AnForm (hessC maDens mdisc levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith)
noncomputable section
variable {D : ℕ}
variable {X : Type*} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution (A : FinHolAtlas D X) (Yo : Set X) {m : ℕ} (P : Fin m → LocPot X)
    (a : Fin D → Fin m → ℝ) (hpot : ∀ i, IsPotential A (P i)) (hnn : ∀ i, FormNonneg A Yo (P i))
    (j : Fin A.n) (y : Fin D → ℂ) (hy : y ∈ (A.chart j).target) (hY : (A.chart j).symm y ∈ Yo) :
    |locDens A (fun k => lincomb m (a k) P) j y| ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * locDens A (fun k => P (σ k)) j y := by
  have hmem : ∀ i, (A.chart j).symm y ∈ (P i).U ((A.chart j).symm y) := fun i => (P i).mem_U _
  let f : Fin m → (Fin D → ℂ) → ℝ := fun i y' => (P i).φ ((A.chart j).symm y) ((A.chart j).symm y')
  have hC : ∀ i, ContDiffAt ℝ 2 (f i) y := fun i =>
    (((hpot i).1 _ j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm
      ((P i).isOpen_U _)).mem_nhds ⟨hy, hmem i⟩)).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)
  have hP : ∀ i, (hessC (f i) y).PosSemidef := fun i =>
    ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hC i) fun w => hnn i _ j y ⟨hy, hY, hmem i⟩ w
  have hS : ∀ k, hessC (fun y' => (lincomb m (a k) P).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      ∑ i, (a k i : ℂ) • hessC (f i) y := fun k => by
    simp_rw [lincomb_φ]
    exact hessC_finset_sum _ _ f y fun i _ => hC i
  have hc : (0 : ℝ) ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg zero_le_two Real.pi_pos.le) _)
  have hL : locDens A (fun k => lincomb m (a k) P) j y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => ∑ i, (a k i : ℂ) • hessC (f i) y).re := by
    simp only [locDens, maDens, hS]
  have hR : ∀ σ : Fin D → Fin m, locDens A (fun k => P (σ k)) j y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => hessC (f (σ k)) y).re := fun σ => rfl
  rw [hL, abs_mul, abs_of_nonneg hc]
  calc (D.factorial : ℝ) * (2 / Real.pi) ^ D *
        |(mdisc fun k => ∑ i, (a k i : ℂ) • hessC (f i) y).re|
      ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D *
          ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * (mdisc fun k => hessC (f (σ k)) y).re :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
          (norm_mdisc_sum_le a (fun k i => hessC (f i) y) fun _ i => hP i)) hc
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [hR]
        ring
end GroundTheory.Heights₂.Heights.AnalyticLimit
