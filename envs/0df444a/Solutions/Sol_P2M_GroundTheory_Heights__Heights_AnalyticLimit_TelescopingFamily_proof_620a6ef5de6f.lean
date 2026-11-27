-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_TelescopingFamily_proof_620a6ef5de6f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:33.190237+00:00
-- url     : https://prove2.me/submissions/a7e5b440-54c2-4c38-80e1-e8d39ea6ea3b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_one_le_of_exp_le_4df85ca77316
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_nonneg_330338178ab7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_mono_55b70623b837
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_teleConst_pos_d7321146ea88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_C_nonneg_072e5126db6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_near_d4efcaad67bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_far_e081df8bf3a3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)
noncomputable section
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
namespace TelescopingFamily
theorem _root_.solution : TelescopingFamily.Statement := by
  intro X _ D A F Λ
  set B : ℝ := ∑ i, (F.sys i).teleConst with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => ((F.sys i).teleConst_pos).le
  have hMB : ∀ i, (F.sys i).teleConst ≤ B := fun i =>
    Finset.single_le_sum (f := fun i => (F.sys i).teleConst)
      (fun i _ => ((F.sys i).teleConst_pos).le) (Finset.mem_univ i)
  have hCB : ∀ i, (F.sys i).C ≤ B := fun i => by
    refine le_trans ?_ (hMB i)
    unfold System.teleConst
    have := le_abs_self (F.sys i).C
    have := abs_nonneg (F.R i).C
    have := sq_nonneg (F.sys i).C
    linarith
  set C' : ℝ := (|Λ| + 1) * B with hC'
  have hBC' : B ≤ C' := by
    rw [hC']
    nlinarith [abs_nonneg Λ]
  refine ⟨C', ∑ i, |(F.sys i).ell₀| + Real.exp 1, fun c hc t t' ht' htt hℓ x hx => ?_⟩
  have h0 : ∀ i, (F.sys i).ell₀ ≤ ell t := fun i => by
    refine le_trans (le_trans (le_abs_self _) ?_) hℓ
    have := Finset.single_le_sum (f := fun i => |(F.sys i).ell₀|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    have := Real.exp_pos 1
    linarith
  have he : Real.exp 1 ≤ ell t := by
    refine le_trans ?_ hℓ
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (F.sys i).ell₀)
    linarith
  have h1 := one_le_of_exp_le he
  have hx' : ∀ i, x ∈ (F.R i).Yo := fun i => (F.Yo_eq i).symm ▸ hx
  have hr' : ∀ i, (F.R i).r x = F.r x := fun i => F.r_eq i x hx
  have hsum : |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤
      ∑ i, |c i| * |(F.sys i).ph t x - (F.sys i).ph t' x| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => abs_mul _ _
  have hc0 : ∑ i, |c i| ≤ |Λ| := le_trans hc (le_abs_self Λ)
  have hfin : ∀ K : ℝ, 0 ≤ K → (∀ i, |(F.sys i).ph t x - (F.sys i).ph t' x| ≤ B * K) →
      |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤ C' * K := by
    intro K hK hi
    refine le_trans hsum (le_trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hi i) (abs_nonneg (c i))) ?_)
    rw [← Finset.sum_mul, hC']
    have hBK := mul_nonneg hB0 hK
    nlinarith [mul_le_mul_of_nonneg_right hc0 hBK]
  have ht : 0 < t := lt_of_lt_of_le ht' htt
  have ha : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
  refine ⟨fun hr => hfin _ (add_nonneg ha (errE_nonneg (hB0.trans hBC') h1)) fun i => ?_,
    fun hr => hfin _ (Real.log_nonneg (le_trans h1 (le_of_lt hr))) fun i => ?_⟩
  · have hCi := (F.sys i).C_nonneg ht (h0 i) h1 x
    refine le_trans ((F.sys i).tele_near ht' htt (h0 i) he (hx' i) ((hr' i).symm ▸ hr))
      (mul_le_mul (hMB i) ?_ (add_nonneg ha (errE_nonneg hCi h1)) hB0)
    linarith [errE_mono ((hCB i).trans hBC') h1]
  · have h := (F.sys i).tele_far ht' htt (h0 i) he (hx' i) ((hr' i).symm ▸ hr)
    rw [hr' i] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (hMB i)
      (Real.log_nonneg (le_trans h1 (le_of_lt hr))))
end TelescopingFamily
end GroundTheory.Heights₂.Heights.AnalyticLimit
