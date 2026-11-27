-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_DegreeRatio_proof_626d54f907a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:25.360588+00:00
-- url     : https://prove2.me/submissions/76bfd95b-9490-41b4-8140-407d69fd1573

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PDegreeRatio
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_one_sub_prod_le_sum_c7f204f56b29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_raiseSmall_factor_3dc9e86772a4
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
namespace GroundTheory.Heights₂.Heights.FourB
namespace DegreeRatio
theorem _root_.solution : DegreeRatio.Statement := by
  intro f N j' x δ ⟨hδ, hx, hacross⟩
  set P : Fin f → Fin N → Fin N → ℝ :=
    fun τ i l => if Across N j' i l then 1 - δ / (x τ i - x τ l) else 1 with hPdef
  set H : Fin f → Fin N → Fin N → ℝ :=
    fun τ i l => if Across N j' i l then δ / (x τ i - x τ l) else 0 with hHdef

  have hfac : ∀ τ (i l : Fin N), 0 < (if i < l then x τ i - x τ l else 1) := by
    intro τ i l
    split_ifs with h
    · exact sub_pos.mpr (hx τ i l h)
    · exact one_pos
  have hdeg : 0 < weightDegree x :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l _ => hfac τ i l

  have hP0 : ∀ τ i l, 0 < P τ i l := by
    intro τ i l
    simp only [hPdef]
    split_ifs with hA
    · have hd := hacross τ i l hA
      have hpos : 0 < x τ i - x τ l := by linarith
      have : δ / (x τ i - x τ l) < 1 := (div_lt_one hpos).mpr hd
      linarith
    · exact one_pos
  have hP1 : ∀ τ i l, P τ i l ≤ 1 := by
    intro τ i l
    simp only [hPdef]
    split_ifs with hA
    · have hd := hacross τ i l hA
      have : 0 ≤ δ / (x τ i - x τ l) := div_nonneg hδ (by linarith)
      linarith
    · exact le_rfl
  have hPH : ∀ τ i l, 1 - P τ i l ≤ H τ i l := by
    intro τ i l
    simp only [hPdef, hHdef]
    split_ifs <;> simp

  have hratio : weightDegree (raiseSmall N j' δ x) / weightDegree x = ∏ τ, ∏ i, ∏ l, P τ i l := by
    rw [div_eq_iff hdeg.ne']
    simp only [weightDegree, raiseSmall_factor N j' x δ hx, Finset.prod_mul_distrib, hPdef]
    ring
  rw [hratio]
  have hin0 : ∀ τ i, 0 ≤ ∏ l, P τ i l := fun τ i => Finset.prod_nonneg fun l _ => (hP0 τ i l).le
  have hin1 : ∀ τ i, ∏ l, P τ i l ≤ 1 :=
    fun τ i => Finset.prod_le_one (fun l _ => (hP0 τ i l).le) fun l _ => hP1 τ i l
  have hmid0 : ∀ τ, 0 ≤ ∏ i, ∏ l, P τ i l := fun τ => Finset.prod_nonneg fun i _ => hin0 τ i
  have hmid1 : ∀ τ, ∏ i, ∏ l, P τ i l ≤ 1 :=
    fun τ => Finset.prod_le_one (fun i _ => hin0 τ i) fun i _ => hin1 τ i
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l _ => hP0 τ i l
  · exact Finset.prod_le_one (fun τ _ => hmid0 τ) fun τ _ => hmid1 τ
  · refine one_sub_prod_le_sum _ _ _ hmid0 hmid1 fun τ => ?_
    refine one_sub_prod_le_sum _ _ _ (hin0 τ) (hin1 τ) fun i => ?_
    exact one_sub_prod_le_sum _ _ _ (fun l => (hP0 τ i l).le) (hP1 τ i) (hPH τ i)
end DegreeRatio
end GroundTheory.Heights₂.Heights.FourB
