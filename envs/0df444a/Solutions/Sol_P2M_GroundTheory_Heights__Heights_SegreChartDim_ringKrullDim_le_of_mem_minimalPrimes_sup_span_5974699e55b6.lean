-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_le_of_mem_minimalPrimes_sup_span_5974699e55b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:24:19.444546+00:00
-- url     : https://prove2.me/submissions/1a6adc9a-5c4d-4eb2-816e-858fb5771bec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_KH_dimPIT
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
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.SegreChartDim
namespace GroundTheory.Heights₂.Heights.SegreChartDim
theorem _root_.solution {F : Type} [Field F] {τ : Type} [Fintype τ]
    (s : Finset (MvPolynomial τ F)) :
    ∀ (V W : Ideal (MvPolynomial τ F)), V.IsPrime → W ∈ (V ⊔ Ideal.span (s : Set (MvPolynomial τ F))).minimalPrimes →
      ringKrullDim (MvPolynomial τ F ⧸ V) ≤ ringKrullDim (MvPolynomial τ F ⧸ W) + (s.card : WithBot ℕ∞) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro V W hV hW
    simp only [Finset.coe_empty, Ideal.span_empty, sup_bot_eq] at hW
    rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hW
    subst hW
    simp
  | insert a s ha ih =>
    intro V W hV hW
    have hWp : W.IsPrime := hW.1.1
    have hsplit : V ⊔ Ideal.span (↑(insert a s) : Set (MvPolynomial τ F)) =
        (V ⊔ Ideal.span (s : Set (MvPolynomial τ F))) ⊔ Ideal.span {a} := by
      rw [Finset.coe_insert, Ideal.span_insert, sup_comm (Ideal.span {a}), sup_assoc]
    rw [hsplit] at hW
    obtain ⟨W', hW', hW'W⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hW.1.2)
    have hW'p : W'.IsPrime := hW'.1.1
    have hmin : W ∈ (W' ⊔ Ideal.span {a}).minimalPrimes := by
      refine ⟨⟨hWp, sup_le hW'W (le_sup_right.trans hW.1.2)⟩, fun Z ⟨hZp, hZ⟩ hZW => ?_⟩
      exact hW.2 ⟨hZp, sup_le (hW'.1.2.trans (le_sup_left.trans hZ)) (le_sup_right.trans hZ)⟩ hZW
    have h1 := ih V W' hV hW'
    rw [Finset.card_insert_of_notMem ha, Nat.cast_succ]
    by_cases haW' : a ∈ W'
    · have heq : W' ⊔ Ideal.span {a} = W' := sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haW')
      rw [heq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hmin
      subst hmin
      exact h1.trans (add_le_add le_rfl
        (show (s.card : WithBot ℕ∞) ≤ (s.card : WithBot ℕ∞) + 1 by exact_mod_cast Nat.le_succ s.card))
    · have h2 := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT F τ W' W a hW'p haW' hmin
      rw [← h2] at h1
      calc ringKrullDim (MvPolynomial τ F ⧸ V) ≤ ringKrullDim (MvPolynomial τ F ⧸ W) + 1 + (s.card : WithBot ℕ∞) := h1
        _ = ringKrullDim (MvPolynomial τ F ⧸ W) + ((s.card : WithBot ℕ∞) + 1) := by rw [add_assoc, add_comm 1]
end GroundTheory.Heights₂.Heights.SegreChartDim
