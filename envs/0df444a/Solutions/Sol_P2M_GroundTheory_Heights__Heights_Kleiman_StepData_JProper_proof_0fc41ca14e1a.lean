-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepData_JProper_proof_0fc41ca14e1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:39.115381+00:00
-- url     : https://prove2.me/submissions/b4f823c2-dd9e-4ceb-9213-0daeb8e5e4e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartInvertible_twistMul_744ff127a3f7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mul_mem_twistMod_9a577238c287
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_form_chart_1de3df5576aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace StepData.JProper
theorem _root_.solution : StepData.JProper.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x T
  have hloc : ∀ I : Chart x, ∃ (g : Poly k N) (e : ℕ), g.IsHomogeneous e ∧ aeval x g ≠ 0 ∧
      ∀ δ ∈ T.D.sub I, ∃ o ∈ twistMod k x (e : ℤ) I, aeval x g * δ = T.si * o := fun I =>
    exists_form_chart (chartInvertible_twistMul T.M T.p (T.m - T.c₁) I)
      ((Submodule.mem_iInf _).mp T.si_mem I) T.si_ne
  choose g e hg hg0 hgD using hloc
  refine ⟨∏ I, g I, ∑ I, e I, Ideal.subset_span ⟨∑ I, e I, IsHomogeneous.prod _ _ _
    fun I _ => hg I, fun I δ hδ => ?_⟩, IsHomogeneous.prod _ _ _ fun I _ => hg I, ?_⟩
  · obtain ⟨o, ho, hδo⟩ := hgD I δ hδ
    have hrest : (∏ J ∈ Finset.univ.erase I, g J).IsHomogeneous (∑ J ∈ Finset.univ.erase I, e J) :=
      IsHomogeneous.prod _ _ _ fun J _ => hg J
    refine ⟨aeval x (∏ J ∈ Finset.univ.erase I, g J) * o, ?_, ?_⟩
    · have hm := aeval_mul_mem_twistMod hrest ho
      have hdeg : ((e I : ℕ) : ℤ) + ((∑ J ∈ Finset.univ.erase I, e J : ℕ) : ℤ) =
          ((∑ J, e J : ℕ) : ℤ) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ I)]; push_cast; ring
      rwa [hdeg] at hm
    · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (aeval x (g I)),
        mul_assoc, hδo]
      ring
  · rw [mem_primeOf_of_isHomogeneous x (IsHomogeneous.prod _ _ _ fun I _ => hg I), map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun I _ => hg0 I
end StepData.JProper
end GroundTheory.Heights₂.Heights.Kleiman
