-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FormIntLelong_proof_27b9bde41f3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:01:49.461668+00:00
-- url     : https://prove2.me/submissions/d8601c83-fa45-47a3-afc2-a07a281fdca4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceFormLelong
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSectionHyperplaneAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivCyclePrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormSectionAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFormIntLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLogBound_proof_ab4a666aa1df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivCyclePrime_proof_a79e8cf92f7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FsLogSmul_proof_706c8ded022f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_proof_cbda02c103b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiffOn_fsLogReg_ea0641a814f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fsLogReg_smul_17c74930b878


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
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
namespace FormIntLelong
theorem _root_.solution (hCP : ConeToProjective.Statement)
    (hCh : ChowFormSectionAlgClosed.Statement) (hFS : FormIntSlice.Statement)
    (hSL : SliceFormLelong.Statement) : FormIntLelong.Statement := by
  intro n e h W u u' δ hW hg hu' hδ
  obtain ⟨F, hF⟩ := hg
  obtain ⟨ℓ, hℓW, hℓP⟩ := SectionHyperplaneAvoid.proof n W u' hW
  have ha0 : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → fsLogReg h u δ (t • x) = fsLogReg h u δ x :=
    fun t x ht => fsLogReg_smul h u δ t x ht
  have ha1 : ContDiffOn ℝ ∞ (fsLogReg h u δ) {x | x ≠ 0} := contDiffOn_fsLogReg h u hδ

  have hWc := hCP n (e + 1) h W F ℓ (fsLogReg h u δ) hW hF hℓW ha0 ha1.continuousOn

  obtain ⟨c, -, gP, hgP, -⟩ := hCh ℂ n (e + 1) W F u' hW hF hu'
  have hcyc : cycleIntegral h (divCycle W u') e (fsLogReg h u δ) =
      ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fsLogReg h u δ)
          (fun _ x => Real.log (h.dualNorm x)) := by
    unfold cycleIntegral
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [hCP n e h P (gP P) ℓ (fsLogReg h u δ) (DivCyclePrime.proof n W u' hW P hP) (hgP P hP)
      (hℓP P hP) ha0 ha1.continuousOn]
  rw [hcyc, hWc]

  refine (hSL n e h W F u' ℓ (fsLogReg h u δ) hW hF hu' hℓW hℓP ha0 ha1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hFS n e h W F ℓ (fsLogReg h u δ) (fsLogReg h u' ε) hW hF hℓW ha0 ha1.continuousOn
    (fun t x ht => fsLogReg_smul h u' ε t x ht) (contDiffOn_fsLogReg h u' hε)).symm
end FormIntLelong
end GroundTheory.Heights₂.Heights
