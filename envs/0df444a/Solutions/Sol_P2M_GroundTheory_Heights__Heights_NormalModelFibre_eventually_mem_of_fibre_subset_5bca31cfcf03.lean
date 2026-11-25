-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelFibre_eventually_mem_of_fibre_subset_5bca31cfcf03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:58.25848+00:00
-- url     : https://prove2.me/submissions/1690828b-facf-47bb-8f8a-afe2ae6600ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PModelLocalizationMaximalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelFibre_isClosed_zeroSetIn_e835e0b1dee8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelFibre_continuous_firstCoords_380cb0872c21
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelProper_proof_63b250feae60
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ModelLocalizationMaximalPoint_proof_1cc86273a304


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
open MvPolynomial Filter Topology ComplexSets Metric
noncomputable section
open GroundTheory.Heights₂.Heights.NormalModelFibre
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
namespace GroundTheory.Heights₂.Heights.NormalModelFibre
theorem _root_.solution {q : Fin n → ℂ} {U : Set (Fin n ⊕ Fin M.m → ℂ)} (hU : IsOpen U)
    (hfib : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q → w ∈ U) :
    ∃ N ∈ 𝓝 q, ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N → w ∈ U := by
  set K : Set (Fin n ⊕ Fin M.m → ℂ) := {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ closedBall q 1} ∩ Uᶜ with hKdef
  have hKb : Bornology.IsBounded K :=
    (IndefiniteRowSideFullHecke.ComplexSets.NormalModelProper.proof n J M (closedBall q 1) isBounded_closedBall).subset
      Set.inter_subset_left
  have hKc : IsClosed K :=
    ((isClosed_zeroSetIn M).inter (isClosed_closedBall.preimage (continuous_firstCoords M))).inter
      hU.isClosed_compl
  have hK : IsCompact K := isCompact_of_isClosed_isBounded hKc hKb
  have hKi : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K) :=
    (hK.image (continuous_firstCoords M)).isClosed
  have hq : q ∉ IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K := by
    rintro ⟨w, ⟨⟨hw, -⟩, hwU⟩, hwq⟩
    exact hwU (hfib w hw hwq)
  refine ⟨closedBall q 1 ∩ (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K)ᶜ,
    inter_mem (closedBall_mem_nhds q one_pos) (hKi.isOpen_compl.mem_nhds hq), ?_⟩
  intro w hw hwN
  by_contra hwU
  exact hwN.2 ⟨w, ⟨⟨hw, hwN.1⟩, hwU⟩, rfl⟩
end GroundTheory.Heights₂.Heights.NormalModelFibre
