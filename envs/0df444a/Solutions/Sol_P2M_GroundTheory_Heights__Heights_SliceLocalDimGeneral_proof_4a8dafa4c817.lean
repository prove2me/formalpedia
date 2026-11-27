-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceLocalDimGeneral_proof_4a8dafa4c817
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:47.989887+00:00
-- url     : https://prove2.me/submissions/32f6426e-b649-4de6-8759-11b9b25b8ff4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLocalDimGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_one_le_ringKrullDim_localRingAt_sliceIdeal_93fe90c97dbc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_eval_ne_zero_of_isOpen_pi_53a6727c2b58


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
open MvPolynomial Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SliceLocalDimGeneral
theorem _root_.solution (hL : LocalDimDomain.Statement)
    (hU : SliceLocalDimUpperZariski.Statement) : SliceLocalDimGeneral.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨F, hF, hgood⟩ := hU n d J q hJ hdim hq
  have hloc := hL n (d + 1) J hJ hdim q hq
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let ψ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hψ : Continuous ψ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hLF => le_antisymm (hgood L hLF)
    (one_le_ringKrullDim_localRingAt_sliceIdeal J L q hloc)⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ := exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hψ) ⟨e L₀, hL₀⟩
    exact ⟨ψ y, hyU, hyF⟩
end SliceLocalDimGeneral
end GroundTheory.Heights₂.Heights
