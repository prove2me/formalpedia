-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Fr.emb_i
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:19.793708+00:00
-- url     : https://prove2.me/submissions/3b9db3da-a39b-494e-b12b-1385baa20800

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β β₁ μ ν : Type} [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁] [Fintype μ] [DecidableEq μ]
  [Fintype ν] [DecidableEq ν]
variable {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {H : Matrix μ μ E} {ι : Matrix β β₁ E} {Z : Matrix β μ E}
  {π : Matrix β₁ β E} {ρ : Matrix μ β E}
namespace PositivityTheory.ThKF0.Chr
namespace Fr
theorem _root_.solution (h : Fr c J J₁ H ι Z π ρ) (p : UG c J₁ × UG c H) : (h.emb p).1.1 * ι = ι * p.1.1.1 := by
  show (ι * p.1.1.1 * π + Z * p.2.1.1 * ρ) * ι = _
  rw [Matrix.add_mul, Matrix.mul_assoc, h.pi, Matrix.mul_assoc (Z * _), h.ri]
  simp
end Fr
end PositivityTheory.ThKF0.Chr
