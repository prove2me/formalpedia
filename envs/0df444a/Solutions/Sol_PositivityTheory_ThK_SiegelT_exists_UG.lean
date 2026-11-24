-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.exists_UG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:37:44.36378+00:00
-- url     : https://prove2.me/submissions/b9e5a4c9-d740-4b71-b738-e6edf1b6c994

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β ν ν' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]
  [Fintype ν'] [DecidableEq ν']
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution {J g : Matrix β β E} (hJ : IsUnit J.det) (hg : gᵀ * J * g.map c = J) :
    ∃ u : UG c J, ((u : GL β E) : Matrix β β E) = g := by
  have hd : g.det * J.det * (g.map c).det = J.det := by
    rw [← Matrix.det_transpose g, ← Matrix.det_mul, ← Matrix.det_mul, hg]
  have hmap : (g.map c).det = c g.det := by
    rw [AlgHom.map_det]; rfl
  have h1 : g.det * c g.det = 1 := by
    apply hJ.mul_left_cancel
    rw [mul_one]
    calc J.det * (g.det * c g.det) = g.det * J.det * (g.map c).det := by rw [hmap]; ring
      _ = J.det := hd
  exact ⟨⟨Matrix.nonsingInvUnit g (isUnit_iff_exists_inv.mpr ⟨_, h1⟩), hg⟩, rfl⟩
end PositivityTheory.ThK.SiegelT
