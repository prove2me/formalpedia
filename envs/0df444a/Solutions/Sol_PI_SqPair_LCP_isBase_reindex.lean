-- Prove2me | solution 1 for PI.SqPair.LCP.isBase_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:35.197125+00:00
-- url     : https://prove2.me/submissions/21aa126e-c2c1-4d29-9fd2-4ac4053765e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.SqPair.LCP
theorem _root_.solution {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (s : κ ≃ ι) {ϖ : R} {h : Matrix ι ι R} {k : ℕ} (hb : IsBase ϖ (h.submatrix s s) k) :
    IsBase ϖ h k := by
  obtain ⟨h₁, hu, he⟩ := hb
  refine ⟨h₁.submatrix s.symm s.symm, by rw [det_submatrix_equiv_self]; exact hu, ?_⟩
  have : h = (h.submatrix s s).submatrix s.symm s.symm := by simp
  rw [this, he, submatrix_smul]; rfl
end PI.SqPair.LCP
