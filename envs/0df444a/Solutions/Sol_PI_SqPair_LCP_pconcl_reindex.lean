-- Prove2me | solution 1 for PI.SqPair.LCP.pconcl_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:08.413183+00:00
-- url     : https://prove2.me/submissions/7df3fa7d-52ba-40c3-974d-e045e55b8b86

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
    (s : κ ≃ ι) {A h : Matrix ι ι R} (hc : PConcl (A.submatrix s s) (h.submatrix s s)) :
    PConcl A h := by
  obtain ⟨e, f, he, heA, hef⟩ := hc
  have hA : A = (A.submatrix s s).submatrix s.symm s.symm := by simp
  have hh : h = (h.submatrix s s).submatrix s.symm s.symm := by simp
  refine ⟨e.submatrix s.symm s.symm, f.submatrix s.symm s.symm, ?_, ?_, ?_⟩
  · rw [submatrix_mul_equiv, he]
  · rw [hA, conjTranspose_submatrix, submatrix_mul_equiv, heA, ← submatrix_one_equiv s.symm]
    rw [show ((1 : Matrix κ κ R).submatrix s.symm s.symm) - e.submatrix s.symm s.symm
      = (1 - e).submatrix s.symm s.symm from rfl, submatrix_mul_equiv]
  · rw [hh, submatrix_mul_equiv, submatrix_mul_equiv, hef]
end PI.SqPair.LCP
