-- Prove2me | solution 1 for PI.SqPair.LCP.phyp_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:12.877+00:00
-- url     : https://prove2.me/submissions/0b9d9ad6-b1d3-475b-967e-0e45a4019a28

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
    (s : κ ≃ ι) {ϖ : R} {A A' h : Matrix ι ι R} {k : ℕ} (hP : PHyp ϖ A A' h k) :
    PHyp ϖ (A.submatrix s s) (A'.submatrix s s) (h.submatrix s s) k := by
  obtain ⟨⟨hA, hAd⟩, ⟨hA', hA'd⟩, hr⟩ := hP
  refine ⟨⟨by rw [conjTranspose_submatrix, hA], by rw [det_submatrix_equiv_self]; exact hAd⟩,
    ⟨by rw [conjTranspose_submatrix, hA'], by rw [det_submatrix_equiv_self]; exact hA'd⟩, ?_⟩
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hr, submatrix_smul]; rfl
end PI.SqPair.LCP
