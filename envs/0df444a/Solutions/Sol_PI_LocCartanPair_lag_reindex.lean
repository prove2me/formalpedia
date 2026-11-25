-- Prove2me | solution 1 for PI.LocCartanPair.lag_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:53.41645+00:00
-- url     : https://prove2.me/submissions/0938f7cb-184d-405f-a943-3b49fd2400a7

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocCartanPair
open Matrix IsLocalRing
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.LocCartanPair
theorem _root_.solution {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (s : β ≃ ι) (A : Matrix ι ι R) (E : Matrix β β R) (hE : E * E = E)
    (hEA : Eᴴ * A.submatrix s s = A.submatrix s s * (1 - E)) :
    E.submatrix s.symm s.symm * E.submatrix s.symm s.symm = E.submatrix s.symm s.symm ∧
      (E.submatrix s.symm s.symm)ᴴ * A = A * (1 - E.submatrix s.symm s.symm) := by
  have hA : A = (A.submatrix s s).submatrix s.symm s.symm := by simp
  constructor
  · rw [submatrix_mul_equiv, hE]
  · have h1 : (1 : Matrix ι ι R) - E.submatrix s.symm s.symm = (1 - E).submatrix s.symm s.symm := by
      ext i j
      simp [Matrix.one_apply]
    rw [h1, conjTranspose_submatrix]
    conv_lhs => rw [hA]
    conv_rhs => rw [hA]
    rw [submatrix_mul_equiv, submatrix_mul_equiv, hEA]
end PI.LocCartanPair
