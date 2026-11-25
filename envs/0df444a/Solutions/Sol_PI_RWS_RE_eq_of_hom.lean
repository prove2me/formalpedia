-- Prove2me | solution 1 for PI.RWS.RE_eq_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:47.582923+00:00
-- url     : https://prove2.me/submissions/ae82944e-b967-4b8c-b083-daabbea03d8a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowWtSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowWeightSpan_RowWtSpanOfBideterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.RWS
open PI.RW
namespace PI.RWS
theorem _root_.solution {K : Type} [CommRing K] {k : ℕ} (a : Fin k)
    (f : MvPolynomial (Fin k × Fin k) K) (d : ℕ)
    (h : IsWeightedHomogeneous (rowW a) f d) : RE K k a a f = (d : K) • f := by
  have h' := h.sum_weight_X_mul_pderiv
  unfold RE
  rw [Nat.cast_smul_eq_nsmul K d f, ← h']
  symm
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun x _ hx => by simp [rowW, hx])
    (fun h => absurd (Finset.mem_univ a) h)]
  simp [rowW]
end PI.RWS
