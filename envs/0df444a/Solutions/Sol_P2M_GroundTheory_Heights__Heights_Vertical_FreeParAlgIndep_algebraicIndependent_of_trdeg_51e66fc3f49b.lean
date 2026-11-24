-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_algebraicIndependent_of_trdeg_51e66fc3f49b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:01.353891+00:00
-- url     : https://prove2.me/submissions/4a8a1d92-5a17-4b1f-ac43-ae384c6beed2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFreeParAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFreeParAlgIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial Cardinal
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.FreeParAlgIndep
namespace GroundTheory.Heights₂.Heights.Vertical.FreeParAlgIndep
theorem _root_.solution {k L : Type} [Field k] [Field L] [Algebra k L]
    (A₀ : Subalgebra k L) {ι : Type} [Finite ι] (w : ι → L)
    [Algebra.IsAlgebraic (Algebra.adjoin A₀ (Set.range w)) L] {e : ℕ}
    (htr : Algebra.trdeg k A₀ ≤ e) (hle : (e : Cardinal) + #ι ≤ Algebra.trdeg k L) :
    AlgebraicIndependent A₀ w := by
  have : FaithfulSMul k A₀ :=
    (faithfulSMul_iff_algebraMap_injective k A₀).2 (algebraMap k A₀).injective
  have : FaithfulSMul A₀ L :=
    (faithfulSMul_iff_algebraMap_injective A₀ L).2 Subtype.val_injective
  have hadd := trdeg_add_eq k A₀ (A := L)
  refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite A₀ w ?_).1
  have h3 : #ι + (e : Cardinal) ≤ Algebra.trdeg A₀ L + e := by
    rw [add_comm, add_comm _ (e : Cardinal)]
    refine hle.trans ?_
    rw [← hadd]
    gcongr
  exact (Cardinal.add_le_add_iff_of_lt_aleph0 (Cardinal.natCast_lt_aleph0)).1 h3
end GroundTheory.Heights₂.Heights.Vertical.FreeParAlgIndep
