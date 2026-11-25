-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_minor_reindex_26cf196fa7b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:31.987863+00:00
-- url     : https://prove2.me/submissions/18ef3795-e0cc-425f-8343-211628e6ca1a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCauchyBinetMinors

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
open Matrix Finset
open GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
namespace GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
theorem _root_.solution {R : Type*} [CommRing R] {n k : ℕ} (X : Matrix (Fin n) (Fin n) R)
    (s : Finset (Fin n)) (hk : s.card = k) :
    (X.submatrix ((↑) : s → Fin n) ((↑) : s → Fin n)).det =
      (X.submatrix (s.orderEmbOfFin hk) (s.orderEmbOfFin hk)).det := by
  rw [← det_submatrix_equiv_self (s.orderIsoOfFin hk).toEquiv]
  congr 1
end GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
