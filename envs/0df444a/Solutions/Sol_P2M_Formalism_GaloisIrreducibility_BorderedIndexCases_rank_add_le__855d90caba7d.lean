-- Prove2me | solution 1 for P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_rank_add_le__855d90caba7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:51.974774+00:00
-- url     : https://prove2.me/submissions/4e9fc195-e7ab-4bc9-a351-f4bd6bc1ce33

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]
namespace Formalism.GaloisIrreducibility.BorderedIndexCases
theorem _root_.solution {K : Type} [Field K] {m : ℕ} (A B : Matrix (Fin m) (Fin m) K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
end Formalism.GaloisIrreducibility.BorderedIndexCases
