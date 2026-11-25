-- Prove2me | solution 1 for P2M_GlobalTheory_DenseSec_factor__comp_factor__7e1aebb4d17b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:15.809272+00:00
-- url     : https://prove2.me/submissions/93f324b6-8e4c-4c44-a7ee-4dfcd3319512

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSectionLiftingResidueValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.DenseSec
namespace GlobalTheory.DenseSec
theorem _root_.solution {P R : Type} [CommRing P] [CommRing R] [Algebra P R] {I J K : Ideal R}
    (hIJ : I ≤ J) (hJK : J ≤ K) :
    (Ideal.Quotient.factorₐ P hJK).comp (Ideal.Quotient.factorₐ P hIJ) =
      Ideal.Quotient.factorₐ P (hIJ.trans hJK) := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl
end GlobalTheory.DenseSec
