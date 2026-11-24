-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_eq_det_c2f7ea43a739
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:14:14.116772+00:00
-- url     : https://prove2.me/submissions/68a2e771-0fdb-4a51-adfb-921b34a7065f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    vandermondeOf v = (Matrix.vandermonde (fun i => -v i)).det := by
  rw [Matrix.det_vandermonde, vandermondeOf]
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
  ring
end GroundTheory.Heights₂.Heights.RestTerms.Flag
