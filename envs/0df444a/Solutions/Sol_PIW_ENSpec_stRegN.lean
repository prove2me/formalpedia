-- Prove2me | solution 1 for PIW.ENSpec.stRegN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:50.892793+00:00
-- url     : https://prove2.me/submissions/f9b89fc3-8623-49d6-80d0-a9945d4f9317

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton
import Theorems.Thm_PIW_ENSpec_wreg_of_subsingleton
import Theorems.Thm_PIW_ENSpec_wreg_ses
import Theorems.Thm_PIW_ENSpec_gmap_surjective
import Theorems.Thm_PIW_ENSpec_piece_wreg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
namespace PIW.ENSpec
theorem _root_.solution : StRegN.{u} := by
  intro R _ D a x hx
  induction a with
  | zero =>
    have : Subsingleton (MvPolynomial (Fin D) R ⧸
        (Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    exact wreg_of_subsingleton _
  | succ a ih =>
    exact wreg_ses (tl x) (LinearMap.ker (gmap a)).subtype (gmap a) Subtype.val_injective
      (LinearMap.exact_subtype_ker_map _) (gmap_surjective a) (piece_wreg a x hx) ih
end PIW.ENSpec
