-- Prove2me | solution 1 for QEC.QLDPC.QuantumCodeFamily.boundedLocality_of_region_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:28:44.820195+00:00
-- url     : https://prove2.me/submissions/bcfc49eb-8403-4d06-894b-77583156ad6e

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_boundedLocality_of_region_bounds


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC.QuantumCodeFamily
theorem _root_.solution
    (F : QuantumCodeFamily A ι κ) (a : A) {bound : Nat}
    (hcheck : ∀ checkIndex,
      ((F.presentation a).checks checkIndex).region.selected.card ≤ bound)
    (hcoordinate : ∀ coordinate,
      ((F.presentation a).incidence.variableSupport coordinate).card ≤ bound) :
    Coding.BoundedLocality (F.localityProfile a) bound :=
  (F.presentation a).boundedLocality_of_region_bounds hcheck hcoordinate
end QEC.QLDPC.QuantumCodeFamily
