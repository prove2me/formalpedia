-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_oneBlock_homogeneousComponent_cdc548b95706
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:15:26.238564+00:00
-- url     : https://prove2.me/submissions/6a91d7ff-8e1c-44c2-9104-49c1a45cf90a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PointDegreePosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPointDegreePos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    oneBlock (S := k) (N := N) (homogeneousComponent n f) =
      homogeneousComponent n (oneBlock (S := k) (N := N) f) := by
  classical
  have ho : ∀ g, oneBlock (S := k) (N := N) g = rename (HilbertPositive.blockEquiv N) g := fun _ => rfl
  ext d
  set d' := Finsupp.mapDomain (HilbertPositive.blockEquiv N).symm d with hd'
  have hd : d = Finsupp.mapDomain (HilbertPositive.blockEquiv N) d' := by
    rw [hd', ← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hdeg : d.degree = d'.degree := by
    rw [hd, Finsupp.degree_mapDomain]
  rw [ho, ho, coeff_homogeneousComponent, hd,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective, coeff_homogeneousComponent, ← hd, hdeg]
end GroundTheory.Heights₂.Heights.Kleiman
