-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:57.87778+00:00
-- url     : https://prove2.me/submissions/d969fc52-c604-4f2a-b3f5-1901a9ab811f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let g := Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  let f : (R ⧸ Ideal.span {x}) →ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x}) :=
    { toFun := g
      map_add' := map_add g
      map_smul' := fun r a => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, g,
          Ideal.quotientEquiv_mk, RingHom.coe_coe] }
  unfold Ring.ord
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact (Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective f (by exact g.bijective))).symm
end GroundTheory.Heights₂.Heights
