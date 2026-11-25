-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ord_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:24.3213+00:00
-- url     : https://prove2.me/submissions/1eaf87ab-6116-420e-b187-a1f21cce1dd5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
universe u v
variable {R S : Type*} [CommRing R] [CommRing S]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (e : R ≃+* S) (x : R) : Ring.ord R x = Ring.ord S (e x) := by
  unfold Ring.ord
  haveI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e
  haveI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.symm _ _
  let q := Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  let g : (R ⧸ Ideal.span {x}) ≃ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x}) :=
    { q.toAddEquiv with
      map_smul' := fun r m => by
        obtain ⟨m', rfl⟩ := Ideal.Quotient.mk_surjective m
        simp only [AddEquiv.toFun_eq_coe, RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv]
        rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq,
          ← map_mul]
        show q (Ideal.Quotient.mk _ (r * m')) = Ideal.Quotient.mk _ (e r) * q (Ideal.Quotient.mk _ m')
        simp [q] }
  have iso : Submodule R (R ⧸ Ideal.span {x}) ≃o Submodule S (S ⧸ Ideal.span {e x}) :=
    Submodule.orderIsoMapComap g
  have h : Order.krullDim (Submodule R (R ⧸ Ideal.span {x})) =
      Order.krullDim (Submodule S (S ⧸ Ideal.span {e x})) := by
    first
      | exact le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono)
          (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)
      | exact Order.krullDim_eq_of_orderIso iso
  unfold Module.length
  first
    | simp only [h]
    | congr 1
end ReciprocityTheory.ChartRestriction.G.AI
