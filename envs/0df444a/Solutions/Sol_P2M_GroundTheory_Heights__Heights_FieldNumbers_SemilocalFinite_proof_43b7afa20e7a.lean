-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalFinite_proof_43b7afa20e7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:55:47.961858+00:00
-- url     : https://prove2.me/submissions/98c5ee10-6532-4bbf-a38d-c2c718719d3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalIntegralClosureFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_module_finite_of_forall_mem_span_0fcf8b912263
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_homFracDegZero_of_mem_degZeroLoc_d64725dd4b85


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace SemilocalFinite
theorem _root_.solution (h1 : SemilocalIntegral.Statement.{u})
    (h2 : LocalIntegralClosureFinite.Statement.{u}) (h3 : DegZeroLocNoetherian.Statement.{u}) :
    SemilocalFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hd' hd W hW hdW hle
  have := hP'.isPrime
  set A := degZeroLoc (contractPrime j P') {W}
  set B := degZeroLoc P' (fibrePrimes j P' W)
  set A' := A.map (contractFracMap j P')
  have : IsNoetherianRing A :=
    h3 F K (fun k => ι' (j k)) _ (isMultiProjPrime_contractPrime _ _ hP') W hW hle
  have hint : Algebra.IsIntegral A B := h1 F K K' j ι' P' hP' n hd' hd W hW hdW hle
  obtain ⟨s, -, hs⟩ := h2 F K K' j ι' P' hP' (hd.trans hd'.symm) W hW hle
  let φA : A →+* A' := (((contractFracMap j P').comp A.val).codRestrict A'
    (fun a => Subalgebra.mem_map.mpr ⟨a, a.2, rfl⟩)).toRingHom
  have hφA : Function.Surjective φA := fun a' => by
    obtain ⟨a, ha, hae⟩ := Subalgebra.mem_map.mp a'.2
    exact ⟨⟨a, ha⟩, Subtype.ext hae⟩
  refine module_finite_of_forall_mem_span φA hφA B.val.toRingHom Subtype.val_injective
    (fun _ _ => rfl) s fun b => ?_
  exact hs _ (mem_homFracDegZero_of_mem_degZeroLoc P' _ _ b.2)
    (IsIntegral.map_of_comp_eq φA B.val.toRingHom (RingHom.ext fun _ => rfl) (hint.isIntegral b))
end SemilocalFinite
end GroundTheory.Heights₂.Heights.FieldNumbers
