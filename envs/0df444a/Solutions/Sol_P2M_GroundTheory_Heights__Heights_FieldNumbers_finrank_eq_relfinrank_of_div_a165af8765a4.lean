-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_eq_relfinrank_of_div_a165af8765a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:20:57.315075+00:00
-- url     : https://prove2.me/submissions/7fcb96a6-8def-4cdb-a41b-842517cf41de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isFractionRing_of_div_9823530e3be1

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
variable {F L₀ L : Type*} [Field F] [Field L₀] [Field L] [Algebra F L₀] [Algebra F L]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (φ : L₀ →ₐ[F] L) {K₀ : IntermediateField F L₀}
    {E : IntermediateField F L} (hKE : K₀.map φ ≤ E) {A : Subalgebra F L₀} {B : Subalgebra F L}
    [Algebra A B] (hφ : ∀ a : A, ((algebraMap A B a : B) : L) = φ a) (hA : ∀ a ∈ A, a ∈ K₀)
    (hB : ∀ b ∈ B, b ∈ E) (fracA : ∀ x ∈ K₀, ∃ y ∈ A, ∃ z ∈ A, z ≠ 0 ∧ x = y / z)
    (fracB : ∀ x ∈ E, ∃ y ∈ B, ∃ z ∈ B, z ≠ 0 ∧ x = y / z) :
    Module.finrank A B = IntermediateField.relfinrank (K₀.map φ) E := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le hKE]
  set K := K₀.map φ
  set Lf := IntermediateField.extendScalars hKE
  let _ : Algebra A K := (((φ.comp A.val).toRingHom).codRestrict K
    (fun a => show φ a ∈ K from ⟨a, hA a a.2, rfl⟩)).toAlgebra
  let _ : Algebra B Lf := ((B.val.toRingHom).codRestrict Lf (fun b => hB b b.2)).toAlgebra
  let _ : Algebra A Lf := ((algebraMap B Lf).comp (algebraMap A B)).toAlgebra
  have _ : IsScalarTower A B Lf := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have _ : IsScalarTower A K Lf := IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext (hφ a))
  have _ : IsFractionRing A K := by
    refine isFractionRing_of_div (fun a b h => Subtype.ext (φ.injective ?_)) ?_
    · exact congrArg Subtype.val h
    · rintro ⟨_, x, hx, rfl⟩
      obtain ⟨y, hy, z, hz, -, rfl⟩ := fracA x hx
      exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext (map_div₀ φ y z)⟩
  have _ : IsFractionRing B Lf := by
    refine isFractionRing_of_div (fun a b h => Subtype.ext (congrArg Subtype.val h :)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, -, rfl⟩ := fracB x hx
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext rfl⟩
  exact (IsFractionRing.finrank_eq A K B Lf).symm
end GroundTheory.Heights₂.Heights.FieldNumbers
