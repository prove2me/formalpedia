-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalResidueLength_proof_25f72b584279
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:56:04.971435+00:00
-- url     : https://prove2.me/submissions/0332a7cb-ea4c-4e85-83a2-c7d21b3ed9b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalResidueLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocalize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalResidueLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_proof_46b509c2b5c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocQuot_proof_f2e3f8a36e28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FibreFinite_proof_e5ac3cafe5ef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_proof_c7e248874611
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_proof_0aacacc92e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RelevantPrimeDimGe_proof_f3a1f51a2659
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_algebraMap_39d4c423cc7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_anti_2b5a3c1121df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_map_homFracDegZero_le_99e71cc4273e


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
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace SemilocalResidueLength
theorem _root_.solution (hRes : DegZeroLocResidue.Statement.{u})
    (hFR : SemilocalFiniteRank.Statement.{u}) (hLoc : DegZeroLocLocalize.Statement.{u}) :
    SemilocalResidueLength.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW
  have := hP'.isPrime
  intro W' hW'
  have := hW'.1.isPrime
  haveI hfin := (hFR F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1
  have h𝒲 := FibreFinite.proof F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  obtain ⟨-, hPW', hc⟩ := id hW'
  subst hc
  obtain ⟨ρO, hρOv, hρOk, hρOr⟩ := hRes F K' ι' P' W' hPW'
  obtain ⟨ρA, hρAv, -, hρAr⟩ := hRes F K (fun k => ι' (j k)) (contractPrime j P') _ hPW
  have hLE := map_homFracDegZero_le j ι' W'
  have hBO := degZeroLoc_anti P' (Set.singleton_subset_iff.mpr hW')
  let L := (homFracDegZero (contractPrime j W')).map (contractFracMap j W')
  let M := IntermediateField.extendScalars hLE
  let τ : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) →+* M :=
    (ρO.comp (Subalgebra.inclusion hBO).toRingHom).codRestrict M (fun b => (hρOr _).mpr ⟨_, rfl⟩)
  let σ : degZeroLoc (contractPrime j P') {contractPrime j W'} →+* L :=
    ((contractFracMap j W').toRingHom.comp ρA).codRestrict L
      (fun a => ⟨ρA a, (hρAr _).mpr ⟨a, rfl⟩, rfl⟩)
  have hσs : Function.Surjective σ := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨a, rfl⟩ := (hρAr w).mp hw
    exact ⟨a, rfl⟩
  letI : Algebra (degZeroLoc (contractPrime j P') {contractPrime j W'}) L := σ.toAlgebra
  letI : Algebra (degZeroLoc (contractPrime j P') {contractPrime j W'}) M :=
    ((algebraMap L M).comp σ).toAlgebra
  haveI : IsScalarTower (degZeroLoc (contractPrime j P') {contractPrime j W'}) L M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hcomp : ∀ a : degZeroLoc (contractPrime j P') {contractPrime j W'}, τ (algebraMap _ _ a) = algebraMap _ M a := by
    intro a
    obtain ⟨b, f, g, hf, hg, -, hgW, hx⟩ := DegZeroLocQuot.proof F K (fun k => ι' (j k))
      (contractPrime j P') {contractPrime j W'} (fun V hV => by rw [hV]; infer_instance) a.1 a.2
    apply Subtype.ext
    show ρO ⟨contractFracMap j P' a, _⟩ = contractFracMap j W' (ρA a)
    rw [hρAv a b f g hf hg (hgW _ rfl) hx, map_div₀, contractFracMap_algebraMap,
      contractFracMap_algebraMap]
    apply hρOv _ _ _ _ (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hg) (hgW _ rfl)
    show contractFracMap j P' a = _
    rw [hx, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
  let τA : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) →ₐ[degZeroLoc (contractPrime j P') {contractPrime j W'}] M :=
    { τ with commutes' := hcomp }

  have hmem : ∀ l : L, algebraMap L M l ∈ τ.rangeS := by
    intro l
    obtain ⟨a, rfl⟩ := hσs l
    exact ⟨_, hcomp a⟩
  let R : Subalgebra L M := { τ.rangeS with algebraMap_mem' := hmem }
  have hsurj : Function.Surjective τ := by
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := (hρOr z).mp hz
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hys⟩ := hLoc F K' ι' P' hP' _ h𝒲
      (fun V hV => ⟨hV.1, hV.2.1⟩) W' hW' y.1 y.2
    have hs0 : τ ⟨s, hs⟩ ≠ 0 := by
      intro h0
      have h1 : ρO ⟨s, hBO hs⟩ * ρO ⟨t, ht⟩ = 1 := by
        rw [← map_mul, ← map_one ρO]
        exact congrArg ρO (Subtype.ext hst)
      rw [show ρO ⟨s, hBO hs⟩ = 0 from congrArg Subtype.val h0, zero_mul] at h1
      exact zero_ne_one h1
    have hint : IsIntegral L (τ ⟨s, hs⟩) :=
      ((Algebra.IsIntegral.isIntegral (R := degZeroLoc (contractPrime j P') {contractPrime j W'})
        (⟨s, hs⟩ : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')))).map τA).tower_top
    obtain ⟨c, hc⟩ := hint.inv_mem (A := R) ⟨⟨s, hs⟩, rfl⟩
    have hbys : τ ⟨b, hb⟩ = ⟨ρO y, hz⟩ * τ ⟨s, hs⟩ := by
      apply Subtype.ext
      show ρO ⟨b, hBO hb⟩ = ρO y * ρO ⟨s, hBO hs⟩
      rw [← map_mul]
      exact congrArg ρO (Subtype.ext hys.symm)
    refine ⟨⟨b, hb⟩ * c, ?_⟩
    rw [map_mul, hc, hbys, mul_inv_cancel_right₀ hs0]
  refine ⟨RingHom.ker τ, fun x => ?_, ?_⟩
  · rw [RingHom.mem_ker, ← ZeroMemClass.coe_eq_zero]
    exact hρOk ⟨x, hBO x.2⟩
  · let e : (degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) ⧸ RingHom.ker τ) ≃ₐ[degZeroLoc (contractPrime j P') {contractPrime j W'}] M :=
      AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hsurj) (fun a => by
        rw [← Ideal.Quotient.mk_algebraMap, RingHom.quotientKerEquivOfSurjective_apply_mk]
        exact hcomp a)
    haveI : Module.Finite (degZeroLoc (contractPrime j P') {contractPrime j W'}) M :=
      Module.Finite.of_surjective τA.toLinearMap hsurj
    haveI : Module.Finite L M :=
      Module.Finite.of_restrictScalars_finite (degZeroLoc (contractPrime j P') {contractPrime j W'}) L M
    refine e.toLinearEquiv.length_eq.trans ?_
    rw [Module.length_eq_of_surjective (R := L) hσs, Module.length_eq_finrank, relDeg,
      IntermediateField.relfinrank_eq_finrank_of_le hLE]
end SemilocalResidueLength
end GroundTheory.Heights₂.Heights.FieldNumbers
