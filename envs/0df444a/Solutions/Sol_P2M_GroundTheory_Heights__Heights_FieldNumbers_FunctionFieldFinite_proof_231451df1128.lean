-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_proof_231451df1128
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:58.783949+00:00
-- url     : https://prove2.me/submissions/a1f48152-5949-47a2-921c-6ddadfff8a9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFunctionFieldFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_homFracDegZero_eq_1e90cfbe461b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_relDim_eq_trdeg_c42302537785
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
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
open FunctionFieldFinite
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace FunctionFieldFinite
theorem _root_.solution (hD : MChartDehomog.Statement.{u})
    (hT : MChartTrdeg.Statement.{u}) : FunctionFieldFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' hrel
  have := hP'.isPrime
  have hP := isMultiProjPrime_contractPrime j ι' hP'
  obtain ⟨n, hn, hrn⟩ := relDim_eq_trdeg hD hT (contractPrime j P') hP
  obtain ⟨n', hn', hrn'⟩ := relDim_eq_trdeg hD hT P' hP'
  have hnn : n = n' := by
    rw [hrel, hrn'] at hrn
    exact_mod_cast (WithTop.coe_injective (WithBot.coe_injective hrn)).symm
  set E := (homFracDegZero (contractPrime j P')).map (contractFracMap j P')
  set κ' := homFracDegZero P'
  have h : E ≤ κ' := map_homFracDegZero_le j ι' P'
  have hE : Algebra.trdeg F E = n :=
    (IntermediateField.equivMap _ (contractFracMap j P')).trdeg_eq.symm.trans hn
  let _ : Algebra E κ' := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E κ' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul E κ' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IntermediateField.inclusion h).injective
  have : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).2 (algebraMap F E).injective
  have htow := trdeg_add_eq F E (A := κ')
  rw [hE, hn', ← hnn] at htow
  have hlt : Algebra.trdeg E κ' < Cardinal.aleph0 :=
    lt_of_le_of_lt (htow ▸ self_le_add_left _ _) (Cardinal.natCast_lt_aleph0 (n := n))
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hm] at htow
  have hm0 : m = 0 := by
    have : n + m = n := by exact_mod_cast htow
    omega
  have : Algebra.IsAlgebraic E κ' := trdeg_eq_zero_iff.mp (by rw [hm, hm0]; rfl)
  let g : κ' →ₐ[E] FractionRing (MRing ι' F ⧸ P') :=
    { (κ'.val : κ' →+* FractionRing (MRing ι' F ⧸ P')) with commutes' := fun _ => rfl }
  choose u hu using hP'.relevant
  have hκ' : κ' = IntermediateField.adjoin F (chartGens P' u) := homFracDegZero_eq hD P' u hu
  have hint : ∀ x ∈ chartGens P' u, IsIntegral E x := by
    intro x hx
    have hx' : x ∈ κ' := hκ' ▸ IntermediateField.subset_adjoin F _ hx
    have hy : IsAlgebraic E (⟨x, hx'⟩ : κ') := Algebra.IsAlgebraic.isAlgebraic _
    exact IsIntegral.map g hy.isIntegral
  have : Finite (chartGens P' u) := (Set.finite_range _).to_subtype
  have := IntermediateField.finiteDimensional_adjoin hint
  show IntermediateField.relfinrank E κ' ≠ 0
  rw [IntermediateField.relfinrank_eq_finrank_of_le h]
  have hext : IntermediateField.extendScalars h = IntermediateField.adjoin E (chartGens P' u) := by
    rw [← IntermediateField.extendScalars_adjoin (h.trans hκ'.le)]
    exact IntermediateField.ext fun x =>
      show x ∈ κ' ↔ x ∈ IntermediateField.adjoin F (chartGens P' u) by rw [hκ']
  rw [hext]
  exact Module.finrank_pos.ne'
end FunctionFieldFinite
end GroundTheory.Heights₂.Heights.FieldNumbers
