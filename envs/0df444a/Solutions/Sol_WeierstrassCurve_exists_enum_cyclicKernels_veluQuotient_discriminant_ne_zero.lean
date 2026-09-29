-- Prove2me | solution 1 for WeierstrassCurve.exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/86ff18a1-f694-5282-9ccb-2e98312eba26

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = ℓ + 1 ∧
      ∃ Q : ι → W.toAffine.Point, (∀ i, addOrderOf (Q i) = ℓ) ∧
        (Function.Injective fun i => AddSubgroup.zmultiples (Q i)) ∧
        ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0 := by
  have hℓP : ℓ.Prime := Fact.out

  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) W (n := ℓ) hℓK
  have hb : W.baseChange K = W := by cases W; rfl
  have htrans : ∀ (V : WeierstrassCurve K), V = W →
      (ZMod ℓ × ZMod ℓ ≃+ Submodule.torsionBy ℤ V.toAffine.Point ℓ) →
      Nonempty (ZMod ℓ × ZMod ℓ ≃+ Submodule.torsionBy ℤ W.toAffine.Point ℓ) := by
    intro V h e'; subst h; exact ⟨e'⟩
  obtain ⟨e⟩ := htrans _ hb e

  have hcard :=
    AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy ℓ e
  rw [ModularCurve.dedekindPsi_prime hℓP] at hcard
  set ι := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = ℓ} with hιdef
  haveI : Finite ι := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  letI : Fintype ι := Fintype.ofFinite ι
  have hι : Fintype.card ι = ℓ + 1 := by rw [← Nat.card_eq_fintype_card, hcard]

  have hgen : ∀ H : ι, ∃ g : W.toAffine.Point,
      addOrderOf g = ℓ ∧ AddSubgroup.zmultiples g = H.1 := by
    rintro ⟨H, hcyc, hcardH⟩
    obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp hcyc
    refine ⟨g, ?_, hg⟩
    rw [← Nat.card_zmultiples g, hg]; exact hcardH
  choose Q hQord hQgen using hgen
  have hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i) := by
    intro i i' h
    apply Subtype.ext
    simp only at h
    rw [← hQgen i, ← hQgen i', h]

  have hodd : ∀ i, addOrderOf (Q i) = 2 * (ℓ / 2) + 1 := by
    intro i
    rw [hQord i]
    rcases hℓP.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · exact (Nat.two_mul_div_two_add_one_of_odd h).symm
  have hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0 := fun i =>
    WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
      W (ℓ / 2) (Q i) (hodd i)

  let f : Fin (ℓ + 1) ≃ ι := (Fintype.equivFinOfCardEq hι).symm
  exact ⟨Fin (ℓ + 1), inferInstance, Fintype.card_fin _, fun k => Q (f k), fun k => hQord _,
    fun k k' h => f.injective (hQinj h), fun k => hΔ _⟩

end S_WeierstrassCurve_exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero (solution)
