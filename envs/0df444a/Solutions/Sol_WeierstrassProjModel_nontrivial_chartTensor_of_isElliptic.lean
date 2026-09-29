-- Prove2me | solution 1 for WeierstrassProjModel.nontrivial_chartTensor_of_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/eaeaad3e-6249-50cd-b903-50b4609e1d1a

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_nontrivial_chart_of_isElliptic
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_nontrivial_chartTensor_of_isElliptic

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3) :
    Nontrivial ((𝒜 i) ⊗[R] (𝒜 j)) := by
  haveI hni : Nontrivial (𝒜 i) := nontrivial_chart_of_isElliptic W i
  haveI hnj : Nontrivial (𝒜 j) := nontrivial_chart_of_isElliptic W j
  haveI : Smooth (π) :=
    (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral (π) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (projModel_pullback_iso_baseChange W.toProjective)
  haveI hIE : IsIntegral (projModelCR W.toProjective) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (π)

  let η : Spec (projModelCR W.toProjective).functionField ⟶ projModelCR W.toProjective :=
    (projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective))
  let awayι : ∀ m : Fin 3, Spec (CommRingCat.of (𝒜 m)) ⟶ projModelCR W.toProjective :=
    fun m => Proj.awayι (projModelGradingCR W.toProjective) _
      (kw_pbac_mk_X_mem_one_CR R W.toProjective m) one_pos

  have hmem : ∀ (m : Fin 3), Nontrivial (𝒜 m) →
      Set.range η.base ⊆ Set.range (awayι m).base := fun m _ => by
    rw [Scheme.range_fromSpecStalk]
    intro y hy
    have hgenmem : genericPoint (projModelCR W.toProjective) ∈ Set.range (awayι m).base :=
      ((genericPoint_spec (projModelCR W.toProjective)).mem_open_set_iff
        (IsOpenImmersion.isOpen_range (awayι m))).mpr
        (by rw [Set.univ_inter]; exact Set.range_nonempty _)
    exact (IsOpenImmersion.isOpen_range (awayι m)).stableUnderGeneralization hy hgenmem

  letI : Algebra R (projModelCR W.toProjective).functionField :=
    (Spec.preimage (η ≫ π)).hom.toAlgebra

  let mkφ : ∀ (m : Fin 3), Nontrivial (𝒜 m) →
      ((𝒜 m) →ₐ[R] (projModelCR W.toProjective).functionField) := fun m hm =>
    { toRingHom := (Spec.preimage (IsOpenImmersion.lift (awayι m) η (hmem m hm))).hom,
      commutes' := fun r => by

        have hfac := IsOpenImmersion.lift_fac (awayι m) η (hmem m hm)
        have heq : IsOpenImmersion.lift (awayι m) η (hmem m hm)
            ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 m))) = η ≫ π := by
          rw [← kw_pbac_awayι_comp_projModelStrCR R W.toProjective m,
            ← Category.assoc, hfac]
        have hpre : (Spec.preimage (IsOpenImmersion.lift (awayι m) η (hmem m hm))).hom.comp
              (algebraMap R (𝒜 m))
            = (Spec.preimage (η ≫ π)).hom := by
          have h₁ := congrArg CommRingCat.Hom.hom
            (congrArg Spec.preimage heq)
          rw [Spec.preimage_comp, CommRingCat.hom_comp, Spec.preimage_map,
            CommRingCat.hom_ofHom] at h₁
          exact h₁
        exact RingHom.congr_fun hpre r }
  exact (Algebra.TensorProduct.lift (mkφ i hni) (mkφ j hnj)
    (fun _ _ => mul_comm _ _)).toRingHom.domain_nontrivial

end

end S_WeierstrassProjModel_nontrivial_chartTensor_of_isElliptic
end P2MW
export P2MW.S_WeierstrassProjModel_nontrivial_chartTensor_of_isElliptic (solution)
