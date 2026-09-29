-- Prove2me | solution 1 for Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq_of_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f64874be-4b13-53f9-bb34-7da481b4031b

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Definitions.Def_GroupCohomology_RelationModule
import Theorems.Thm_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq
import Theorems.Thm_Rep_bijective_tateDelta_of_isZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq_of_shortExact
p2m_attr_erase "simp" "Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply"

set_option autoImplicit false
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

theorem solution {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
    {P B : Rep ℤ G} (f : Rep.of ρ ⟶ P) (g : P ⟶ B) (w : f ≫ g = 0)
    (S : Subgroup G) [Fintype S] (cup : Rep.TateCupFamily ℤ S) (hcup : Rep.IsTateCupProduct cup)
    (hX : ((ShortComplex.mk f g w).map (Rep.resFunctor S.subtype)).ShortExact)
    (hP : ∀ q : ℤ, CategoryTheory.Limits.IsZero ((Rep.res S.subtype P).tateCohomology q))
    (n q : ℤ) (h : n + 1 + q = 2)
    (φ : (Rep.res S.subtype B).tateCohomology n →ₗ[ℤ] groupCohomology (Rep.res S.subtype C) 2) :
    ∃ a : ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)).tateCohomology q,
      ∀ y : (Rep.res S.subtype B).tateCohomology n,
        (Rep.tateMap ((ihom.ev (Rep.res S.subtype (Rep.of ρ))).app (Rep.res S.subtype C)) 2).hom
          (cup (Rep.res S.subtype (Rep.of ρ)) ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)) (n + 1) q 2 h ((Rep.tateδ hX n).hom y) a) = φ y := by
  have hδ := Rep.bijective_tateDelta_of_isZero hX n (hP n) (hP (n + 1))
  let e := LinearEquiv.ofBijective (Rep.tateδ hX n).hom hδ
  have key : ∀ (m : ℤ) (hm : m + q = 2) (ψ : (Rep.res S.subtype (Rep.of ρ)).tateCohomology m →ₗ[ℤ] groupCohomology (Rep.res S.subtype C) 2),
      ∃ a : ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)).tateCohomology q,
        ∀ x : (Rep.res S.subtype (Rep.of ρ)).tateCohomology m, (Rep.tateMap ((ihom.ev (Rep.res S.subtype (Rep.of ρ))).app (Rep.res S.subtype C)) 2).hom (cup (Rep.res S.subtype (Rep.of ρ)) ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)) m q 2 hm x a) = ψ x := by
    intro m hm ψ
    obtain rfl : m = 2 - q := by omega
    exact Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq C u h1 h2card h2gen V ρ S cup hcup q ψ
  obtain ⟨a, ha⟩ := key (n + 1) h (φ ∘ₗ e.symm.toLinearMap)
  refine ⟨a, fun y => ?_⟩
  rw [ha]
  simp only [LinearMap.comp_apply]
  congr 1
  exact e.symm_apply_apply y

end S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq_of_shortExact
end P2MW
export P2MW.S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq_of_shortExact (solution)
