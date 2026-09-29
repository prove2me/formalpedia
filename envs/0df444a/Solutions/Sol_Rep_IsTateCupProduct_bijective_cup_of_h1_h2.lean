-- Prove2me | solution 1 for Rep.IsTateCupProduct.bijective_cup_of_h1_h2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ffbc0190-a39e-5667-b9fe-855365067291

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Definitions.Def_GroupCohomology_SplittingModule
import Theorems.Thm_Rep_augShortComplex_shortExact
import Theorems.Thm_Rep_splittingShortComplex_shortExact
import Theorems.Thm_Rep_isZero_tateCohomology_res_splittingModule
import Theorems.Thm_Rep_isZero_tateCohomology_res_tensor_of_forall_isZero
import Theorems.Thm_Rep_bijective_tateDelta_of_isZero
import Theorems.Thm_Rep_isZero_tateCohomology_free_tensor
import Theorems.Thm_Rep_nonempty_res_free_iso_free
import Theorems.Thm_Rep_shortExact_map_resFunctor
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_of_iso
import Theorems.Thm_Rep_tateMap_comp
import Theorems.Thm_Rep_tateMap_id
import Theorems.Thm_Rep_IsTateCupProduct_cup_mk_left_eq_tateMap
import Theorems.Thm_Rep_tateDelta_splitting_tateDelta_aug_eq_map_H2pi
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_IsTateCupProduct_bijective_cup_of_h1_h2
p2m_attr_erase "simp" "Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply"

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

attribute [local instance 2000] Rep.hV2 Rep.hV1

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V)
    (S : Subgroup G) [Fintype S] (cup : Rep.TateCupFamily ℤ S) (hcup : Rep.IsTateCupProduct cup) (q : ℤ) :
    Function.Bijective (fun x : (Rep.res S.subtype (Rep.of ρ)).tateCohomology q =>
      (cup (Rep.res S.subtype C) (Rep.res S.subtype (Rep.of ρ)) 2 q (q + 2) (add_comm 2 q)
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u) x :
          (Rep.res S.subtype (C ⊗ Rep.of ρ)).tateCohomology (q + 2))) := by
  classical

  suffices H : ∀ (r : ℤ) (h : 2 + q = r),
      Function.Bijective (fun x : (Rep.res S.subtype (Rep.of ρ)).tateCohomology q =>
        cup (Rep.res S.subtype C) (Rep.res S.subtype (Rep.of ρ)) 2 q r h
          ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u) x) from
    H (q + 2) (add_comm 2 q)
  intro r h
  obtain rfl : r = q + 1 + 1 := by omega
  set M : Rep ℤ G := Rep.of ρ with hM
  set M' : Rep ℤ S := Rep.res S.subtype M with hM'

  obtain ⟨φ, hφ⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).1 inferInstance u
  have h2gen' : ∀ (T : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map T.subtype (𝟙 (Rep.res T.subtype C)) 2).hom (groupCohomology.H2π C φ)} = ⊤ := by
    intro T; rw [hφ]; exact h2gen T

  have hrT : ∀ {X₁ X₂ : Rep ℤ S} (ψ : X₁ ⟶ X₂), (ψ ▷ M').hom.toLinearMap = LinearMap.rTensor V ψ.hom.toLinearMap :=
    fun ψ => by rw [Rep.hom_whiskerRight, Representation.IntertwiningMap.toLinearMap_rTensor]
  have tensSE : ∀ {X : ShortComplex (Rep ℤ S)}, X.ShortExact → (X.map (MonoidalCategory.tensorRight M')).ShortExact := by
    intro X hX
    have hfg : Function.Exact X.f.hom.toLinearMap X.g.hom.toLinearMap :=
      LinearMap.exact_iff.2 (Rep.seam_range_eq_ker hX).symm
    have hgs : Function.Surjective X.g.hom.toLinearMap := Rep.seam_g_surjective hX
    exact
      { exact := by
          refine (forget₂ (Rep ℤ S) (ModuleCat ℤ)).reflects_exact_of_faithful _ ((ShortComplex.moduleCat_exact_iff _).2 ?_)
          intro y hy
          have ex := rTensor_exact V hfg hgs
          have hy' : LinearMap.rTensor V X.g.hom.toLinearMap y = 0 := by rw [← hrT]; exact hy
          obtain ⟨x, hx⟩ := (ex y).1 hy'
          refine ⟨x, ?_⟩
          change (X.f ▷ M').hom.toLinearMap x = y
          rw [hrT]; exact hx
        mono_f := (Rep.mono_iff_injective _).2 (by
          change Function.Injective (X.f ▷ M').hom.toLinearMap
          rw [hrT]
          exact Module.Flat.rTensor_preserves_injective_linearMap _ (Rep.seam_f_injective hX))
        epi_g := (Rep.epi_iff_surjective _).2 (by
          change Function.Surjective (X.g ▷ M').hom.toLinearMap
          rw [hrT]
          exact LinearMap.rTensor_surjective V hgs) }

  have hE := Rep.shortExact_map_resFunctor S.subtype (Rep.augShortComplex_shortExact ℤ G)
  have hF := Rep.shortExact_map_resFunctor S.subtype (Rep.splittingShortComplex_shortExact C φ)
  set ES := (Rep.augShortComplex ℤ G).map (Rep.resFunctor S.subtype) with hES
  set FS := (Rep.splittingShortComplex C φ).map (Rep.resFunctor S.subtype) with hFS
  have hEM := tensSE hE
  have hFM := tensSE hF

  have eL : Rep.leftRegularFinsupp ℤ G ≅ Rep.free ℤ G PUnit := by
    let Φ : (G →₀ ℤ) ≃ₗ[ℤ] (PUnit →₀ MonoidAlgebra ℤ G) :=
      (Finsupp.LinearEquiv.finsuppUnique ℤ (G →₀ ℤ) PUnit).symm ≪≫ₗ
        Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm
    have hΦ : ∀ f, Φ f = Finsupp.single PUnit.unit (MonoidAlgebra.ofCoeff f) := fun f => by
      apply Finsupp.ext; intro x; simp [Φ, Finsupp.LinearEquiv.finsuppUnique]
    have hequiv : ∀ g : G, Φ.toLinearMap ∘ₗ (Rep.leftRegularFinsupp ℤ G).ρ g = (Rep.free ℤ G PUnit).ρ g ∘ₗ Φ.toLinearMap := by
      intro g
      apply Finsupp.lhom_ext
      intro x r
      change Φ (Representation.leftRegularFinsupp ℤ G g (Finsupp.single x r)) = Representation.free ℤ G PUnit g (Φ (Finsupp.single x r))
      rw [hΦ, hΦ]
      change Finsupp.single PUnit.unit (MonoidAlgebra.ofCoeff (Finsupp.lmapDomain ℤ ℤ (g * ·) (Finsupp.single x r))) = _
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        show MonoidAlgebra.ofCoeff (Finsupp.single x r) = MonoidAlgebra.single x r from rfl,
        show MonoidAlgebra.ofCoeff (Finsupp.single (g * x) r) = MonoidAlgebra.single (g * x) r from rfl,
        Representation.free_single_single]
    have hequiv' : ∀ (g : G) f, Φ ((Rep.leftRegularFinsupp ℤ G).ρ g f) = (Rep.free ℤ G PUnit).ρ g (Φ f) :=
      fun g f => LinearMap.congr_fun (hequiv g) f
    have hequiv_symm : ∀ g : G, Φ.symm.toLinearMap ∘ₗ (Rep.free ℤ G PUnit).ρ g = (Rep.leftRegularFinsupp ℤ G).ρ g ∘ₗ Φ.symm.toLinearMap := by
      intro g
      apply LinearMap.ext
      intro y
      obtain ⟨f, rfl⟩ := Φ.surjective y
      change Φ.symm _ = (Rep.leftRegularFinsupp ℤ G).ρ g (Φ.symm (Φ f))
      rw [← hequiv', Φ.symm_apply_apply, Φ.symm_apply_apply]
    exact
      { hom := Rep.ofHom ⟨Φ.toLinearMap, hequiv⟩
        inv := Rep.ofHom ⟨Φ.symm.toLinearMap, hequiv_symm⟩
        hom_inv_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => Φ.symm_apply_apply x))
        inv_hom_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun y => Φ.apply_symm_apply y)) }
  have hL : ∀ n : ℤ, CategoryTheory.Limits.IsZero ((Rep.res S.subtype (Rep.leftRegularFinsupp ℤ G) ⊗ M').tateCohomology n) := by
    intro n
    obtain ⟨γ, ⟨eγ⟩⟩ := Rep.nonempty_res_free_iso_free (k := ℤ) S PUnit
    obtain ⟨e⟩ := Rep.nonempty_tateCohomology_iso_of_iso
      ((((Rep.resFunctor S.subtype).mapIso eL) ≪≫ eγ) ▷ᵢ M') n
    exact Limits.IsZero.of_iso (Rep.isZero_tateCohomology_free_tensor γ M' n) e

  have hCφ : ∀ n : ℤ, CategoryTheory.Limits.IsZero ((Rep.res S.subtype (Rep.splittingModule C φ) ⊗ M').tateCohomology n) :=
    fun n => Rep.isZero_tateCohomology_res_tensor_of_forall_isZero (Rep.splittingModule C φ) V ρ
      (fun T _ m => Rep.isZero_tateCohomology_res_splittingModule C φ h1 h2card h2gen' T m) S n

  have b1 : Function.Bijective (Rep.tateδ hEM q).hom :=
    Rep.bijective_tateDelta_of_isZero hEM q (hL q) (hL (q + 1))
  have b2 : Function.Bijective (Rep.tateδ hFM (q + 1)).hom :=
    Rep.bijective_tateDelta_of_isZero hFM (q + 1) (hCφ (q + 1)) (hCφ (q + 1 + 1))

  let I0 : M' ≅ ES.X₃ ⊗ M' := (Rep.resFunctor S.subtype).mapIso (MonoidalCategory.leftUnitor M).symm
  have b0 : Function.Bijective (Rep.tateMap I0.hom q).hom := by
    have hc1 : Rep.tateMap I0.hom q ≫ Rep.tateMap I0.inv q = 𝟙 _ := by
      rw [← Rep.tateMap_comp, I0.hom_inv_id, Rep.tateMap_id]
    have hc2 : Rep.tateMap I0.inv q ≫ Rep.tateMap I0.hom q = 𝟙 _ := by
      rw [← Rep.tateMap_comp, I0.inv_hom_id, Rep.tateMap_id]
    have l : ∀ x, (Rep.tateMap I0.inv q).hom ((Rep.tateMap I0.hom q).hom x) = x := fun x => by
      have := congrArg (fun f => f.hom x) hc1
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using this
    have r' : ∀ y, (Rep.tateMap I0.hom q).hom ((Rep.tateMap I0.inv q).hom y) = y := fun y => by
      have := congrArg (fun f => f.hom y) hc2
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using this
    exact ⟨Function.LeftInverse.injective l, Function.RightInverse.surjective r'⟩

  let e1 : ES.X₃.ρ.invariants := ⟨(1 : ℤ), fun _ => rfl⟩
  have hI0 : ∀ m : M', I0.hom.hom m = ((e1 : ES.X₃) : ES.X₃) ⊗ₜ[ℤ] m := fun _ => rfl

  have c3 : (Rep.tateδ hF (0 + 1)).hom ((Rep.tateδ hE 0).hom (Submodule.Quotient.mk e1 : ES.X₃.tateH0))
      = (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u := by
    rw [← hφ]
    exact Rep.tateDelta_splitting_tateDelta_aug_eq_map_H2pi C φ S hE hF e1 rfl

  have key : ∀ x : M'.tateCohomology q,
      cup (Rep.res S.subtype C) M' 2 q (q + 1 + 1) (by omega)
          ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u) x
        = (Rep.tateδ hFM (q + 1)).hom ((Rep.tateδ hEM q).hom ((Rep.tateMap I0.hom q).hom x)) := by
    intro x
    have c0 := Rep.IsTateCupProduct.cup_mk_left_eq_tateMap hcup ES.X₃ M' e1 I0.hom hI0 q x
    have c1 := hcup.delta_cup hE M' hEM 0 q q (zero_add q) (Submodule.Quotient.mk e1 : ES.X₃.tateH0) x
    have c2 := hcup.delta_cup hF M' hFM (0 + 1) q (q + 1) (by omega)
      (show FS.X₃.tateCohomology (0 + 1) from (Rep.tateδ hE 0).hom (Submodule.Quotient.mk e1 : ES.X₃.tateH0)) x
    have c4 := congrArg (fun w => cup FS.X₁ M' (0 + 1 + 1) q (q + 1 + 1) (by omega) w x) c3
    exact (((congrArg (fun w => (Rep.tateδ hFM (q + 1)).hom ((Rep.tateδ hEM q).hom w)) c0.symm).trans
      ((congrArg (Rep.tateδ hFM (q + 1)).hom c1).trans (c2.trans c4)))).symm
  rw [show (fun x : (Rep.res S.subtype (Rep.of ρ)).tateCohomology q =>
      cup (Rep.res S.subtype C) (Rep.res S.subtype (Rep.of ρ)) 2 q (q + 1 + 1) (by omega)
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u) x)
      = (Rep.tateδ hFM (q + 1)).hom ∘ (Rep.tateδ hEM q).hom ∘ (Rep.tateMap I0.hom q).hom from funext key]
  exact b2.comp (b1.comp b0)

end S_Rep_IsTateCupProduct_bijective_cup_of_h1_h2
end P2MW
export P2MW.S_Rep_IsTateCupProduct_bijective_cup_of_h1_h2 (solution)
