-- Prove2me | solution 1 for Rep.isZero_tateCohomology_res_tensor_of_forall_isZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/34ac900d-fe5a-527f-94b6-60393916905b

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Theorems.Thm_Rep_exists_shortExact_free_of_forall_isZero
import Theorems.Thm_Rep_isZero_tateCohomology_free_tensor
import Theorems.Thm_Rep_isZero_tateCohomology_of_retract
import Theorems.Thm_Rep_exact_tateMap_tateDelta
import Theorems.Thm_Rep_nonempty_res_free_iso_free
import Theorems.Thm_Rep_shortExact_map_resFunctor
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_isZero_tateCohomology_res_tensor_of_forall_isZero
p2m_attr_erase "simp" "Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply"

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

attribute [local instance 2000] Rep.hV2 Rep.hV1

theorem solution {G : Type} [Group G] [Fintype G] (B : Rep ℤ G)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V)
    (hB : ∀ (S : Subgroup G) [Fintype S] (q : ℤ), CategoryTheory.Limits.IsZero ((Rep.res S.subtype B).tateCohomology q))
    (S : Subgroup G) [Fintype S] (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.res S.subtype (B ⊗ Rep.of ρ)).tateCohomology q) := by
  classical
  let M : Rep ℤ G := Rep.of ρ
  have zelt : ∀ {N : ModuleCat.{0} ℤ}, CategoryTheory.Limits.IsZero N → ∀ x : N, x = 0 := fun hN x => by
    simpa using congrArg (fun ψ => ψ.hom x) (hN.eq_of_src (𝟙 _) 0)

  obtain ⟨α, β, P₁, i, r, hir, f, g, w, hX⟩ := Rep.exists_shortExact_free_of_forall_isZero B hB

  have hrT : ∀ {X₁ X₂ : Rep ℤ G} (φ : X₁ ⟶ X₂), (φ ▷ M).hom.toLinearMap = LinearMap.rTensor V φ.hom.toLinearMap :=
    fun φ => by rw [Rep.hom_whiskerRight, Representation.IntertwiningMap.toLinearMap_rTensor]
  have w' : (f ▷ M) ≫ (g ▷ M) = 0 := by
    rw [← MonoidalCategory.comp_whiskerRight, w]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rw [hrT]
    exact LinearMap.rTensor_zero V
  have hfg : Function.Exact f.hom.toLinearMap g.hom.toLinearMap := LinearMap.exact_iff.2 (Rep.seam_range_eq_ker hX).symm
  have hgs : Function.Surjective g.hom.toLinearMap := Rep.seam_g_surjective hX
  let X' : ShortComplex (Rep ℤ G) := ShortComplex.mk (f ▷ M) (g ▷ M) w'
  have hX' : X'.ShortExact :=
    { exact := by
        refine (forget₂ (Rep ℤ G) (ModuleCat ℤ)).reflects_exact_of_faithful _ ((ShortComplex.moduleCat_exact_iff _).2 ?_)
        intro y hy
        have ex := rTensor_exact V hfg hgs
        have hy' : LinearMap.rTensor V g.hom.toLinearMap y = 0 := by rw [← hrT]; exact hy
        obtain ⟨x, hx⟩ := (ex y).1 hy'
        refine ⟨x, ?_⟩
        change (f ▷ M).hom.toLinearMap x = y
        rw [hrT]; exact hx
      mono_f := (Rep.mono_iff_injective _).2 (by
        change Function.Injective (f ▷ M).hom.toLinearMap
        rw [hrT]
        exact Module.Flat.rTensor_preserves_injective_linearMap _ (Rep.seam_f_injective hX))
      epi_g := (Rep.epi_iff_surjective _).2 (by
        change Function.Surjective (g ▷ M).hom.toLinearMap
        rw [hrT]
        exact LinearMap.rTensor_surjective V hgs) }

  have hXS := Rep.shortExact_map_resFunctor S.subtype hX'
  obtain ⟨γ, ⟨eα⟩⟩ := Rep.nonempty_res_free_iso_free (k := ℤ) S α
  obtain ⟨γ', ⟨eβ⟩⟩ := Rep.nonempty_res_free_iso_free (k := ℤ) S β
  have hF : ∀ n : ℤ, CategoryTheory.Limits.IsZero ((Rep.res S.subtype (Rep.free ℤ G α ⊗ M)).tateCohomology n) := by
    intro n
    change CategoryTheory.Limits.IsZero ((Rep.res S.subtype (Rep.free ℤ G α) ⊗ Rep.res S.subtype M).tateCohomology n)
    obtain ⟨e⟩ := Rep.nonempty_tateCohomology_iso_of_iso (eα ▷ᵢ (Rep.res S.subtype M)) n
    exact Limits.IsZero.of_iso (Rep.isZero_tateCohomology_free_tensor γ (Rep.res S.subtype M) n) e
  have hP : ∀ n : ℤ, CategoryTheory.Limits.IsZero ((Rep.res S.subtype (P₁ ⊗ M)).tateCohomology n) := by
    intro n
    change CategoryTheory.Limits.IsZero ((Rep.res S.subtype P₁ ⊗ Rep.res S.subtype M).tateCohomology n)
    refine Rep.isZero_tateCohomology_of_retract ((Rep.resFunctor S.subtype).map i ▷ Rep.res S.subtype M)
      ((Rep.resFunctor S.subtype).map r ▷ Rep.res S.subtype M) ?_ n ?_
    · rw [← MonoidalCategory.comp_whiskerRight, ← Functor.map_comp, hir]
      exact MonoidalCategory.id_whiskerRight _ _
    · change CategoryTheory.Limits.IsZero ((Rep.res S.subtype (Rep.free ℤ G β) ⊗ Rep.res S.subtype M).tateCohomology n)
      obtain ⟨e⟩ := Rep.nonempty_tateCohomology_iso_of_iso (eβ ▷ᵢ (Rep.res S.subtype M)) n
      exact Limits.IsZero.of_iso (Rep.isZero_tateCohomology_free_tensor γ' (Rep.res S.subtype M) n) e

  have hall : ∀ y : (Rep.res S.subtype (B ⊗ M)).tateCohomology q, y = 0 := fun y => by
    have ex := Rep.exact_tateMap_tateDelta hXS q
    have hδ : (Rep.tateδ hXS q).hom y = 0 := zelt (hP (q + 1)) _
    obtain ⟨x, hx⟩ := (ex y).1 hδ
    have hz : (Rep.tateMap (X'.map (Rep.resFunctor S.subtype)).g q).hom 0 = 0 :=
      (Rep.tateMap (X'.map (Rep.resFunctor S.subtype)).g q).hom.map_zero
    rw [← hx, zelt (hF q) x]
    exact hz
  haveI : Subsingleton ((Rep.res S.subtype (B ⊗ M)).tateCohomology q) := ⟨fun a b => by rw [hall a, hall b]⟩
  exact ModuleCat.isZero_of_subsingleton _

end S_Rep_isZero_tateCohomology_res_tensor_of_forall_isZero
end P2MW
export P2MW.S_Rep_isZero_tateCohomology_res_tensor_of_forall_isZero (solution)
