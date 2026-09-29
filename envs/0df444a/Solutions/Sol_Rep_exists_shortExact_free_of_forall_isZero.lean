-- Prove2me | solution 1 for Rep.exists_shortExact_free_of_forall_isZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fe4bcbcc-b845-5364-a19d-14957e5d232b

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Theorems.Thm_Submodule_free_of_free_of_isPrincipalIdealRing
import Theorems.Thm_Rep_exists_retract_free_of_forall_isZero
import Theorems.Thm_Rep_isZero_tateCohomology_free_tensor
import Theorems.Thm_Rep_nonempty_res_free_iso_free
import Theorems.Thm_Rep_shortExact_map_resFunctor
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_of_iso
import Theorems.Thm_Rep_exact_tateDelta_tateMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_shortExact_free_of_forall_isZero
p2m_attr_erase "simp" "Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply"

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

attribute [local instance 2000] Rep.hV2 Rep.hV1

theorem solution {G : Type} [Group G] [Fintype G] (B : Rep ℤ G)
    (hB : ∀ (S : Subgroup G) [Fintype S] (q : ℤ), CategoryTheory.Limits.IsZero ((Rep.res S.subtype B).tateCohomology q)) :
    ∃ (α β : Type) (P₁ : Rep ℤ G) (i : P₁ ⟶ Rep.free ℤ G β) (r : Rep.free ℤ G β ⟶ P₁) (_ : i ≫ r = 𝟙 P₁)
      (f : P₁ ⟶ Rep.free ℤ G α) (g : Rep.free ℤ G α ⟶ B) (w : f ≫ g = 0),
      (CategoryTheory.ShortComplex.mk f g w).ShortExact := by
  classical
  have zelt : ∀ {N : ModuleCat.{0} ℤ}, CategoryTheory.Limits.IsZero N → ∀ x : N, x = 0 := fun hN x => by
    simpa using congrArg (fun ψ => ψ.hom x) (hN.eq_of_src (𝟙 _) 0)

  let F : Rep ℤ G := Rep.free ℤ G B
  let g : F ⟶ B := Rep.freeLift ℤ G B (fun b => b)
  have hg1 : ∀ b : B, g.hom (Finsupp.single b (MonoidAlgebra.single (1 : G) (1 : ℤ))) = b := fun b => by
    change (Representation.freeLift B.ρ (fun b : B => b)) (Finsupp.single b (MonoidAlgebra.single 1 1)) = b
    rw [Representation.freeLift_single_single, map_one, Module.End.one_apply]
    exact (int_smul_eq_zsmul B.hV2 1 b).trans (one_zsmul b)
  have hgsurj : Function.Surjective g.hom := fun b => ⟨_, hg1 b⟩

  let K : Submodule ℤ (B →₀ MonoidAlgebra ℤ G) := LinearMap.ker g.hom.toLinearMap
  have hK : ∀ s : G, K ≤ Submodule.comap (F.ρ s) K := fun s x hx => by
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply, K] at hx ⊢
    rw [Rep.hom_comm_apply, hx, map_zero]
  let ρ₁ : Representation ℤ G K := Representation.subrepresentation F.ρ K hK
  let P₁ : Rep ℤ G := Rep.of ρ₁
  let f : P₁ ⟶ F := Rep.ofHom ⟨Submodule.subtype K, fun _ => rfl⟩
  have w : f ≫ g = 0 := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.2))
  have hX : (ShortComplex.mk f g w).ShortExact :=
    { exact := (forget₂ (Rep ℤ G) (ModuleCat ℤ)).reflects_exact_of_faithful _
        ((ShortComplex.moduleCat_exact_iff _).2 fun (y : F) (hy : g.hom y = 0) => ⟨(⟨y, hy⟩ : K), rfl⟩)
      mono_f := (Rep.mono_iff_injective f).2 Subtype.val_injective
      epi_g := (Rep.epi_iff_surjective g).2 hgsurj }

  haveI : Module.Free ℤ K := Submodule.free_of_free_of_isPrincipalIdealRing K
  have hF : ∀ (S : Subgroup G) [Fintype S] (n : ℤ), CategoryTheory.Limits.IsZero ((Rep.res S.subtype F).tateCohomology n) := by
    intro S _ n
    obtain ⟨γ, ⟨e⟩⟩ := Rep.nonempty_res_free_iso_free (k := ℤ) S (B : Type)
    obtain ⟨e'⟩ := Rep.nonempty_tateCohomology_iso_of_iso (e ≪≫ (MonoidalCategory.rightUnitor (Rep.free ℤ S γ)).symm) n
    exact Limits.IsZero.of_iso (Rep.isZero_tateCohomology_free_tensor γ (𝟙_ (Rep ℤ S)) n) e'
  have hP : ∀ (S : Subgroup G) [Fintype S] (q : ℤ), CategoryTheory.Limits.IsZero ((Rep.res S.subtype P₁).tateCohomology q) := by
    intro S _ q
    have hXS := Rep.shortExact_map_resFunctor S.subtype hX
    have key : ∀ n : ℤ, CategoryTheory.Limits.IsZero ((Rep.res S.subtype P₁).tateCohomology (n + 1)) := fun n => by
      have ex := Rep.exact_tateDelta_tateMap hXS n
      have hall : ∀ y : (Rep.res S.subtype P₁).tateCohomology (n + 1), y = 0 := fun y => by
        have hy : (Rep.tateMap ((ShortComplex.mk f g w).map (Rep.resFunctor S.subtype)).f (n + 1)).hom y = 0 :=
          zelt (hF S (n + 1)) _
        obtain ⟨x, hx⟩ := (ex y).1 hy
        have hz : (Rep.tateδ hXS n).hom 0 = 0 := (Rep.tateδ hXS n).hom.map_zero
        rw [← hx, zelt (hB S n) x]
        exact hz
      haveI : Subsingleton ((Rep.res S.subtype P₁).tateCohomology (n + 1)) := ⟨fun a b => by rw [hall a, hall b]⟩
      exact ModuleCat.isZero_of_subsingleton _
    have := key (q - 1)
    rwa [Int.sub_add_cancel] at this

  obtain ⟨β, i, r, hir⟩ := Rep.exists_retract_free_of_forall_isZero (K : Type) ρ₁ hP
  exact ⟨B, β, P₁, i, r, hir, f, g, w, hX⟩

end S_Rep_exists_shortExact_free_of_forall_isZero
end P2MW
export P2MW.S_Rep_exists_shortExact_free_of_forall_isZero (solution)
