-- Prove2me | solution 1 for Rep.exists_retract_free_of_forall_isZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/79f56fac-e762-5e29-b9c6-c93ced7db344

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_Rep_isZero_tateCohomology_of_forall_sylow
import Theorems.Thm_Rep_isZero_tateCohomology_ihom_of_isPGroup
import Theorems.Thm_Rep_nonempty_splitting_of_isZero_H1_ihom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_retract_free_of_forall_isZero
p2m_attr_erase "simp" "Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply"

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

attribute [local instance 2000] Rep.hV2 Rep.hV1

theorem solution {G : Type} [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V)
    (hA : ∀ (S : Subgroup G) [Fintype S] (q : ℤ),
      CategoryTheory.Limits.IsZero ((Rep.res S.subtype (Rep.of ρ)).tateCohomology q)) :
    ∃ (α : Type) (i : Rep.of ρ ⟶ Rep.free ℤ G α) (r : Rep.free ℤ G α ⟶ Rep.of ρ), i ≫ r = 𝟙 (Rep.of ρ) := by
  classical
  let A : Rep ℤ G := Rep.of ρ

  let F : Rep ℤ G := Rep.free ℤ G V
  let g : F ⟶ A := Rep.freeLift ℤ G A (fun v => v)
  have hg1 : ∀ v : V, g.hom (Finsupp.single v (MonoidAlgebra.single (1 : G) (1 : ℤ))) = v := fun v => by
    change (Representation.freeLift ρ (fun v : V => v)) (Finsupp.single v (MonoidAlgebra.single 1 1)) = v
    rw [Representation.freeLift_single_single, map_one, Module.End.one_apply, one_smul]
  have hgsurj : Function.Surjective g.hom := fun v => ⟨_, hg1 v⟩
  let K : Submodule ℤ (V →₀ MonoidAlgebra ℤ G) := LinearMap.ker g.hom.toLinearMap
  have hK : ∀ s : G, K ≤ Submodule.comap (F.ρ s) K := fun s x hx => by
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply, K] at hx ⊢
    rw [Rep.hom_comm_apply, hx, map_zero]
  let σ : Representation ℤ G K := Representation.subrepresentation F.ρ K hK
  let R : Rep ℤ G := Rep.of σ
  let f : R ⟶ F := Rep.ofHom ⟨Submodule.subtype K, fun _ => rfl⟩
  have w : f ≫ g = 0 := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.2))
  let X : ShortComplex (Rep ℤ G) := ShortComplex.mk f g w
  have hX : X.ShortExact :=
    { exact := (forget₂ (Rep ℤ G) (ModuleCat ℤ)).reflects_exact_of_faithful _
        ((ShortComplex.moduleCat_exact_iff _).2 fun (y : F) (hy : g.hom y = 0) => ⟨(⟨y, hy⟩ : K), rfl⟩)
      mono_f := (Rep.mono_iff_injective f).2 Subtype.val_injective
      epi_g := (Rep.epi_iff_surjective g).2 hgsurj }

  haveI : NoZeroSMulDivisors ℤ (V →₀ MonoidAlgebra ℤ G) := ⟨fun {c x} h => by
    refine or_iff_not_imp_left.mpr fun hc => Finsupp.ext fun v => MonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_)
    have := congrArg (fun f : V →₀ MonoidAlgebra ℤ G => (f v).coeff g) h
    simp only [Finsupp.smul_apply, MonoidAlgebra.coeff_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      Finsupp.coe_zero, Pi.zero_apply, MonoidAlgebra.coeff_zero] at this
    simpa using (mul_eq_zero.mp this).resolve_left hc⟩
  haveI : NoZeroSMulDivisors ℤ K :=
    Function.Injective.noZeroSMulDivisors (Submodule.subtype K) Subtype.val_injective (map_zero _) (fun c x => rfl)

  have hH1 : CategoryTheory.Limits.IsZero (((ihom A).obj R).tateCohomology 1) := by
    apply Rep.isZero_tateCohomology_of_forall_sylow
    intro p _ P _
    change CategoryTheory.Limits.IsZero
      (((ihom (Rep.of (ρ.comp (P : Subgroup G).subtype))).obj (Rep.of (σ.comp (P : Subgroup G).subtype))).tateCohomology 1)
    exact Rep.isZero_tateCohomology_ihom_of_isPGroup P.isPGroup' V (ρ.comp (P : Subgroup G).subtype) K
      (σ.comp (P : Subgroup G).subtype) (hA P (-1)) (hA P (-2)) 1
  have hH1' : CategoryTheory.Limits.IsZero (groupCohomology ((ihom X.X₃).obj X.X₁) 1) := hH1

  obtain ⟨spl⟩ := Rep.nonempty_splitting_of_isZero_H1_ihom hX hH1'
  exact ⟨V, spl.s, g, spl.s_g⟩

end S_Rep_exists_retract_free_of_forall_isZero
end P2MW
export P2MW.S_Rep_exists_retract_free_of_forall_isZero (solution)
