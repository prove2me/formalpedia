-- Prove2me | solution 1 for Rep.nonempty_groupCohomology_res_iso_res_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/396f3a9e-b8bf-5efc-81a5-11d5a5a9d209

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_groupCohomology_res_iso_res_range

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G P : Type u} [CommRing k] [Group G] [Group P]
    (f : P →* G) (hf : Function.Injective f) (A : Rep.{u} k G) (n : ℕ) :
    Nonempty (groupCohomology (Rep.res f A) n ≅ groupCohomology (Rep.res f.range.subtype A) n) := by
  let e : P ≃* f.range := MonoidHom.ofInjective hf

  let ψ : Rep.res (e : P →* f.range) (Rep.res f.range.subtype A) ⟶ Rep.res f A :=
    Rep.ofHom ⟨LinearMap.id, fun x => rfl⟩
  let φ : Rep.res (e.symm : f.range →* P) (Rep.res f A) ⟶ Rep.res f.range.subtype A :=
    Rep.ofHom ⟨LinearMap.id, fun x => by
      ext a
      change A.ρ (f (e.symm x)) a = A.ρ (x : G) a
      rw [MonoidHom.apply_ofInjective_symm]⟩
  let ι : groupCohomology.inhomogeneousCochains (Rep.res f.range.subtype A) ≅
      groupCohomology.inhomogeneousCochains (Rep.res f A) :=
    { hom := groupCohomology.cochainsMap (e : P →* f.range) ψ
      inv := groupCohomology.cochainsMap (e.symm : f.range →* P) φ
      hom_inv_id := by
        refine HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext (LinearMap.ext fun x => funext fun h => ?_)
        simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, groupCohomology.cochainsMap_f, ModuleCat.hom_comp,
          ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply, LinearMap.funLeft_apply,
          LinearMap.compLeft_apply, Function.comp_def]
        change x (fun j => e (e.symm (h j))) = x h
        simp only [MulEquiv.apply_symm_apply]
      inv_hom_id := by
        refine HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext (LinearMap.ext fun x => funext fun h => ?_)
        simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, groupCohomology.cochainsMap_f, ModuleCat.hom_comp,
          ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply, LinearMap.funLeft_apply,
          LinearMap.compLeft_apply, Function.comp_def]
        change x (fun j => e.symm (e (h j))) = x h
        simp only [MulEquiv.symm_apply_apply] }
  exact ⟨((HomologicalComplex.homologyFunctor (ModuleCat k) _ n).mapIso ι).symm⟩

end S_Rep_nonempty_groupCohomology_res_iso_res_range
end P2MW
export P2MW.S_Rep_nonempty_groupCohomology_res_iso_res_range (solution)
