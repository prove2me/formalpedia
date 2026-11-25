-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_homologyFunctorIso__moduleLeftHomologyData_apply_b9da34f1dace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:42:38.997244+00:00
-- url     : https://prove2.me/submissions/6a99518e-d4c1-4730-a304-e9b6c3dfa98e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Theorems.Thm_P2M_GroundTheory_GroupCoh_moduleLeftHomologyData_homologyIso_hom_homology__192a5dc2c4b8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.GroupCoh
theorem _root_.solution {ιc : Type*} {c : ComplexShape ιc}
    (C : HomologicalComplex (ModuleCat.{u} R) c) (i j k : ιc) (hi : c.prev j = i)
    (hk : c.next j = k) (K : Type u) [AddCommGroup K] [Module R K]
    (ι : K →ₗ[R] (C.sc' i j k).X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker (C.sc' i j k).g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range (C.sc' i j k).f.hom)
    (z : C.cycles j) (x : K) (hx : ι x = (C.iCycles j).hom z) :
    (moduleLeftHomologyData _ K ι hι hrange N hN).homologyIso.hom.hom
      (((HomologicalComplex.homologyFunctorIso' _ c i j k hi hk).hom.app C).hom
        ((C.homologyπ j).hom z)) = Submodule.Quotient.mk x := by
  set e := (HomologicalComplex.natIsoSc' (ModuleCat.{u} R) c i j k hi hk).hom.app C
  have h1 : (HomologicalComplex.homologyFunctorIso' _ c i j k hi hk).hom.app C =
      ShortComplex.homologyMap e := by
    simp [HomologicalComplex.homologyFunctorIso', e]
    exact Category.id_comp _
  have h2 : (ShortComplex.homologyMap e).hom ((C.sc j).homologyπ.hom z) =
      (C.sc' i j k).homologyπ.hom ((ShortComplex.cyclesMap e).hom z) :=
    congr(($(ShortComplex.homologyπ_naturality e)).hom z)
  have h3 : (C.sc' i j k).iCycles.hom ((ShortComplex.cyclesMap e).hom z) =
      e.τ₂.hom ((C.sc j).iCycles.hom z) :=
    congr(($(ShortComplex.cyclesMap_i e)).hom z)
  have h4 : (C.sc' i j k).iCycles.hom ((ShortComplex.cyclesMap e).hom z) = (C.iCycles j).hom z := by
    rw [h3]
    simp [e]
    rfl
  rw [h1]
  refine (congrArg (fun w => (moduleLeftHomologyData _ K ι hι hrange N hN).homologyIso.hom.hom w)
    h2).trans ?_
  exact moduleLeftHomologyData_homologyIso_hom_homologyπ _ K ι hι hrange N hN _ x (hx.trans h4.symm)
end GroundTheory.GroupCoh
