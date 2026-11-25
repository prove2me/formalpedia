-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_moduleLeftHomologyData_homologyIso_hom_homology__192a5dc2c4b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:00.414373+00:00
-- url     : https://prove2.me/submissions/099c08b8-b541-45cb-8888-d1800061fc67

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData

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
variable (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range S.f.hom)
namespace GroundTheory.GroupCoh
theorem _root_.solution [S.HasHomology]
    (z : S.cycles) (x : K) (hx : ι x = S.iCycles.hom z) :
    (moduleLeftHomologyData S K ι hι hrange N hN).homologyIso.hom.hom (S.homologyπ.hom z) =
      Submodule.Quotient.mk x := by
  set h := moduleLeftHomologyData S K ι hι hrange N hN
  have h1 : (S.homologyπ ≫ h.homologyIso.hom).hom z = (h.cyclesIso.hom ≫ h.π).hom z := by
    rw [h.homologyπ_comp_homologyIso_hom]
  have h2 : (h.cyclesIso.hom ≫ h.i).hom z = S.iCycles.hom z := by
    rw [h.cyclesIso_hom_comp_i]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [h1]
  have : h.cyclesIso.hom.hom z = x := hι (by rw [hx, ← h2]; rfl)
  rw [this]
  rfl
end GroundTheory.GroupCoh
