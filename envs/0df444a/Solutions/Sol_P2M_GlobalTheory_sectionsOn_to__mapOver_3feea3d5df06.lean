-- Prove2me | solution 1 for P2M_GlobalTheory_sectionsOn_to__mapOver_3feea3d5df06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:31.796802+00:00
-- url     : https://prove2.me/submissions/7e61d50b-2914-401b-9560-839445bd7c46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe t v u
noncomputable section
open GlobalTheory
variable {X Y : Scheme.{u}} {ι : Type}
variable (g : Y ⟶ X) (V : X.Opens) (U : ι → X.Opens)
variable {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)] {S : Type t} [CommRing S]
  [Algebra S Γ(Y, ⊤)] {σ : R →+* S}
  {g} (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
  {F : X.Modules} {G : Y.Modules} (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)
namespace GlobalTheory
namespace sectionsOn
theorem _root_.solution (W : X.Opens) (x : sectionsOn F W) :
    sectionsOn.toΓ G (g ⁻¹ᵁ W) (sectionsOn.mapOver hσ φ W x) = φ.app W (sectionsOn.toΓ F W x) :=
  rfl
end sectionsOn
end GlobalTheory
