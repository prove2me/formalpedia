-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_restrictImage_c6b16aec65a8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:47.839528+00:00
-- url     : https://prove2.me/submissions/ab8e3307-c007-47f3-8910-4cc7d4860b05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.Model
namespace IsBasisOn
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    {U : X.Opens} {n : ℕ} {s : Fin n → Γ(M, f ''ᵁ U)} (hs : IsBasisOn M (f ''ᵁ U) s) :
    IsBasisOn (M.restrict f) U (fun i => (M.restrictAppIso f U).inv.hom (s i)) := by
  intro W hWU
  let e : Γ(X, W) ≃+* Γ(Y, f ''ᵁ W) := ((f.appIso W).commRingCatIsoToRingEquiv).symm
  have hb := (hs (f ''ᵁ W) (Scheme.Hom.image_mono f hWU)).comp
    (Equiv.piCongrRight fun _ : Fin n => e.toEquiv).bijective
  exact hb
end IsBasisOn
end GroundTheory.Heights₂.Heights.Model
