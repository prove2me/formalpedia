-- Prove2me | solution 1 for P2M_GlobalTheory_adicLevelMap___951f147d84c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:40.557573+00:00
-- url     : https://prove2.me/submissions/e6e49baf-ef4d-4d15-8037-c0eaeaeb886d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
namespace GlobalTheory
theorem _root_.solution {m n : ℕ} (h : m ≤ n) :
    adicLevelMap I h ≫ adicLevelι I n = adicLevelι I m := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl
end GlobalTheory
