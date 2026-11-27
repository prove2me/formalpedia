-- Prove2me | solution 1 for P2M_GlobalTheory_localized__saturationIn_2c26f398bac4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:52:46.765504+00:00
-- url     : https://prove2.me/submissions/3c763e74-2f86-4e31-84ba-e5f495f4b65a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R) [IsLocalization p S]
  {Mp : Type*} [AddCommGroup Mp] [Module R Mp] [Module S Mp] [IsScalarTower R S Mp]
  (f : M →ₗ[R] Mp) [IsLocalizedModule p f]
namespace GlobalTheory
theorem _root_.solution (hp : p ≤ R⁰) (P N : Submodule R M) :
    (saturationIn P N).localized' S p f =
      saturationIn (P.localized' S p f) (N.localized' S p f) := by
  rw [saturationIn_def, saturationIn_def, Submodule.localized'_inf, localized'_saturation S p f hp]
end GlobalTheory
