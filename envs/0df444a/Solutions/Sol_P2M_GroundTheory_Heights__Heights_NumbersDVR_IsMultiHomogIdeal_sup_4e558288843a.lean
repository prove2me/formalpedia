-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IsMultiHomogIdeal_sup_4e558288843a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:34.379816+00:00
-- url     : https://prove2.me/submissions/c55bf187-bedd-4df0-8db4-324f8fa62862

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PColonMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsSide

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace IsMultiHomogIdeal
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
    {I J : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) (hJ : IsMultiHomogIdeal J) :
    IsMultiHomogIdeal (I ⊔ J) := by
  intro f hf b
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.add_mem_sup (hI x hx b) (hJ y hy b)
end IsMultiHomogIdeal
end GroundTheory.Heights₂.Heights.NumbersDVR
