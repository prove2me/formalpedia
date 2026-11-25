-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_HCdecomp_Red_mul___00b8b2883c0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:29.094661+00:00
-- url     : https://prove2.me/submissions/afa89061-e2fa-41f6-b33d-1f910d01caa5

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_JJ_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Low_red_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.HCdecomp
namespace Red
theorem _root_.solution {a : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (p : Fin n × Fin n) :
    Red (a * FreeAlgebra.ι ℂ p) := by
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨u', hu', h'⟩ := hu.red_mul p
  refine ⟨u', hu', fun V _ _ E hE => ?_⟩
  have := (JJ E).add_mem (JJ_mul E (h V E hE) (ev E (FreeAlgebra.ι ℂ p))) (h' V E hE)
  rw [map_mul] at this ⊢
  convert this using 1
  rw [sub_mul]; abel
end Red
end GlobalTheory.CompanionTheory.HCdecomp
