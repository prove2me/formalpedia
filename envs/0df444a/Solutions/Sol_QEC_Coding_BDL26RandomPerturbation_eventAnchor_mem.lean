-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.eventAnchor_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:50:08.960441+00:00
-- url     : https://prove2.me/submissions/f9e91835-c593-4eb5-8f97-4c6f5daa4135

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleKey_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ)
    (e : Event P J radius) : eventAnchor P J radius e ∈ e.val := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' (triangleKey P) (triangleKey_injective P)
  exact Finset.min'_mem e.val (event_nonempty P J radius e)
end QEC.Coding.BDL26RandomPerturbation
