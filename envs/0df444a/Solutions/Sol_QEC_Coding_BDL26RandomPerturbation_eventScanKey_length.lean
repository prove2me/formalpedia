-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.eventScanKey_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:56:03.977009+00:00
-- url     : https://prove2.me/submissions/c31b479a-7ff9-4d4c-9605-a010604fc9f6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Mathlib.Data.List.Lex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleKey_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : (eventScanKey P J radius e).length = 4 := by
  rw [eventScanKey,Finset.length_sort,Finset.card_image_of_injective _ (triangleKey_injective P)]
  exact e.property.1
end QEC.Coding.BDL26RandomPerturbation
