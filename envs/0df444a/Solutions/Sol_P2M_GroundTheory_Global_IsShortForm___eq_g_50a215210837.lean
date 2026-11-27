-- Prove2me | solution 1 for P2M_GroundTheory_Global_IsShortForm___eq_g_50a215210837
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:19.727045+00:00
-- url     : https://prove2.me/submissions/ad1d5f3c-1613-4a3c-a347-931519a413ba

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass
theorem _root_.solution {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = g₂ W ^ 3 - 27 * g₃ W ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := hW
  first
  | (simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, g₂, g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, h1, h2, h3]; ring)



