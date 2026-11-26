-- Prove2me | solution 1 for bddAbove_norm_eval_image_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:33:07.618895+00:00
-- url     : https://prove2.me/submissions/6f591879-2f14-42ef-b4f7-0102cefdb06a

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann

set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
theorem _root_.solution (p : ℂ[X]) {K : Set ℂ} (hK : IsCompact K) :
    BddAbove ((fun z => ‖p.eval z‖) '' K) :=
  hK.bddAbove_image p.continuous.norm.continuousOn
