-- Prove2me | solution 1 for QFS.formHs_congr_ae
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:01.200296+00:00
-- url     : https://prove2.me/submissions/df5f4416-3037-461f-817f-600ae4698816

import Theorems.Thm_QFS_form_congr_ae


import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

open QFS

variable {d : ℕ}


set_option autoImplicit false

theorem solution {Ω : Set (EuclideanSpace ℝ (Fin d))} (α : ℝ)
    {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hfg : ∀ᵐ x ∂(volume.restrict Ω), f x = g x) : formHs Ω α f = formHs Ω α g := QFS.form_congr_ae _ hfg
#print axioms solution
