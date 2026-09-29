-- Prove2me | solution 1 for QFS.le_pi_div_two_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:01.839307+00:00
-- url     : https://prove2.me/submissions/df82a545-d2b8-4a35-ad78-4eb69741b04a




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

theorem solution {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {ϑ : ℝ}
    (hΓ : IsBounded Γ ϑ) : ϑ ≤ Real.pi / 2 := le_trans (hΓ.2 0) (Γ 0).apex_le
#print axioms solution
