-- Prove2me | solution 1 for QFS.path_props
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:18:28.931506+00:00
-- url     : https://prove2.me/submissions/2a2d1fe2-5c8e-4cd2-85d9-be9b310757cd

import Theorems.Thm_QFS_path_props_long


import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric

open QFS

variable {d : ℕ}


set_option autoImplicit false

theorem solution (hd : 1 ≤ d) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (R₀ : ℝ) :
    PathPropsHolds d ϑ R₀ := by
  obtain ⟨N, M, lam, hN, hM, hlam, hp⟩ := QFS.path_props_long hd hϑ hϑ' R₀
  refine ⟨N, M, lam, hN, hM, hlam, fun Γ hΓ => ?_⟩
  obtain ⟨p, h1, h2, h3⟩ := hp Γ hΓ
  exact ⟨p, h1, h2, fun x y D hD => ⟨(h3 x y D hD).1, (h3 x y D hD).2.1⟩⟩
#print axioms solution
