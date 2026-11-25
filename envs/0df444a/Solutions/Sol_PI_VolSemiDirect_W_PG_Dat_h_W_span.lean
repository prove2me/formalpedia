-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_W_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:38.891888+00:00
-- url     : https://prove2.me/submissions/787f3df8-6bc6-47d6-bf0f-2cf2e69c35c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_W_e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable (D : Dat A n r)
variable {D}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) {w : n → A} (hw : IsW D w) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : D.h w x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact h_W_e H hw a
  | zero =>
    change D.hL w 0 = 0
    exact map_zero _
  | add x y _ _ hx hy =>
    change D.hL w (x + y) = 0
    rw [map_add]
    change D.h w x + D.h w y = 0
    rw [hx, hy, add_zero]
  | smul c x _ hx =>
    change D.hL w (c • x) = 0
    rw [map_smul]
    change c • D.h w x = 0
    rw [hx, smul_zero]
end PI.VolSemiDirect.W.PG.Dat
