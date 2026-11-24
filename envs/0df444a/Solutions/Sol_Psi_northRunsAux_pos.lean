-- Prove2me | solution 1 for Psi.northRunsAux_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:37:24.18703+00:00
-- url     : https://prove2.me/submissions/df7dec5b-376d-40cc-bb6b-c78d30452c35

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (Y : List Bool) (c : ℕ) : ∀ x ∈ northRunsAux Y c, 0 < x := by
  induction Y generalizing c with
  | nil =>
    intro x hx; simp only [northRunsAux] at hx; split at hx <;> simp_all
  | cons a r ih =>
    cases a with
    | true => intro x hx; simp only [northRunsAux] at hx; exact ih (c + 1) x hx
    | false =>
      intro x hx; simp only [northRunsAux, List.mem_append] at hx
      rcases hx with h1 | h2
      · split at h1 <;> simp_all
      · exact ih 0 x h2
end Psi
