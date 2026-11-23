-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_e_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:54.159447+00:00
-- url     : https://prove2.me/submissions/942db15a-6f74-492c-afe6-e3ba3f1163a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement

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
variable {D : Dat A n r}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (b : Fin r)
    (w : n → A) : D.h (D.e b) (S w) = D.h (D.e b) w := by
  have h1 := hU (D.e b) w
  rwa [(show (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z from hS).1 b] at h1
end PI.VolSemiDirect.W.PG.Dat
