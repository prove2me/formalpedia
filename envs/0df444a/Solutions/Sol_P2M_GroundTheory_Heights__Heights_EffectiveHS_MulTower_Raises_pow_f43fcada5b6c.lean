-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Raises_pow_f43fcada5b6c
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:33:17.103108+00:00
-- url     : https://prove2.me/submissions/5f8b4090-4a5e-4d9f-a0ac-8fa44cb5fe9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)


theorem solution {τ : MulTower R A} {k : ℕ} {x : A} (hx : τ.Raises k x) (n : ℕ) :
    τ.Raises (k * n) (x ^ n) := by
  induction n with
  | zero => intro j f hf; simpa using hf
  | succ n ih => simpa [pow_succ, Nat.mul_succ] using ih.mul hx
