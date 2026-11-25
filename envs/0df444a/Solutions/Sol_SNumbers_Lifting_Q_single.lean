-- Prove2me | solution 1 for SNumbers.Lifting.Q_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:39:35.208966+00:00
-- url     : https://prove2.me/submissions/cfe9c650-3093-4cdc-8411-f3f961770332

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]
namespace SNumbers.Lifting
theorem _root_.solution (x : X) (hx : ‖x‖ ≤ 1) (c : 𝕜) :
    letI : DecidableEq (Ball X) := Classical.decEq _
    (Q : BallLp 𝕜 X →L[𝕜] X) (lp.single 1 (⟨x, hx⟩ : Ball X) c) = c • x := by
  let : DecidableEq (Ball X) := Classical.decEq _
  rw [Q_apply, tsum_eq_single (⟨x, hx⟩ : Ball X)]
  · rw [lp.single_apply_self]
  · intro y hy; rw [lp.single_apply_ne 1 _ _ hy, zero_smul]
end SNumbers.Lifting
