-- Prove2me | solution 1 for SNumbers.Lifting.kolmogorovNumber_eq_zero_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:30:22.333797+00:00
-- url     : https://prove2.me/submissions/1f3cd6fa-2b03-44f0-8f75-6b8ab9757916

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_approximationNumber_eq_zero_of_rank_le


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
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    kolmogorovNumber S n = 0 :=
  approximationNumber_eq_zero_of_rank_le <|
    (Submodule.rank_mono (by rintro y ⟨α, hα⟩; exact ⟨Q α, hα⟩)).trans hS
end SNumbers.Lifting
