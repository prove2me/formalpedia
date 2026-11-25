-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:42:26.936156+00:00
-- url     : https://prove2.me/submissions/110865ea-942e-4ab6-b59d-1bc9638ca2c3

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_kolmogorovNumber_antitone
public import Theorems.Thm_SNumbers_kolmogorovNumber_zero_eq_norm

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ ‖S‖ :=
  (antitone_nat_of_succ_le (kolmogorovNumber_antitone S) (Nat.zero_le n)).trans_eq
    (kolmogorovNumber_zero_eq_norm S)
end SNumbers
