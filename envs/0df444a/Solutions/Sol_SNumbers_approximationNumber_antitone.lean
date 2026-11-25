-- Prove2me | solution 1 for SNumbers.approximationNumber_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:54:58.245965+00:00
-- url     : https://prove2.me/submissions/ec2a1ee7-fefa-425e-a5ff-208ac8ce99dd

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_P2M_SNumbers_approximationNumber_antitone__260bc309c16c

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
    approximationNumber S (n + 1) ≤ approximationNumber S n :=
  approximationNumber_antitone' (Nat.le_succ n)
end SNumbers
