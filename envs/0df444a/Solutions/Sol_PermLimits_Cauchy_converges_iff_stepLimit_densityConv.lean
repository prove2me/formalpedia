-- Prove2me | solution 1 for PermLimits.Cauchy.converges_iff_stepLimit_densityConv
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:11:16.333751+00:00
-- url     : https://prove2.me/submissions/a213e544-4193-459e-851a-0dc9233d5924

import Theorems.Thm_PermLimits_Existence_converges_iff_stepLimit_densityConv

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_ConvergesTo
import Definitions.Def_PermLimits_Shared_StepLimit
import Definitions.Def_PermLimits_Shared_LimitConvergence
open PermLimits
open PermLimits.Shared


open Filter unitInterval

/-- **Eq. (49)** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2,
Sect. 5.2, p. 17). For a permutation sequence `(σ_m)` with `|σ_m| → ∞` and `Z ∈ 𝒵`,
`σ_m → Z ⟺ Z_{σ_m} →ᵗ Z`.

**Formalization Note.** The sequence is named `s` (`σ` is reserved notation once `unitInterval`
is opened). `|σ_m| → ∞` is the standing assumption the paper sets in the sentence before (49).
-/
theorem solution (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun m => (s m).1) atTop atTop) (Z : I → I → ℝ) (hZ : IsLimitPerm Z) :
    ConvergesTo s Z ↔ DensityConv (fun m => stepLimit (s m).2) Z :=
  PermLimits.Existence.converges_iff_stepLimit_densityConv s hs Z hZ