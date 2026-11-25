-- Prove2me | solution 1 for PI.Dv.ProjAW.span_cut_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:45.929797+00:00
-- url     : https://prove2.me/submissions/ac2e818b-a91e-4853-811d-d44c253e4e6b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
import Theorems.Thm_PI_Dv_ProjAW_part1
import Theorems.Thm_PI_Dv_ProjAW_part2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution {f : Module.End K A.V} (hf : f * f = f) {n : ℕ} (hn0 : 0 < n)
    (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) :
    Submodule.span K (imgE A f A.L : Set A.V) = Submodule.span K (cutE A f A.L : Set A.V) := by
  refine le_antisymm ?_ (Submodule.span_mono (part2 A hf))
  rw [Submodule.span_le]
  intro x hx
  have h1 := part1 A hn x hx
  have h2 : ((n : ℕ) : K) • x ∈ Submodule.span K (cutE A f A.L : Set A.V) := by
    have : ((n : ℕ) : K) • x = ((n : ℕ) : 𝓞 K) • x := by
      rw [Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul (𝓞 K)]
    rw [this]
    exact Submodule.subset_span h1
  have hnz : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn0.ne'
  have h3 := Submodule.smul_mem _ ((n : ℕ) : K)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ hnz, one_smul] at h3
end PI.Dv.ProjAW
