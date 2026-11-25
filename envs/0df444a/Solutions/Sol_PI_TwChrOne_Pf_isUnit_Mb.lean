-- Prove2me | solution 1 for PI.TwChrOne.Pf.isUnit_Mb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:44:09.600958+00:00
-- url     : https://prove2.me/submissions/f6ed92ca-ea38-41aa-9aeb-ca4b9dc9317d

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Theorems.Thm_PI_TwChrOne_Pf_Mb_mul_of
import Theorems.Thm_PI_TwChrOne_Pf_Mb_one
import Theorems.Thm_PI_TwChrOne_Pf_hDA_of
import Theorems.Thm_PI_TwChrOne_Pf_hI_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}
variable {kj N c : ℕ}
namespace PI.TwChrOne.Pf
theorem _root_.solution {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) :
    IsUnit (Mb P kj N c r).det := by
  have hr' : r⁻¹ ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c := inv_mem hr
  have hm := Mb_mul_of P (h := 1) (r := r) (g := r⁻¹) (hDA_of P hr) (hI_of P hr) (hI_of P hr')
    (fun t => by show _ = (r * r⁻¹) _; rw [mul_inv_cancel])
  rw [Mb_one] at hm
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_one, Matrix.det_mul] at hd
  exact isUnit_iff_exists_inv.2 ⟨_, hd.symm⟩
end PI.TwChrOne.Pf
