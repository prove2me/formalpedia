-- Prove2me | solution 1 for ReciprocityTheory.Cheb.chebyshev_second_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:07:36.830014+00:00
-- url     : https://prove2.me/submissions/8610a991-9055-4bbf-995a-920209d37dbb

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Theorems.Thm_ReciprocityTheory_Cheb_ehold_norm_cpow
import Theorems.Thm_ReciprocityTheory_Cheb_ehold_summable
import Theorems.Thm_ReciprocityTheory_Cheb_euler_exp_log
import Theorems.Thm_ReciprocityTheory_Cheb_two_le_Nrm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution : E2 := by
  intro E _ _ l _ χ s hs
  have key := euler_exp_log (E := E)
    (fun a => χ ((Ideal.absNorm a : ℕ) : ZMod l) * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-(s : ℂ)))
    (by simp) (fun a b => by
      simp only [map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]; ring)
    (ehold_summable (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l)) (fun a => DirichletCharacter.norm_le_one χ _) hs)
    (fun q => by
      rw [norm_mul, ehold_norm_cpow _ hs]
      have h2 : (2 : ℝ) ≤ ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
      have h3 : ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) ^ (-s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
      calc _ ≤ 1 * ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) ^ (-s) :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (Real.rpow_nonneg (by positivity) _)
        _ < 1 := by rw [one_mul]; exact h3)
  exact key
end ReciprocityTheory.Cheb
