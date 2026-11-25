-- Prove2me | solution 1 for ReciprocityTheory.Cheb.psum_term_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:59.771105+00:00
-- url     : https://prove2.me/submissions/4eaa3a0f-48a1-4a8e-a8a0-8be37fbcbd8c

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
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
theorem _root_.solution {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (q : Prm E) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  have hN : (0 : ℕ) < Nrm q := by have := two_le_Nrm q; omega
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN]
  simp only [Complex.neg_re, Complex.ofReal_re]
  have := DirichletCharacter.norm_le_one χ ((Nrm q : ℕ) : ZMod l)
  have hp : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
  nlinarith
end ReciprocityTheory.Cheb
