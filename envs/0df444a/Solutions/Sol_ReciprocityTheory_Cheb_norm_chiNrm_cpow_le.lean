-- Prove2me | solution 1 for ReciprocityTheory.Cheb.norm_chiNrm_cpow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:05.02988+00:00
-- url     : https://prove2.me/submissions/2f1d7e8e-1320-4896-837d-87917c7b21bf

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
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
theorem _root_.solution {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (q : Prm E) (s : ℝ) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  have hN : 0 < Nrm q := lt_of_lt_of_le (by norm_num) (two_le_Nrm q)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN]
  have h1 := χ.norm_le_one ((Nrm q : ℕ) : ZMod l)
  have h2 : (0:ℝ) ≤ ((Nrm q : ℕ) : ℝ) ^ (-(s:ℂ)).re := Real.rpow_nonneg (by positivity) _
  simp only [Complex.neg_re, Complex.ofReal_re] at h2 ⊢
  nlinarith [norm_nonneg (χ ((Nrm q : ℕ) : ZMod l))]
end ReciprocityTheory.Cheb
