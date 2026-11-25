-- Prove2me | solution 1 for ReciprocityTheory.Cheb.primeBelow_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:32.155607+00:00
-- url     : https://prove2.me/submissions/7a815d97-a2d4-4f17-8510-affd959e6728

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Theorems.Thm_ReciprocityTheory_Cheb_primeBelow_prime
import Theorems.Thm_ReciprocityTheory_Cheb_nrm_eq_primeBelow_pow
import Theorems.Thm_ReciprocityTheory_Cheb_two_le_nrm__ac429c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (q : Prm E) (h : ¬ (Nrm q).Prime) : primeBelow q ^ 2 ≤ Nrm q := by
  obtain ⟨f, hf⟩ := nrm_eq_primeBelow_pow q
  have hp := primeBelow_prime q
  have h1 : Nrm q ≠ 1 := by have := two_le_nrm q; omega
  rw [hf] at h h1 ⊢
  have hf0 : f ≠ 0 := by rintro rfl; simp at h1
  have hf1 : f ≠ 1 := by rintro rfl; simp [hp] at h
  exact Nat.pow_le_pow_right hp.pos (by omega)
end ReciprocityTheory.Cheb
