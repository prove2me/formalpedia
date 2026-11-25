-- Prove2me | solution 1 for PI.ScRefExists.PPA.hG_mem_Ap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:49.348929+00:00
-- url     : https://prove2.me/submissions/fd9a2878-8691-47a8-b3f6-5981511a522e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
import Theorems.Thm_PI_ScRefExists_PPA_hG_smul_left
import Theorems.Thm_PI_ScRefExists_PPA_hG_smul_right
import Theorems.Thm_PI_ScRefExists_PPA_LA_clear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
namespace PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
private theorem mem_Ap_lemma (p : ℕ) (x : I.E) :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) :=
  Iff.rfl
end PI.ScRefExists.PPA
end
end

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.PPA
theorem _root_.solution (p : ℕ) {v v' : Fin I.n → I.E} (hv : v ∈ LA I p) (hv' : v' ∈ LA I p) :
    hG I v v' ∈ Ap I p := by
  obtain ⟨s, hs, hsv⟩ := LA_clear I p hv
  obtain ⟨t, ht, htv⟩ := LA_clear I p hv'
  obtain ⟨a, ha⟩ := RingHom.mem_range.mp ((I.L_dual _).mp htv _ hsv)
  have e : hG I ((s : I.E) • v) ((t : I.E) • v') = (s : I.E) * t * hG I v v' := by
    rw [hG_smul_left, hG_smul_right, star_natCast]
    ring
  refine (mem_Ap_lemma I p _).mpr ⟨s * t, Nat.Coprime.mul hs ht, a, ?_⟩
  rw [Nat.cast_mul, ← e]
  exact ha.symm
end PI.ScRefExists.PPA
