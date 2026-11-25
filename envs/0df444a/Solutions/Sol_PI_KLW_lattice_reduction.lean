-- Prove2me | solution 1 for PI.KLW.lattice_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:15.127006+00:00
-- url     : https://prove2.me/submissions/8e38f979-19c2-459b-b3cd-9d664cc119c4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairingFactorsThroughPeriods
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeReduction
import Theorems.Thm_PI_KLW_Rp_fintype
import Theorems.Thm_PI_KLW_conjK_invol
import Theorems.Thm_PI_KLW_lset_spans
import Theorems.Thm_PI_KLW_lset_unimod
import Theorems.Thm_PI_KLW_splitK_of
import Theorems.Thm_PI_KLW_sum_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
namespace PI.KLW
theorem _root_.solution : LocalIsoOfLatticeIso := by
  intro hLat K E _ _ _ _ _ cj n _ I p hK hc hp hs hI hg0
  obtain ⟨g₀, hg⟩ := hg0
  set c := conjK cj hc.2.1 with hcdef
  obtain ⟨u, hu, huL⟩ := hLat K c p (Fin 4 × n) (Lset I p g₀) hK (conjK_invol cj hc) hp
    (splitK_of cj hc hs) (lset_unimod cj hc I p g₀ hI hg) (lset_spans cj hc I p g₀ hI)
  refine ⟨g₀.trans u, ?_, ?_, ?_⟩
  · intro x y
    rw [sum_conj cj hc.2.1, ← hg x y, sum_conj cj hc.2.1]
    congr 1
    exact hu (g₀ x) (g₀ y)
  · intro x hx
    have hmem : g₀ x ∈ Lset I p g₀ := ⟨1, Nat.coprime_one_left p, fun a => by
      rw [Nat.cast_one, one_mul, LinearEquiv.symm_apply_apply]; exact hx a⟩
    obtain ⟨s, hs', hsx⟩ := Rp_fintype (p := p) _ ((huL _).1 hmem)
    exact ⟨s, hs', fun w => hsx w⟩
  · intro v hv
    have hmem : u.symm v ∈ Lset I p g₀ := (huL _).2 fun i => by
      rw [LinearEquiv.apply_symm_apply]
      obtain ⟨y, hy⟩ := hv i
      exact ⟨1, Nat.coprime_one_left p, ⟨y, by rw [Nat.cast_one, one_mul]; exact hy⟩⟩
    obtain ⟨s, hs', hsv⟩ := hmem
    exact ⟨s, hs', fun a => hsv a⟩
end PI.KLW
