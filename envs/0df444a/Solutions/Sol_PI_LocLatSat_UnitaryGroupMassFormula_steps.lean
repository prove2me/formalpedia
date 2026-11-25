-- Prove2me | solution 1 for PI.LocLatSat.UnitaryGroupMassFormula.steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:39.382823+00:00
-- url     : https://prove2.me/submissions/4f370ee3-0a05-41c9-bc04-20dd724a996c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_LocLatSat
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_step
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open PI PI.LocLatSat PI.LocLatSat.UnitaryGroupMassFormula
variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}
namespace PI.LocLatSat.UnitaryGroupMassFormula
theorem _root_.solution {ι : Type*} [DecidableEq ι] (g : ι → (Fin n → K) →ₗ[K] K)
    (Λ : Submodule R (Fin n → K)) (hΛ : Λ.FG) {x : Fin n → S} (hx : x ∈ latG φ O Λ)
    (T : Finset ι) (h0 : ∀ i ∈ T, fP φ (g i) x = 0) :
    x ∈ latG φ O (Λ ⊓ ⨅ i ∈ T, (LinearMap.ker (g i)).restrictScalars R) := by
  induction T using Finset.induction_on with
  | empty => simpa using hx
  | @insert a T ha ih =>
    have hx' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have hfr : IsFractional R⁰ ((Λ ⊓ ⨅ i ∈ T, (LinearMap.ker (g i)).restrictScalars R).map
        ((g a).restrictScalars R)) := by
      have hfg : (Λ.map ((g a).restrictScalars R)).FG := hΛ.map _
      exact FractionalIdeal.isFractional_of_le (J := ⟨_, FractionalIdeal.isFractional_of_fg hfg⟩)
        (Submodule.map_mono inf_le_left)
    have hs := step φ O _ (g a) hfr hx' (h0 a (Finset.mem_insert_self a T))
    have e : Λ ⊓ ⨅ i ∈ insert a T, (LinearMap.ker (g i)).restrictScalars R =
        (Λ ⊓ ⨅ i ∈ T, (LinearMap.ker (g i)).restrictScalars R) ⊓
          (LinearMap.ker (g a)).restrictScalars R := by
      rw [Finset.iInf_insert]
      exact (inf_left_comm _ _ _).trans (inf_comm _ _)
    rw [e]
    exact hs
end PI.LocLatSat.UnitaryGroupMassFormula
