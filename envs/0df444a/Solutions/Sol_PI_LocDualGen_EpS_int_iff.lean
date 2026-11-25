-- Prove2me | solution 1 for PI.LocDualGen.EpS.int_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:21.601892+00:00
-- url     : https://prove2.me/submissions/17c64e1d-6b76-4dfa-989d-2204ecf89858

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Theorems.Thm_PI_LocDualGen_EpS_isIntegral_idem
import Theorems.Thm_PI_LocDualGen_EpS_mem_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Module
open PI PI.LocDualGen PI.LocDualGen.EpS
variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]
variable (hr : finrank K L = 2) (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1)
variable [ValuativeRel K]
namespace PI.LocDualGen.EpS
theorem _root_.solution (z : L) :
    IsIntegral 𝒪[K] z ↔ pr hr e he h0 h1 0 z ∈ 𝒪[K] ∧ pr hr e he h0 h1 1 z ∈ 𝒪[K] := by
  constructor
  · intro h
    exact ⟨mem_of_isIntegral (h.map ((pr hr e he h0 h1 0).restrictScalars 𝒪[K])),
      mem_of_isIntegral (h.map ((pr hr e he h0 h1 1).restrictScalars 𝒪[K]))⟩
  · rintro ⟨ha, hb⟩
    rw [decomp hr e he h0 h1 z, Algebra.smul_def, Algebra.smul_def]
    have hie := isIntegral_idem (K := K) e he
    have hif : IsIntegral 𝒪[K] (1 - e) := isIntegral_one.sub hie
    have ia : IsIntegral 𝒪[K] (algebraMap K L ((bas hr e he h0 h1).repr z 0)) :=
      isIntegral_algebraMap (R := 𝒪[K]) (x := (⟨_, ha⟩ : 𝒪[K]))
    have ib : IsIntegral 𝒪[K] (algebraMap K L ((bas hr e he h0 h1).repr z 1)) :=
      isIntegral_algebraMap (R := 𝒪[K]) (x := (⟨_, hb⟩ : 𝒪[K]))
    exact (ia.mul hie).add (ib.mul hif)
end PI.LocDualGen.EpS
