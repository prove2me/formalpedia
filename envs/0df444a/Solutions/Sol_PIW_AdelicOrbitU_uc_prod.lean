-- Prove2me | solution 1 for PIW.AdelicOrbitU.uc_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:02.035809+00:00
-- url     : https://prove2.me/submissions/105e5476-1a17-49a4-947b-57d95275de71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum
import Theorems.Thm_PIW_AdelicOrbitU_uc_coeffs
import Theorems.Thm_PIW_AdelicOrbitU_uc_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped RestrictedProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (hA : UnitChoice A) (hB : UnitChoice B) :
    UnitChoice (A × B) := by
  unfold UnitChoice at hA hB ⊢
  intro k f hf
  obtain ⟨a, ha⟩ := uc_coeffs hf
  have hA1 : Ideal.span (Set.range fun i => (f i).1) = ⊤ :=
    uc_span (fun i => (f i).1) (fun i => (a i).1) (by
      have h := congrArg Prod.fst ha
      simpa [Prod.fst_sum] using h)
  have hB1 : Ideal.span (Set.range fun i => (f i).2) = ⊤ :=
    uc_span (fun i => (f i).2) (fun i => (a i).2) (by
      have h := congrArg Prod.snd ha
      simpa [Prod.snd_sum] using h)
  obtain ⟨eA, hA1', hA2, hA3, hA4⟩ := hA k _ hA1
  obtain ⟨eB, hB1', hB2, hB3, hB4⟩ := hB k _ hB1
  refine ⟨fun i => (eA i, eB i), ?_, ?_, ?_, ?_⟩
  · intro i
    exact Prod.ext (hA1' i) (hB1' i)
  · intro i j hij
    exact Prod.ext (hA2 i j hij) (hB2 i j hij)
  · exact Prod.ext (by simpa [Prod.fst_sum] using hA3) (by simpa [Prod.snd_sum] using hB3)
  · rw [Prod.isUnit_iff]
    constructor
    · simpa [Prod.fst_sum] using hA4
    · simpa [Prod.snd_sum] using hB4
end PIW.AdelicOrbitU
