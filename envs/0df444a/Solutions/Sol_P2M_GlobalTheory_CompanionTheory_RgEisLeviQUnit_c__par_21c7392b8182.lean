-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_c__par_21c7392b8182
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:53.098824+00:00
-- url     : https://prove2.me/submissions/1bdf1ddd-1871-47fd-b571-e81f2b2950eb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_uQ_closed
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_mulQ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_contQ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_ratQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (A : Ad E R) (ε : ℤˣ)
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {_fF : Fintype ↥sᶜ} {_fD : DecidableEq ↥sᶜ}
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (hB : BdetLaw) (hA : A.Good) (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι)) :
    IsPar (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (c₀ A ε s) := by
  have hL := hA.toGoodL
  refine ⟨uQ_closed A ε s hB hL, fun g => ?_, ⟨fun p hp q hq => ?_, fun p _ => ?_, fun γ hγ hq => ?_, ?_⟩⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := hI g
    exact ⟨p, hp.1, k, hk, rfl⟩
  · simp only [c₀]
    rw [bdet_mulQ A ε s hB hL p q hp hq, map_mul, Circle.coe_mul]
  · exact Circle.norm_coe _
  · obtain ⟨x, hx⟩ := bdet_ratQ A ε s hB hL γ hq hγ
    simp only [c₀]
    rw [hx, hL.χi]
    rfl
  · have hc : Continuous (fun z : Circle => (z : ℂ)) := by
      first | fun_prop | exact continuous_subtype_val | exact continuous_induced_dom
    exact hc.comp_continuousOn (hL.χcont.comp_continuousOn (bdet_contQ A ε s hB hL))
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
