-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.ann_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:19.396199+00:00
-- url     : https://prove2.me/submissions/e012e979-d15c-4e76-aa1b-5cca42cb56bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.VolAAW
theorem _root_.solution {V : Type} (ψ0 : Fv F v → ℂ) (B : V → V → Fv F v) (L : Set V)
    (hC : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) ↔
      t ∈ v.adicCompletionIntegers F)
    (hs : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y)
    (hD : {y | ∀ x ∈ L, B x y ∈ v.adicCompletionIntegers F} = L) :
    ann (fun x y => ψ0 (B x y)) L = L := by
  ext y
  constructor
  · intro hy
    rw [← hD]
    intro x hx
    rw [← hC]
    intro s hs'
    obtain ⟨x', hx', h⟩ := hs s hs' x hx
    rw [← h y]
    exact hy x' hx'
  · intro hy
    rw [← hD] at hy
    intro x hx
    have ht := (hC _).2 (hy x hx) 1 (one_mem _)
    simpa using ht
end PI.VolStabSW.VolAAW
