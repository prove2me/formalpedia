-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.le_logicalEnergyBarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:56:18.247985+00:00
-- url     : https://prove2.me/submissions/8ce27ae8-934e-458c-979f-006d16532139

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (bound : Nat)
    (hexists : ∃ γ : PauliErrorPath (ι := ι), H.HasLogicalEndpoint γ)
    (hlower : ∀ γ : PauliErrorPath (ι := ι),
      H.HasLogicalEndpoint γ → bound ≤ H.pathHeight γ) :
    bound ≤ H.logicalEnergyBarrier := by
  apply le_csInf
  · obtain ⟨γ, hγ⟩ := hexists
    exact ⟨H.pathHeight γ, γ, hγ, rfl⟩
  · rintro height ⟨γ, hγ, rfl⟩
    exact hlower γ hγ
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
