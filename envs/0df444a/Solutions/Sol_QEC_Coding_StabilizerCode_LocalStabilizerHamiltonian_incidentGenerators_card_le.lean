-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.incidentGenerators_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:26:24.885417+00:00
-- url     : https://prove2.me/submissions/001da1c1-cf55-4085-9f35-523cebab8b3f

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (i : ι) :
    (H.incidentGenerators i).card ≤ H.participationBound :=
  H.participation_le i
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
