-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_d_b9ed291a3cb0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:24.016645+00:00
-- url     : https://prove2.me/submissions/db5afbe9-8c0b-47bc-bc8a-32e470a48761

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
theorem _root_.solution (J : Finset (Fin (N + 1))) (i : ℕ) (z : Cech.Cochain (G S N) i) :
    Cech.d (G S N) (ρ S N) i (partC S J i z) = partC S J (i + 1) (Cech.d (G S N) (ρ S N) i z) :=
  (Cech.mapC_d (ρ := ρ S N) (ρ' := ρ S N) (fun _ => part S J) (fun _ _ _ _ => rfl) i z).symm
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
