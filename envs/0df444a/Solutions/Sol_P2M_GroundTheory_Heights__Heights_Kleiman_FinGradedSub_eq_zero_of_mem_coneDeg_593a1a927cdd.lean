-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_zero_of_mem_coneDeg_593a1a927cdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:23.35082+00:00
-- url     : https://prove2.me/submissions/731301d3-d57c-4f8e-b830-41a76e34734c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_not_4e0646e9c831

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
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution {I : StdCell N} (hI : ¬ I.1 ⊆ support x) {y : ConeLaurent S x}
    (hy : y ∈ M.coneDeg c I) : y = 0 := by
  obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hy
  change M.cellCone I z = 0
  rw [M.cellCone_of_not hI]
  rfl
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
