-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:13.03881+00:00
-- url     : https://prove2.me/submissions/6e82684b-a4bd-4541-baed-2c0c1f0f70ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
variable (P : ArithVariety n)
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.ArithVariety
theorem _root_.solution :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal :=
  ⟨fun k ↦ (P.relevant k).choose, fun k ↦ (P.relevant k).choose_spec⟩
end GroundTheory.Heights₂.Heights.ArithVariety
