-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_rowAct_hw_ed98cf931f05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:42:01.080415+00:00
-- url     : https://prove2.me/submissions/eb98262d-fe14-460a-bddc-c11a56c3bc0b

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Definitions.Def_Lemmata_GeneralBFactRightBisForm_Imports
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_rowAct_lpMinor_ed01b70d5739

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.GradedWeylDivisibility
variable (R : Type) [CommRing R] {r n : ℕ}
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (hn : n ≤ r) (ν : Fin n → ℕ) (h : Matrix (Fin r) (Fin r) R) (hl : ∀ i j, i < j → h i j = 0) :
    rowAct R h (hw R hn ν) = hwScal R hn ν h • hw R hn ν := by
  unfold hw hwScal
  rw [map_prod, smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, rowAct_lpMinor R h hl, mul_pow, map_pow]
end Formalism.BasicNotions.Examples₂.NZ
