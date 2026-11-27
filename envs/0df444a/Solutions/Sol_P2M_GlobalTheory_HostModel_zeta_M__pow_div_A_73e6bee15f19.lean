-- Prove2me | solution 1 for P2M_GlobalTheory_HostModel_zeta_M__pow_div_A_73e6bee15f19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:19.218454+00:00
-- url     : https://prove2.me/submissions/c28a96bf-310c-44e9-b396-0c8bbbfbd67e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Theorems.Thm_GlobalTheory_HostModel_zeta_pow_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.HostModel
theorem _root_.solution (l : Level H) : zeta l.M' ^ (l.M' / l.A) = zeta l.A :=
  zeta_pow_div (LevelExist.M'_pos l) (Nat.dvd_lcm_right l.M l.A)
end GlobalTheory.HostModel
