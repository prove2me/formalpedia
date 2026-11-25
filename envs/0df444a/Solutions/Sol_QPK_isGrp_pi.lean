-- Prove2me | solution 1 for QPK.isGrp_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:48.737505+00:00
-- url     : https://prove2.me/submissions/15d561e8-20ec-4e1d-a850-182521fcb515

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_LintegralFintypeProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_WeilQuotientGlobalAssumptions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)]
namespace QPK
theorem _root_.solution (K : ∀ v, Set (G v)) (hK : ∀ v, IsGrp (K v)) : IsGrp (Set.pi univ K) := by
  refine ⟨fun v _ => (hK v).1, fun a ha b hb v _ => (hK v).2.1 _ (ha v trivial) _ (hb v trivial),
    fun a ha v _ => (hK v).2.2 _ (ha v trivial)⟩
end QPK
