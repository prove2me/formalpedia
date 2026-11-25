-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.HX.tensInt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:42.954613+00:00
-- url     : https://prove2.me/submissions/100f838e-5a62-4b95-a0af-d2ea18c613b8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_TcoordBound
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_HX_tensA_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
open PI.UnitaryGroupMassFormula.UJClassMass.HX
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassMass.HX
theorem _root_.solution (t : HeightOneSpectrum (𝓞 F)) {s : E ⊗[F] t.adicCompletion F}
    (hs : s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (t.adicCompletionIntegers F).toSubring) :
    s ∈ tensA (E := E) t := by
  unfold PI.UnitaryApproxDefs.tensInt at hs
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact AddSubgroup.subset_closure ⟨x, hx, 1, (t.adicCompletionIntegers F).one_mem, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, (PI.UnitaryApproxDefs.intOE E).one_mem, y, hy, rfl⟩
  | zero => exact (tensA (E := E) t).zero_mem
  | one => exact AddSubgroup.subset_closure ⟨1, (PI.UnitaryApproxDefs.intOE E).one_mem, 1,
      (t.adicCompletionIntegers F).one_mem, rfl⟩
  | add a b _ _ ha hb => exact (tensA (E := E) t).add_mem ha hb
  | neg a _ ha => exact (tensA (E := E) t).neg_mem ha
  | mul a b _ _ ha hb => exact tensA_mul t ha hb
end PI.UnitaryGroupMassFormula.UJClassMass.HX
