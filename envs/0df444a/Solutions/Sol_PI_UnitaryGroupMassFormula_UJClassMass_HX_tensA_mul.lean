-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.HX.tensA_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:44.414586+00:00
-- url     : https://prove2.me/submissions/b21813d5-2917-4d1b-80a9-ea3fb2a21b20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_TcoordBound

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
theorem _root_.solution (t : HeightOneSpectrum (𝓞 F)) {a b : E ⊗[F] t.adicCompletion F}
    (ha : a ∈ tensA (E := E) t) (hb : b ∈ tensA (E := E) t) : a * b ∈ tensA (E := E) t := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha' =>
    induction hb using AddSubgroup.closure_induction with
    | mem b hb' =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ha'
      obtain ⟨x', hx', y', hy', rfl⟩ := hb'
      apply AddSubgroup.subset_closure
      exact ⟨x * x', (PI.UnitaryApproxDefs.intOE E).mul_mem hx hx', y * y',
        mul_mem hy hy', by rw [Algebra.TensorProduct.tmul_mul_tmul]⟩
    | zero => rw [mul_zero]; exact (tensA (E := E) t).zero_mem
    | add b c _ _ hb hc => rw [mul_add]; exact (tensA (E := E) t).add_mem hb hc
    | neg b _ hb => rw [mul_neg]; exact (tensA (E := E) t).neg_mem hb
  | zero => rw [zero_mul]; exact (tensA (E := E) t).zero_mem
  | add a c _ _ ha hc => rw [add_mul]; exact (tensA (E := E) t).add_mem ha hc
  | neg a _ ha => rw [neg_mul]; exact (tensA (E := E) t).neg_mem ha
end PI.UnitaryGroupMassFormula.UJClassMass.HX
