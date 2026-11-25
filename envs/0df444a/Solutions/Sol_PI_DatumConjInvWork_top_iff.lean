-- Prove2me | solution 1 for PI.DatumConjInvWork.top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:06.482489+00:00
-- url     : https://prove2.me/submissions/6a927e0d-baaf-4d26-8461-a5d13b899365

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumConjInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugationInvariance_SecondRowsBlockDiagMul
import Theorems.Thm_PI_DatumConjInvWork_conj_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumConjInvWork
variable {F : Type} [Field F] {a t : ℕ}
namespace PI.DatumConjInvWork
theorem _root_.solution (O : Subring F) (ϖ : F) (k : GL (Fin a) F) (hk : k ∈ Formalism.DoubleCosetMeasures.GLint O a)
    (X : Matrix (Fin a) (Fin a) F) :
    (∃ g : Formalism.DoubleCosetMeasures.congSub O ϖ a, ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) =
        ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * X * (k : Matrix (Fin a) (Fin a) F)) ↔
      (∃ g : Formalism.DoubleCosetMeasures.congSub O ϖ a, ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = X) := by
  constructor
  · rintro ⟨g, hg⟩
    have hm := conj_mem O ϖ k⁻¹ ((Formalism.DoubleCosetMeasures.GLint O a).inv_mem hk) (g : GL (Fin a) F) g.2
    refine ⟨⟨_, hm⟩, ?_⟩
    simp only [inv_inv, Units.val_mul, hg]
    simp [Matrix.mul_assoc]
  · rintro ⟨g, hg⟩
    have hm := conj_mem O ϖ k hk (g : GL (Fin a) F) g.2
    refine ⟨⟨_, hm⟩, ?_⟩
    simp [hg, Matrix.mul_assoc]
end PI.DatumConjInvWork
