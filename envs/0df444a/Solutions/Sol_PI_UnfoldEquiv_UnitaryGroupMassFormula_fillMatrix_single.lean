-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.fillMatrix_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:49.240813+00:00
-- url     : https://prove2.me/submissions/173a1fe3-9a5f-4a78-984a-43a77f0e7b09

import Definitions.Def_Formalism_PeriodIntegrals_UnfoldEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
theorem _root_.solution {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' (c + 1) n c → k)
    (l : Fin (n + c)) (s : Fin (n' + (c + 1))) :
    xx1 xj t (Pi.single s 1) l = if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩ else base xj l s := by
  simp only [xx1, Matrix.toLin'_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
    Matrix.of_apply, base]
end PI.UnfoldEquiv.UnitaryGroupMassFormula
