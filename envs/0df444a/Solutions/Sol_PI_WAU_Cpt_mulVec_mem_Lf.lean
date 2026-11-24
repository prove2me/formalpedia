-- Prove2me | solution 1 for PI.WAU.Cpt.mulVec_mem_Lf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:40:13.953888+00:00
-- url     : https://prove2.me/submissions/402486d1-f686-439e-81ea-5f416aba04f6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hM : ∀ l ∈ I.L, M *ᵥ inclV (F := I.F) l ∈ I.Lf) : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨⟨l, hl⟩, rfl⟩ := hx; exact hM l hl
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, Matrix.mulVec_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ a hx
end PI.WAU.Cpt
