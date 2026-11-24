-- Prove2me | solution 1 for PIW.AdelClassFin.DictGen.mulVec_mem_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:54:48.765717+00:00
-- url     : https://prove2.me/submissions/5ed1c894-0541-4ab1-b884-56ea22586675

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
import Theorems.Thm_PIW_AdelClassFin_DictGen_lf_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictGen
variable (I : AutInst)
namespace PIW.AdelClassFin.DictGen
theorem _root_.solution {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (h : I.L ≤ lamM I M) :
    ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf := by
  intro y hy
  rw [lf_eq] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    exact (show M *ᵥ iv I l ∈ I.Lf from h hl)
  | zero =>
    rw [Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  | add a b _ _ ha hb =>
    rw [Matrix.mulVec_add]
    exact I.Lf.add_mem ha hb
  | smul s a _ ha =>
    have e : M *ᵥ (s • a) = s • (M *ᵥ a) := by
      show M *ᵥ ((s : (I.E ⊗[I.F] Af I.F)) • a) = (s : (I.E ⊗[I.F] Af I.F)) • (M *ᵥ a)
      exact Matrix.mulVec_smul M _ a
    rw [e]
    exact I.Lf.smul_mem s ha
end PIW.AdelClassFin.DictGen
