-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.evX_actU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:20:55.858635+00:00
-- url     : https://prove2.me/submissions/ffabb87a-61c0-4a92-a6a6-3ff53cf45418

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.KSplit
theorem _root_.solution (u : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) (v : Matrix (Fin m) (Fin n) ℂ) :
    evX (actU u P) v = evX P (u * v) := by
  have h : (aeval (R := ℂ) fun k : Fin m × Fin n × Bool =>
      if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1).comp (actU u) =
      aeval fun k : Fin m × Fin n × Bool => if k.2.2 then star ((u * v) k.1 k.2.1) else (u * v) k.1 k.2.1 := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, i, b⟩
    cases b
    · simp [actU, mul_apply]
    · simp [actU, mul_apply, star_sum]
  have e := congrArg (fun f : PX m n →ₐ[ℂ] ℂ => f P) h
  simp only [AlgHom.comp_apply, coe_aeval_eq_eval] at e
  exact e
end PositivityTheory.SiegelWeilFormula.KSplit
