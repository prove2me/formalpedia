-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneNull_proof_f57f8fc92d55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:17.32647+00:00
-- url     : https://prove2.me/submissions/99b57565-c84d-4674-927c-98edebe5e2ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeProjHyperplaneNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_coneFirstForm_bc87d2d7c017


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
namespace GroundTheory.Heights₂.Heights
namespace ConeProjHyperplaneNull
theorem _root_.solution (hNull : NullSmaller.Statement)
    (hDim : ConeProjHyperplaneDim.Statement) : ConeProjHyperplaneNull.Statement := by
  intro n e P Ψ hP hΨ
  set J : Ideal (MvPolynomial (Fin n) ℂ) := complexFibreIdeal P ⊔ Ideal.span {coneFirstForm Ψ} with hJ

  have hlt : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (hDim n e P Ψ hP hΨ).trans_lt (by exact_mod_cast Nat.lt_succ_self e)

  refine measure_mono_null (fun z hz => ?_) (hNull n (e + 1) J hlt)
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hq
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  rw [map_add, map_mul, hz.1 a ha, eval_coneFirstForm, hz.2, mul_zero, add_zero]
end ConeProjHyperplaneNull
end GroundTheory.Heights₂.Heights
