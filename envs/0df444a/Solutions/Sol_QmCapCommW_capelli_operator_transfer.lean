-- Prove2me | solution 1 for QmCapCommW.capelli_operator_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:01.502537+00:00
-- url     : https://prove2.me/submissions/2fc81e00-a6f8-4bcd-b243-cf4bb8b32561

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer
import Theorems.Thm_QmCapCommW_qdet_rep
import Theorems.Thm_QmCapCommW_EE_gl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open QmCapCommW
namespace QmCapCommW
theorem _root_.solution : CapTransfer := by
  unfold CapTransfer
  intro hC hQ hP hG
  unfold CapCommute
  unfold QdetCommute at hQ
  intro E _ _ k r i D f hD hf g hg u v
  have hmem : (fun q : Pt k r i D => f q.1) ∈ SS k r i D E :=
    smooth_congr hD (fun g' hg' => (extension_by_zero_apply (φ := fun q : Pt k r i D => f q.1) hg').symm) hf
  let x : SS k r i D E := ⟨fun q => f q.1, hmem⟩
  have hx : Rep f x.1 := fun _ _ => rfl
  have h1 := qdet_rep hC hP hD u (qdet_rep hC hP hD v hx)
  have h2 := qdet_rep hC hP hD v (qdet_rep hC hP hD u hx)
  have hcomm := hQ (Module.End ℂ (SS k r i D E)) (mdim k r i) (EE hP hD) (EE_gl hC hP hG hD) u v
  rw [h1 g hg, h2 g hg]
  have := congrArg (fun T => (T x).1 ⟨g, hg⟩) hcomm
  simpa only [Module.End.mul_apply] using this
end QmCapCommW
