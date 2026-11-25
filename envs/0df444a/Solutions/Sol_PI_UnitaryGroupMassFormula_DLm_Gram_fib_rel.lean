-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DLm.Gram.fib_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:36.865921+00:00
-- url     : https://prove2.me/submissions/d93ed4e5-b603-48d4-82a8-b9b14aecdf1b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFdGramCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm PI.UnitaryGroupMassFormula.DLm.Gram
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace PI.UnitaryGroupMassFormula.DLm.Gram
theorem _root_.solution (hE : FibEquivU) (hN : FiberIntegralUnipotentInvariant) (D : B.RealPlaceData k r Wp Wq) {μ0 μ0' : Measure (Mt k r)}
    (h0 : B.IsHaarOn (C2.N0set k r D.z) μ0) (h0' : B.IsHaarOn (C2.N0set k r D.z') μ0')
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) {a b : B.Mat k r} (hR : Rel D.z D.z' a b) :
    fibInt D μ0 μ0' F b = fibInt D μ0 μ0' F a := by
  obtain ⟨n, hn, m, hm, n', hn', m', hm', c, hc, c', hc', hb, ha⟩ := hR
  have hE' := hE
  unfold FibEquivU at hE'
  have hN' := hN
  unfold FiberIntegralUnipotentInvariant at hN'
  have e1 := hE' k r Wp Wq D μ0 μ0' h0 h0' F (n⁻¹ * a * n') c hc c' hc'
  have e2 := hE' k r Wp Wq D μ0 μ0' h0 h0' F (m⁻¹ * a * m') c hc c' hc'
  rw [hN' k r Wp Wq D μ0 μ0' h0 h0' F a n hn n' hn'] at e1
  rw [hN' k r Wp Wq D μ0 μ0' h0 h0' F a m hm m' hm', ha] at e2
  rw [hb, e1, ← e2]
end PI.UnitaryGroupMassFormula.DLm.Gram
