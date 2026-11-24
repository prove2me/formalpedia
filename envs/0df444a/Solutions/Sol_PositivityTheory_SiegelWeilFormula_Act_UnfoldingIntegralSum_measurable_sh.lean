-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum.measurable_sh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:20.766204+00:00
-- url     : https://prove2.me/submissions/ae4be033-607d-4e70-a82c-3dd310de26b4

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_IsFirstChernFamily
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_MeasurableSh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
variable {V A : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
namespace PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
theorem _root_.solution {Λ : (V × V) ≃ₜ+ (V × V)} {Q : V × V → A} (hQ : Measurable Q) {Z : V → V → A}
    (hZ : Measurable (Function.uncurry Z)) (c : V × A) : Measurable (sh Λ Q Z c) := by
  show Measurable fun p : V × (V × A) => ((c.1 + (Λ (p.2.1, p.1)).2,
    c.2 + (p.2.2 + (Q (p.2.1, p.1) + Z c.1 (Λ (p.2.1, p.1)).1))) : V × A)
  have hΛm : Measurable fun p : V × (V × A) => Λ (p.2.1, p.1) :=
    Λ.continuous.measurable.comp (measurable_snd.fst.prodMk measurable_fst)
  exact (hΛm.snd.const_add _).prodMk ((measurable_snd.snd.add
    ((hQ.comp (measurable_snd.fst.prodMk measurable_fst)).add
      (hZ.comp (measurable_const.prodMk hΛm.fst)))).const_add _)
end PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
