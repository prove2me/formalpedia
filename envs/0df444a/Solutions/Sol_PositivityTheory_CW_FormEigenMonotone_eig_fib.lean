-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.eig_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:25:13.859147+00:00
-- url     : https://prove2.me/submissions/b16a65e5-9ce8-4116-aa17-f973b2e9408b

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FormEigenMonotone
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
namespace PositivityTheory.CW.FormEigenMonotone
theorem _root_.solution (hb : ∀ i, Eig ε E (μ i) (b i)) (ν : ℝ) (F : Finset ι) (hF : ∀ j ∈ F, μ j = ν)
    (a : ι → ℂ) : Eig ε E ν (∑ j ∈ F, a j • b j) := by
  unfold Eig
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_smul, hb j, hF j hj, smul_comm]
end PositivityTheory.CW.FormEigenMonotone
