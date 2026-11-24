-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_chartMonomial_mem_primeCompl_232337c8b957
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:12.539535+00:00
-- url     : https://prove2.me/submissions/787edd21-f0ff-4833-a639-0ba9d44ee84c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution {W : Ideal (MvPolynomial (Coord D.extSizes) ℤ)} [W.IsPrime]
    {c : (k : ι) → Fin (n k + 1)} (hW : ∀ k, (X (D.oldCoord ⟨k, c k⟩) : MvPolynomial _ ℤ) ∉ W)
    (e : ι → ℕ) : D.liftOld (chartMonomial c e) ∈ W.primeCompl := by
  rw [chartMonomial, map_prod]
  refine Submonoid.prod_mem _ fun k _ ↦ ?_
  rw [map_pow, AddBlockData.liftOld, rename_X]
  exact Submonoid.pow_mem _ ((Ideal.mem_primeCompl_iff).mpr (hW k)) _
end GroundTheory.Heights₂.Heights.SectionCycle
