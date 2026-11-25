-- Prove2me | solution 1 for QPK.Bru.Eset_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:18.07717+00:00
-- url     : https://prove2.me/submissions/788d68ee-fc7a-462f-9208-51dbf3412ec5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_BruhatDecomposition
import Theorems.Thm_QPK_Bru_gf_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
open QPK.Bru
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace QPK.Bru
theorem _root_.solution (μ : Measure G) (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) (S : Set G)
    (hr : ∀ s ∈ S, μ.map (fun x => x * s) = μ) (n : ℕ) {t : G} (ht : t ∈ S) (x : G) :
    t * x ∈ Eset μ K n ↔ x ∈ Eset μ K n := by
  have h : ∀ k, gf μ K k (t * x) = gf μ K k x := fun k => gf_inv μ K hK S hr k ht x
  simp only [Eset, Set.mem_setOf_eq, h]
end QPK.Bru
