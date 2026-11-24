-- Prove2me | solution 1 for QPK.Bru.gf_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:00:04.694687+00:00
-- url     : https://prove2.me/submissions/98376b2b-64da-4db0-9002-ebfb1267c8eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_BruhatDecomposition

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
    gf μ K n (t * x) = gf μ K n x := by
  have hm : MeasurableSet ((fun s => s * x) ⁻¹' K n) :=
    (hK n).measurableSet.preimage (measurable_mul_const x)
  show μ ((fun s => s * (t * x)) ⁻¹' K n) = μ ((fun s => s * x) ⁻¹' K n)
  calc μ ((fun s => s * (t * x)) ⁻¹' K n)
      = μ.map (fun s => s * t) ((fun s => s * x) ⁻¹' K n) := by
        rw [Measure.map_apply (measurable_mul_const t) hm]
        congr 1
        ext s
        simp [mul_assoc]
    _ = μ ((fun s => s * x) ⁻¹' K n) := by rw [hr t ht]
end QPK.Bru
