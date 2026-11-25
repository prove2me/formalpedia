-- Prove2me | solution 1 for PI.VolStabSW.cos_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:16:38.724472+00:00
-- url     : https://prove2.me/submissions/017a3bb3-141c-4f45-860e-4c0f4d9ce7cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HenselCountHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHF
import Theorems.Thm_PI_VolStabSW_cos_inter_eq
import Theorems.Thm_PI_VolStabSW_hensel_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
namespace PI.VolStabSW
theorem _root_.solution (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (T : X) (hyT : G y - T ∈ H 0) (n : ℕ) :
    μ ({x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n}) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  have hset : {x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n} =
      (fun x => -y + x) ⁻¹' hlev (Λ 0) (H n) G y T := cos_inter_eq (Λ 0) (H n) G y T
  rw [hset, measure_preimage_add]
  exact hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T
    (by simpa [neg_sub] using (H 0).neg_mem hyT) n
end PI.VolStabSW
