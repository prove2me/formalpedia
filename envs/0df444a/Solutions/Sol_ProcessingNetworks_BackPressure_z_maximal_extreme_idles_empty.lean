-- Prove2me | solution 1 for ProcessingNetworks.BackPressure.z_maximal_extreme_idles_empty
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:17:11.775153+00:00
-- url     : https://prove2.me/submissions/f30d757a-a375-4d9f-a216-738104301ebc

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope

namespace ProcessingNetworks.BackPressure.ZMaxCE

open ProcessingNetworks.BackPressure

noncomputable def dat : SPNPlanningData 1 1 1 :=
  { B := 1, Γ := 0, m := fun _ => 1, hm := fun _ => one_pos, A := 0, b := fun _ => 1,
    hb := fun _ => one_pos }

theorem R_eq : dat.R = 1 := by
  ext i j; fin_cases i; fin_cases j
  simp [SPNPlanningData.R, dat]

theorem h91 : SatisfiesAssumption91 dat := by
  intro j
  refine ⟨0, ?_, fun i _ => Subsingleton.elim i 0⟩
  rw [R_eq]; fin_cases j; exact one_pos

theorem p_eq (β : Fin 1 → ℝ) : p dat β (fun _ => 1) = β 0 := by
  simp [p, R_eq, dotProduct]

end ProcessingNetworks.BackPressure.ZMaxCE

open ProcessingNetworks.BackPressure in
theorem solution : ¬ (∀ {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i),
    ∃ β ∈ ExtremeAllocations dat, IsZMaximal dat β z ∧
      ∀ j : Fin J, z (servesBuffer h91 j) = 0 → β j = 0) := by
  intro h
  obtain ⟨β, -, ⟨hβ, hmax⟩, -⟩ := h ZMaxCE.dat ZMaxCE.h91 (fun _ => 1) (fun _ => zero_le_one)
  have hα : (fun _ => β 0 + 1 : Fin 1 → ℝ) ∈ AllocationPolytope ZMaxCE.dat := by
    refine ⟨fun j => ?_, fun k => ?_⟩
    · fin_cases j; simp; linarith [hβ.1 0]
    · simp [ZMaxCE.dat]
  have := hmax _ hα
  rw [ZMaxCE.p_eq, ZMaxCE.p_eq] at this
  linarith


