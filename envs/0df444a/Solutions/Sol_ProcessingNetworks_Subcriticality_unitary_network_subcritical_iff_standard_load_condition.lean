-- Prove2me | solution 1 for ProcessingNetworks.Subcriticality.unitary_network_subcritical_iff_standard_load_condition
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:05:48.872331+00:00
-- url     : https://prove2.me/submissions/3d179479-92e7-4148-9f9d-5a3fd913a24a

import Mathlib
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem

open ProcessingNetworks.Subcriticality in
theorem solution : ¬ (∀ {I K : ℕ} (P : Matrix (Fin I) (Fin I) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (P ^ n) i j) Filter.atTop (nhds 0))
    (m : Fin I → ℝ) (hm : ∀ i, 0 < m i)
    (A : Matrix (Fin K) (Fin I) ℝ) (b : Fin K → ℝ) (hb : ∀ k, 0 < b k)
    (lam alpha : Fin I → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (halpha : (1 - P.transpose).mulVec alpha = lam),
    lam ∈ SubcriticalRegion (SPNPlanningData.ofUnitary P m hm A b hb) ↔
      ∀ k, (A.mulVec ((Matrix.diagonal m).mulVec alpha)) k < b k) := by
  intro h
  have h0 := (h (I := 0) (K := 0) 0 (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (fun _ => 0) (fun i => i.elim0) 0 (fun _ => 0) (fun k => k.elim0) (fun _ => 0) (fun _ => 0)
    (fun i => i.elim0) (funext fun i => i.elim0)).mpr (fun k => k.elim0)
  obtain ⟨-, γ, ⟨-, hlow⟩, -⟩ := h0
  have hmem : γ - 1 ∈ {γ : ℝ | ∃ x, SPPFeasible
      (SPNPlanningData.ofUnitary (0 : Matrix (Fin 0) (Fin 0) ℝ) (fun _ => 0) (fun i => i.elim0)
        (0 : Matrix (Fin 0) (Fin 0) ℝ) (fun _ => 0) (fun k => k.elim0)) γ (fun _ => 0) x} :=
    ⟨fun _ => 0, funext fun i => i.elim0, fun j => j.elim0, fun k => k.elim0⟩
  have := hlow hmem
  linarith


