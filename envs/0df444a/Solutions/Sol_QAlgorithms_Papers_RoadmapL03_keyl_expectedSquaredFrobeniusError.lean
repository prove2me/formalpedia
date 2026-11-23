-- Prove2me | solution 1 for QAlgorithms.Papers.RoadmapL03.keyl_expectedSquaredFrobeniusError
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T11:41:17.341613+00:00
-- url     : https://prove2.me/submissions/57a5163a-652d-4a78-879a-62d03c67f1d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_RoadmapL03_keyl_born_realization
import Theorems.Thm_QAlgorithms_Papers_RoadmapL03_keyl_squaredRisk_bound
set_option autoImplicit false

noncomputable section

open QAlgorithms in
theorem solution
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    ∃ measurement : Measurements.OperatorPOVM (Fin n → Fin d)
        (Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ),
      ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (density : IsDensityMatrix rho),
        Measurements.bornLaw measurement (piKron n rho)
            (Tomography.tensorDensity rho density n) =
          Tomography.keylJointLaw hd hn rho density ∧
        Tomography.keylSquaredRisk hd hn rho density ≤
          ENNReal.ofReal (((4 : ℝ) * d - 3) / n) := by
  obtain ⟨M, hM⟩ := QAlgorithms.Papers.RoadmapL03.keyl_born_realization d n hd hn
  exact ⟨M, fun rho density => ⟨hM rho density,
    QAlgorithms.Papers.RoadmapL03.keyl_squaredRisk_bound d n hd hn rho density⟩⟩
