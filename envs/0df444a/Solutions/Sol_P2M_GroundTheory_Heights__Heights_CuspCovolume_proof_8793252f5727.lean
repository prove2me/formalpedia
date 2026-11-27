-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspCovolume_proof_8793252f5727
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:55:10.697434+00:00
-- url     : https://prove2.me/submissions/cdd561d8-5057-45c4-a7dc-92551c03ef66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspCovolume_periodGram_castAdd_5c2e72ba1c67
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspCovolume_inv_diag_le_of_ge_d220717e0ddd

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CuspCovolume
theorem _root_.solution (hImPos : ChartPeriodImPos.Statement)
    (hPG : PeriodGramPosDef.Statement) (hCB : CuspCoordinateBound.Statement)
    (hPB : PivotBounds.Statement) (hGP : GramPivotProduct.Statement)
    (hPP : PivotProductBound.Statement) (hLC : PeriodLatticeCovolume.Statement)
    (hLead : LeadingCovolume.Statement) : CuspCovolume.Statement := by
  intro D T
  obtain ⟨ε, hε, hεb⟩ := hCB D T
  set κ : ℝ := min 1 ε ^ (D.g + D.g) * (max 1 (1 / D.c))⁻¹ ^ T.r with hκ
  have hκpos : 0 < κ := by
    have h1 : 0 < min 1 ε := lt_min one_pos hε
    have h2 : 0 < max 1 (1 / D.c) := lt_max_of_lt_left one_pos
    positivity
  refine ⟨Real.sqrt κ, Real.sqrt_pos.mpr hκpos, ?_⟩
  intro p hpK hpU ℓ hℓ k v hv hind
  set τ := D.period p.1 ℓ with hτ
  obtain ⟨hYpos, hYc⟩ := hImPos D p.1 hpU ℓ hℓ
  have hS : (periodGram τ).PosDef := (hPG D.g τ hYpos).1
  obtain ⟨N, -, hN, hcov⟩ := hLC D.g τ k v hv hind
  obtain ⟨P, hPd, hPdet⟩ := hGP (D.g + D.g) (periodGram τ) hS k N hN
  have hlow : ∀ i, i < T.r → pivot (periodGram τ) i ≤ 1 / D.c := by
    intro i hi
    have hig : i < D.g := lt_of_lt_of_le hi T.r_le
    have hb := (hPB (D.g + D.g) (periodGram τ) hS (Fin.castAdd D.g ⟨i, hig⟩)).1
    simp only [Fin.val_castAdd] at hb
    rw [CuspCovolume.periodGram_castAdd] at hb
    exact hb.trans (CuspCovolume.inv_diag_le_of_ge hYpos D.c_pos hYc _)
  have hhigh : ∀ i, T.r ≤ i → i < D.g + D.g → ε ≤ pivot (periodGram τ) i := by
    intro i hri hid
    exact (hPB (D.g + D.g) (periodGram τ) hS ⟨i, hid⟩).2 ε hε fun y =>
      hεb p hpK hpU ℓ hℓ y ⟨i, hid⟩ hri
  have hprod := hPP (D.g + D.g) T.r (periodGram τ) hS (T.r_le.trans (Nat.le_add_right _ _))
    (1 / D.c) ε hε hlow hhigh P hPd
  rw [hcov, hLead D.g τ T.r T.r_le, ← Real.sqrt_mul hκpos.le]
  exact Real.sqrt_le_sqrt (hprod.trans hPdet)
end CuspCovolume
end GroundTheory.Heights₂.Heights
