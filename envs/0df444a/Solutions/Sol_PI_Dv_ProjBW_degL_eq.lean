-- Prove2me | solution 1 for PI.Dv.ProjBW.degL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:54.5928+00:00
-- url     : https://prove2.me/submissions/3e270628-11bd-484b-bf04-21370a9edcf9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MajorantVanishing_MajAtZeroRight
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HN_plLat
import Theorems.Thm_Formalism_HN_satBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjBW
open NumberField Formalism.HN
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.Dv.ProjBW
theorem _root_.solution (A : Formalism.BasicNotions.HLat K) (hX : ∀ v, IsUnit (A.X v).det) (M : Submodule (𝓞 K) A.V) (hM : M.FG) :
    PI.Dv.degL A M = 2 * deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M / (Module.finrank ℚ K : ℝ) +
      (- Real.log 2 + logDisc K / (Module.finrank ℚ K : ℝ)) * (rkK M : ℝ) := by
  obtain ⟨hlat, hrk, -⟩ := plLat K A.V A.ι A.b A.X hX M hM
  have hr : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hsat := satBasic (𝓞 K) A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2))
    (Formalism.HermitianLatticesTheory.realize A.b A.X) M hlat
  have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize A.b A.X) M =
      deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M / ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ)) := by
    have h1 : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize A.b A.X) M) = Module.finrank ℚ K * rkK M := hrk
    unfold Formalism.HN.slope Formalism.F.slope
    rw [h1]
    push_cast
    rfl
  unfold PI.Dv.degL muDef
  by_cases h0 : rkK M = 0
  · have hb : M = ⊥ := (hsat.2.2.2.1 M le_rfl).1 (by rw [hrk, h0, mul_zero])
    have hd : deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M = 0 := by rw [hb]; exact hsat.2.2.2.2.1
    rw [hs, h0, hd]
    simp
  · have h0' : (rkK M : ℝ) ≠ 0 := by exact_mod_cast h0
    rw [hs]
    field_simp
    ring
end PI.Dv.ProjBW
