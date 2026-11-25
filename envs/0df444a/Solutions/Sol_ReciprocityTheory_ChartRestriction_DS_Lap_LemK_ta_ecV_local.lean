-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.ta_ecV_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:23.373381+00:00
-- url     : https://prove2.me/submissions/52994feb-e4bd-4476-b477-73dcbefd3064

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_inG_cpart1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_inG_cpart2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_cpart_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_rdV_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {W : Set (Matrix (Fin n) (Fin n) ℂ)} {m g : Matrix (Fin n) (Fin n) ℂ}
    (hW : IsOpen W) (hg : g ∈ W) (hgu : inUJ ε g)
    (hF : DifferentiableAt ℂ F (g⁻¹ * m)) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ h ∈ W, inUJ ε h → f h = F (h⁻¹ * m)) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε Z f g = Lhol (-Z) F (g⁻¹ * m) := by
  unfold EcV Lhol
  rw [ta_rdV_local ε hW hg hgu (ta_inG_cpart1 ε Z) hF hf, ta_rdV_local ε hW hg hgu (ta_inG_cpart2 ε Z) hF hf,
    ← map_smul, ← map_add]
  congr 1
  calc -cpart1 ε Z * (g⁻¹ * m) + Complex.I • (-cpart2 ε Z * (g⁻¹ * m))
      = -(cpart1 ε Z + Complex.I • cpart2 ε Z) * (g⁻¹ * m) := by
        simp only [neg_mul, smul_neg, add_mul, smul_mul_assoc, neg_add]
    _ = -Z * (g⁻¹ * m) := by rw [ta_cpart_sum ε Z]
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
