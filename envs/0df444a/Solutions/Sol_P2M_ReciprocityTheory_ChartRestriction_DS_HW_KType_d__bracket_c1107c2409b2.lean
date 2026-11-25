-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__bracket_c1107c2409b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:32.32498+00:00
-- url     : https://prove2.me/submissions/43d06f52-d33f-4cca-8687-aa8897ba8703

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_iff__24a5ac304dfc
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_star_d__89a207fa12af
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_conj_d__50b083afe397
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_d__conj_hasDerivAt_41ef9a6a2b9d
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_curve


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
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
namespace KType
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    T.dτ X * T.dτ Y - T.dτ Y * T.dτ X = T.dτ (X * Y - Y * X) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := T.dτ X
  set B := T.dτ Y
  have hA := KType.star_dτ T hX
  have hXs := ((inK_iff' ε X).1 hX).1
  have key : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • A) * B * NormedSpace.exp ((s : ℂ) • (-A)) =
      T.dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) := by
    intro s
    have h := KType.conj_dτ T (γ s) hY
    rw [KType.op_curve T hX γ hγ s, hγ s, NormedSpace.star_exp, star_smul, hA,
      Complex.star_def, Complex.conj_ofReal] at h
    rw [h]
    congr 2
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs,
      Complex.star_def, Complex.conj_ofReal]
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ)).mul_const B).mul
      (hasDerivAt_exp_smul_const (-A) ((0 : ℝ) : ℂ)))
  have h2 := dτ_conj_hasDerivAt T X Y
  have h1' := h1.congr_of_eventuallyEq
    (f₁ := fun s : ℝ => T.dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))))
    (Filter.Eventually.of_forall fun s => (key s).symm)
  have := h1'.unique h2
  rw [← this]
  simp [sub_eq_add_neg]
end KType
end ReciprocityTheory.ChartRestriction.DS.HW
