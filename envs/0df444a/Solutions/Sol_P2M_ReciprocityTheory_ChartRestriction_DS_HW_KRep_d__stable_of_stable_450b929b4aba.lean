-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_d__stable_of_stable_450b929b4aba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:40.086172+00:00
-- url     : https://prove2.me/submissions/d1224558-9eb7-4f91-b21b-5ccc800da6bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_inK_of_skew_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_single_mul_Jm_comm


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
namespace KRep
theorem _root_.solution {ε : Fin n → Bool} (R : KRep ε)
    (W : Submodule ℂ R.V) (hW : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W) :
    ∀ a b, ε a = ε b → ∀ v ∈ W, R.dτ (Matrix.single a b 1) v ∈ W := by
  have hK : ∀ X, inK ε X → ∀ v ∈ W, R.dτ X v ∈ W := by
    intro X hX v hv
    obtain ⟨γ, hγ⟩ := exists_curve ε hX
    have hd := R.hasDeriv X hX γ hγ
    let L : (R.V →L[ℂ] R.V) →L[ℝ] R.V := (ContinuousLinearMap.apply ℂ R.V v).restrictScalars ℝ
    have hdv : HasDerivAt (fun t => R.op (γ t) v) (R.dτ X v) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hd
    have hclosed : IsClosed (W : Set R.V) := W.closed_of_finiteDimensional
    refine hclosed.mem_of_tendsto hdv.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
    exact W.smul_of_tower_mem _ (W.sub_mem (hW _ v hv) (hW _ v hv))
  intro a b hab v hv
  have hX1 : inK ε (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    apply inK_of_skew_comm
    · simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
    · rw [sub_mul, mul_sub, single_mul_Jm_comm hab, single_mul_Jm_comm hab.symm]
  have hX2 : inK ε (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1)) := by
    apply inK_of_skew_comm
    · simp [Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm,
        Matrix.single_neg]
    · rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, single_mul_Jm_comm hab,
        single_mul_Jm_comm hab.symm]
  have hI : -Complex.I / 2 * Complex.I = 1 / 2 := by
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
    norm_num
  have hdec : Matrix.single a b (1 : ℂ) =
      (1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) +
        (-Complex.I / 2) • (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1)) := by
    rw [smul_smul, hI]
    module
  rw [hdec, map_add, map_smul, map_smul, _root_.add_apply,
    _root_.smul_apply, _root_.smul_apply]
  exact W.add_mem (W.smul_mem _ (hK _ hX1 v hv)) (W.smul_mem _ (hK _ hX2 v hv))
end KRep
end ReciprocityTheory.ChartRestriction.DS.HW
