-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__stable_of_stable_ffd49588c4b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:16:54.130855+00:00
-- url     : https://prove2.me/submissions/fecdd9c8-1ef6-4fa6-b78c-25384dd93705

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_single_mul_Jm_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_inK_of_skew_comm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
private theorem single_conjTranspose_lemma_2 {a b : Fin n} :
    (Matrix.single a b (1 : ℂ))ᴴ = Matrix.single b a 1 := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]
end ReciprocityTheory.ChartRestriction.DS.HW
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
namespace KType
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (W : Submodule ℂ T.V) (hW : ∀ k : KG ε, ∀ v ∈ W, T.op k v ∈ W) :
    ∀ a b, ε a = ε b → ∀ v ∈ W, T.dτ (Matrix.single a b 1) v ∈ W := by
  have key : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → X * Jm ε = Jm ε * X →
      ∀ v ∈ W, T.dτ X v ∈ W := by
    intro X h1 h2 v hv
    have hc : Commute (Jm ε) X := h2.symm
    have hcomm : ∀ s : ℂ, Commute (Jm ε) (NormedSpace.exp (s • X)) := fun s =>
      (hc.smul_right s).exp_right
    have hinv : ∀ s : ℂ, NormedSpace.exp (s • X) * NormedSpace.exp (-(s • X)) = 1 ∧
        NormedSpace.exp (-(s • X)) * NormedSpace.exp (s • X) = 1 := fun s =>
      ⟨by rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (s • X)).neg_right), add_neg_cancel,
          NormedSpace.exp_zero],
       by rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (s • X)).neg_left), neg_add_cancel,
          NormedSpace.exp_zero]⟩
    have hstar : ∀ t : ℝ,
        (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp (-((t : ℂ) • X)) := by
      intro t
      have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
      rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, h1, ht, smul_neg]
    let γ : ℝ → KG ε := fun t =>
      ⟨⟨⟨NormedSpace.exp ((t : ℂ) • X), NormedSpace.exp (-((t : ℂ) • X)), (hinv t).1,
          (hinv t).2⟩, by
        show inUJ ε (NormedSpace.exp ((t : ℂ) • X))
        unfold inUJ
        rw [hstar t, mul_assoc, (hcomm t).eq, ← mul_assoc, (hinv t).2, one_mul]⟩, by
        show NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          NormedSpace.exp ((t : ℂ) • X) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • X)
        refine ⟨?_, (hcomm t).eq.symm⟩
        rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hstar t]
        exact (hinv t).1⟩
    have hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
    have hd := T.hasDeriv X (inK_of_skew_comm h1 h2) γ hγ
    have hs := ((ContinuousLinearMap.apply ℂ T.V v).continuous.tendsto _).comp
      (hasDerivAt_iff_tendsto_slope.mp hd)
    refine (Submodule.closed_of_finiteDimensional W).mem_of_tendsto hs
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, slope_def_module,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, SetLike.mem_coe]
    exact W.smul_of_tower_mem _ (W.sub_mem (hW _ v hv) (hW _ v hv))
  intro a b hab v hv
  generalize hY : Matrix.single a b (1 : ℂ) = Y at hv ⊢
  have hYc : Y * Jm ε = Jm ε * Y := by rw [← hY]; exact single_mul_Jm_comm hab 1
  have hYH : Yᴴ = Matrix.single b a 1 := by rw [← hY]; exact single_conjTranspose_lemma_2
  have hYHc : Yᴴ * Jm ε = Jm ε * Yᴴ := by rw [hYH]; exact single_mul_Jm_comm hab.symm 1
  have hc : star ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := Complex.conj_ofReal _
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have h1 : (((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ))ᴴ = -(((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      hc, ← neg_sub Y Yᴴ, smul_neg]
  have h2 : (Complex.I • (Y + Yᴴ))ᴴ = -(Complex.I • (Y + Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      hI, neg_smul, add_comm]
  have h1J : (((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ)) * Jm ε = Jm ε * (((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ)) := by
    rw [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, hYc, hYHc]
  have h2J : (Complex.I • (Y + Yᴴ)) * Jm ε = Jm ε * (Complex.I • (Y + Yᴴ)) := by
    rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hYc, hYHc]
  have hdec : Y = ((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ) + (-(Complex.I / 2)) • (Complex.I • (Y + Yᴴ)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast
    linear_combination ((Y i j + Yᴴ i j) / 2) * Complex.I_sq
  rw [hdec, map_add, ContinuousLinearMap.add_apply,
    map_smul T.dτ (-(Complex.I / 2)) (Complex.I • (Y + Yᴴ)), ContinuousLinearMap.smul_apply]
  exact W.add_mem (key _ h1 h1J v hv) (W.smul_mem _ (key _ h2 h2J v hv))
end KType
end ReciprocityTheory.ChartRestriction.DS.HW
