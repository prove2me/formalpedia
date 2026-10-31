-- Prove2me | solution 1 for RobustPrefLearn.MTP.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:06:12.12387+00:00
-- url     : https://prove2.me/submissions/5af41093-8c6e-4768-8497-6f0f1cdfd2f1

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp
import Theorems.Thm_RobustPrefLearn_MTP_theorem_1
import Theorems.Thm_RobustPrefLearn_MTP_theorem_6
import Theorems.Thm_RobustPrefLearn_MTP_theorem_7

open scoped ENNReal Topology

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ β : ℝ → ℝ, (∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 < β δ) ∧ ∀ S1 : DS K,
      IsAccurate p (fun δ => mtp p S1 (β δ)) ∧
      ∀ fam : ℝ → Policy K, IsAccurate p fam →
        worstRate p (fun δ => mtp p S1 (β δ)) ≤ worstRate p fam := by
  obtain ⟨C1, hC1⟩ := theorem_7 K hK
  -- the threshold `β(δ) = |C₁| + log(1/δ)`
  have hlog : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 < Real.log (1 / δ) := by
    intro δ hδ
    apply Real.log_pos
    rw [lt_one_div (by norm_num) hδ.1]
    simpa using hδ.2
  have hβ : ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
      0 < |C1| + Real.log (1 / δ) ∧ |C1| + Real.log (1 / δ) ≤ |C1| + Real.log (1 / δ) :=
    fun δ hδ => ⟨by have := hlog δ hδ; positivity, le_rfl⟩
  refine ⟨fun δ => |C1| + Real.log (1 / δ), fun δ hδ => (hβ δ hδ).1, fun S1 => ?_⟩
  -- upper bound: every rate of MTP is at most `1/I^OA_*`
  have hup : worstRate p (fun δ => mtp p S1 (|C1| + Real.log (1 / δ))) ≤ (IOA (K := K) p)⁻¹ := by
    unfold worstRate rate
    refine iSup₂_le fun f hf => ?_
    exact (theorem_6 K hK p hp0 hp1 |C1| (fun δ => |C1| + Real.log (1 / δ)) hβ S1 f hf).2
  refine ⟨fun δ hδ => hC1 p hp0 hp1 S1 δ hδ _ (by linarith [le_abs_self C1]), ?_⟩
  intro fam hfam
  refine hup.trans ?_
  -- lower bound: `1/I^OA_* = sup_f 1/I_*(f) ≤ sup_f liminf ≤ sup_f limsup`
  have h1 := (theorem_1 K hK p hp0 hp1).2 fam hfam
  unfold IOA worstRate rate
  rw [ENNReal.inv_iInf]
  refine iSup_le fun f => ?_
  rw [ENNReal.inv_iInf]
  refine iSup_le fun hf => ?_
  refine le_trans ?_ (le_iSup₂ (f := fun f (_ : f ∈ (Mp p : Set (Pref K))) =>
    Filter.limsup (fun δ : ℝ => expTau (fam δ) f / ENNReal.ofReal (Real.log (1 / δ)))
      (𝓝[>] 0)) f hf)
  exact (h1 f hf).trans Filter.liminf_le_limsup
