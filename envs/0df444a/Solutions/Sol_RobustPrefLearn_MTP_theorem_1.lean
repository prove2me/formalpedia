-- Prove2me | solution 1 for RobustPrefLearn.MTP.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:26:08.439232+00:00
-- url     : https://prove2.me/submissions/38dd83f1-6837-4c53-85b7-aae67a828187

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp
import Theorems.Thm_RobustPrefLearn_MTP_theorem_1_part_i

open scoped ENNReal Topology

namespace MTPAux1
open RobustPrefLearn.MTP

lemma kl_eq (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) :
    kl δ (1 - δ) = (1 - 2 * δ) * (Real.log (1 - δ) - Real.log δ) := by
  unfold kl
  have h1' : 0 < 1 - δ := by linarith
  rw [show 1 - (1 - δ) = δ by ring, Real.log_div h0.ne' h1'.ne', Real.log_div h1'.ne' h0.ne']
  ring

lemma kl_pos (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 2) : 0 < kl δ (1 - δ) := by
  rw [kl_eq δ h0 (by linarith)]
  apply mul_pos (by linarith)
  have : Real.log δ < Real.log (1 - δ) := Real.log_lt_log h0 (by linarith)
  linarith

lemma ratio_tendsto :
    Filter.Tendsto (fun δ : ℝ => kl δ (1 - δ) / Real.log (1 / δ)) (𝓝[>] 0) (𝓝 1) := by
  have hlog : Filter.Tendsto Real.log (𝓝[>] 0) Filter.atBot := Real.tendsto_log_nhdsGT_zero
  have hinv : Filter.Tendsto (fun δ => (Real.log δ)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atBot_zero.comp hlog
  have hid : Filter.Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
  have hl1 : Filter.Tendsto (fun δ : ℝ => Real.log (1 - δ)) (𝓝[>] 0) (𝓝 0) := by
    have : Filter.Tendsto (fun δ : ℝ => Real.log (1 - δ)) (𝓝 0) (𝓝 (Real.log (1 - 0))) :=
      ((Real.continuousAt_log (by norm_num)).comp
        ((continuous_const.sub continuous_id).continuousAt)).tendsto
    simpa using tendsto_nhdsWithin_of_tendsto_nhds this
  have hlim : Filter.Tendsto (fun δ : ℝ => (1 - 2 * δ) * (1 - Real.log (1 - δ) * (Real.log δ)⁻¹))
      (𝓝[>] 0) (𝓝 ((1 - 2 * 0) * (1 - 0 * 0))) :=
    ((tendsto_const_nhds.sub (hid.const_mul 2)).mul
      (tendsto_const_nhds.sub (hl1.mul hinv)))
  simp only [mul_zero, sub_zero, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
  rw [kl_eq δ hδ.1 hδ.2, one_div, Real.log_inv]
  have hl : Real.log δ ≠ 0 := (Real.log_neg hδ.1 hδ.2).ne
  field_simp
  ring

end MTPAux1

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ π : Policy K, IsDeltaAccurate p δ π →
      ∀ f ∈ (Mp p : Set (Pref K)),
        ENNReal.ofReal (kl δ (1 - δ)) ≤ Istar p f * expTau π f) ∧
    (∀ fam : ℝ → Policy K, IsAccurate p fam → ∀ f ∈ (Mp p : Set (Pref K)),
      (Istar p f)⁻¹ ≤ Filter.liminf
        (fun δ : ℝ => expTau (fam δ) f / ENNReal.ofReal (Real.log (1 / δ))) (𝓝[>] 0)) := by
  have h1 := theorem_1_part_i K hK p hp0 hp1
  refine ⟨h1, fun fam hfam f hf => ?_⟩
  set I := Istar p f with hI
  -- `I ≠ 0`, otherwise part (i) at `δ = 1/4` fails
  have hI0 : I ≠ 0 := by
    intro h0
    have := h1 (1 / 4) (by norm_num) (by norm_num) (fam (1 / 4))
      (hfam (1 / 4) ⟨by norm_num, by norm_num⟩) f hf
    rw [← hI, h0, zero_mul, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
    have := MTPAux1.kl_pos (1 / 4) (by norm_num) (by norm_num)
    linarith
  by_cases hItop : I = ⊤
  · rw [hItop, ENNReal.inv_top]; exact bot_le
  -- lower function
  have hlow : Filter.Tendsto
      (fun δ : ℝ => ENNReal.ofReal (kl δ (1 - δ) / Real.log (1 / δ)) * I⁻¹) (𝓝[>] 0)
      (𝓝 (I⁻¹)) := by
    have := ENNReal.Tendsto.mul_const (b := I⁻¹) (ENNReal.tendsto_ofReal MTPAux1.ratio_tendsto)
      (Or.inr (ENNReal.inv_ne_top.2 hI0))
    simpa using this
  rw [← hlow.liminf_eq]
  refine Filter.liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
  have hL : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [lt_one_div (by norm_num) hδ.1]
    linarith [hδ.2]
  have hkl := MTPAux1.kl_pos δ hδ.1 hδ.2
  have hmain := h1 δ hδ.1 hδ.2.le (fam δ) (hfam δ ⟨hδ.1, by linarith [hδ.2]⟩) f hf
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hL)) (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_right_comm, ← ENNReal.ofReal_mul (div_nonneg hkl.le hL.le), div_mul_cancel₀ _ hL.ne']
  rw [← hI] at hmain
  calc ENNReal.ofReal (kl δ (1 - δ)) * I⁻¹ ≤ I * expTau (fam δ) f * I⁻¹ := by gcongr
    _ = expTau (fam δ) f := by
      rw [mul_comm I, mul_assoc, ENNReal.mul_inv_cancel hI0 hItop, mul_one]
