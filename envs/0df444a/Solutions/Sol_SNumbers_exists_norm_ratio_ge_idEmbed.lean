-- Prove2me | solution 1 for SNumbers.exists_norm_ratio_ge_idEmbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:42.475391+00:00
-- url     : https://prove2.me/submissions/104bbe71-50bd-4317-ad52-dff4587f1200

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity
public import Theorems.Thm_SNumbers_idEmbed_apply
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_exists_flat_vector
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SNumbers_toReal_pos_of_ne_top
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply


attribute [local simp] SNumbers.idEmbed_apply
section
@[expose] public section
universe u
open scoped ENNReal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
private lemma norm_ratio_of_flat {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {k : ℕ} (hk : 1 ≤ k) (w : Fin m → 𝕜)
    (hle : ∀ i, ‖w i‖ ≤ 1)
    (hk_card : k ≤ (Finset.univ.filter (fun i => ‖w i‖ = 1)).card) :
    (k : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q w : PiLp q (fun _ : Fin m => 𝕜))‖
      ≤ ‖(WithLp.toLp p w : PiLp p (fun _ : Fin m => 𝕜))‖ := by
  have hpf : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hP : 0 < p.toReal := toReal_pos_of_ne_top hpf
  have hQ : 0 < q.toReal := toReal_pos_of_ne_top hq
  have hPQ : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  set P := p.toReal
  set Q := q.toReal
  set Sp : ℝ := ∑ i, ‖w i‖ ^ P with hSp
  set Sq : ℝ := ∑ i, ‖w i‖ ^ Q with hSq
  have hSpnn : 0 ≤ Sp := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hSqnn : 0 ≤ Sq := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hnp : ‖(WithLp.toLp p w : PiLp p (fun _ : Fin m => 𝕜))‖ = Sp ^ (1 / P) := by
    rw [PiLp.norm_eq_sum hP]
  have hnq : ‖(WithLp.toLp q w : PiLp q (fun _ : Fin m => 𝕜))‖ = Sq ^ (1 / Q) := by
    rw [PiLp.norm_eq_sum hQ]
  rw [hnp, hnq]
  have hkSp : (k : ℝ) ≤ Sp := by
    have hcard_le : ((Finset.univ.filter (fun i => ‖w i‖ = 1)).card : ℝ) ≤ Sp := by
      rw [hSp]
      calc ((Finset.univ.filter (fun i => ‖w i‖ = 1)).card : ℝ)
          = ∑ _i ∈ Finset.univ.filter (fun i => ‖w i‖ = 1), (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = ∑ i ∈ Finset.univ.filter (fun i => ‖w i‖ = 1), ‖w i‖ ^ P := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Finset.mem_filter] at hi; rw [hi.2, Real.one_rpow]
        _ ≤ ∑ i, ‖w i‖ ^ P :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => Real.rpow_nonneg (norm_nonneg _) _)
    exact le_trans (Nat.cast_le.mpr hk_card) hcard_le
  have hSp_pos : 0 < Sp := lt_of_lt_of_le (by exact_mod_cast hk) hkSp
  have hSqSp : Sq ≤ Sp := by
    rw [hSq, hSp]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h0 : ‖w i‖ = 0
    · simp only [h0, Real.zero_rpow hP.ne', Real.zero_rpow hQ.ne', le_refl]
    · exact Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))
        (hle i) hPQ
  have hexp : 0 ≤ 1 / P - 1 / Q := by
    have : 1 / Q ≤ 1 / P := one_div_le_one_div_of_le hP hPQ
    linarith
  calc (k : ℝ) ^ (1 / P - 1 / Q) * Sq ^ (1 / Q)
      ≤ (k : ℝ) ^ (1 / P - 1 / Q) * Sp ^ (1 / Q) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hSqnn hSqSp (by positivity))
          (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    _ ≤ Sp ^ (1 / P - 1 / Q) * Sp ^ (1 / Q) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg k) hkSp hexp)
          (Real.rpow_nonneg hSpnn _)
    _ = Sp ^ (1 / P) := by rw [← Real.rpow_add hSp_pos]; congr 1; ring
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
namespace SNumbers
theorem _root_.solution {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m)
    (V : Submodule 𝕜 (PiLp q (fun _ : Fin m => 𝕜))) (hV : m - n ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖x‖
      ≤ ‖idEmbed (𝕜 := 𝕜) (m := m) p q x‖ := by
  set e : PiLp q (fun _ : Fin m => 𝕜) ≃ₗ[𝕜] (Fin m → 𝕜) :=
    WithLp.linearEquiv q 𝕜 (Fin m → 𝕜) with he
  have hkV' : m - n ≤
      Module.finrank 𝕜 (V.map (e : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] (Fin m → 𝕜))) :=
    le_of_le_of_eq hV (LinearEquiv.finrank_map_eq e V).symm
  obtain ⟨w, hwV', hw0, hwle, hwcard⟩ := exists_flat_vector (k := m - n) (by omega) hkV'
  obtain ⟨v, hvV, hev⟩ := Submodule.mem_map.mp hwV'
  have hxV : e.symm w ∈ V := by rw [← hev]; simpa using hvV
  refine ⟨e.symm w, hxV, fun h0 => hw0 (by simpa using congrArg e h0),
    norm_ratio_of_flat hpq hq (by omega) w hwle hwcard⟩
end SNumbers
