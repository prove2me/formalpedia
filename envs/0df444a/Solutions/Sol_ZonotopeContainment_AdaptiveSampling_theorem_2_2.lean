-- Prove2me | solution 1 for ZonotopeContainment.AdaptiveSampling.theorem_2_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:48:07.366457+00:00
-- url     : https://prove2.me/submissions/e8c96039-5c2d-4478-9931-bd6d520f7d20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm
import Theorems.Thm_ZonotopeContainment_AdaptiveSampling_proposition_2_1

open MeasureTheory
open scoped Pointwise
open scoped MatrixOrder
open ZonotopeContainment.AdaptiveSampling

namespace Thm22Aux

lemma support_ge_of_mem_zonotope {d n : ℕ} {w : Fin n → E d} {x : E d}
    (hx : x ∈ zonotope w) (a : E d) :
    inner ℝ a x ≤ support w a := by
  have hbdd : BddAbove ((fun y => inner ℝ a y) '' zonotope w) := by
    refine ⟨∑ i, |inner ℝ a (w i)|, ?_⟩
    rintro _ ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    calc
      inner ℝ a (∑ i, t i • w i)
        = ∑ i, t i * inner ℝ a (w i) := by simp [inner_sum, real_inner_smul_right]
      _ ≤ ∑ i, |t i * inner ℝ a (w i)| := Finset.sum_le_sum (fun i _ => le_abs_self _)
      _ = ∑ i, |t i| * |inner ℝ a (w i)| := by simp [abs_mul]
      _ ≤ ∑ i, 1 * |inner ℝ a (w i)| := by
          gcongr with i
          exact ht i
      _ = ∑ i, |inner ℝ a (w i)| := by simp
  exact le_csSup hbdd ⟨x, hx, rfl⟩

lemma isClosed_smul_of_pos {d : ℕ} {Q : Set (E d)} (hQ : IsClosed Q) {s : ℝ} (hs : 0 < s) :
    IsClosed (s • Q) := by
  have hunit : IsUnit s := isUnit_iff_ne_zero.mpr (ne_of_gt hs)
  rcases hunit with ⟨u, rfl⟩
  exact (Homeomorph.smul u).isClosedMap Q hQ

end Thm22Aux

theorem solution (C : ℝ) (hC : 64 ≤ C) :
    ∃ η : ℝ, 0 < η ∧ ∃ K : ℝ, 0 < K ∧
    ∀ (d n : ℕ), 3 ≤ d → ∀ (w : Fin n → E d) (T : Mat d), ApproxLewis w T →
    ∀ Q : Set (E d), IsClosed Q → Convex ℝ Q → (0 : E d) ∈ interior Q →
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ N : ℕ,
    K * d * (Real.log d) ^ 4 * Real.log (1 / δ) ≤ N →
    (∀ (z : Tapes d N) (k : Fin N) (j : Fin (rounds d)),
      recorded C w T (z k) j ∈ zonotope w) ∧
    (¬ zonotope w ⊆ ((2 / η) * Real.sqrt (d / Real.log d)) • Q →
      runsLaw d N {z | reportsInclusion C w T Q z} ≤ ENNReal.ofReal δ) := by
  obtain ⟨c, hc, hprop⟩ := proposition_2_1 C hC
  refine ⟨2 * c, by linarith, 1 / c, by positivity, ?_⟩
  intro d n hd w T hT Q hQclosed hQconv hQ0 δ hδ0 hδ1 N hN
  obtain ⟨_, hrec, hprob⟩ := hprop d n hd w T hT
  refine ⟨fun z k j => hrec (z k) j, ?_⟩
  intro hnotSub
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd_gt1 : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hlogd_pos : 0 < Real.log d := Real.log_pos hd_gt1
  set S : ℝ := (2 / (2 * c)) * Real.sqrt (d / Real.log d)
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  have hSQ_closed : IsClosed (S • Q) := Thm22Aux.isClosed_smul_of_pos hQclosed hS_pos
  have hSQ_conv : Convex ℝ (S • Q) := hQconv.smul S
  obtain ⟨xstar, hxstarZ, hxstarNot⟩ := Set.not_subset.mp hnotSub
  obtain ⟨f, u, hfu_left, hfu_right⟩ :=
    geometric_hahn_banach_closed_point hSQ_conv hSQ_closed hxstarNot
  set a : E d := (InnerProductSpace.toDual ℝ (E d)).symm f
  have hf_eq : ∀ y : E d, f y = inner ℝ a y := fun y => by
    simp [a]
  have h0Q : (0 : E d) ∈ Q := interior_subset hQ0
  have h0SQ : (0 : E d) ∈ S • Q := ⟨0, h0Q, smul_zero S⟩
  have hu_pos : 0 < u := by
    have := hfu_left 0 h0SQ
    simpa [hf_eq] using this
  have hu_lt_supp : u < support w a := by
    have hx_le : inner ℝ a xstar ≤ support w a :=
      Thm22Aux.support_ge_of_mem_zonotope hxstarZ a
    have hu_lt_x : u < inner ℝ a xstar := by simpa [hf_eq] using hfu_right
    exact lt_of_lt_of_le hu_lt_x hx_le
  have hQ_bound : ∀ y ∈ Q, inner ℝ a y < c * Real.sqrt (Real.log d / d) * support w a := by
    intro y hy
    have hSy : S • y ∈ S • Q := Set.smul_mem_smul_set hy
    have h1 : S * inner ℝ a y < u := by
      have := hfu_left (S • y) hSy
      simpa [hf_eq, real_inner_smul_right] using this
    have h2 : inner ℝ a y < u / S := (lt_div_iff₀ hS_pos).mpr (by linarith)
    have h3 : u / S < support w a / S := div_lt_div_of_pos_right hu_lt_supp hS_pos
    have hS_inv : support w a / S = c * Real.sqrt (Real.log d / d) * support w a := by
      have hsqrt : (Real.sqrt (d / Real.log d))⁻¹ = Real.sqrt (Real.log d / d) := by
        rw [← Real.sqrt_inv, inv_div]
      calc
        support w a / S
          = support w a * ((2 / (2 * c))⁻¹ * (Real.sqrt (d / Real.log d))⁻¹) := by
            dsimp [S]; rw [div_eq_mul_inv, mul_inv]
        _ = support w a * (c * Real.sqrt (Real.log d / d)) := by
            rw [hsqrt]
            have hc_ne : c ≠ 0 := ne_of_gt hc
            field_simp [hc_ne]
        _ = c * Real.sqrt (Real.log d / d) * support w a := by ring
    exact lt_trans h2 (hS_inv ▸ h3)
  set Bad : Set (Tape d) := {t | ∀ j : Fin (rounds d),
    inner ℝ a (recorded C w T t j) < c * Real.sqrt (Real.log d / d) * support w a}
  have hsub : {z : Tapes d N | reportsInclusion C w T Q z} ⊆
      Set.univ.pi (fun _ : Fin N => Bad) := by
    intro z hz k _ j
    exact hQ_bound _ (hz k j)
  have hlog_inv_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [one_div]
    exact (one_lt_inv₀ hδ0).mpr hδ1
  have hN_pos_real : (0 : ℝ) < N := by
    have hlhs_pos : 0 < (1 / c) * d * (Real.log d) ^ 4 * Real.log (1 / δ) := by positivity
    exact lt_of_lt_of_le hlhs_pos hN
  have hN_ne : N ≠ 0 := by
    intro h0
    subst h0
    simp at hN_pos_real
  set p : ℝ := c / (d * (Real.log d) ^ 4)
  have hp_pos : 0 < p := by positivity
  calc
    runsLaw d N {z | reportsInclusion C w T Q z}
      ≤ runsLaw d N (Set.univ.pi (fun _ : Fin N => Bad)) := measure_mono hsub
    _ = ∏ _k : Fin N, runLaw d Bad := by
        unfold runsLaw
        rw [Measure.pi_pi]
    _ = (runLaw d Bad) ^ N := by simp
    _ ≤ (1 - ENNReal.ofReal p) ^ N := pow_le_pow_left' (hprob a) N
    _ ≤ ENNReal.ofReal δ := by
        by_cases hp1 : 1 ≤ p
        · have hsub0 : (1 : ENNReal) - ENNReal.ofReal p = 0 := by
            rw [tsub_eq_zero_iff_le]
            simpa using ENNReal.ofReal_le_ofReal hp1
          rw [hsub0, zero_pow hN_ne]
          exact zero_le
        · have hp1' : p < 1 := not_le.mp hp1
          have h1mp_nonneg : 0 ≤ 1 - p := by linarith
          have hsub_eq : (1 : ENNReal) - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (le_of_lt hp_pos)]
          rw [hsub_eq, ← ENNReal.ofReal_pow h1mp_nonneg]
          apply ENNReal.ofReal_le_ofReal
          have hexp1 : (1 - p) ^ N ≤ (Real.exp (-p)) ^ N := by
            gcongr
            linarith [Real.add_one_le_exp (-p)]
          have hexp2 : (Real.exp (-p)) ^ N = Real.exp (- (N : ℝ) * p) := by
            rw [← Real.exp_nat_mul]
            ring_nf
          have hNp : Real.log (1 / δ) ≤ (N : ℝ) * p := by
            have hdlog_pos : 0 < (d : ℝ) * (Real.log d) ^ 4 := by positivity
            have hc_ne : c ≠ 0 := ne_of_gt hc
            have hdlog_ne : (d : ℝ) * (Real.log d) ^ 4 ≠ 0 := ne_of_gt hdlog_pos
            have hmul := mul_le_mul_of_nonneg_right hN (le_of_lt hp_pos)
            calc
              Real.log (1 / δ)
                = ((1 / c) * d * (Real.log d) ^ 4 * Real.log (1 / δ)) * p := by
                  dsimp [p]
                  field_simp [hc_ne, hdlog_ne]
              _ ≤ (N : ℝ) * p := hmul
          have hexp3 : Real.exp (- (N : ℝ) * p) ≤ δ := by
            have hlog_inv : Real.log (1 / δ) = - Real.log δ := by
              rw [one_div, Real.log_inv]
            have hle : - (N : ℝ) * p ≤ Real.log δ := by linarith
            calc
              Real.exp (- (N : ℝ) * p) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hle
              _ = δ := Real.exp_log hδ0
          exact le_trans (hexp2 ▸ hexp1) hexp3
