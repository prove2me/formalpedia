-- Prove2me | solution 1 for QH.kappa4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:05.855608+00:00
-- url     : https://prove2.me/submissions/6d1b1d41-0a0a-4a9f-848a-013e133503a6

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailFinal
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mertensUpper
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_Kappa4Loglog
import Theorems.Thm_Deduction_mertens_upper
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_contour
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_diff_schi
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_alg
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_rpow
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_third

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace QH
private theorem kappa4_num (K : ℝ) (hK : 0 ≤ K) (s Q : ℝ) (hs : 3 ≤ s) (hQ : 0 < Q)
    (hQs : (s ^ 4) ^ 1006 ≤ Q) (x : ℝ) (hx : x = s ^ 10) :
    ((K * s ^ 4 * (s ^ 4 * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ 2 * K + 802 := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hx3 : 3 ≤ x := by
    rw [hx]; exact hs.trans (le_self_pow₀ hs1 (by norm_num))
  have hx0 : 0 < x := by linarith
  have hxa : x ^ ((2 / 5) / 4 : ℝ) = s := by
    rw [hx, ← Real.rpow_natCast s 10, ← Real.rpow_mul hs0.le]
    norm_num
  apply le_of_mul_le_mul_left _ hx0
  rw [Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow x (2 / 5) hx0, hxa,
    Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg x Q K _ _ _ hx0 hQ]
  have t3 := Formalism.HermitianLattices.Ext.BoxTail.tail_num_third x hx3
  have t1 : (s ^ 4) ^ 2 * s ≤ x := by
    rw [hx]
    calc (s ^ 4) ^ 2 * s = s ^ 9 := by ring
      _ ≤ s ^ 10 := pow_le_pow_right₀ hs1 (by norm_num)
  have t2 : s ^ 4 * x ^ 403 / Q ≤ x := by
    rw [div_le_iff₀ hQ]
    have e : s ^ 4 * x ^ 403 = x * (s ^ 4) ^ 1006 := by
      rw [hx, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    rw [e]
    exact mul_le_mul_of_nonneg_left hQs hx0.le
  have u1 := mul_le_mul_of_nonneg_left t1 hK
  have u2 := mul_le_mul_of_nonneg_left t2 hK
  have u3 : (802 : ℝ) ≤ x * 802 := by linarith
  have e1 : K * (s ^ 4) ^ 2 * s = K * ((s ^ 4) ^ 2 * s) := mul_assoc _ _ _
  have e2 : x * (2 * K + 802) = K * x + K * x + x * 802 := by ring
  rw [e1, e2]
  exact add_le_add (add_le_add u1 u2) (t3.trans u3)
private theorem kappa4_loglog : ∃ C l₀ : ℝ, 1 ≤ l₀ ∧ ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    l₀ ≤ Real.log Q → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 1000 * Real.log (Real.log Q) + C := by
  obtain ⟨K, hK0, hK⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_contour ((2 / 5) / 1600) (by positivity) (by norm_num)
  have hev : ∀ᶠ l : ℝ in Filter.atTop, l ^ 1006 ≤ Real.exp l := by
    have h := (Real.tendsto_exp_div_pow_atTop 1006).eventually_ge_atTop 1
    filter_upwards [h, Filter.eventually_gt_atTop 0] with l hl hl0
    rwa [le_div_iff₀ (by positivity), one_mul] at hl
  obtain ⟨l₀, hl₀⟩ := Filter.eventually_atTop.1 (hev.and (Filter.eventually_ge_atTop 81))
  refine ⟨2 * K + 802 + 2, l₀, by linarith [(hl₀ l₀ le_rfl).2], ?_⟩
  intro Q N _ χ hQlo hgood
  obtain ⟨hχ, hNQ, hbox⟩ := hgood
  obtain ⟨hexp, h81⟩ := hl₀ _ hQlo
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hQ0 : 0 < Q := by linarith
  rw [Real.exp_log hQ0] at hexp
  have hQ2 : 2 ≤ Q := by
    have := Real.log_le_self hQ0.le
    linarith
  obtain ⟨s, hs0, hs4⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 4 = Real.log Q :=
    ⟨Real.log Q ^ ((4 : ℕ) : ℝ)⁻¹, Real.rpow_nonneg (by linarith) _,
      Real.rpow_inv_natCast_pow (by linarith) (by norm_num)⟩
  have hs3 : 3 ≤ s := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hs0
    rw [hs4]; linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = s ^ 10 := ⟨_, rfl⟩
  have hnum := kappa4_num K hK0 s Q hs3 hQ0 (by rw [hs4]; exact hexp) x hx
  rw [hs4] at hnum
  have hx3 : 3 ≤ x := by
    rw [hx]; exact hs3.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hx0 : 0 < x := by linarith
  have hlogz : Real.log (x ^ 400) = 1000 * Real.log (Real.log Q) := by
    rw [← hs4, hx, Real.log_pow, Real.log_pow, Real.log_pow]; push_cast; ring
  set z : ℝ := x ^ 400 with hz
  set η : ℝ := 1 / x ^ 2 with hη
  have hz1 : 1 ≤ z := one_le_pow₀ (by linarith)
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  have hzη : 0 < z * η := by positivity
  have hC := hK N χ Q z η hχ hQ2 hNQ hbox hz1 hη0 hη1
  have hD := Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi χ z (z * η) hz1 hzη
  set P : ℂ := ∑ n ∈ Icc 1 ⌊z⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) with hP
  have hkey : ((z * η : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.negLD χ 1 - P) =
      -(Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) +
      (Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * P) := by ring
  have hnorm : ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤
      (K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + z ^ 2 / Q)
        + z * η * (z * η + 1) * Real.log (z + z * η) / z) / (z * η) := by
    rw [le_div_iff₀ hzη]
    have h1 := congrArg norm hkey
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hzη.le] at h1
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ * (z * η) = z * η * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := mul_comm _ _
      _ = _ := h1
      _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        exact add_le_add hC hD
  have htail := hnorm.trans hnum
  have hPle : ‖P‖ ≤ Real.log z + 2 := by
    have hM : ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ≤ Real.log z + 2 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (Deduction.mertens_upper z hz1)
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
      · intro n _ _
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
    refine le_trans (norm_sum_le _ _) (le_trans ?_ hM)
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχn : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    gcongr
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * ‖χ (n : ZMod N)‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 := by gcongr
      _ = ArithmeticFunction.vonMangoldt n := mul_one _
  have hLD : logDerivLAtOne χ = -(Formalism.ZeroFreeDirichlet.negLD χ 1) := by
    simp only [logDerivLAtOne, Formalism.ZeroFreeDirichlet.negLD, neg_neg]
  rw [hLD, norm_neg]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1‖ = ‖P + (Formalism.ZeroFreeDirichlet.negLD χ 1 - P)‖ := by rw [add_sub_cancel]
    _ ≤ ‖P‖ + ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := norm_add_le _ _
    _ ≤ _ := by rw [← hlogz]; linarith
end QH
end

set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∀ ε A : ℝ, 0 < ε → ε < 1 / 52 → 0 < A → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ A * Y ^ (ε / 5) * Real.log Y ^ 2 → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 4 * Real.log Y := by
  intro ε A hε hε1 hA
  obtain ⟨C, l₀, hl₀, hC⟩ := kappa4_loglog
  have e1 : ∀ᶠ Y : ℝ in Filter.atTop, l₀ ≤ Y ^ (ε / 6) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 6)).eventually_ge_atTop _
  have e2 : ∀ᶠ u : ℝ in Filter.atTop, ‖Real.log u‖ ≤ (1 / 26000) * ‖u‖ :=
    Real.isLittleO_log_id_atTop.bound (by norm_num)
  have e3 : ∀ᶠ u : ℝ in Filter.atTop, 13 * (1000 * Real.log A + C) ≤ u := Filter.eventually_ge_atTop _
  have e4 := Real.tendsto_log_atTop.eventually (e2.and (e3.and (Filter.eventually_ge_atTop 1)))
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 (e1.and (e4.and (Filter.eventually_gt_atTop 0)))
  refine ⟨Y₀, ?_⟩
  intro Y hY Q N _ χ hlo hhi hgood
  obtain ⟨h1, ⟨h2, h3, h4⟩, hY0⟩ := hY₀ Y hY
  have hb := hC Q N χ (h1.trans hlo) hgood
  have hu0 : 0 < Real.log Y := by linarith
  have hp : 0 < Y ^ (ε / 5) := Real.rpow_pos_of_pos hY0 _
  have hl : Real.log (Real.log Q) ≤ Real.log A + ε / 5 * Real.log Y + 2 * Real.log (Real.log Y) := by
    refine (Real.log_le_log (by linarith) hhi).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hA.ne' hp.ne', Real.log_rpow hY0,
      Real.log_pow]
    push_cast; ring
  rw [Real.norm_of_nonneg hu0.le, Real.norm_of_nonneg (Real.log_nonneg h4)] at h2
  have h5 : ε * Real.log Y ≤ 1 / 52 * Real.log Y := mul_le_mul_of_nonneg_right hε1.le hu0.le
  have h6 : ε / 5 * Real.log Y = ε * Real.log Y / 5 := by ring
  rw [h6] at hl
  linarith
end QH
