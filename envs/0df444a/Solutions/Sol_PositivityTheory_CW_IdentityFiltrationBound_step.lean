-- Prove2me | solution 1 for PositivityTheory.CW.IdentityFiltrationBound.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:16.128074+00:00
-- url     : https://prove2.me/submissions/f1a0e841-ebbb-4605-99c3-64cc33a85d1a

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EnvelopingAlgebraGrowthBound
import Theorems.Thm_PositivityTheory_CW_IdentityFiltrationBound_mem_W
import Theorems.Thm_PositivityTheory_CW_IdentityFiltrationBound_N_nonneg
import Theorems.Thm_PositivityTheory_CW_IdentityFiltrationBound_le_N
import Theorems.Thm_PositivityTheory_CW_IdentityFiltrationBound_quad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.IdentityFiltrationBound
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.IdentityFiltrationBound
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (ε : Fin n → Bool) (κ μ c : ℝ) (k : ℕ)
    (hcas : ∀ w : V, ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2)
    (hc0 : 0 ≤ c)
    (hc : ∀ l : List (Fin n × Fin n), l.length ≤ k → ∀ v,
      ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ c * N E (k + 1) v)
    (v : V) (hv : casimirK ε E v = (μ : ℂ) • v) (hμ : 0 ≤ μ) :
    N E (k + 1) v ≤ (2 * ((W n (k + 1)).card : ℝ) ^ 2 * c + ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) *
      Real.sqrt (1 + μ) * N E k v := by
  have hx : 0 ≤ N E (k + 1) v := N_nonneg E _ v
  have hy : 0 ≤ N E k v := N_nonneg E _ v
  set x := N E (k + 1) v with hxdef
  set y := N E k v with hydef
  set M : ℝ := ((W n (k + 1)).card : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hκ := abs_nonneg κ
  have key : ∀ l : List (Fin n × Fin n), l.length ≤ k + 1 →
      ‖wd E l v‖ ^ 2 ≤ (2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y := by
    intro l hl
    cases l with
    | nil =>
      have h1 : ‖wd E [] v‖ ≤ y := le_N E (l := []) (k := k) (Nat.zero_le _) v
      have h2 : 0 ≤ ‖wd E [] v‖ := norm_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hc0 hx) hy,
        mul_nonneg (add_nonneg (mul_nonneg zero_le_two hμ) hκ) (sq_nonneg y)]
    | cons p l' =>
      have hl' : l'.length ≤ k := by simpa using hl
      have hwy : ‖wd E l' v‖ ≤ y := le_N E hl' v
      have hz := hc l' hl' v
      have hOw : casimirK ε E (wd E l' v) =
          (casimirK ε E * wd E l' - wd E l' * casimirK ε E) v + (μ : ℂ) • wd E l' v := by
        simp only [LinearMap.sub_apply, Module.End.mul_apply, hv, map_smul]
        abel
      have hsplit : wd E (p :: l') v = E p.1 p.2 (wd E l' v) := by
        simp [wd, Module.End.mul_apply]
      rw [hsplit]
      have hle : ‖E p.1 p.2 (wd E l' v)‖ ^ 2 ≤ ∑ a, ∑ b, ‖E a b (wd E l' v)‖ ^ 2 := by
        calc ‖E p.1 p.2 (wd E l' v)‖ ^ 2 ≤ ∑ b, ‖E p.1 b (wd E l' v)‖ ^ 2 :=
              Finset.single_le_sum (f := fun b => ‖E p.1 b (wd E l' v)‖ ^ 2) (fun _ _ => sq_nonneg _)
                (Finset.mem_univ _)
          _ ≤ ∑ a, ∑ b, ‖E a b (wd E l' v)‖ ^ 2 :=
              Finset.single_le_sum (f := fun a => ∑ b, ‖E a b (wd E l' v)‖ ^ 2)
                (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      have hin : (inner ℂ (wd E l' v) (casimirK ε E (wd E l' v))).re ≤
          ‖wd E l' v‖ * ‖(casimirK ε E * wd E l' - wd E l' * casimirK ε E) v‖ + μ * ‖wd E l' v‖ ^ 2 := by
        have hself : (inner ℂ (wd E l' v) (wd E l' v)).re = ‖wd E l' v‖ ^ 2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        rw [hOw, inner_add_right, Complex.add_re, inner_smul_right, Complex.re_ofReal_mul, hself]
        have := (Complex.re_le_norm (inner ℂ (wd E l' v)
          ((casimirK ε E * wd E l' - wd E l' * casimirK ε E) v))).trans (norm_inner_le_norm _ _)
        linarith
      rw [hcas] at hle
      have hw0 := norm_nonneg (wd E l' v)
      have hz0 := norm_nonneg ((casimirK ε E * wd E l' - wd E l' * casimirK ε E) v)
      have e1 := mul_le_mul hwy hz hz0 hy
      have e2 : ‖wd E l' v‖ ^ 2 ≤ y ^ 2 := by nlinarith
      have e3 := mul_le_mul_of_nonneg_left e2 hμ
      have e4 := mul_le_mul_of_nonneg_left e2 hκ
      have hk : -κ * ‖wd E l' v‖ ^ 2 ≤ |κ| * ‖wd E l' v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [neg_abs_le κ]) (sq_nonneg _)
      nlinarith [sq_nonneg y]
  have hR0 : 0 ≤ (2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y := by positivity
  have hsum : x ≤ M * Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by
    calc x = ∑ l ∈ W n (k + 1), ‖wd E l v‖ := rfl
      _ ≤ ∑ l ∈ W n (k + 1), Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) :=
          Finset.sum_le_sum fun l hl => (le_abs_self _).trans (Real.abs_le_sqrt (key l (mem_W.1 hl)))
      _ = M * Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by simp [hM]
  have hsq : x ^ 2 ≤ M ^ 2 * ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by
    have := Real.sq_sqrt hR0
    have h0 := mul_nonneg hM0 (Real.sqrt_nonneg ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y))
    nlinarith
  have hA : 0 ≤ 2 * μ + |κ| + 1 := by positivity
  have hq := quad (P := M ^ 2 * (2 * μ + |κ| + 1)) (Q := 2 * M ^ 2 * c) hx hy (by positivity) (by positivity)
    (by linarith)
  rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0] at hq
  have ha : Real.sqrt (2 * μ + |κ| + 1) ≤ Real.sqrt (2 + |κ|) * Real.sqrt (1 + μ) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have ht : 1 ≤ Real.sqrt (1 + μ) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + μ by linarith)
    rwa [Real.sqrt_one] at this
  have h1 := mul_le_mul_of_nonneg_left ht (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * M ^ 2 * c) hy)
  have h2 := mul_le_mul_of_nonneg_left ha (mul_nonneg hM0 hy)
  nlinarith
end PositivityTheory.CW.IdentityFiltrationBound
