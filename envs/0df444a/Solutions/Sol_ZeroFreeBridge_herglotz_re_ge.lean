-- Prove2me | solution 1 for ZeroFreeBridge.herglotz_re_ge
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:44:54.16574+00:00
-- url     : https://prove2.me/submissions/53d4209e-4448-4199-afea-d38acb6930d2

import Mathlib
/- PHASE 4 (dVP frontier, rung 1): the ZERO-EXTRACTION core of the de la Vallee Poussin
   `hzero` bound.

   `dlvp_core_estimate` (ZeroFreeRegion.lean) is proved but CONDITIONAL on three bounds on
   `-Re(ζ'/ζ)`; the analytic frontier is producing them from Borel-Caratheodory + the
   Hadamard zero-sum.  The `hzero` bound
     -Re(ζ'/ζ)(σ+iγ) ≤ A·L - k/(σ-β)
   has a clean mathematical HEART, isolated here: evaluated at the height of the zero,
   `s - ρ = σ - β` is a POSITIVE REAL (the imaginary parts cancel), so
   `Re(k/(s-ρ)) = k/(σ-β)` EXACTLY (`re_smul_inv_sub_at_equal_height`); and every OTHER
   zero `ρ'` (with `Re ρ' ≤ 1 < σ`) contributes a NONNEGATIVE real part
   (`re_inv_sub_nonneg_of_re_lt`), so it may be dropped from the Herglotz sum.

   `hzero_of_herglotz` combines these: it REDUCES the conditional `hzero` to a single
   Herglotz-form bound `hbound`, which is exactly the Borel-Caratheodory output
     -Re(ζ'/ζ)(s) ≤ A·L - Σ_ρ Re(k_ρ/(s-ρ)).
   This shrinks the dVP frontier for `hzero` to that one sum bound (see the effort spec).
   It improves the region CONSTANT chain only; NOT a proof of RH.  conjecture1_proved = False.
-/


open Complex

namespace ZeroFreeBridge

/-- At the zero's OWN height `s = σ+iγ`, `ρ = β+iγ`, the difference `s-ρ = σ-β` is a REAL
    number (the `iγ` cancels), so `Re(k/(s-ρ)) = k/(σ-β)` EXACTLY.  This is why the de la
    Vallee Poussin argument evaluates the log-derivative at the height of the zero.  Stated
    unconditionally; in use `β < σ` makes `k/(σ-β) > 0` a genuine gain. -/
theorem re_smul_inv_sub_at_equal_height (σ γ β : ℝ) (k : ℝ) :
    (((k : ℂ)) / (((σ : ℂ) + (γ : ℂ) * I) - ((β : ℂ) + (γ : ℂ) * I))).re = k / (σ - β) := by
  have hsub : ((σ : ℂ) + (γ : ℂ) * I) - ((β : ℂ) + (γ : ℂ) * I) = ((σ - β : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub, ← Complex.ofReal_div, Complex.ofReal_re]

/-- Any zero `ρ'` with `Re ρ' < s.re` contributes a NONNEGATIVE real part at `s`, so it may
    be dropped from the Herglotz sum (for `σ > 1`, every nontrivial zero has `Re ρ' ≤ 1 < σ`). -/
theorem re_inv_sub_nonneg_of_re_lt (s ρ : ℂ) (h : ρ.re < s.re) :
    0 ≤ (1 / (s - ρ)).re := by
  have hz : 0 < (s - ρ).re := by rw [Complex.sub_re]; linarith
  rw [one_div, Complex.inv_re]
  exact div_nonneg hz.le (Complex.normSq_nonneg _)



end ZeroFreeBridge


/- PHASE 4 (dVP frontier, BLASCHKE → skeleton bridge): the Herglotz lower bound.

   `DlvpBCSumBlaschke.bc_sum_blaschke` gives `-Re(ζ'/ζ) ≤ A·L − Re(Z)` with `Z = Σ_ρ (divisor ρ)/(z−ρ)`.
   To reach the skeleton's `hzero` shape `-Re(ζ'/ζ) ≤ A·L − k/(σ−β)`, one needs `Re(Z) ≥ k/(σ−β)`:
   keep the zero `ρ₀ = β+γI` at the SAME height as `z = σ+γI` (its real part is exactly `k/(σ−β)`,
   rung 1 `re_smul_inv_sub_at_equal_height`) and DROP the other zeros (each `Re ≥ 0` since their real
   part is `< σ`, rung 1 `re_inv_sub_nonneg_of_re_lt`, times the nonnegative multiplicity).

     `herglotz_re_ge` :  ρ₀ ∈ s with `ρ₀ = β+γI`, `m ρ₀ = k`, `m ≥ 0`, other zeros `Re < σ`
       ⟹  `k/(σ−β) ≤ Re(Σ_ρ (m ρ)/((σ+γI) − ρ))`.

   Combined with `bc_sum_blaschke` (a `linarith`) this yields the `hzero`/`htwo` inputs the reduction
   skeleton `DlvpPole.dlvp_region_of_bc_inputs` consumes.  conjecture1_proved = False (NOT RH).
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {s : Finset ℂ} (m : ℂ → ℤ) (σ γ β : ℝ) (k : ℤ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ s) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I) (hmρ₀ : m ρ₀ = k)
    (hother : ∀ ρ ∈ s, ρ ≠ ρ₀ → ρ.re < σ) :
    (k : ℝ) / (σ - β)
      ≤ (∑ ρ ∈ s, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * I) - ρ)).re := by
  set z : ℂ := (σ : ℂ) + (γ : ℂ) * I with hz
  rw [Complex.re_sum, ← Finset.add_sum_erase _ _ hρ₀]
  -- the distinguished term equals `k/(σ-β)`.
  have hterm₀ : ((m ρ₀ : ℂ) / (z - ρ₀)).re = (k : ℝ) / (σ - β) := by
    rw [hmρ₀, hρ₀_eq, hz]
    exact_mod_cast re_smul_inv_sub_at_equal_height σ γ β (k : ℝ)
  -- the remaining terms are nonnegative.
  have hrest : 0 ≤ ∑ ρ ∈ s.erase ρ₀, ((m ρ : ℂ) / (z - ρ)).re := by
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρs : ρ ∈ s := Finset.mem_of_mem_erase hρ
    have hρne : ρ ≠ ρ₀ := Finset.ne_of_mem_erase hρ
    have hlt : ρ.re < z.re := by rw [hz]; simpa using hother ρ hρs hρne
    have hdiv : (m ρ : ℂ) / (z - ρ) = (m ρ : ℂ) * (1 / (z - ρ)) := by rw [mul_one_div]
    rw [hdiv, ← Complex.ofReal_intCast, Complex.re_ofReal_mul]
    exact mul_nonneg (by exact_mod_cast hm ρ hρs) (re_inv_sub_nonneg_of_re_lt z ρ hlt)
  rw [hterm₀]
  linarith
