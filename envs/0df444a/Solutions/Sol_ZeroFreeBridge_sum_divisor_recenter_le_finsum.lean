-- Prove2me | solution 1 for ZeroFreeBridge.sum_divisor_recenter_le_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:52:49.671576+00:00
-- url     : https://prove2.me/submissions/40e3a4c4-0b8c-44c8-badb-c1e7d374ff61

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
/- PHASE 4 (dVP frontier, the divisor-TRANSLATION lemma — item 3 core): `divisor` commutes with a
   constant shift.  `bc_sum_blaschke` is centred at `0`, so ζ enters as `f = ζ(c₀+·)` and its divisor is
   `divisor (ζ(c₀+·)) (ball 0 R)`; the Herglotz-sum reindexing needs this to be `divisor ζ (ball c₀ R)`
   evaluated at the shifted point.

   `divisor f U z = (meromorphicOrderAt f z).untop₀` (`divisor_apply`), and the meromorphic order is
   invariant under a translation `g = (c₀+·)` because `deriv g = 1 ≠ 0`
   (`meromorphicOrderAt_comp_of_deriv_ne_zero`).  Hence

     `divisor (fun w => f (c₀+w)) U' u = divisor f U (c₀+u)`

   whenever both sides are in-domain and `f` is meromorphic on `U`.  This is the last uncertain-API
   piece of the ζ instantiation, and it is a direct consequence of the Mathlib order-composition API.
   conjecture1_proved = False (NOT a proof of RH).
-/


open Complex MeromorphicOn

namespace ZeroFreeBridge

/-- **Divisor under a constant shift.**  `divisor (fun w => f (c₀+w)) U' u = divisor f U (c₀+u)`. -/
theorem divisor_comp_const_add_apply {f : ℂ → ℂ} {U U' : Set ℂ} (c₀ : ℂ)
    (hf : MeromorphicOn f U) (hf' : MeromorphicOn (fun w => f (c₀ + w)) U')
    {u : ℂ} (hu' : u ∈ U') (hu : c₀ + u ∈ U) :
    divisor (fun w => f (c₀ + w)) U' u = divisor f U (c₀ + u) := by
  rw [divisor_apply hf' hu', divisor_apply hf hu]
  congr 1
  have hg : AnalyticAt ℂ (fun w => c₀ + w) u := by fun_prop
  have hg' : deriv (fun w => c₀ + w) u ≠ 0 := by
    rw [deriv_const_add']; simp
  have hcomp : (fun w => f (c₀ + w)) = f ∘ (fun w => c₀ + w) := rfl
  rw [hcomp, meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']



end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 2(i) — the count RECONCILIATION core): bound the recentred divisor
   sum (the Herglotz-sum zero count over `ball 0 R`) by the ζ finsum over `closedBall c₀ R`, which
   `zeta_zero_count_strip` then bounds by an O(log|c₀.im|) Jensen quantity.

   The gap `hAL` faces: its sum is `∑ over toFinset` of the RECENTRED divisor on `ball 0 R`, while
   the Jensen count is a finsum of `divisor ζ` on a `closedBall`.  This file bridges them (the hard
   discrete part; `finsum_le_finsum` is absent in Mathlib, so it is assembled from lower-level pieces):
     * `sum_divisor_recenter_eq_image` — pointwise translate (`divisor_comp_const_add_apply`) +
       shift-reindex (`Finset.sum_image`, `add_left_cancel` injective) ⟹ recentred sum = ζ sum over
       the shifted image `{c₀+u}`;
     * `sum_divisor_recenter_le_finsum` — `ball c₀ R = closedBall c₀ R` divisor on interior points
       (`divisor_apply` both sides = same order), then `image ⊆ finiteSupport` (compact-domain
       `locallyFinsuppWithin.finiteSupport`) + `Finset.sum_le_sum_of_subset_of_nonneg` (`divisor ≥ 0`)
       + `finsum_eq_finset_sum_of_support_subset` ⟹ `∑ ≤ ∑ᶠ divisor ζ (closedBall c₀ R)`.
   Chaining with `zeta_zero_count_strip` (inner `R`, outer `R' > R`) gives the O(L) `hcount` that
   `hAL_concrete` consumes.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

theorem sum_divisor_recenter_eq_image {c₀ : ℂ} {R : ℝ}
    (hf_mero : MeromorphicOn riemannZeta (ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (ball 0 R))
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite) :
    (∑ u ∈ hfin.toFinset, (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℤ))
      = ∑ ρ ∈ hfin.toFinset.image (fun u => c₀ + u),
          (divisor riemannZeta (ball c₀ R) ρ : ℤ) := by
  rw [Finset.sum_image (fun a _ b _ h => add_left_cancel h)]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  have hune : divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u ≠ 0 := by
    rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
  have huball : u ∈ ball (0 : ℂ) R :=
    (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
      (Function.mem_support.mpr hune)
  have hcuball : c₀ + u ∈ ball c₀ R := by
    rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
  exact divisor_comp_const_add_apply c₀ hf_mero hf'_mero huball hcuball





end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 2(i) — the count RECONCILIATION core): bound the recentred divisor
   sum (the Herglotz-sum zero count over `ball 0 R`) by the ζ finsum over `closedBall c₀ R`, which
   `zeta_zero_count_strip` then bounds by an O(log|c₀.im|) Jensen quantity.

   The gap `hAL` faces: its sum is `∑ over toFinset` of the RECENTRED divisor on `ball 0 R`, while
   the Jensen count is a finsum of `divisor ζ` on a `closedBall`.  This file bridges them (the hard
   discrete part; `finsum_le_finsum` is absent in Mathlib, so it is assembled from lower-level pieces):
     * `sum_divisor_recenter_eq_image` — pointwise translate (`divisor_comp_const_add_apply`) +
       shift-reindex (`Finset.sum_image`, `add_left_cancel` injective) ⟹ recentred sum = ζ sum over
       the shifted image `{c₀+u}`;
     * `sum_divisor_recenter_le_finsum` — `ball c₀ R = closedBall c₀ R` divisor on interior points
       (`divisor_apply` both sides = same order), then `image ⊆ finiteSupport` (compact-domain
       `locallyFinsuppWithin.finiteSupport`) + `Finset.sum_le_sum_of_subset_of_nonneg` (`divisor ≥ 0`)
       + `finsum_eq_finset_sum_of_support_subset` ⟹ `∑ ≤ ∑ᶠ divisor ζ (closedBall c₀ R)`.
   Chaining with `zeta_zero_count_strip` (inner `R`, outer `R' > R`) gives the O(L) `hcount` that
   `hAL_concrete` consumes.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge




theorem solution {c₀ : ℂ} {R : ℝ}
    (hf_mero : MeromorphicOn riemannZeta (ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (ball 0 R))
    (hf_ana_cl : AnalyticOnNhd ℂ riemannZeta (closedBall c₀ R))
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite) :
    (∑ u ∈ hfin.toFinset, (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℤ))
      ≤ ∑ᶠ ρ, divisor riemannZeta (closedBall c₀ R) ρ := by
  rw [sum_divisor_recenter_eq_image hf_mero hf'_mero hfin]
  -- step 1: ball = closedBall divisor on image points
  have hf_mero_cl := hf_ana_cl.meromorphicOn
  have hstep1 : ∀ ρ ∈ hfin.toFinset.image (fun u => c₀ + u),
      divisor riemannZeta (ball c₀ R) ρ = divisor riemannZeta (closedBall c₀ R) ρ := by
    intro ρ hρ
    rw [Finset.mem_image] at hρ
    obtain ⟨u, hu, rfl⟩ := hρ
    have hune : divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
        (Function.mem_support.mpr hune)
    have hcuball : c₀ + u ∈ ball c₀ R := by
      rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
    have hcucl : c₀ + u ∈ closedBall c₀ R := ball_subset_closedBall hcuball
    rw [hf_mero.divisor_apply hcuball, hf_mero_cl.divisor_apply hcucl]
  rw [Finset.sum_congr rfl (fun ρ hρ => by rw [hstep1 ρ hρ])]
  -- step 2+3: image ⊆ finiteSupport, nonneg
  have hDnn : (0 : _) ≤ divisor riemannZeta (closedBall c₀ R) := hf_ana_cl.divisor_nonneg
  have hDfin : Set.Finite (Function.support ((divisor riemannZeta (closedBall c₀ R) : ℂ → ℤ))) :=
    (divisor riemannZeta (closedBall c₀ R)).finiteSupport (isCompact_closedBall c₀ R)
  have hfinsum : ∑ᶠ ρ, divisor riemannZeta (closedBall c₀ R) ρ
      = ∑ ρ ∈ hDfin.toFinset, divisor riemannZeta (closedBall c₀ R) ρ :=
    finsum_eq_finset_sum_of_support_subset _ (by
      intro ρ hρ; rw [Set.Finite.coe_toFinset]; exact hρ)
  rw [hfinsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    rw [Finset.mem_image] at hρ
    obtain ⟨u, hu, rfl⟩ := hρ
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    rw [← hstep1 (c₀ + u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)]
    have hune : divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
        (Function.mem_support.mpr hune)
    have hcuball : c₀ + u ∈ ball c₀ R := by
      rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
    rwa [← divisor_comp_const_add_apply c₀ hf_mero hf'_mero huball hcuball]
  · intro ρ _ _; exact hDnn ρ
