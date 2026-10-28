-- Prove2me | solution 1 for ZeroFreeBridge.norm_logDeriv_g_le_wired
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:09:40.038759+00:00
-- url     : https://prove2.me/submissions/e7bdc55f-bad2-4df6-8b3e-58365281dd91

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_continuousAt_blaschke_smul_g_zero
import Theorems.Thm_ZeroFreeBridge_norm_blaschke_center_le_one
import Theorems.Thm_ZeroFreeBridge_norm_logDeriv_g_le_strip
import Theorems.Thm_ZeroFreeBridge_zeta_center_factorization
/- PHASE 4 (dVP frontier, BLASCHKE step 2): the canonical-decomposition part `g` is analytic and
   zero-free on the open ball.

   `MeromorphicOn.exists_canonicalDecomp` returns `g` in meromorphic NORMAL FORM on `closedBall 0 R`
   with `g ≠ 0` on `ball 0 R` (`CanonicalDecomp.ne_zero`).  Normal form + nonvanishing forces order 0,
   hence analyticity: `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff` (`g z ≠ 0 ⟹ order 0`) then
   `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt` (`order ≥ 0 ⟹ AnalyticAt`).

   Output: `g` is `AnalyticOnNhd` and zero-free on `ball 0 R` — the input `DlvpMaxMod` needs for the
   log branch and max-modulus.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric MeromorphicOn

namespace ZeroFreeBridge

/-- **The canonical-decomposition part `g` is analytic on the ball.**  From a `CanonicalDecomp f g R`,
    `g` is analytic at every point of `ball 0 R` (normal form + nonvanishing ⟹ order 0 ⟹ analytic). -/
theorem canonicalDecomp_analyticOnNhd {f g : ℂ → ℂ} {R : ℝ} (D : CanonicalDecomp f g R) :
    AnalyticOnNhd ℂ g (ball 0 R) := by
  intro z hz
  have hzc : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hz
  have hnf : MeromorphicNFAt g z := D.meromorphicNFOn hzc
  have hne : g z ≠ 0 := D.ne_zero z hz
  exact hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (le_of_eq (hnf.meromorphicOrderAt_eq_zero_iff.mpr hne).symm)

/-- `g` is zero-free on `ball 0 R` (a restatement of `CanonicalDecomp.ne_zero`). -/
theorem canonicalDecomp_ne_zero {f g : ℂ → ℂ} {R : ℝ} (D : CanonicalDecomp f g R) :
    ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0 := D.ne_zero

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 1 RESOLVED — g boundary regularity via option (b)): the
   canonical-decomp quotient `g` is analytic UP TO THE SPHERE, so `hg_cont`/`hg_dcc` (the two
   remaining inputs of `norm_logDeriv_g_le_strip`) are discharged.

   The subtlety (PR #287): `D` only gives `g` `MeromorphicNFOn (closedBall 0 R)` + zero-free on the
   OPEN ball; `D.eventuallyEq` holds only `codiscreteWithin (closedBall)`, giving no control in a full
   punctured neighbourhood of a sphere point — so an order-transfer via `meromorphicOrderAt_congr`
   fails there.

   RESOLUTION: Mathlib's `CanonicalDecomp.divisor_eq_divisor` already proves the hard step,
   `divisor g (closedBall 0 R) x = divisor f (sphere 0 R) x` (its sphere case: the canonical factors
   are analytic and non-vanishing there, so the orders of `f` and `g` agree).  When `f = ζ(c₀+·)` is
   analytic on the sphere, `divisor f (sphere) ≥ 0`, hence `divisor g (closedBall) ≥ 0`, hence — by
   `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd` — `g` is `AnalyticOnNhd (closedBall 0 R)`.
   `ContinuousOn` (sphere) and `DiffContOnCl` (ball) follow immediately.  conjecture1_proved = False.
-/


open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **`g` analytic up to the sphere.**  If `f` is analytic on `sphere 0 R`, the canonical-decomp
    quotient `g` is `AnalyticOnNhd` on the CLOSED ball.  Via `CanonicalDecomp.divisor_eq_divisor`
    (order `g` = order `f` on the sphere) + `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`. -/
theorem canonicalDecomp_analyticOnNhd_closedBall {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R) (hf_sphere : AnalyticOnNhd ℂ f (sphere 0 R)) :
    AnalyticOnNhd ℂ g (closedBall 0 R) := by
  rw [← D.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd]
  intro x
  rw [D.divisor_eq_divisor hR]
  exact hf_sphere.divisor_nonneg x

/-- **`hg_cont`.**  `g` continuous on the sphere. -/
theorem canonicalDecomp_contOn_sphere {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R) (hf_sphere : AnalyticOnNhd ℂ f (sphere 0 R)) :
    ContinuousOn g (sphere 0 R) :=
  ((canonicalDecomp_analyticOnNhd_closedBall hR D hf_sphere).mono
    sphere_subset_closedBall).continuousOn

/-- **`hg_dcc`.**  `g` is `DiffContOnCl` on the open ball (differentiable inside, continuous up to
    the closed ball). -/
theorem canonicalDecomp_diffContOnCl {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R) (hf_sphere : AnalyticOnNhd ℂ f (sphere 0 R)) :
    DiffContOnCl ℂ g (ball 0 R) := by
  have hg := canonicalDecomp_analyticOnNhd_closedBall hR D hf_sphere
  refine ⟨(hg.mono ball_subset_closedBall).differentiableOn, ?_⟩
  rw [closure_ball 0 hR.ne']
  exact hg.continuousOn

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the Blaschke-CENTRE relation, assembled): `‖ζ c₀‖ ≤ ‖g 0‖` from `‖B 0‖ ≤ 1`
   (`DlvpBlaschkeCenter.norm_blaschke_center_le_one`) and the centre factorization `ζ c₀ = B 0 · g 0`.

   The recentred ζ is `f = ζ(c₀+·)`, `f 0 = ζ c₀`; the CanonicalDecomp gives `f = B·g` codiscretely, and
   at the centre (`ζ c₀ ≠ 0`, so `0` is not a zero and `B` is analytic there) the identity principle
   upgrades this to the pointwise `ζ c₀ = B 0 · g 0`.  Taking that pointwise factorization as the single
   hypothesis `hfac0`, `‖B 0‖ ≤ 1` yields `‖ζ c₀‖ = ‖B 0‖·‖g 0‖ ≤ ‖g 0‖` — exactly the hypothesis
   `DlvpZetaEntire.norm_logDeriv_g_le` needs.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **The Blaschke-centre relation.**  `‖ζ c₀‖ ≤ ‖g 0‖`, from `‖B 0‖ ≤ 1` and the centre factorization
    `ζ c₀ = B 0 · g 0`. -/
theorem zeta_norm_le_g_zero {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (m : ℂ → ℤ) (hfin : (Function.support (fun u => -(m u))).Finite)
    (hsupp : ∀ u ∈ hfin.toFinset, u ≠ 0 ∧ ‖u‖ < R) (hm : ∀ u ∈ hfin.toFinset, 0 ≤ m u)
    (hfac0 : riemannZeta c₀
      = (∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) 0 * g 0) :
    ‖riemannZeta c₀‖ ≤ ‖g 0‖ := by
  have hB : ‖(∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) 0‖ ≤ 1 :=
    norm_blaschke_center_le_one hR m hfin hsupp hm
  calc ‖riemannZeta c₀‖ = ‖(∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) 0‖ * ‖g 0‖ := by
        rw [hfac0, norm_mul]
    _ ≤ 1 * ‖g 0‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg _)
    _ = ‖g 0‖ := one_mul _

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, rung 2 analytic core — ζ zero-count, UNCONDITIONAL): ζ on a disk
   about `2 + iγ`, the Jensen zero-count applied to ζ, and its boundary bound discharged.

   Obligation (ii) of BC-SUM needs the number of ζ-zeros in a disk near the 1-line to be
   `O(log|γ|)`.  Mathlib v4.32's Jensen count `AnalyticOnNhd.sum_divisor_le`
   (`Mathlib.Analysis.Complex.JensenFormula`) has three hypotheses for `f = ζ`:
     * ζ analytic on the closed disk avoiding `s = 1`  — `zeta_analyticOnNhd_disk`;
     * `ζ c ≠ 0`                                       — `zeta_ne_zero_of_one_lt_re`;
     * a boundary bound `‖ζ‖ ≤ M` on the sphere        — `zeta_sphere_bound` (from
       `zeta_strip_bound`).
   `zeta_zero_count_le` wires the first two in (taking the boundary bound); `zeta_sphere_bound`
   supplies the third with an EXPLICIT `M = (‖c‖+R)/(c.re-R-1) + (‖c‖+R)/(c.re-R)` (`O(|γ|)` for
   `c = 2+iγ`); `zeta_zero_count_unconditional` combines them into a hypothesis-free
   `O(log|γ|)` count.

   This discharges the ZERO-COUNT half of obligation (ii).  The remaining core: the
   partial-fraction split ζ'/ζ = Z + E via the `divisor` (obligation (i)) and
   `borel_caratheodory_deriv` bounding `E`.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex MeromorphicOn

namespace ZeroFreeBridge

/-- ζ is nonzero right of the 1-line (`Re s > 1`) — the `f c ≠ 0` hypothesis of Jensen's
    `sum_divisor_le` at a disk center like `2 + iγ`. -/
theorem zeta_ne_zero_of_one_lt_re (c : ℂ) (hc : 1 < c.re) : riemannZeta c ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (le_of_lt hc)

/-- ζ is analytic on any closed disk that avoids the pole `s = 1` — the `AnalyticOnNhd`
    hypothesis of Jensen's `sum_divisor_le` / `circleAverage_log_norm`. -/
theorem zeta_analyticOnNhd_disk (c : ℂ) (r : ℝ) (h1 : (1 : ℂ) ∉ Metric.closedBall c r) :
    AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c r) := by
  have hsub : Metric.closedBall c r ⊆ {(1 : ℂ)}ᶜ := by
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact h1 hs
  have hdiff : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) := fun s hs =>
    (differentiableAt_riemannZeta (by simpa using hs)).differentiableWithinAt
  exact (hdiff.analyticOnNhd isOpen_compl_singleton).mono hsub







end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 1 partial — the ζ-side sphere continuity `hf_cont`): one of the four
   inputs `norm_logDeriv_g_le_strip` needs to produce `hg_bound`.

   `norm_logDeriv_g_le_strip` (via `norm_logDeriv_le_of_sphere_log_norm_le_interior`) requires, on the
   sphere `sphere 0 R`:  `hf_cont` (ζ(c₀+·) continuous), `hg_cont` (g continuous), `hg_dcc`
   (`DiffContOnCl g (ball 0 R)`), plus `hfg0` (`zeta_norm_le_g_zero`, already built).

   `hf_cont` is elementary: ζ is analytic (hence continuous) on `closedBall c₀ R` when `1 ∉ closedBall`,
   and the shift `w ↦ c₀ + w` maps `sphere 0 R` into `closedBall c₀ R`.

   BOUNDARY-REGULARITY SUBTLETY (the genuinely hard remainder of item 1): `hg_cont`/`hg_dcc` are NOT
   derivable from the `CanonicalDecomp` alone.  `D` gives `g` `MeromorphicNFOn (closedBall 0 R)` and
   zero-free only on the OPEN ball; `D.eventuallyEq` holds `codiscreteWithin (closedBall 0 R)`, which
   gives NO control in a full punctured neighbourhood of a sphere point (points just OUTSIDE the ball
   are uncontrolled), so the order-transfer `order g = order f - order B` (which would give `g`
   analytic on the sphere) cannot be run via `meromorphicOrderAt_congr` at boundary points.  The two
   candidate resolutions — (a) reformulate the entire-part bound at a strictly smaller radius `r < R`
   (where `g` is analytic, but then the Blaschke modulus-1 identity `‖g‖=‖ζ‖` no longer holds on
   `sphere r`), or (b) a construction-level argument that `g = ζ(c₀+·)·∏canonicalFactor^{divisor}` is
   analytic up to the sphere — are each real work, not a quick lemma.  conjecture1_proved = False.
-/


open Complex Metric

namespace ZeroFreeBridge

/-- **`hf_cont`: the recentred ζ is continuous on the sphere.**  For `1 ∉ closedBall c₀ R`,
    `fun w => riemannZeta (c₀ + w)` is `ContinuousOn` `sphere 0 R` (ζ analytic on the disk, composed
    with the shift into `closedBall c₀ R`). -/
theorem zeta_recenter_cont_sphere {c₀ : ℂ} {R : ℝ}
    (h1 : (1 : ℂ) ∉ closedBall c₀ R) :
    ContinuousOn (fun w => riemannZeta (c₀ + w)) (sphere 0 R) := by
  have hζ : ContinuousOn riemannZeta (closedBall c₀ R) :=
    (zeta_analyticOnNhd_disk c₀ R h1).continuousOn
  have hmaps : Set.MapsTo (fun w => c₀ + w) (sphere (0 : ℂ) R) (closedBall c₀ R) := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    rw [mem_closedBall_iff_norm, add_sub_cancel_left, hw]
  exact hζ.comp ((continuous_const.add continuous_id).continuousOn) hmaps

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 1 COMPLETE — hg_bound fully wired): the entire-part bound
   `‖logDeriv g z₀‖ ≤ 4·Aζ''·(R+‖z₀‖)/(R-‖z₀‖)² = O(L)` for the recentred-ζ Blaschke quotient g,
   from JUST a `CanonicalDecomp` + the disk geometry — every sub-input discharged internally.

   `norm_logDeriv_g_le_strip` needs 4 inputs beyond D/geometry: hf_cont, hg_cont, hg_dcc, hfg0.
   This wrapper discharges all four (general in c₀, so reusable for the height-γ disk c₀=2+iγ AND
   the height-2γ disk c₁=2+2iγ):
     * hf_cont  = `zeta_recenter_cont_sphere` (ζ(c₀+·) cont on sphere);
     * hg_cont  = `canonicalDecomp_contOn_sphere`, hg_dcc = `canonicalDecomp_diffContOnCl`
                  (g analytic up to the sphere, PR #289, needs f analytic on the sphere);
     * hfg0     = `zeta_norm_le_g_zero` (‖ζ c₀‖≤‖g 0‖ from ‖B 0‖≤1), fed by the centre factorization
                  `zeta_center_factorization` ← `continuousAt_blaschke_smul_g_zero` (B·g cont at 0) +
                  the divisor-support facts (u≠0 since ζ(c₀)≠0 ⟹ divisor 0 =0; ‖u‖<R; divisor ≥0).
   `1∉closedBall c₀ R` is derived from `|c₀.im| ≥ R+2`; the recentred ζ analyticity on closedBall 0 R
   is the standard `zeta_analyticOnNhd_disk ∘ shift`.  conjecture1_proved = False (NOT a proof of RH).
-/







open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem solution {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hc2 : 2 ≤ c₀.re) (hRlt : R < c₀.re - 1/2) (himc : R + 2 ≤ |c₀.im|)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < R) :
    ‖logDeriv g z₀‖
      ≤ 4 * (Real.log ((‖c₀‖ + R) / (|c₀.im| - R) + (‖c₀‖ + R) / (c₀.re - R))
              - Real.log (2 - Real.pi ^ 2 / 6))
          * (R + ‖z₀ - 0‖) / (R - ‖z₀ - 0‖) ^ 2 := by
  have hc : 1 < c₀.re := by linarith
  -- 1 ∉ closedBall c₀ R (from |c₀.im| ≥ R+2)
  have h1 : (1 : ℂ) ∉ closedBall c₀ R := by
    rw [mem_closedBall, Complex.dist_eq]
    intro hle
    have h3 : |((1 : ℂ) - c₀).im| = |c₀.im| := by
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    have h4 : |((1 : ℂ) - c₀).im| ≤ ‖(1 : ℂ) - c₀‖ := Complex.abs_im_le_norm _
    rw [h3] at h4; linarith
  -- recentred ζ analytic on closedBall 0 R
  have hana : AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (closedBall 0 R) := by
    have hshift_ana : AnalyticOnNhd ℂ (fun w => c₀ + w) (closedBall 0 R) :=
      fun z _ => analyticAt_const.add analyticAt_id
    have hmaps : Set.MapsTo (fun w => c₀ + w) (closedBall (0 : ℂ) R) (closedBall c₀ R) := by
      intro w hw
      rw [mem_closedBall, Complex.dist_eq] at hw
      rw [mem_closedBall, Complex.dist_eq, add_sub_cancel_left]; simpa using hw
    exact (zeta_analyticOnNhd_disk c₀ R h1).comp hshift_ana hmaps
  have hf_sphere := hana.mono sphere_subset_closedBall
  have hf_cont := zeta_recenter_cont_sphere h1
  have hg_cont := canonicalDecomp_contOn_sphere hR D hf_sphere
  have hg_dcc := canonicalDecomp_diffContOnCl hR D hf_sphere
  have hg_ne := canonicalDecomp_ne_zero D
  have hg_ana := canonicalDecomp_analyticOnNhd D
  -- divisor support finite
  have hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite := by
    simpa [Function.support_neg] using D.meromorphicOn.divisor_ball_support_finite
  set m : ℂ → ℤ := fun u => divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u with hm_def
  -- support facts
  have hfb : AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (ball 0 R) :=
    hana.mono ball_subset_closedBall
  have hsupp0 : ∀ u ∈ hfin.toFinset, u ≠ 0 := by
    intro u hu h0
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    subst h0
    apply hu
    rw [neg_eq_zero]
    show divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) 0 = 0
    rw [hfb.divisor_apply (mem_ball_self hR)]
    have hf0 : (fun w => riemannZeta (c₀ + w)) 0 ≠ 0 := by
      simp only [add_zero]; exact zeta_ne_zero_of_one_lt_re c₀ hc
    rw [(hfb 0 (mem_ball_self hR)).analyticOrderAt_eq_zero.mpr hf0]
    simp
  have hsupp : ∀ u ∈ hfin.toFinset, u ≠ 0 ∧ ‖u‖ < R := by
    intro u hu
    refine ⟨hsupp0 u hu, ?_⟩
    rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu
    have := (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
      (Function.mem_support.mpr hu)
    rwa [mem_ball_zero_iff] at this
  have hm : ∀ u ∈ hfin.toFinset, 0 ≤ m u := fun u _ =>
    hfb.divisor_nonneg u
  -- centre factorization → hfg0
  have hf_cont0 : ContinuousAt (fun w => riemannZeta (c₀ + w)) 0 :=
    (hfb 0 (mem_ball_self hR)).continuousAt
  have hg_cont0 : ContinuousAt g 0 := (hg_ana 0 (mem_ball_self hR)).continuousAt
  have hBg_cont0 := continuousAt_blaschke_smul_g_zero hR m hfin hsupp0 hg_cont0
  have hfac0 := zeta_center_factorization hR D hf_cont0 hBg_cont0
  have hfg0 := zeta_norm_le_g_zero hR m hfin hsupp hm hfac0
  exact norm_logDeriv_g_le_strip hR hc2 hRlt himc D hf_cont hg_cont hg_dcc hg_ne hfg0 hz₀
