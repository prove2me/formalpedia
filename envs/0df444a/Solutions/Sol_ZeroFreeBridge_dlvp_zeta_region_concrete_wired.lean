-- Prove2me | solution 1 for ZeroFreeBridge.dlvp_zeta_region_concrete_wired
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:09:41.710355+00:00
-- url     : https://prove2.me/submissions/5cfea72c-fe07-447c-bfa9-c004a9296a22

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_dlvp_region_bound
import Theorems.Thm_ZeroFreeBridge_dlvp_region_gap
import Theorems.Thm_ZeroFreeBridge_hbc1_from_bounds
import Theorems.Thm_ZeroFreeBridge_htwo_shape_of_bc_sum
import Theorems.Thm_ZeroFreeBridge_hzero_shape_of_bc_sum
import Theorems.Thm_ZeroFreeBridge_sum_divisor_recenter_le_finsum
import Theorems.Thm_ZeroFreeBridge_zeta_logDeriv_comb_nonneg
import Theorems.Thm_ZeroFreeBridge_zeta_recentered_canonical_decomp
import Theorems.Thm_ZeroFreeBridge_zeta_zero_re_lt
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


/- PHASE 4 (dVP frontier, entire-part PLUMBING): the two mechanical lemmas that connect the
   interior-point bound (`DlvpBCDerivInterior`) to the Blaschke BC-SUM (`bc_sum_blaschke`).

   (a) `norm_logDeriv_le_of_sphere_log_norm_le_interior` — the interior entire-part bound driven by a
       SPHERE oscillation bound (not the whole ball): `log‖g‖ = Re(log g)` is harmonic, so a boundary
       bound propagates to the disk by maximum modulus (`DlvpMaxMod.norm_le_on_ball_of_sphere`, via
       `exp`), and the resulting ball bound feeds `norm_logDeriv_le_of_log_norm_le_interior`.  This is
       exactly the shape available for ζ's Blaschke `g`, whose boundary `log‖g‖` equals `log‖ζ‖`
       (Blaschke factors have modulus 1 on the sphere).

   (b) `logDeriv_comp_const_add` — the RECENTRING: `bc_sum_blaschke` lives on `ball 0 R`, so ζ enters as
       `f(w) = ζ(c + w)`; its log-derivative is ζ's, shifted: `logDeriv (fun w => ζ(c+w)) z =
       logDeriv ζ (c+z)` (chain rule, `deriv (c+·) = 1`).

   conjecture1_proved = False (NOT a proof of RH).
-/



open Complex Metric

namespace ZeroFreeBridge



/-- **(b) Recentring the log-derivative.**  `logDeriv (fun w => f (c + w)) z = logDeriv f (c + z)`
    (chain rule; `deriv (c + ·) = 1`).  Sends ζ's log-derivative into `bc_sum_blaschke`'s `ball 0 R`
    coordinates. -/
theorem logDeriv_comp_const_add (f : ℂ → ℂ) (c z : ℂ) (hf : DifferentiableAt ℂ f (c + z)) :
    logDeriv (fun w => f (c + w)) z = logDeriv f (c + z) := by
  have hg : DifferentiableAt ℂ (fun w => c + w) z := by fun_prop
  have := logDeriv_comp hf hg
  simp only [Function.comp_def] at this
  rw [this]
  simp

end ZeroFreeBridge


/- PHASE 4 (core): the quantitative de la Vallee Poussin estimate for the zero-free REGION,
   conditional on the Borel-Caratheodory-derived log-derivative bounds.

   From the 3-4-1 positivity `zeta_logDeriv_comb_nonneg` and the three analytic bounds
     -Re(ζ'/ζ)(σ)      ≤ 1/(σ-1) + A       (simple pole at s = 1),
     -Re(ζ'/ζ)(σ+iγ)   ≤ A·L - k/(σ-β)     (a zero of order k ≥ 1 at β+iγ; L ~ log|γ|),
     -Re(ζ'/ζ)(σ+2iγ)  ≤ A·L               (no forced pole),
   the pole contribution of the zero must beat the log-size background:
     4·(k/(σ-β)) ≤ 3/(σ-1) + 3A + 5·A·L.
   Choosing σ = 1 + c/L then forces β ≤ 1 - c'/L -- the classical zero-free region (the next step).

   The three bounds are the genuine analytic frontier (Borel-Caratheodory applied to `log ζ` on a
   disk, fed by the crude strip bound `zeta_strip_bound`); they are ISOLATED here as explicit
   hypotheses, exactly as `zeta_boundary_contradiction` isolates its residue limits.  This lemma is
   the exact real-inequality CORE that turns them into the region.  It improves the region CONSTANT
   only (the 3-4-1 cosine cone is Fejer-capped), NOT the Vinogradov-Korobov rate, and is NOT a proof
   of RH.  conjecture1_proved = False.
-/


namespace ZeroFreeBridge

/-- de la Vallee Poussin CORE ESTIMATE (conditional on the log-derivative bounds).  Given the 3-4-1
    positivity and the pole/zero/double bounds on `-Re(ζ'/ζ)`, the order-`k` zero at `β+iγ` must
    satisfy `4·(k/(σ-β)) ≤ 3/(σ-1) + 3A + 5·A·L`.  See the file header for how this yields the
    region on optimizing `σ = 1 + c/L`. -/
theorem dlvp_core_estimate (σ t β : ℝ) (k : ℤ) (A L : ℝ) (hσ : 1 < σ)
    (hpole : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A)
    (hzero : (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤ A * L - (k : ℝ) / (σ - β))
    (htwo : (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re ≤ A * L) :
    (4 : ℝ) * ((k : ℝ) / (σ - β)) ≤ 3 / (σ - 1) + 3 * A + 5 * (A * L) := by
  have hpos := zeta_logDeriv_comb_nonneg σ t hσ
  rw [show (3 : ℝ) / (σ - 1) = 3 * (1 / (σ - 1)) by ring]
  linarith [hpos, hpole, hzero, htwo]



end ZeroFreeBridge


/- PHASE 4 (dVP frontier, rungs 3-5): the pole bound `hpole`, the double bound `htwo`,
   and the REGION ASSEMBLY.

   `dlvp_core_estimate` (ZeroFreeRegion.lean) is conditional on three bounds on `-Re(ζ'/ζ)`;
   `DlvpZeroSum.lean` (rung 1) reduced `hzero` to a Herglotz/Borel-Caratheodory sum bound.
   This file reduces the other two and assembles the region:

   * `hpole` — the pole term `1/(s-1)` at REAL argument σ is exactly `1/(σ-1)`
     (`re_inv_sub_one_at_real`); off-axis it is bounded by `1/(σ-1)` and nonneg
     (`re_inv_sub_one_le`, `re_inv_sub_one_nonneg`).  `hpole_of_partialfraction` reduces
     the conditional `hpole` to the partial-fraction bound.
   * `htwo` — the zero sum is NONNEGATIVE (`sum_re_inv_sub_nonneg`, via rung 1's per-term
     lemma), so it drops (`htwo_of_bound`), leaving the `A·L` background.
   * `dlvp_region_of_bc_inputs` — chains rungs 1/3/4 into `dlvp_core_estimate` then
     `dlvp_region_gap`, so the WHOLE de la Vallee Poussin region reduces to the three
     Borel-Caratheodory inputs (the pole partial-fraction bound + the two Herglotz/BC sum
     bounds).  The sole remaining analytic frontier is BC-SUM itself (rung 2).

   Improves the region CONSTANT only; NOT a proof of RH.  conjecture1_proved = False.
-/



open Complex

namespace ZeroFreeBridge

/-! ### Rung 3 — the pole term `1/(s-1)` -/

/-- At a REAL argument σ the pole term is real: `Re(1/((σ:ℂ)-1)) = 1/(σ-1)`. -/
theorem re_inv_sub_one_at_real (σ : ℝ) :
    (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
  have h : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h, show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div, Complex.ofReal_re]





/-- REDUCTION rung 3 (`hpole`): the pole bound of `dlvp_core_estimate` follows from the
    partial-fraction bound `-Re(ζ'/ζ)(σ) ≤ Re(1/(σ-1)) + A` by evaluating the pole term at
    the real argument. -/
theorem hpole_of_partialfraction (σ A : ℝ)
    (hbound : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
              ≤ (1 / ((σ : ℂ) - 1)).re + A) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A := by
  rwa [re_inv_sub_one_at_real σ] at hbound

/-! ### Rung 4 — the double bound `htwo` (drop the nonnegative zero sum) -/



/-- REDUCTION rung 4 (`htwo`): dropping a nonnegative remainder from the Borel-Caratheodory
    bound at height `2γ` leaves the `A·L` background. -/
theorem htwo_of_bound (x AL rest : ℝ) (hrest : 0 ≤ rest) (h : x ≤ AL - rest) : x ≤ AL := by
  linarith

/-! ### Rung 5 — the region assembly from the three Borel-Caratheodory inputs -/

/-- **REGION ⟸ Borel-Caratheodory inputs.**  Given the three inputs the analytic frontier
    must supply — the partial-fraction pole bound (`hpole_pf`, reduced by rung 3), the
    reduced Herglotz zero bound at height `t` (`hzero`, the output of rung 1's
    `hzero_of_herglotz`), and the Borel-Caratheodory bound at height `2t` (`htwo_bc`,
    nonnegative rest dropped by rung 4) — the cleared de la Vallee Poussin region gap
    follows, via `dlvp_core_estimate` → `dlvp_region_gap`.  Composed with rung 1, the WHOLE
    region reduces to producing those bounds, i.e. to BC-SUM (rung 2). -/
theorem dlvp_region_of_bc_inputs (σ t β A L : ℝ) (k : ℤ)
    (hk : 1 ≤ k) (hσ : 1 < σ) (hβσ : β < σ)
    (hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
                ≤ (1 / ((σ : ℂ) - 1)).re + A)
    (hzero : (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
              ≤ A * L - (k : ℝ) / (σ - β))
    (rest₂ : ℝ) (hr₂ : 0 ≤ rest₂)
    (htwo_bc : (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                  / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re
                ≤ A * L - rest₂) :
    (σ - 1) * (1 - (σ - 1) * (3 * A + 5 * (A * L)))
      ≤ (1 - β) * (3 + (σ - 1) * (3 * A + 5 * (A * L))) := by
  have hpole := hpole_of_partialfraction σ A hpole_pf
  have htwo := htwo_of_bound _ (A * L) rest₂ hr₂ htwo_bc
  have hcore := dlvp_core_estimate σ t β k A L hσ hpole hzero htwo
  have hcore' : (4 : ℝ) * ((k : ℝ) / (σ - β))
      ≤ 3 / (σ - 1) + (3 * A + 5 * (A * L)) := by linarith [hcore]
  exact dlvp_region_gap σ β A L k hk hσ hβσ hcore'

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


/- PHASE 4 (dVP frontier, final-assembly foundation atoms): reusable helpers that cut the boilerplate
   of the capstone `dlvp_zeta_region_of_bc_sums` instantiation for c₀=2+iγ (and c₁=2+2iγ).

   Every downstream analyticity hypothesis derives from ONE atom, `zeta_recenter_ana_closedBall`
   (recentred ζ analytic on `closedBall 0 R`): `hf_ana` = `.mono ball_subset_closedBall`, sphere
   continuity = `.mono sphere_subset_closedBall |>.continuousOn`, `hf'_mero` = `.meromorphicOn`; and
   `hf_ana_cl`/`hf_mero` on the physical disk = `zeta_analyticOnNhd_disk` directly.  The `1∉closedBall`
   precondition is `one_notMem_closedBall_of_himc` (from `R+2 ≤ |c₀.im|`).  conjecture1_proved = False.
-/

open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- `1 ∉ closedBall c₀ R` from `R + 2 ≤ |c₀.im|` (the height dominates the radius). -/
theorem one_notMem_closedBall_of_himc {c₀ : ℂ} {R : ℝ} (himc : R + 2 ≤ |c₀.im|) :
    (1 : ℂ) ∉ closedBall c₀ R := by
  rw [mem_closedBall, Complex.dist_eq]
  intro hle
  have h3 : |((1 : ℂ) - c₀).im| = |c₀.im| := by
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  have h4 : |((1 : ℂ) - c₀).im| ≤ ‖(1 : ℂ) - c₀‖ := Complex.abs_im_le_norm _
  rw [h3] at h4; linarith

/-- **The recentred-ζ closed-ball analyticity atom.**  `fun w => ζ(c₀+w)` is `AnalyticOnNhd` on
    `closedBall 0 R` when `1 ∉ closedBall c₀ R`.  Foundation from which every downstream analyticity
    (`hf_ana` on the ball, sphere continuity, `hf'_mero`) derives by `.mono`/`.meromorphicOn`. -/
theorem zeta_recenter_ana_closedBall (c₀ : ℂ) (R : ℝ) (h1 : (1 : ℂ) ∉ closedBall c₀ R) :
    AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (closedBall 0 R) := by
  have hshift : AnalyticOnNhd ℂ (fun w => c₀ + w) (closedBall 0 R) :=
    fun z _ => analyticAt_const.add analyticAt_id
  have hmaps : Set.MapsTo (fun w => c₀ + w) (closedBall (0 : ℂ) R) (closedBall c₀ R) := by
    intro w hw
    rw [mem_closedBall, Complex.dist_eq] at hw
    rw [mem_closedBall, Complex.dist_eq, add_sub_cancel_left]; simpa using hw
  exact (zeta_analyticOnNhd_disk c₀ R h1).comp hshift hmaps

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the LHS recentring bridge): connect `bc_sum_blaschke`'s output form
   `(-(logDeriv f z)).re` (with `f = ζ(c₀+·)` the recentred ζ) to the `(-deriv ζ w / ζ w).re` form that
   the region skeleton (`DlvpPole.dlvp_region_of_bc_inputs`, `DlvpZetaRegion.dlvp_zeta_region`) consumes.

   `logDeriv (fun w => ζ(c₀+w)) z = logDeriv ζ (c₀+z)` (`DlvpEntirePlumbing.logDeriv_comp_const_add`), and
   `logDeriv ζ w = deriv ζ w / ζ w` by definition, with `-(a/b) = -a/b`.  So the recentred BC-SUM's
   left-hand side is exactly the skeleton's.  This is the last piece of connective tissue between the
   Blaschke BC-SUM and the region skeleton (the remaining work is the Herglotz-sum reindexing, whose
   VALUE is recentring-invariant since `(z-c₀)-(ρ-c₀) = z-ρ`).  conjecture1_proved = False (NOT RH).
-/


open Complex

namespace ZeroFreeBridge

/-- **LHS recentring.**  The recentred log-derivative real part equals the skeleton's `-Re(ζ'/ζ)` at the
    shifted point: `(-(logDeriv (fun w => ζ(c₀+w)) z)).re = (-deriv ζ (c₀+z) / ζ (c₀+z)).re`. -/
theorem neg_logDeriv_zeta_recenter_re (c₀ z : ℂ)
    (hf : DifferentiableAt ℂ riemannZeta (c₀ + z)) :
    (-(logDeriv (fun w => riemannZeta (c₀ + w)) z)).re
      = (-deriv riemannZeta (c₀ + z) / riemannZeta (c₀ + z)).re := by
  rw [logDeriv_comp_const_add riemannZeta c₀ z hf]
  simp only [logDeriv, Pi.div_apply, neg_div]

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the REGION CAPSTONE): the de la Vallée Poussin zero-free region
   `β ≤ 1 - c/(A·L)` from the three Borel–Carathéodory inputs, at the OPTIMAL width `σ - 1 = 1/(2B)`.

   `DlvpPole.dlvp_region_of_bc_inputs` turns the three inputs (pole `hpole_pf`, zero-height `hzero`,
   double-height `htwo_bc`) at a width `σ > 1` into the cleared region GAP.  `DlvpRegionBound.
   dlvp_region_bound` optimizes the gap at `σ - 1 = 1/(2B)`, `B = 3A + 5AL`, into `β ≤ 1 - 1/(112 A L)`.
   This capstone chains them: it is the dVP region theorem, reduced to the three BC inputs (which
   `bc_sum_blaschke` + the Herglotz lower bound + the interior entire-part bound + rung 3 supply).

   conjecture1_proved = False (NOT a proof of RH — the region constant is improved from the polylog one).
-/



open Complex

namespace ZeroFreeBridge

/-- **The de la Vallée Poussin region, from the three BC inputs.**  At the optimal width
    `σ - 1 = 1/(2B)` (`B = 3A + 5AL`), the pole / zero-height / double-height Borel–Carathéodory bounds
    on `-Re(ζ'/ζ)` force the zero `β = Re ρ₀` off the line by `β ≤ 1 - 1/(112·A·L)` (`= 1 - c/log|t|`). -/
theorem dlvp_zeta_region (σ A L β t : ℝ) (k : ℤ) (hA : 0 < A) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hσ_opt : σ - 1 = 1 / (2 * (3 * A + 5 * (A * L)))) (hβσ : β < σ)
    (hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
                ≤ (1 / ((σ : ℂ) - 1)).re + A)
    (hzero : (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
              ≤ A * L - (k : ℝ) / (σ - β))
    (rest₂ : ℝ) (hr₂ : 0 ≤ rest₂)
    (htwo_bc : (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                  / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re
                ≤ A * L - rest₂) :
    β ≤ 1 - 1 / (112 * (A * L)) := by
  have hAL : 0 < A * L := mul_pos hA (by linarith)
  have hBpos : 0 < 3 * A + 5 * (A * L) := by nlinarith
  have hδpos : 0 < σ - 1 := by rw [hσ_opt]; positivity
  have hσ1 : 1 < σ := by linarith
  -- the region gap from the three BC inputs
  have hgap := dlvp_region_of_bc_inputs σ t β A L k hk hσ1 hβσ hpole_pf hzero rest₂ hr₂ htwo_bc
  -- the optimal choice δ = σ - 1 = 1/(2B) makes δ·B = 1/2
  have hδB : (σ - 1) * (3 * A + 5 * (A * L)) = 1 / 2 := by rw [hσ_opt]; field_simp
  exact dlvp_region_bound A L β (σ - 1) hA hL hδpos hδB hgap

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the downstream BRIDGE): turn `bc_sum_blaschke`'s recentred output into the
   region skeleton's `hzero` input, entirely by composition of already-built lemmas.

   `bc_sum_blaschke` gives (for `f = ζ(c₀+·)`, recentred eval point `zr = (σ+γI) - c₀`)
     `-Re(logDeriv f zr) ≤ AL - Re(Σ_u divisor f (ball 0 R) u /(zr - u))`.
   `herglotz_sum_reindex` rewrites the sum to the ORIGINAL-coordinate Herglotz sum
     `Σ_ρ divisor ζ (ball c₀ R) ρ /((σ+γI) - ρ)`; `neg_logDeriv_zeta_recenter_re` rewrites the left side
   to `-deriv ζ (σ+γI)/ζ(σ+γI)`; `hzero_of_blaschke` (the Herglotz lower bound) then delivers the
   `hzero` shape `-Re(ζ'/ζ)(σ+γI) ≤ AL - k/(σ-β)` that `DlvpZetaRegion.dlvp_zeta_region` consumes.

   conjecture1_proved = False (NOT a proof of RH).
-/





open Complex MeromorphicOn

namespace ZeroFreeBridge





/-- **The de la Vallée Poussin region for ζ, from the two Blaschke BC-SUM outputs + the pole bound.**
    Assembles `hzero_shape_of_bc_sum` (height γ), `htwo_shape_of_bc_sum` (height 2γ), and the rung-3
    pole bound `hpole_pf` at the optimal width `σ - 1 = 1/(2B)` into `β ≤ 1 - 1/(112·A·L)`. -/
theorem dlvp_zeta_region_of_bc_sums (c₀ : ℂ) (σ A L β γ : ℝ) (k : ℤ) (R : ℝ)
    (hA : 0 < A) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hσ_opt : σ - 1 = 1 / (2 * (3 * A + 5 * (A * L)))) (hβσ : β < σ)
    (hf_mero : MeromorphicOn riemannZeta (Metric.ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R))
    (hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
                ≤ (1 / ((σ : ℂ) - 1)).re + A)
    -- height-γ inputs (hzero)
    (s₁ : Finset ℂ) (hs₁_dom : ∀ u ∈ s₁, u ∈ Metric.ball (0 : ℂ) R ∧ c₀ + u ∈ Metric.ball c₀ R)
    (hcz₁ : c₀ + ((σ : ℂ) + (γ : ℂ) * I - c₀) = (σ : ℂ) + (γ : ℂ) * I)
    (hdiff₁ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (γ : ℂ) * I))
    (hbc₁ : (-(logDeriv (fun w => riemannZeta (c₀ + w)) ((σ : ℂ) + (γ : ℂ) * I - c₀))).re
             ≤ A * L - (∑ u ∈ s₁,
                 (divisor (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R) u : ℂ)
                   / (((σ : ℂ) + (γ : ℂ) * I - c₀) - u)).re)
    (hm₁ : ∀ ρ ∈ s₁.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (Metric.ball c₀ R) ρ)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ s₁.image (fun u => c₀ + u)) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I)
    (hmρ₀ : divisor riemannZeta (Metric.ball c₀ R) ρ₀ = k)
    (hother₁ : ∀ ρ ∈ s₁.image (fun u => c₀ + u), ρ ≠ ρ₀ → ρ.re < σ)
    -- height-2γ inputs (htwo)
    (s₂ : Finset ℂ) (hs₂_dom : ∀ u ∈ s₂, u ∈ Metric.ball (0 : ℂ) R ∧ c₀ + u ∈ Metric.ball c₀ R)
    (hcz₂ : c₀ + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
    (hdiff₂ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I))
    (hbc₂ : (-(logDeriv (fun w => riemannZeta (c₀ + w))
                ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀))).re
             ≤ A * L - (∑ u ∈ s₂,
                 (divisor (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R) u : ℂ)
                   / (((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) - u)).re)
    (hm₂ : ∀ ρ ∈ s₂.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (Metric.ball c₀ R) ρ)
    (hlt₂ : ∀ ρ ∈ s₂.image (fun u => c₀ + u), ρ.re < σ) :
    β ≤ 1 - 1 / (112 * (A * L)) := by
  have hzero := hzero_shape_of_bc_sum c₀ σ γ β (A * L) k R hf_mero hf'_mero s₁ hs₁_dom hcz₁ hdiff₁
    hbc₁ hm₁ ρ₀ hρ₀ hρ₀_eq hmρ₀ hother₁
  have htwo := htwo_shape_of_bc_sum c₀ σ γ (A * L) R hf_mero hf'_mero s₂ hs₂_dom hcz₂ hdiff₂
    hbc₂ hm₂ hlt₂
  exact dlvp_zeta_region σ A L β γ k hA hL hk hσ_opt hβσ hpole_pf hzero 0 le_rfl (by simpa using htwo)

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 3 — concrete-instantiation ring/geometry facts): the mechanical
   hypotheses of `dlvp_zeta_region_of_canonical_decomp` for the concrete centre `c₀ = 2 + iγ` and
   evaluation point `σ + iγ`.

   With the analytic inputs all in place (CanonicalDecomp, `norm_logDeriv_g_le_strip`,
   `zeta_zero_count_strip`, `hAL_arith`, `g_sphere_log_osc_strip`), the region theorem's remaining
   hypotheses at `c₀ = 2 + iγ` are pure ring/geometry/arithmetic:

     * `hcz`   `c₀ + ((σ+iγ) - c₀) = σ+iγ`                         (c₀ cancels; `ring`);
     * `hz`    `(σ+iγ) - c₀ ∈ ball 0 R`                            (`‖σ-2‖ = 2-σ < R`);
     * `hzne`  eval point is not a shifted zero                    (ζ(σ+iγ) ≠ 0, `Re = σ > 1`);
     * `hβσ`   `β < σ`                                             (`σ > 1 > β`).

   These discharge the geometric/algebraic side of the concrete instantiation.
   conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric MeromorphicOn

namespace ZeroFreeBridge

section Concrete
variable (σ γ R : ℝ)

/-- `hcz`: `c₀ + ((σ+iγ) - c₀) = σ+iγ` at `c₀ = 2+iγ` (the centre cancels). -/
theorem concrete_hcz :
    ((2 : ℂ) + (γ : ℂ) * I) + ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))
      = (σ : ℂ) + (γ : ℂ) * I := by ring











end Concrete
end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 4 — zero location): every ζ-zero in the disk has `Re < σ` (`σ > 1`),
   which discharges the `hother`/`hlt` hypotheses of `dlvp_zeta_region_of_canonical_decomp`.

   A point `ρ` in the divisor support of ζ is a zero (`divisor ≠ 0` ⟹ `analyticOrderAt ≠ 0` ⟹ `ζ ρ = 0`,
   using `AnalyticOnNhd.divisor_apply` + `apply_eq_zero_of_analyticOrderAt_ne_zero`), and ζ has no zeros
   with `Re ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`), so `Re ρ < 1 < σ`.  conjecture1_proved = False.
-/



open Complex MeromorphicOn Metric

namespace ZeroFreeBridge



/-- **ζ divisor is nonnegative on the disk** (no poles there — `hm`). -/
theorem zeta_divisor_nonneg {c₀ : ℂ} {R : ℝ} (h1 : (1 : ℂ) ∉ closedBall c₀ R) (ρ : ℂ) :
    0 ≤ divisor riemannZeta (ball c₀ R) ρ := by
  have hana : AnalyticOnNhd ℂ riemannZeta (ball c₀ R) :=
    (zeta_analyticOnNhd_disk c₀ R h1).mono ball_subset_closedBall
  exact hana.divisor_nonneg ρ

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the CAPSTONE WIRING): the concrete instantiation of
   `dlvp_zeta_region_of_bc_sums` for an actual ζ-zero `ρ₀ = β+iγ` (`β < 1`).

   This discharges — internally, for the two disks `c₀ = 2+iγ` (height γ) and `c₁ = 2+2iγ`
   (height 2γ) — every hypothesis of the lower-layer region theorem EXCEPT the pole bound and the
   two O(L) numeric constraints:
     * both `CanonicalDecomp`s (`zeta_recentered_canonical_decomp`), analyticity bundles
       (`zeta_recenter_ana_closedBall`/`.mono`), and `MeromorphicOn`s;
     * `hbc₁` (height γ) via `hbc1_from_bounds` fed by the abstract `Bg₁`/`C₁` bounds
       (`hgb₁`, `hC₁` via `sum_divisor_recenter_le_finsum`);
     * `hbc₂` (height 2γ) via the PARALLEL `c₁`-disk `hbc1_from_bounds`, dropped to `A·L` with
       `htwo_shape_of_bc_sum` and recentred to the `c₀` form (`neg_logDeriv_zeta_recenter_re`),
       with `s₂ = ∅`;
     * the divisor/geometry data for the concrete zero (`divisor_comp_const_add_apply`,
       `zeta_zero_re_lt`, `zeta_divisor_nonneg`).

   The remaining inputs — the pole bound `hpole_pf` (via `hpole_bounded`, needs `σ` near 1) and the
   two numeric couplings `hnum₁`/`hnum₂` (`C/(R-‖z₀‖) + Bg ≤ A·L`, with `Bg = O(L)` from
   `hg_bound_gamma` and `C = O(L)` from `sum_divisor_recenter_le_jensen`) — are taken as clean
   hypotheses here: they are the numeric-coupling crux, isolated for a dedicated closing lemma.
   `Bg₁`/`C₁`/`Bg₂`/`C₂` are abstracted so the caller supplies the explicit O(L) values.

   conjecture1_proved = False (NOT a proof of RH — this is a REDUCTION).
-/









open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution
    (σ A L β γ : ℝ) (k : ℤ) (R : ℝ) (Bg₁ C₁ Bg₂ C₂ : ℝ)
    (hA : 0 < A) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hσ_opt : σ - 1 = 1 / (2 * (3 * A + 5 * (A * L))))
    (hβ1 : β < 1) (hσ2 : σ ≤ 2)
    (hR : 0 < R) (hβR : 2 - β < R) (himc0 : R + 2 ≤ |γ|)
    (hmρ₀ : divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) R) ((β : ℂ) + (γ : ℂ) * I) = k)
    (hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
                ≤ (1 / ((σ : ℂ) - 1)).re + A)
    (hgb₁ : ∀ g : ℂ → ℂ,
        CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) g R →
        ‖logDeriv g ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))‖ ≤ Bg₁)
    (hC₁ : ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + (γ : ℂ) * I) R) ρ : ℤ) : ℝ) ≤ C₁)
    (hnum₁ : C₁ / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖) + Bg₁ ≤ A * L)
    (hgb₂ : ∀ g : ℂ → ℂ,
        CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) g R →
        ‖logDeriv g ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I))‖ ≤ Bg₂)
    (hC₂ : ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) ρ : ℤ) : ℝ)
             ≤ C₂)
    (hnum₂ : C₂ / (R - ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖) + Bg₂
             ≤ A * L) :
    β ≤ 1 - 1 / (112 * (A * L)) := by
  -- basic derived scalar facts
  have hden : (0 : ℝ) < 2 * (3 * A + 5 * (A * L)) := by
    have : (0 : ℝ) < A * L := mul_pos hA (by linarith)
    nlinarith [hA]
  have hσ1 : 1 < σ := by
    have : 0 < σ - 1 := by rw [hσ_opt]; exact div_pos one_pos hden
    linarith
  have hR1 : 1 < R := by linarith
  have hσR : 2 - σ < R := by linarith
  have hβσ : β < σ := by linarith
  -- centre real/imag parts
  have hc0re : ((2 : ℂ) + (γ : ℂ) * I).re = 2 := by simp
  have hc0im : ((2 : ℂ) + (γ : ℂ) * I).im = γ := by simp
  have hc1re : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re = 2 := by simp
  have hc1im : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).im = 2 * γ := by simp
  -- 1 ∉ the two closed balls
  have h1c0 : (1 : ℂ) ∉ closedBall ((2 : ℂ) + (γ : ℂ) * I) R :=
    one_notMem_closedBall_of_himc (by rw [hc0im]; exact himc0)
  have h1c1 : (1 : ℂ) ∉ closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R := by
    refine one_notMem_closedBall_of_himc ?_
    rw [hc1im]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    have : |γ| ≤ |2 * γ| := by rw [abs_mul, h2]; nlinarith [abs_nonneg γ]
    linarith
  have hc0lt : (1 : ℝ) < ((2 : ℂ) + (γ : ℂ) * I).re := by rw [hc0re]; norm_num
  have hc1lt : (1 : ℝ) < ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re := by rw [hc1re]; norm_num
  -- ζ ≠ 1 differentiability points
  have hev0_re : ((σ : ℂ) + (γ : ℂ) * I).re = σ := by simp
  have hev1_re : ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re = σ := by simp
  have hdiff₁ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (γ : ℂ) * I) := by
    refine differentiableAt_riemannZeta ?_
    intro h; have := congrArg Complex.re h; rw [hev0_re] at this; simp at this; linarith
  have hdiff₂ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) := by
    refine differentiableAt_riemannZeta ?_
    intro h; have := congrArg Complex.re h; rw [hev1_re] at this; simp at this; linarith
  -- ============ c₀ disk bundle (height γ) ============
  obtain ⟨g₀, D₀⟩ := zeta_recentered_canonical_decomp ((2 : ℂ) + (γ : ℂ) * I) R hR h1c0 hc0lt
  have hana0 : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w))
      (closedBall 0 R) := zeta_recenter_ana_closedBall _ R h1c0
  have hf_ana0 : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) :=
    hana0.mono ball_subset_closedBall
  have hζ_ana_cl0 : AnalyticOnNhd ℂ riemannZeta (closedBall ((2 : ℂ) + (γ : ℂ) * I) R) :=
    zeta_analyticOnNhd_disk _ R h1c0
  have hf_mero0 : MeromorphicOn riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) R) :=
    MeromorphicOn.mono_set (hζ_ana_cl0.meromorphicOn) ball_subset_closedBall
  have hf'_mero0 : MeromorphicOn (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) :=
    hf_ana0.meromorphicOn
  have hg_ana0 := canonicalDecomp_analyticOnNhd D₀
  have hg_ne0 := canonicalDecomp_ne_zero D₀
  have hfin0 : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u))).Finite := by
    simpa [Function.support_neg] using D₀.meromorphicOn.divisor_ball_support_finite
  have heval_ne0 : riemannZeta (((2 : ℂ) + (γ : ℂ) * I)
      + ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))) ≠ 0 := by
    rw [concrete_hcz]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hev0_re]; linarith)
  -- count bound for c₀
  have hcount₁ : (∑ u ∈ hfin0.toFinset,
      (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℝ)) ≤ C₁ := by
    have hZ := sum_divisor_recenter_le_finsum hf_mero0 hf'_mero0 hζ_ana_cl0 hfin0
    calc (∑ u ∈ hfin0.toFinset,
          (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℝ))
        = ((∑ u ∈ hfin0.toFinset,
            divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℤ) : ℝ) := by
          push_cast; ring
      _ ≤ ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + (γ : ℂ) * I) R) ρ : ℤ) : ℝ) := by
          exact_mod_cast hZ
      _ ≤ C₁ := hC₁
  -- height-γ hbc₁
  have hbc₁ := hbc1_from_bounds σ γ hR hσ1 hσ2 hσR g₀ D₀ hf_ana0 hg_ana0 hg_ne0 hfin0 heval_ne0
    (hgb₁ g₀ D₀) hcount₁ hnum₁
  -- domain facts for s₁
  have hs₁_dom : ∀ u ∈ hfin0.toFinset,
      u ∈ ball (0 : ℂ) R ∧ ((2 : ℂ) + (γ : ℂ) * I) + u ∈ ball ((2 : ℂ) + (γ : ℂ) * I) R := by
    intro u hu
    have hune : divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R)).supportWithinDomain
        (Function.mem_support.mpr hune)
    refine ⟨huball, ?_⟩
    rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
  have hm₁ : ∀ ρ ∈ hfin0.toFinset.image (fun u => ((2 : ℂ) + (γ : ℂ) * I) + u),
      0 ≤ divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) R) ρ :=
    fun ρ _ => zeta_divisor_nonneg h1c0 ρ
  -- ρ₀ membership + zero-location
  have hρ₀mem : (β : ℂ) + (γ : ℂ) * I
      ∈ hfin0.toFinset.image (fun u => ((2 : ℂ) + (γ : ℂ) * I) + u) := by
    have heq : (β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) = ((β - 2 : ℝ) : ℂ) := by
      push_cast; ring
    have hu0ball : (β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : β - 2 ≤ 0)]
      linarith
    have hρ₀ball : (β : ℂ) + (γ : ℂ) * I ∈ ball ((2 : ℂ) + (γ : ℂ) * I) R := by
      rw [mem_ball_iff_norm, heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : β - 2 ≤ 0)]
      linarith
    have hcadd : ((2 : ℂ) + (γ : ℂ) * I) + ((β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))
        = (β : ℂ) + (γ : ℂ) * I := by ring
    have hdivne : divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R)
        ((β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)) ≠ 0 := by
      rw [divisor_comp_const_add_apply _ hf_mero0 hf'_mero0 hu0ball (by rw [hcadd]; exact hρ₀ball),
        hcadd, hmρ₀]
      omega
    refine Finset.mem_image.mpr ⟨(β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I), ?_, by ring⟩
    rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero]; exact hdivne
  have hother₁ : ∀ ρ ∈ hfin0.toFinset.image (fun u => ((2 : ℂ) + (γ : ℂ) * I) + u),
      ρ ≠ (β : ℂ) + (γ : ℂ) * I → ρ.re < σ := by
    intro ρ hρ _
    rw [Finset.mem_image] at hρ
    obtain ⟨u, hu, rfl⟩ := hρ
    have hune : divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R)).supportWithinDomain
        (Function.mem_support.mpr hune)
    have hcuball : ((2 : ℂ) + (γ : ℂ) * I) + u ∈ ball ((2 : ℂ) + (γ : ℂ) * I) R := by
      rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
    have hdivρ : divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) R) (((2 : ℂ) + (γ : ℂ) * I) + u) ≠ 0 := by
      rw [← divisor_comp_const_add_apply _ hf_mero0 hf'_mero0 huball hcuball]; exact hune
    exact zeta_zero_re_lt hσ1 h1c0 hcuball hdivρ
  -- ============ c₁ disk bundle (height 2γ) ============
  obtain ⟨g₁, D₁⟩ := zeta_recentered_canonical_decomp ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R hR h1c1 hc1lt
  have hana1 : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
      (closedBall 0 R) := zeta_recenter_ana_closedBall _ R h1c1
  have hf_ana1 : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
      (ball 0 R) := hana1.mono ball_subset_closedBall
  have hζ_ana_cl1 : AnalyticOnNhd ℂ riemannZeta (closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) :=
    zeta_analyticOnNhd_disk _ R h1c1
  have hf_mero1 : MeromorphicOn riemannZeta (ball ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) :=
    MeromorphicOn.mono_set (hζ_ana_cl1.meromorphicOn) ball_subset_closedBall
  have hf'_mero1 : MeromorphicOn (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
      (ball 0 R) := hf_ana1.meromorphicOn
  have hg_ana1 := canonicalDecomp_analyticOnNhd D₁
  have hg_ne1 := canonicalDecomp_ne_zero D₁
  have hfin1 : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
        (ball 0 R) u))).Finite := by
    simpa [Function.support_neg] using D₁.meromorphicOn.divisor_ball_support_finite
  have heval_ne1 : riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
      + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I))) ≠ 0 := by
    rw [concrete_hcz]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hev1_re]; linarith)
  have hcount₂ : (∑ u ∈ hfin1.toFinset,
      (divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) (ball 0 R) u : ℝ))
        ≤ C₂ := by
    have hZ := sum_divisor_recenter_le_finsum hf_mero1 hf'_mero1 hζ_ana_cl1 hfin1
    calc (∑ u ∈ hfin1.toFinset,
          (divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) (ball 0 R) u : ℝ))
        = ((∑ u ∈ hfin1.toFinset,
            divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) (ball 0 R) u
              : ℤ) : ℝ) := by push_cast; ring
      _ ≤ ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) ρ : ℤ) : ℝ) := by
          exact_mod_cast hZ
      _ ≤ C₂ := hC₂
  -- c₁ BC-SUM
  have hbc_c1 := hbc1_from_bounds σ (2 * γ) hR hσ1 hσ2 hσR g₁ D₁ hf_ana1 hg_ana1 hg_ne1 hfin1
    heval_ne1 (hgb₂ g₁ D₁) hcount₂ hnum₂
  have hs₂_dom : ∀ u ∈ hfin1.toFinset,
      u ∈ ball (0 : ℂ) R ∧ ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + u
        ∈ ball ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R := by
    intro u hu
    have hune : divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) (ball 0 R) u
        ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
        (ball 0 R)).supportWithinDomain (Function.mem_support.mpr hune)
    refine ⟨huball, ?_⟩
    rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
  have hm_c1 : ∀ ρ ∈ hfin1.toFinset.image (fun u => ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + u),
      0 ≤ divisor riemannZeta (ball ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) ρ :=
    fun ρ _ => zeta_divisor_nonneg h1c1 ρ
  have hlt_c1 : ∀ ρ ∈ hfin1.toFinset.image (fun u => ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + u),
      ρ.re < σ := by
    intro ρ hρ
    rw [Finset.mem_image] at hρ
    obtain ⟨u, hu, rfl⟩ := hρ
    have hune : divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) (ball 0 R) u
        ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
        (ball 0 R)).supportWithinDomain (Function.mem_support.mpr hune)
    have hcuball : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + u
        ∈ ball ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R := by
      rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
    have hdivρ : divisor riemannZeta (ball ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R)
        (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + u) ≠ 0 := by
      rw [← divisor_comp_const_add_apply _ hf_mero1 hf'_mero1 huball hcuball]; exact hune
    exact zeta_zero_re_lt hσ1 h1c1 hcuball hdivρ
  -- c₁ height-2γ shape: Re(-ζ'/ζ(σ+2iγ)) ≤ A*L
  have hcz_c1 : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
      + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I))
      = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I := by ring
  have htwo := htwo_shape_of_bc_sum ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) σ γ (A * L) R
    hf_mero1 hf'_mero1 hfin1.toFinset hs₂_dom hcz_c1 hdiff₂ hbc_c1 hm_c1 hlt_c1
  -- convert htwo to the c₀-recentred hbc₂ form (s₂ = ∅)
  have hbc₂ : (-(logDeriv (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w))
        ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)))).re
      ≤ A * L - (∑ u ∈ (∅ : Finset ℂ),
          (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℂ)
            / (((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)) - u)).re := by
    rw [Finset.sum_empty, Complex.zero_re, sub_zero]
    have hdc0 : DifferentiableAt ℂ riemannZeta
        (((2 : ℂ) + (γ : ℂ) * I) + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))) := by
      rw [show ((2 : ℂ) + (γ : ℂ) * I) + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))
          = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I from by ring]
      exact hdiff₂
    rw [neg_logDeriv_zeta_recenter_re ((2 : ℂ) + (γ : ℂ) * I)
      ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)) hdc0,
      show ((2 : ℂ) + (γ : ℂ) * I) + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))
          = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I from by ring]
    exact htwo
  -- ============ final assembly ============
  have hcz₂ : ((2 : ℂ) + (γ : ℂ) * I)
      + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))
      = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I := by ring
  exact dlvp_zeta_region_of_bc_sums ((2 : ℂ) + (γ : ℂ) * I) σ A L β γ k R hA hL hk hσ_opt hβσ
    hf_mero0 hf'_mero0 hpole_pf
    hfin0.toFinset hs₁_dom (concrete_hcz σ γ) hdiff₁ hbc₁ hm₁ ((β : ℂ) + (γ : ℂ) * I) hρ₀mem rfl
    hmρ₀ hother₁
    (∅ : Finset ℂ) (by intro u hu; exact absurd hu (Finset.notMem_empty u)) hcz₂ hdiff₂ hbc₂
    (by intro ρ hρ; rw [Finset.image_empty] at hρ; exact absurd hρ (Finset.notMem_empty ρ))
    (by intro ρ hρ; rw [Finset.image_empty] at hρ; exact absurd hρ (Finset.notMem_empty ρ))
