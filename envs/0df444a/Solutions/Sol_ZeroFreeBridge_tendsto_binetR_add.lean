-- Prove2me | solution 1 for ZeroFreeBridge.tendsto_binetR_add
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:56:17.164779+00:00
-- url     : https://prove2.me/submissions/e3a41354-ff5d-4ad6-b851-2ffe7efa9f10

import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Mathlib
import Theorems.Thm_ZeroFreeBridge_gamma_hasDerivAt_ofReal
import Theorems.Thm_ZeroFreeBridge_tendsto_digamma_sub_log_one_add_nat
/- TURING RUNG T2, brick 1: the Riemann–Siegel theta function, defined BRANCH-CUT-FREE as the
   integral of an explicit real integrand (TURING_METHOD_SCOPING §3, rung T2).

   Classically `θ(t) = Im logΓ(1/4 + it/2) − (t/2)·log π` with a continuously-tracked branch of
   `logΓ` — awkward to formalize.  Instead we DEFINE

     `θ(t) := ∫_0^t ( (1/2)·Re ψ(1/4 + i·u/2) − (1/2)·log π ) du`,

   where `ψ = Complex.digamma = logDeriv Γ` (Mathlib).  This agrees with the classical `θ`
   (both vanish at `0` and have the same derivative `θ'(u) = (1/2)·Re ψ(1/4 + iu/2) − (1/2)·log π`)
   and needs NO branch tracking: the integrand is a plain continuous real function of `u`.

   This brick: the ray `1/4 + (u/2)·i` avoids all Γ-poles (`Re = 1/4 > 0`), Γ is ANALYTIC there
   (differentiable on the open right half-plane ⟹ analytic), `ψ` is continuous on the ray
   (`deriv Γ / Γ`, with `Γ ≠ 0` by `Gamma_ne_zero_of_re_pos`), hence the integrand is continuous,
   `θ` is well-defined with `θ(0) = 0` and `θ' = integrand` (FTC for continuous integrands).

   Later bricks (T2 cont.): effective two-sided bounds `θ(t) = (t/2)log(t/2π) − t/2 − π/8 +
   O*(explicit/t)` via Binet-type digamma estimates; then T3 wires `θ` into the rectangle
   argument identity `N(T) = θ(T)/π + 1 + S(T)`.

   conjecture1_proved = False. -/


open Complex

namespace ZeroFreeBridge























/-! ## Brick 2: the Archimedean bridge — `θ'` IS the `Gammaℝ` log-derivative on the critical line.

`Gammaℝ s = π^(-s/2)·Γ(s/2)` is the Archimedean factor of the completed zeta
(`Λ = Gammaℝ · ζ` up to the `s(s-1)` polynomial), the object the T3 rectangle identity
splits off of `logDeriv Λ`.  We compute `logDeriv Gammaℝ s = -(log π)/2 + (1/2)·ψ(s/2)`
on `Re(s/2) > 0` and specialize to the critical line `s = 1/2 + iu`, where `s/2 = thetaRay u`:
the θ integrand is EXACTLY `Re (logDeriv Gammaℝ (1/2 + iu))`.  This hard-wires the
branch-cut-free `θ` into the counting formula's Archimedean term. -/















/-! ## Brick 3a: the θ-asymptotics skeleton (T2 rung, first sub-brick).

Target (brick 3 complete): `θ(t) = (t/2)·log(t/(2π)) − t/2 − π/8 + O*(explicit/t)`.
This sub-brick ships the three UNCONDITIONAL pieces every derivation route needs:

  * `digamma_shift` — the iterated recursion `ψ(s+N) = ψ(s) + Σ_{k<N} (s+k)⁻¹` (from Mathlib's
    single-step `digamma_apply_add_one`), which moves the evaluation point right, where the
    Stirling comparison is easy;
  * `norm_inv_sub_log_one_add_inv_le` — the telescoping step bound
    `‖s⁻¹ − log(1+s⁻¹)‖ ≤ ‖s⁻¹‖²·(1−‖s⁻¹‖)⁻¹/2` (Mathlib `norm_log_one_add_sub_self_le`):
    the summand of the Binet-series `ψ(s) − log s = −Σ_{k≥0} [(s+k)⁻¹ − log(1+(s+k)⁻¹)] + …`
    is quadratically small, so the telescoped series converges with an explicit `O(1/‖s‖)` tail;
  * `thetaMain` + `thetaMain_hasDerivAt` — the main term and its derivative
    `(log(t/(2π)))/2`, matching `θ'`'s leading behaviour, so brick 3c can compare the two via
    FTC on `[t₀, t]`.

Remaining sub-bricks: 3b = sum the telescoped series (Summable + tail bound ⟹ effective
`|ψ(s) − log s| ≤ C/‖s‖` on `Re s ≥ 1`, plus the anchor `ψ(s+N) − log(s+N) → 0`); 3c = integrate
`θ' − thetaMain'` and fix the `−π/8` constant.  conjecture1_proved = False. -/













/-! ## Brick 3b: the telescoped Binet series — `|ψ(s) − log s| ≤ 1/(Re s − 1)` modulo the anchor.

Telescoping `d(s) = ψ(s) − log s` with `d(s+1) − d(s) = s⁻¹ − log(1+s⁻¹)` (branch-safe on
`Re s > 0` since `|arg| < π/2` on the right half-plane) gives the FINITE identity
`d(s) = d(s+N) − Σ_{k<N} [(s+k)⁻¹ − log(1+(s+k)⁻¹)]`; the 3a step bound + an elementary
inline telescoping estimate `Σ_{k<N} 1/(x+k)² ≤ 1/(x−1)` bound the sum UNIFORMLY in `N`;
letting `N → ∞` against the anchor `d(s+N) → 0` (the ONE remaining analytic input, carried as
an explicit hypothesis — brick 3b′ discharges it) yields the effective Binet bound.
conjecture1_proved = False. -/













/-! ## Brick 3b′-i: the INTEGER anchor — `ψ(1+N) − log(1+N) → 0`.

The first of the anchor's three sub-bricks (3b′ plan: (i) integer anchor via the Euler–Mascheroni
limit, (ii) real-axis sandwich via `ψ` monotonicity (log-convexity of `Γ`) killing the 1-periodic
ambiguity `L(s+1) = L(s)` on a full real interval, (iii) identity theorem
(`eqOn_of_preconnected_of_frequently_eq`, the corpus `DlvpTransfer` pattern) extending `L ≡ 0`
to all `Re s > 1`).  Here: `ψ(1+N) = −γ + H_N` (our `digamma_shift` at `s = 1` + Mathlib
`digamma_one`), so `ψ(1+N) − log(1+N) = −γ + (H_N − log(N+1)) → −γ + γ = 0` by Mathlib's
`Real.tendsto_harmonic_sub_log_add_one`.  conjecture1_proved = False. -/



/-! ## Brick 3b′-ii-a: `ψ` is REAL on the positive reals, equals `deriv (log ∘ Γ)`, and that
derivative is MONOTONE (log-convexity of `Γ`, Bohr–Mollerup).  These are the sandwich's two
pillars; 3b′-ii-b squeezes `ψ(x+N) − log(x+N) → 0` for real `x` between integer anchors. -/



/-- **`ψ` is real on the positive reals**, and equals `deriv (log ∘ Γ)` there:
    `ψ(x) = ↑(deriv (Real.log ∘ Real.Gamma) x)` for `0 < x`. -/
theorem digamma_ofReal_eq {x : ℝ} (hx : 0 < x) :
    Complex.digamma ((x : ℝ) : ℂ) = ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
  obtain ⟨d, hC, hR⟩ := gamma_hasDerivAt_ofReal hx
  have hΓpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hlog : HasDerivAt (Real.log ∘ Real.Gamma) ((Real.Gamma x)⁻¹ * d) x :=
    (Real.hasDerivAt_log hΓpos.ne').comp x hR
  rw [Complex.digamma_def, logDeriv_apply, hC.deriv, hlog.deriv, Complex.Gamma_ofReal]
  push_cast
  rw [div_eq_mul_inv, mul_comm]

/-- **The real digamma is monotone on `(0, ∞)`** — the derivative of the log-convex
    `log ∘ Γ` (Bohr–Mollerup `Real.convexOn_log_Gamma` + `ConvexOn.monotoneOn_deriv`).
    The sandwich pillar of the anchor's real-axis step. -/
theorem monotoneOn_deriv_log_Gamma :
    MonotoneOn (deriv (Real.log ∘ Real.Gamma)) (Set.Ioi (0 : ℝ)) := by
  refine Real.convexOn_log_Gamma.monotoneOn_deriv ?_
  intro x hx
  obtain ⟨d, _, hR⟩ := gamma_hasDerivAt_ofReal (Set.mem_Ioi.mp hx)
  exact ((Real.hasDerivAt_log
    (Real.Gamma_pos_of_pos (Set.mem_Ioi.mp hx)).ne').comp x hR).differentiableAt

/-! ## Brick 3b′-ii-b: the REAL-AXIS SQUEEZE — the anchor discharged on `[1, 3]`.

Sandwich `d(x+N) = ψ(x+N) − log(x+N)` for real `x ∈ [1,3]` between the integer-anchor
sequences: `ψ` monotone (pillar ii-a) gives `ψ(1+N) ≤ ψ(x+N) ≤ ψ(3+N)`; `log` monotone gives
the reverse for the log part; both outer sequences → 0 by the integer anchor (3b′-i, plus its
`N ↦ N+2` shift) and the vanishing log gap (`Real.tendsto_log_comp_add_sub_log`).  Squeeze ⟹
`d(x+N) → 0` for every real `x ∈ [1,3]` — the anchor hypothesis of
`norm_digamma_sub_log_le_of_anchor` is DISCHARGED on the real segment, yielding the first
UNCONDITIONAL effective Binet points (`norm_digamma_sub_log_le_ofReal`).  Brick (iii) extends
to complex `s` by the identity theorem.  conjecture1_proved = False. -/



/-- Pointwise complex-to-real identification: for `t > 0`,
    `ψ(↑t) − log ↑t = ↑(binetR t)`. -/
theorem digamma_sub_log_ofReal_eq {t : ℝ} (ht : 0 < t) :
    Complex.digamma ((t : ℝ) : ℂ) - Complex.log ((t : ℝ) : ℂ) = ((binetR t : ℝ) : ℂ) := by
  rw [digamma_ofReal_eq ht, ← Complex.ofReal_log ht.le, ← Complex.ofReal_sub]
  rfl

/-- **The real integer anchor:** `binetR (1+N) → 0` (real part of brick 3b′-i). -/
theorem tendsto_binetR_one_add : Filter.Tendsto (fun N : ℕ => binetR (1 + N))
    Filter.atTop (nhds 0) := by
  have h := (Complex.continuous_re.tendsto (0 : ℂ)).comp tendsto_digamma_sub_log_one_add_nat
  rw [Complex.zero_re] at h
  refine h.congr fun N => ?_
  show (Complex.digamma (1 + N) - Complex.log (1 + N)).re = binetR (1 + N)
  have hcast : (1 : ℂ) + (N : ℂ) = (((1 + N : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, digamma_sub_log_ofReal_eq (by positivity), Complex.ofReal_re]

/-- Shifted real anchor: `binetR (3+N) → 0` (the `N ↦ N+2` shift of the integer anchor). -/
theorem tendsto_binetR_three_add : Filter.Tendsto (fun N : ℕ => binetR (3 + N))
    Filter.atTop (nhds 0) := by
  have h := (Filter.tendsto_add_atTop_iff_nat (f := fun N : ℕ => binetR (1 + N))
    (l := nhds 0) 2).mpr tendsto_binetR_one_add
  refine h.congr fun N => ?_
  show binetR (1 + ↑(N + 2)) = binetR (3 + N)
  congr 1
  push_cast
  ring

/-- The log gap vanishes: `log(3+N) − log(1+N) → 0`. -/
theorem tendsto_log_gap : Filter.Tendsto
    (fun N : ℕ => Real.log (3 + N) - Real.log (1 + N)) Filter.atTop (nhds 0) := by
  have hn : Filter.Tendsto (fun N : ℕ => (1 + N : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
    push_cast
    linarith
  have h := (Real.tendsto_log_comp_add_sub_log 2).comp hn
  refine h.congr fun N => ?_
  show Real.log ((1 + N) + 2) - Real.log (1 + N) = Real.log (3 + N) - Real.log (1 + N)
  congr 2
  ring







/-! ## Brick 3b′-iii: the IDENTITY THEOREM — the anchor discharged for ALL `Re s ≥ 2`.

The limit function `binetLimit s := (ψ(s) − log s) + Σ′_k [(s+k)⁻¹ − log(1+(s+k)⁻¹)]` is the
`N → ∞` limit of `ψ(s+N) − log(s+N)` (partial sums = the telescoped Binet identity).  It is
HOLOMORPHIC on `U = {Re > 3/2}` (Weierstrass M-test: `‖tail_k‖ ≤ (3/2)/(3/2+k)²`, uniform on
`U`, summable by our own partial-sum lemma), and VANISHES on the real segment `[2,3]` (brick
ii-b's squeeze + uniqueness of limits).  The identity theorem on the convex half-plane then
forces `binetLimit ≡ 0` on all of `U` — so the anchor `ψ(s+N) − log(s+N) → 0` holds for EVERY
`s` with `Re s ≥ 2`, and the effective Binet bound `‖ψ(s) − log s‖ ≤ 1/(Re s − 1)` is
UNCONDITIONAL.  The analytic heart of Turing rung T2 is complete.
conjecture1_proved = False. -/

























end ZeroFreeBridge


/- TURING RUNG T2, brick 1: the Riemann–Siegel theta function, defined BRANCH-CUT-FREE as the
   integral of an explicit real integrand (TURING_METHOD_SCOPING §3, rung T2).

   Classically `θ(t) = Im logΓ(1/4 + it/2) − (t/2)·log π` with a continuously-tracked branch of
   `logΓ` — awkward to formalize.  Instead we DEFINE

     `θ(t) := ∫_0^t ( (1/2)·Re ψ(1/4 + i·u/2) − (1/2)·log π ) du`,

   where `ψ = Complex.digamma = logDeriv Γ` (Mathlib).  This agrees with the classical `θ`
   (both vanish at `0` and have the same derivative `θ'(u) = (1/2)·Re ψ(1/4 + iu/2) − (1/2)·log π`)
   and needs NO branch tracking: the integrand is a plain continuous real function of `u`.

   This brick: the ray `1/4 + (u/2)·i` avoids all Γ-poles (`Re = 1/4 > 0`), Γ is ANALYTIC there
   (differentiable on the open right half-plane ⟹ analytic), `ψ` is continuous on the ray
   (`deriv Γ / Γ`, with `Γ ≠ 0` by `Gamma_ne_zero_of_re_pos`), hence the integrand is continuous,
   `θ` is well-defined with `θ(0) = 0` and `θ' = integrand` (FTC for continuous integrands).

   Later bricks (T2 cont.): effective two-sided bounds `θ(t) = (t/2)log(t/2π) − t/2 − π/8 +
   O*(explicit/t)` via Binet-type digamma estimates; then T3 wires `θ` into the rectangle
   argument identity `N(T) = θ(T)/π + 1 + S(T)`.

   conjecture1_proved = False. -/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge























/-! ## Brick 2: the Archimedean bridge — `θ'` IS the `Gammaℝ` log-derivative on the critical line.

`Gammaℝ s = π^(-s/2)·Γ(s/2)` is the Archimedean factor of the completed zeta
(`Λ = Gammaℝ · ζ` up to the `s(s-1)` polynomial), the object the T3 rectangle identity
splits off of `logDeriv Λ`.  We compute `logDeriv Gammaℝ s = -(log π)/2 + (1/2)·ψ(s/2)`
on `Re(s/2) > 0` and specialize to the critical line `s = 1/2 + iu`, where `s/2 = thetaRay u`:
the θ integrand is EXACTLY `Re (logDeriv Gammaℝ (1/2 + iu))`.  This hard-wires the
branch-cut-free `θ` into the counting formula's Archimedean term. -/















/-! ## Brick 3a: the θ-asymptotics skeleton (T2 rung, first sub-brick).

Target (brick 3 complete): `θ(t) = (t/2)·log(t/(2π)) − t/2 − π/8 + O*(explicit/t)`.
This sub-brick ships the three UNCONDITIONAL pieces every derivation route needs:

  * `digamma_shift` — the iterated recursion `ψ(s+N) = ψ(s) + Σ_{k<N} (s+k)⁻¹` (from Mathlib's
    single-step `digamma_apply_add_one`), which moves the evaluation point right, where the
    Stirling comparison is easy;
  * `norm_inv_sub_log_one_add_inv_le` — the telescoping step bound
    `‖s⁻¹ − log(1+s⁻¹)‖ ≤ ‖s⁻¹‖²·(1−‖s⁻¹‖)⁻¹/2` (Mathlib `norm_log_one_add_sub_self_le`):
    the summand of the Binet-series `ψ(s) − log s = −Σ_{k≥0} [(s+k)⁻¹ − log(1+(s+k)⁻¹)] + …`
    is quadratically small, so the telescoped series converges with an explicit `O(1/‖s‖)` tail;
  * `thetaMain` + `thetaMain_hasDerivAt` — the main term and its derivative
    `(log(t/(2π)))/2`, matching `θ'`'s leading behaviour, so brick 3c can compare the two via
    FTC on `[t₀, t]`.

Remaining sub-bricks: 3b = sum the telescoped series (Summable + tail bound ⟹ effective
`|ψ(s) − log s| ≤ C/‖s‖` on `Re s ≥ 1`, plus the anchor `ψ(s+N) − log(s+N) → 0`); 3c = integrate
`θ' − thetaMain'` and fix the `−π/8` constant.  conjecture1_proved = False. -/













/-! ## Brick 3b: the telescoped Binet series — `|ψ(s) − log s| ≤ 1/(Re s − 1)` modulo the anchor.

Telescoping `d(s) = ψ(s) − log s` with `d(s+1) − d(s) = s⁻¹ − log(1+s⁻¹)` (branch-safe on
`Re s > 0` since `|arg| < π/2` on the right half-plane) gives the FINITE identity
`d(s) = d(s+N) − Σ_{k<N} [(s+k)⁻¹ − log(1+(s+k)⁻¹)]`; the 3a step bound + an elementary
inline telescoping estimate `Σ_{k<N} 1/(x+k)² ≤ 1/(x−1)` bound the sum UNIFORMLY in `N`;
letting `N → ∞` against the anchor `d(s+N) → 0` (the ONE remaining analytic input, carried as
an explicit hypothesis — brick 3b′ discharges it) yields the effective Binet bound.
conjecture1_proved = False. -/













/-! ## Brick 3b′-i: the INTEGER anchor — `ψ(1+N) − log(1+N) → 0`.

The first of the anchor's three sub-bricks (3b′ plan: (i) integer anchor via the Euler–Mascheroni
limit, (ii) real-axis sandwich via `ψ` monotonicity (log-convexity of `Γ`) killing the 1-periodic
ambiguity `L(s+1) = L(s)` on a full real interval, (iii) identity theorem
(`eqOn_of_preconnected_of_frequently_eq`, the corpus `DlvpTransfer` pattern) extending `L ≡ 0`
to all `Re s > 1`).  Here: `ψ(1+N) = −γ + H_N` (our `digamma_shift` at `s = 1` + Mathlib
`digamma_one`), so `ψ(1+N) − log(1+N) = −γ + (H_N − log(N+1)) → −γ + γ = 0` by Mathlib's
`Real.tendsto_harmonic_sub_log_add_one`.  conjecture1_proved = False. -/



/-! ## Brick 3b′-ii-a: `ψ` is REAL on the positive reals, equals `deriv (log ∘ Γ)`, and that
derivative is MONOTONE (log-convexity of `Γ`, Bohr–Mollerup).  These are the sandwich's two
pillars; 3b′-ii-b squeezes `ψ(x+N) − log(x+N) → 0` for real `x` between integer anchors. -/







/-! ## Brick 3b′-ii-b: the REAL-AXIS SQUEEZE — the anchor discharged on `[1, 3]`.

Sandwich `d(x+N) = ψ(x+N) − log(x+N)` for real `x ∈ [1,3]` between the integer-anchor
sequences: `ψ` monotone (pillar ii-a) gives `ψ(1+N) ≤ ψ(x+N) ≤ ψ(3+N)`; `log` monotone gives
the reverse for the log part; both outer sequences → 0 by the integer anchor (3b′-i, plus its
`N ↦ N+2` shift) and the vanishing log gap (`Real.tendsto_log_comp_add_sub_log`).  Squeeze ⟹
`d(x+N) → 0` for every real `x ∈ [1,3]` — the anchor hypothesis of
`norm_digamma_sub_log_le_of_anchor` is DISCHARGED on the real segment, yielding the first
UNCONDITIONAL effective Binet points (`norm_digamma_sub_log_le_ofReal`).  Brick (iii) extends
to complex `s` by the identity theorem.  conjecture1_proved = False. -/












theorem solution {x : ℝ} (hx1 : 1 ≤ x) (hx3 : x ≤ 3) :
    Filter.Tendsto (fun N : ℕ => binetR (x + N)) Filter.atTop (nhds 0) := by
  have hψ := monotoneOn_deriv_log_Gamma
  have hlow : Filter.Tendsto
      (fun N : ℕ => binetR (1 + N) - (Real.log (3 + N) - Real.log (1 + N)))
      Filter.atTop (nhds (0 - 0)) := tendsto_binetR_one_add.sub tendsto_log_gap
  have hup : Filter.Tendsto
      (fun N : ℕ => binetR (3 + N) + (Real.log (3 + N) - Real.log (1 + N)))
      Filter.atTop (nhds (0 + 0)) := tendsto_binetR_three_add.add tendsto_log_gap
  rw [sub_zero] at hlow
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun N => ?_) (fun N => ?_)
  · -- lower: ψ(1+N) − log(3+N) ≤ ψ(x+N) − log(x+N)
    have hm : deriv (Real.log ∘ Real.Gamma) (1 + N) ≤ deriv (Real.log ∘ Real.Gamma) (x + N) :=
      hψ (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) (by linarith)
    have hl : Real.log (x + N) ≤ Real.log (3 + N) :=
      Real.log_le_log (by positivity) (by linarith)
    simp only [binetR]
    linarith
  · -- upper: ψ(x+N) − log(x+N) ≤ ψ(3+N) − log(1+N)
    have hm : deriv (Real.log ∘ Real.Gamma) (x + N) ≤ deriv (Real.log ∘ Real.Gamma) (3 + N) :=
      hψ (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) (by linarith)
    have hl : Real.log (1 + N) ≤ Real.log (x + N) :=
      Real.log_le_log (by positivity) (by linarith)
    simp only [binetR]
    linarith
