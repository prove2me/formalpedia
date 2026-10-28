-- Prove2me | solution 1 for RS5.check5_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:48:43.315307+00:00
-- url     : https://prove2.me/submissions/fba272a8-7220-4f61-b5f0-7bc9865a0496

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RS4_Sound
import Definitions.Def_ArdaRH65K_RS5_Sound
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Band
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_ArdaRS_Dyadic
import Definitions.Def_ArdaRS_DyadicOps
import Definitions.Def_ArdaRS_Evaluator
import Mathlib
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ArbEcon_cpow_term
import Theorems.Thm_ArbEcon_step_sound
import Theorems.Thm_ArbEcon_trig_sound
import Theorems.Thm_DIntvProd_DIntv_add_sound
import Theorems.Thm_RS4_log_one_add_near
import Theorems.Thm_RS5_lg_lo
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Trig
end ArbEcon.Trig
namespace ArbEcon.sgn
end ArbEcon.sgn
namespace DIntvProd
end DIntvProd
namespace DIntvProd.DIntv
end DIntvProd.DIntv
namespace RS4
end RS4
namespace RS4.Cert
end RS4.Cert
namespace RS4.Lser
end RS4.Lser
namespace RS4.negIf
end RS4.negIf
namespace RS4.sgnI
end RS4.sgnI
/-  DIntvDef.lean -- production-intended dyadic interval definitions + mem-soundness.

    This is the cleaner, production sibling of `Spike/DIntvMini.lean`.  It carries the
    SAME computable ops (add, mul, neg) and, crucially, PROVES that they are sound with
    respect to the real interval they denote:

        I.memR x  :=  (I.lo : ℝ) * 2^I.e ≤ x ∧ x ≤ (I.hi : ℝ) * 2^I.e

    We prove `add_sound` and `mul_sound` ONLY (the A0 remit): if `x ∈ I` and `y ∈ J`
    then `x + y ∈ I.add J` and `x * y ∈ I.mul J`.  These validate the Real-bridging
    proof style that the full A1 correctness surface will scale up.

    Design note for A1: to keep the soundness proofs clean we store BOTH endpoints at a
    COMMON exponent (add aligns to the shared exponent; mul adds exponents).  `roundTo`
    (outward widening) is a separate, monotone op whose soundness is a one-liner from
    `add`/`mul` monotonicity and is deferred to A1.

    conjecture1_proved = False.  This is finite interval arithmetic, not a proof of RH.
-/



namespace DIntvProd



namespace DIntv









/-! ### Soundness -/

/-- `2^e > 0` in ℝ for any `e : Int`. -/
theorem two_zpow_pos (e : Int) : (0 : ℝ) < (2 : ℝ) ^ e :=
  zpow_pos (by norm_num) e



/-- Real bilinear corner bound: if `a ≤ u ≤ b` and `c ≤ v ≤ d` then `u*v` lies between
    `min` and `max` of the four corner products.  Proved from `mul_le_mul`-style endpoint
    monotonicity, splitting on the signs of `u` and `v` (4 quadrants).  No `sorry`. -/
private theorem prod_between_corners {a b c d u v : ℝ}
    (hau : a ≤ u) (hub : u ≤ b) (hcv : c ≤ v) (hvd : v ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ u * v
    ∧ u * v ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  constructor
  · -- lower bound: exhibit a corner ≤ u*v, chained through mid products a*v and u*v.
    rcases le_total 0 v with hv0 | hv0
    · -- v ≥ 0 : a*v ≤ u*v (mono in first arg), and (a*c or a*d) ≤ a*v.
      have step1 : a * v ≤ u * v := mul_le_mul_of_nonneg_right hau hv0
      have step2 : min (a*c) (a*d) ≤ a * v := by
        rcases le_total 0 a with ha0 | ha0
        · -- a ≥ 0, c ≤ v : a*c ≤ a*v
          exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hcv ha0)
        · -- a ≤ 0, v ≤ d : a*d ≤ a*v
          exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hvd ha0)
      exact le_trans (le_trans (min_le_left _ _) step2) step1
    · -- v ≤ 0 : b*v ≤ u*v (mono in first arg, v ≤ 0 flips), and (b*c or b*d) ≤ b*v.
      have step1 : b * v ≤ u * v := by
        have := mul_le_mul_of_nonpos_right hub hv0; linarith [this]
      have step2 : min (b*c) (b*d) ≤ b * v := by
        rcases le_total 0 b with hb0 | hb0
        · -- b ≥ 0, c ≤ v : b*c ≤ b*v
          exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hcv hb0)
        · -- b ≤ 0, v ≤ d : b*d ≤ b*v
          exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hvd hb0)
      exact le_trans (le_trans (min_le_right _ _) step2) step1
  · -- upper bound: symmetric.
    rcases le_total 0 v with hv0 | hv0
    · have step1 : u * v ≤ b * v := mul_le_mul_of_nonneg_right hub hv0
      have step2 : b * v ≤ max (b*c) (b*d) := by
        rcases le_total 0 b with hb0 | hb0
        · -- b ≥ 0, v ≤ d : b*v ≤ b*d
          exact le_trans (mul_le_mul_of_nonneg_left hvd hb0) (le_max_right _ _)
        · -- b ≤ 0, c ≤ v : b*v ≤ b*c
          exact le_trans (mul_le_mul_of_nonpos_left hcv hb0) (le_max_left _ _)
      exact le_trans step1 (le_trans step2 (le_max_right _ _))
    · have step1 : u * v ≤ a * v := by
        have := mul_le_mul_of_nonpos_right hau hv0; linarith [this]
      have step2 : a * v ≤ max (a*c) (a*d) := by
        rcases le_total 0 a with ha0 | ha0
        · -- a ≥ 0, v ≤ d : a*v ≤ a*d
          exact le_trans (mul_le_mul_of_nonneg_left hvd ha0) (le_max_right _ _)
        · -- a ≤ 0, c ≤ v : a*v ≤ a*c
          exact le_trans (mul_le_mul_of_nonpos_left hcv ha0) (le_max_left _ _)
      exact le_trans step1 (le_trans step2 (le_max_left _ _))

/-- The four real corner products bound `x*y`, as an auxiliary for `mul_sound`. -/
private theorem mul_mem_of_corners {x y : ℝ} {I J : DIntv}
    (hx : memR x I) (hy : memR y J) :
    ((min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)) : Int) : ℝ)
        * (2 : ℝ) ^ (I.e + J.e) ≤ x * y
    ∧ x * y ≤ ((max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi)) : Int) : ℝ)
        * (2 : ℝ) ^ (I.e + J.e) := by
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  -- Work in "unscaled" coordinates u = x / 2^eI, v = y / 2^eJ.
  set pI : ℝ := (2 : ℝ) ^ I.e with hpI
  set pJ : ℝ := (2 : ℝ) ^ J.e with hpJ
  have hpIpos : 0 < pI := two_zpow_pos I.e
  have hpJpos : 0 < pJ := two_zpow_pos J.e
  set u : ℝ := x / pI with hu
  set v : ℝ := y / pJ with hv
  have hxu : x = u * pI := by rw [hu, div_mul_cancel₀ _ (ne_of_gt hpIpos)]
  have hyv : y = v * pJ := by rw [hv, div_mul_cancel₀ _ (ne_of_gt hpJpos)]
  have hulo : (I.lo : ℝ) ≤ u := by rw [hu, le_div_iff₀ hpIpos]; simpa [hpI] using hxlo
  have huhi : u ≤ (I.hi : ℝ) := by rw [hu, div_le_iff₀ hpIpos]; simpa [hpI] using hxhi
  have hvlo : (J.lo : ℝ) ≤ v := by rw [hv, le_div_iff₀ hpJpos]; simpa [hpJ] using hylo
  have hvhi : v ≤ (J.hi : ℝ) := by rw [hv, div_le_iff₀ hpJpos]; simpa [hpJ] using hyhi
  have hscale : (2 : ℝ) ^ (I.e + J.e) = pI * pJ := by
    rw [hpI, hpJ, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  have hscalepos : 0 < (2 : ℝ) ^ (I.e + J.e) := two_zpow_pos _
  have hxy : x * y = (u * v) * (2 : ℝ) ^ (I.e + J.e) := by rw [hxu, hyv, hscale]; ring
  -- Int min/max cast out to real corner products.
  have hcastmin :
      ((min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)) : Int) : ℝ)
        = min (min ((I.lo:ℝ)*(J.lo:ℝ)) ((I.lo:ℝ)*(J.hi:ℝ)))
              (min ((I.hi:ℝ)*(J.lo:ℝ)) ((I.hi:ℝ)*(J.hi:ℝ))) := by push_cast; rfl
  have hcastmax :
      ((max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi)) : Int) : ℝ)
        = max (max ((I.lo:ℝ)*(J.lo:ℝ)) ((I.lo:ℝ)*(J.hi:ℝ)))
              (max ((I.hi:ℝ)*(J.lo:ℝ)) ((I.hi:ℝ)*(J.hi:ℝ))) := by push_cast; rfl
  obtain ⟨hlow, hupp⟩ := prod_between_corners hulo huhi hvlo hvhi
  refine ⟨?_, ?_⟩
  · rw [hcastmin, hxy]
    exact mul_le_mul_of_nonneg_right hlow (le_of_lt hscalepos)
  · rw [hcastmax, hxy]
    exact mul_le_mul_of_nonneg_right hupp (le_of_lt hscalepos)

/-- Multiplication soundness: `x ∈ I`, `y ∈ J` ⇒ `x * y ∈ I.mul J`. -/
theorem mul_sound {x y : ℝ} {I J : DIntv}
    (hx : memR x I) (hy : memR y J) : memR (x * y) (mul I J) := by
  have := mul_mem_of_corners hx hy
  unfold mul memR
  exact this

end DIntv
end DIntvProd


/-  DIntvCorrect.lean -- the DIntv correctness surface (A1).

    Builds on `DIntvDef`'s proven `add_sound`/`mul_sound`.  Completes the op surface with
    Real mem-soundness proofs for every operation the evaluators need:

      * `neg`, `sub`               -- exact, same/aligned exponent
      * `abs`                      -- |·| envelope (sign split)
      * `scale2`                   -- exact power-of-two rescale (no rounding)
      * `ofInt`                    -- exact integer point
      * `roundTo`                  -- directed OUTWARD truncation (the width-control primitive):
                                      memR x I → memR x (I.roundTo p).  THE key lemma.
      * `union` / `hull`           -- interval hull: memR x I → memR x (hull I J) (and sym)
      * `nonneg` / `nonpos` / `isPos` / `isNeg` / `sign?`  -- sign-definite predicates with
                                      their Real meanings
      * `ltOf` / `sepR`            -- interval comparison: I.hi·2^eI < J.lo·2^eJ
                                      ⇒ ∀ x∈I, y∈J, x < y.

    Design: `DIntvDef.DIntv` stores `lo hi : Int` at a single exponent `e : Int`, mem
    `(lo:ℝ)·2^e ≤ x ≤ (hi:ℝ)·2^e`.  `roundTo` DROPS `d` low mantissa bits, flooring `lo`
    and ceiling `hi`, and raises the exponent by `d` -- so the denoted real interval only
    GROWS.  All arithmetic is pure `Int` (no `Rat`, no division, no WF recursion).

    conjecture1_proved = False.  Finite interval arithmetic, not a proof of RH.
-/


namespace DIntvProd
namespace DIntv

/-! ### Exact / structural ops (no rounding) -/







             -- straddles 0



/-! ### Directed OUTWARD truncation -- the width-control primitive -/







/-! ### Sign-definite predicates -/











/-! ### Comparison -/



/-! ### Soundness proofs -/





/-- `neg` soundness: `x ∈ I ⇒ -x ∈ neg I`. -/
theorem neg_sound {x : ℝ} {I : DIntv} (hx : memR x I) : memR (-x) (neg I) := by
  obtain ⟨hlo, hhi⟩ := hx
  unfold neg memR
  simp only [Int.cast_neg]
  constructor
  · -- (-hi)·2^e ≤ -x  ⇐  x ≤ hi·2^e
    have : -((I.hi : ℝ) * (2:ℝ)^I.e) ≤ -x := neg_le_neg hhi
    linarith [this]
  · -- -x ≤ (-lo)·2^e  ⇐  lo·2^e ≤ x
    have : -x ≤ -((I.lo : ℝ) * (2:ℝ)^I.e) := neg_le_neg hlo
    linarith [this]

/-- `sub` soundness: `x ∈ I`, `y ∈ J`, same exponent ⇒ `x - y ∈ sub I J`. -/
theorem sub_sound {x y : ℝ} {I J : DIntv} (h : I.e = J.e)
    (hx : memR x I) (hy : memR y J) : memR (x - y) (sub I J h) := by
  unfold sub
  have hny : memR (-y) (neg J) := neg_sound hy
  have := add_sound (I := I) (J := neg J) (by simp [neg, h]) hx hny
  simpa [sub_eq_add_neg] using this







/-! #### roundTo soundness -- the width-control primitive

`floorShift m d = m >>> d = ⌊m / 2^d⌋` and `ceilShift m d = ⌈m / 2^d⌉` as `Int`.  We first
establish the two integer facts `floorShift m d · 2^d ≤ m ≤ ceilShift m d · 2^d`, cast them
to ℝ, and combine with `2^e ≥ 0` and `2^(e+d) = 2^e · 2^d`. -/







/-! #### Predicate meanings -/













/-! #### Comparison soundness -/



end DIntv
end DIntvProd


/-  Probes/ArbEconomics_Sound.lean -- soundness of the Nat-only zeta evaluator (ArbEconomics_Eval).

    Every function of `ArbEconomics_Eval` is shown to produce a TRUE enclosure:
      * `logInc`   : `S <= (log m - log (m-1)) 2^P <= S + K + T`
                     (Mathlib `Real.hasSum_pow_div_log_of_abs_lt_one`, `abs_log_sub_add_sum_range_le`);
      * `termOf`   : `Rlo <= 2^P / sqrt m <= Rhi` for ANY Newton iterate (two-sided validation);
      * `trig`     : cos/sin balls of `theta` from the (pi/2)-reduction, the Horner scheme
                     (Mathlib `Complex.exp_bound`) and the quadrant rotation;
      * `step`/`run` : the loop invariant `Inv` (log bracket + Re/Im balls of the partial zeta sum).

    The main theorem `run_sound` turns a kernel-checked chunk equation
    `St.beq (run cfg L s) s' = true` into `Inv n s -> Inv (n + L) s'`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/










open Real Finset

namespace ArbEcon

/-! ## A. floor division / shifts, cast to ℝ -/











/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























/-! ## H. the zeta term, the term product, one step, the run -/











theorem inv_init (c : Cfg) (t : ℝ) (hone : c.one = 2 ^ c.P) : Inv c t 1 (St.init c) := by
  have hps : psum t 1 = 1 := by simp [psum]
  refine ⟨rfl, le_rfl, ?_, ?_, ?_, ?_⟩ <;> simp [St.init, hps, hone]





theorem run_sound (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) :
    ∀ (L n : ℕ) (s : St), Inv c t n s → Inv c t (n + L) (run c L s) := by
  intro L
  induction L with
  | zero => intro n s h; exact h
  | succ L ih =>
    intro n s h
    have := ih (n + 1) (step c s) (step_sound c t K hv n s h)
    rw [show n + (L + 1) = n + 1 + L by ring]
    exact this





end ArbEcon


/-  RS4_Sound.lean -- lane B4: SOUNDNESS of the Riemann-Siegel main-term checker `RS4.check`.

    ## The headline

      `RS4.check_sound` : for an evaluator configuration `c` valid at height `t`
      (`ArbEcon.Valid c t K`, i.e. `t = tn / 2^tq` and the pi / Horner / log-kernel facts) and any
      certificate `z`, if the KERNEL accepts (`check c z = true`) then
        * `10000 <= t`, `rsNn t = z.N`, `0 < rsFrac t`, `cos (2 pi rsFrac t) ≠ 0`, and
        * for EVERY phase `phi` with `|phi - rsThetaMain t| <= 1/t`,
              z.zlo / 2^(2P) <= Zmain t phi <= z.zhi / 2^(2P),
          where `Zmain t phi = 2 sum_{n <= N} n^(-1/2) cos(phi - t log n)
                                + (-1)^(N+1) (t/2pi)^(-1/4) rsPsi (rsFrac t)`
          is VERBATIM the main term of `RSInt.rs_Z_C0`.

    The hypotheses of `rs_Z_C0` (`t >= 10000`, `0 < p`, `cos 2 pi p ≠ 0`) are OUTPUTS of the checker,
    so `RS4_Z` combines the two into a hypothesis-free enclosure of Hardy's Z.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/




open Real Finset
open ArbEcon DIntvProd

namespace RS4

noncomputable section



/-! ## 0. small real facts -/





theorem lp_real (Y o : ℕ) (ho : 0 < o) :
    ((lpPos Y o : ℕ) : ℝ) - (lpNeg Y o : ℕ) = 840 * (o : ℝ) ^ 9 * Lser ((Y : ℝ) / o) := by
  have hoR : (o : ℝ) ≠ 0 := by exact_mod_cast ho.ne'
  unfold lpPos lpNeg Lser
  push_cast
  field_simp
  ring

theorem sgnI_cast (b : Bool) (m : ℕ) : ((sgnI b m : ℤ) : ℝ) = sgn b * m := by
  cases b <;> simp [sgnI, sgn]

theorem two_zpow_negP (P : ℕ) : (2 : ℝ) ^ (-(P : ℤ)) = 1 / 2 ^ P := by
  rw [zpow_neg, zpow_natCast, one_div]

/-- A signed ball `|x 2^P - m| <= r` is DIntv membership in `ballD P m r`. -/
theorem ballD_mem {P : ℕ} {x : ℝ} {m : ℤ} {r : ℕ} (h : |x * 2 ^ P - m| ≤ r) :
    (ballD P m r).memR x := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  unfold ballD DIntv.memR
  simp only [two_zpow_negP]
  rw [abs_le] at h
  push_cast
  constructor
  · rw [← mul_div_assoc, mul_one, div_le_iff₀ hP]; linarith
  · rw [← mul_div_assoc, mul_one, le_div_iff₀ hP]; linarith

/-- A Nat/Int bracket `lo <= x 2^P <= hi` is DIntv membership at exponent `-P`. -/
theorem brD_mem {P : ℕ} {x : ℝ} {lo hi : ℤ} (h0 : (lo : ℝ) ≤ x * 2 ^ P) (h1 : x * 2 ^ P ≤ hi) :
    DIntv.memR x ⟨lo, hi, -(P : ℤ)⟩ := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  unfold DIntv.memR
  simp only [two_zpow_negP]
  constructor
  · rw [← mul_div_assoc, mul_one, div_le_iff₀ hP]; linarith
  · rw [← mul_div_assoc, mul_one, le_div_iff₀ hP]; linarith

theorem negIf_mem {x : ℝ} {I : DIntv} (b : Bool) (h : I.memR x) :
    (negIf b I).memR (if b then x else -x) := by
  cases b
  · have := DIntv.neg_sound h
    simpa [negIf, DIntv.neg] using this
  · simpa [negIf] using h

/-! ## 1. the checker's facts, over the reals -/

section Facts

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}























































/-! ## 2. the Dirichlet state: `psum t N` and `log N` -/







/-! ## 3. the phase ball -/











/-! ## 4. the C0 amplitude `(t/2pi)^(-1/4) = a^(-1/2)` -/









/-! ## 5. the angles `2 pi p` and `2 pi (p - p^2 + 1/16)` -/















end Facts

/-! ## 6. the quotient `Psi = cos v / cos 2 pi p` (denominator bounded away from 0) -/







/-! ## 7. the main sum as `Re (e^{i phi} psum t N)` -/



/-! ## 8. the DIntv assembly -/

section Assembly

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}









end Assembly

/-! ## 9. THE SOUNDNESS THEOREM -/



end

end RS4


/-  RS5_Eval.lean -- lane B5: the t >= 509 variant of the RS4 kernel checker, the margin check,
    and the BAND checker over a list of dyadic sample heights (computable side only; soundness is
    `RS5_Sound`, `RS5_Z`, `RS5_Band`).

    ## Why a variant (and not an edit of RS4)

    `RS4.Checks` hard-codes the height floor `10000 * 2^tq <= tn` (it feeds `RSInt.rs_Z_C0`, t >= 10000).
    The seam bound `RSSeam.rs_Z_C0_seam` holds from t >= 509.  `RS5.Checks5` / `RS5.check5` are
    `RS4.Checks` / `RS4.check` VERBATIM with the floor `509` instead of `10000`; every computable
    ingredient (`RS4.Cert`, `RS4.zBox`, `RS4.mainBox`, `RS4.c0Box`, `RS4.QuotOK`, `RS4.lpPos`, ...) is
    REUSED from `RS4_Eval`, unchanged.  The RS4 files are not edited.

    ## The margin

    The seam remainder is `(13/5) t^(-3/4)`.  A sample carries a Nat `E`; `MarginOK c E` is the integer
    inequality `one^4 (2^tq)^3 <= E^4 tn^3`, i.e. `(E / 2^P)^4 t^3 >= 1`, i.e. `E / 2^P >= t^(-3/4)`.
    `PosOK` / `NegOK` compare the certified box against `(13/5) E / 2^P` (exact integer inequalities).

    ## The band checker

    A `Sample` is a dyadic height `t = tn / 2^tq`, a margin `E` and an RS4 certificate `z` for the P = 64
    configuration `ArbEcon.OrderK.cfg64 tn tq` (valid at every height, `ArbEcon.OrderK.valid64`).
    Its claimed sign is `pos = (0 < zlo)`.  `bandOK l` checks every sample (`sampleOK`) and that the
    heights are STRICTLY increasing; `chgBy Sample.pos l` counts adjacent sign changes.

    conjecture1_proved = False.  Finite interval arithmetic at finitely many heights; nothing about RH.
-/



namespace RS5

open ArbEcon DIntvProd RS4

noncomputable section







theorem checks5_of {c : Cfg} {z : Cert} (h : ChecksP5 c z) : Checks5 c z := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩



/-! ## the margin `E / 2^P >= t^(-3/4)` and the two sign conditions -/











/-! ## samples and the band checker -/





















end

end RS5


/-  RS5_Sound.lean -- lane B5: SOUNDNESS of the t >= 509 checker `RS5.check5`.

    This file is lane B4's `RS4_Sound` sections 1-9 (the checker's facts over the reals, the DIntv
    assembly and the soundness theorem) re-stated for `RS5.Checks5`, which differs from `RS4.Checks`
    ONLY in the height floor (`509 * 2^tq <= tn` instead of `10000 * 2^tq <= tn`).  The floor is used by
    exactly two facts, `t_ge` and `tn_pos`; every other proof is unchanged text.  The height-free
    helpers of `RS4_Sound` (`Zmain`, `Lser`, `log_one_add_near`, `lp_real`, `ballD_mem`, ...) and all
    computable definitions of `RS4_Eval` are REUSED (selective `open RS4 (...)`), not duplicated.

    ## The headline

      `RS5.check5_sound` : `Valid c t K` and `check5 c z = true` imply
        `509 <= t`, `rsNn t = z.N`, `0 < rsFrac t`, `cos (2 pi rsFrac t) ≠ 0`, and for EVERY phase
        `phi` with `|phi - rsThetaMain t| <= 1/t`:  `zlo / 2^(2P) <= RS4.Zmain t phi <= zhi / 2^(2P)`.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/



open Real Finset
open ArbEcon DIntvProd
open RS4 (Cert lpPos lpNeg sgnI ballD negIf dstate phTrig mainBox c0Box zBox QuotOK Zmain Lser
  log_one_add_near lp_real sgnI_cast two_zpow_negP ballD_mem brD_mem negIf_mem)

namespace RS5

noncomputable section

/-! ## 1. the checker's facts, over the reals -/

section Facts

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}

theorem oneR (hv : Valid c t K) : (c.one : ℝ) = 2 ^ c.P := by
  rw [hv.one_eq]; push_cast; ring

theorem pi_lo (hv : Valid c t K) : (c.hp : ℝ) - c.rp ≤ π / 2 * 2 ^ c.P := by
  have := hv.pi_ball; rw [abs_le] at this; linarith [this.1]

theorem pi_hi (hv : Valid c t K) : π / 2 * 2 ^ c.P ≤ (c.hp : ℝ) + c.rp := by
  have := hv.pi_ball; rw [abs_le] at this; linarith [this.2]

theorem t_ge (hv : Valid c t K) (hk : Checks5 c z) : 509 ≤ t := by
  rw [hv.t_eq, le_div_iff₀ (by positivity)]
  have := hk.ht
  exact_mod_cast this

theorem t_pos (hv : Valid c t K) (hk : Checks5 c z) : 0 < t := by
  linarith [t_ge hv hk]

/-- `a = rsAlpha t` squared. -/
theorem alpha_sq (ht : 0 < t) : RSInt.rsAlpha t ^ 2 = t / (2 * π) :=
  Real.sq_sqrt (by positivity)

theorem alpha_nonneg (t : ℝ) : 0 ≤ RSInt.rsAlpha t := Real.sqrt_nonneg _

/-- `(a 2^P)^2 * (2^tq * 4 * (pi/2 * 2^P)) = tn * 2^(3P)`. -/
theorem alpha_key (hv : Valid c t K) (hk : Checks5 c z) :
    (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) =
      (c.tn : ℝ) * (2 ^ c.P * 2 ^ c.P * 2 ^ c.P) := by
  have ht := t_pos hv hk
  have hq : (0 : ℝ) < 2 ^ c.tq := by positivity
  rw [mul_pow, alpha_sq ht, hv.t_eq]
  field_simp
  ring

theorem A0_le (hv : Valid c t K) (hk : Checks5 c z) :
    (z.A0 : ℝ) ≤ RSInt.rsAlpha t * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hq : (0 : ℝ) < 2 ^ c.tq := by positivity
  have h := hk.hA0
  have hR : ((z.A0 * z.A0 * 2 ^ c.tq * 4 * (c.hp + c.rp) : ℕ) : ℝ)
      ≤ ((c.tn * (c.one * c.one * c.one) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hR
  rw [oneR hv] at hR
  have key := alpha_key hv hk
  have hpi := pi_hi hv
  have hx := mul_nonneg (alpha_nonneg t) hP.le
  by_contra hcon
  rw [not_le] at hcon
  have hsq : (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 < (z.A0 : ℝ) ^ 2 := by
    apply pow_lt_pow_left₀ hcon hx (by norm_num)
  have hw : (0 : ℝ) < 2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P) := by positivity
  have h1 : (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P))
      < (z.A0 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) := mul_lt_mul_of_pos_right hsq hw
  have h2 : (z.A0 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P))
      ≤ (z.A0 : ℝ) ^ 2 * (2 ^ c.tq * 4 * ((c.hp : ℝ) + c.rp)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left hpi (by positivity)
  nlinarith

theorem A1_ge (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsAlpha t * 2 ^ c.P ≤ (z.A1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h := hk.hA1
  have hR : ((c.tn * (c.one * c.one * c.one) : ℕ) : ℝ)
      ≤ ((z.A1 * z.A1 * 2 ^ c.tq * 4 * (c.hp - c.rp) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_sub hk.hrp] at hR
  rw [oneR hv] at hR
  have key := alpha_key hv hk
  have hpi := pi_lo hv
  have hx := mul_nonneg (alpha_nonneg t) hP.le
  by_contra hcon
  rw [not_le] at hcon
  have hsq : (z.A1 : ℝ) ^ 2 < (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 := by
    apply pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  have hpipos : (0 : ℝ) < π / 2 * 2 ^ c.P := by positivity
  have h2 : (z.A1 : ℝ) ^ 2 * (2 ^ c.tq * 4 * ((c.hp : ℝ) - c.rp))
      ≤ (z.A1 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left hpi (by positivity)
  have hw : (0 : ℝ) < 2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P) := by positivity
  have h1 : (z.A1 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P))
      < (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) :=
    mul_lt_mul_of_pos_right hsq hw
  nlinarith

theorem N_lt_alpha (hv : Valid c t K) (hk : Checks5 c z) : (z.N : ℝ) < RSInt.rsAlpha t := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((z.N * c.one : ℕ) : ℝ) < (z.A0 : ℝ) := by exact_mod_cast hk.hNlo
  push_cast at h; rw [oneR hv] at h
  have := A0_le hv hk
  by_contra hc; rw [not_lt] at hc
  nlinarith

theorem alpha_lt_N1 (hv : Valid c t K) (hk : Checks5 c z) : RSInt.rsAlpha t < (z.N : ℝ) + 1 := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : (z.A1 : ℝ) < (((z.N + 1) * c.one : ℕ) : ℝ) := by exact_mod_cast hk.hNhi
  push_cast at h; rw [oneR hv] at h
  have := A1_ge hv hk
  by_contra hc; rw [not_lt] at hc
  nlinarith

theorem N_eq (hv : Valid c t K) (hk : Checks5 c z) : RSInt.rsNn t = z.N := by
  unfold RSInt.rsNn
  rw [Nat.floor_eq_iff (alpha_nonneg t)]
  exact ⟨(N_lt_alpha hv hk).le, alpha_lt_N1 hv hk⟩

theorem frac_eq (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsFrac t = RSInt.rsAlpha t - z.N := by
  unfold RSInt.rsFrac; rw [N_eq hv hk]

theorem frac_pos (hv : Valid c t K) (hk : Checks5 c z) : 0 < RSInt.rsFrac t := by
  rw [frac_eq hv hk]; linarith [N_lt_alpha hv hk]

theorem NO_le_A0 (hk : Checks5 c z) : z.N * c.one ≤ z.A0 := le_of_lt hk.hNlo

theorem NO_le_A1 (hv : Valid c t K) (hk : Checks5 c z) : z.N * c.one ≤ z.A1 := by
  have h1 : ((z.N * c.one : ℕ) : ℝ) < z.A0 := by exact_mod_cast hk.hNlo
  have h2 := A0_le hv hk
  have h3 := A1_ge hv hk
  have : ((z.N * c.one : ℕ) : ℝ) ≤ z.A1 := by linarith
  exact_mod_cast this

/-- `p 2^P` lies in `[A0 - N o, A1 - N o]`. -/
theorem p_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (((z.A0 - z.N * c.one : ℕ)) : ℝ) ≤ RSInt.rsFrac t * 2 ^ c.P := by
  rw [Nat.cast_sub (NO_le_A0 hk), frac_eq hv hk]
  push_cast; rw [oneR hv]
  have := A0_le hv hk
  nlinarith

theorem p_hi (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsFrac t * 2 ^ c.P ≤ (((z.A1 - z.N * c.one : ℕ)) : ℝ) := by
  rw [Nat.cast_sub (NO_le_A1 hv hk), frac_eq hv hk]
  push_cast; rw [oneR hv]
  have := A1_ge hv hk
  nlinarith

theorem N_pos (hk : Checks5 c z) : (0 : ℝ) < z.N := by
  have := hk.hN; exact_mod_cast this



theorem y_hi (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsFrac t / z.N * 2 ^ c.P ≤ (z.Y1 : ℝ) := by
  have hN := N_pos hk
  have h : ((z.A1 - z.N * c.one : ℕ) : ℝ) ≤ ((z.Y1 * z.N : ℕ) : ℝ) := by exact_mod_cast hk.hY1
  have hp := p_hi hv hk
  push_cast at h
  rw [div_mul_eq_mul_div, div_le_iff₀ hN]
  linarith

theorem y_nonneg (hv : Valid c t K) (hk : Checks5 c z) : 0 ≤ RSInt.rsFrac t / z.N :=
  div_nonneg (frac_pos hv hk).le (N_pos hk).le



/-- `a = N (1 + y)`, hence `log a = log N + log (1 + y)`. -/
theorem log_alpha (hv : Valid c t K) (hk : Checks5 c z) :
    Real.log (RSInt.rsAlpha t) = Real.log (z.N : ℝ) + Real.log (1 + RSInt.rsFrac t / z.N) := by
  have hN := N_pos hk
  have hy := y_nonneg hv hk
  rw [← Real.log_mul hN.ne' (by linarith)]
  congr 1
  rw [frac_eq hv hk]; field_simp; ring



theorem lg_hi (hv : Valid c t K) (hk : Checks5 c z) :
    Real.log (1 + RSInt.rsFrac t / z.N) * 2 ^ c.P ≤ (z.LG1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have ho : 0 < c.one := by rw [hv.one_eq]; positivity
  set y := RSInt.rsFrac t / z.N with hydef
  set y1 : ℝ := (z.Y1 : ℝ) / 2 ^ c.P with hy1
  have hyle : y ≤ y1 := by rw [hy1, le_div_iff₀ hP]; exact y_hi hv hk
  have hy0 := y_nonneg hv hk
  have hy1h : y1 ≤ 1 / 2 := by
    have h : ((2 * z.Y1 : ℕ) : ℝ) ≤ (c.one : ℝ) := by exact_mod_cast hk.hYhalf
    push_cast at h; rw [oneR hv] at h
    rw [hy1, div_le_iff₀ hP]; linarith
  have hmono : Real.log (1 + y) ≤ Real.log (1 + y1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hser := log_one_add_near (by linarith : 0 ≤ y1) hy1h
  rw [abs_le] at hser
  have h : ((lpPos z.Y1 c.one + 1680 * z.Y1 ^ 9 : ℕ) : ℝ)
      ≤ ((z.LG1 * 840 * c.one ^ 8 + lpNeg z.Y1 c.one : ℕ) : ℝ) := by exact_mod_cast hk.hLG1
  have hl := lp_real z.Y1 c.one ho
  rw [oneR hv] at hl
  push_cast at h
  rw [oneR hv] at h
  have hY : (z.Y1 : ℝ) = y1 * 2 ^ c.P := by rw [hy1]; field_simp
  rw [← hy1] at hl
  have h2 : 840 * (2 ^ c.P) ^ 9 * Lser y1 + 1680 * (y1 * 2 ^ c.P) ^ 9
      ≤ (z.LG1 : ℝ) * 840 * (2 ^ c.P) ^ 8 := by rw [← hY]; linarith
  have h3 : (Lser y1 + 2 * y1 ^ 9) * 2 ^ c.P ≤ (z.LG1 : ℝ) := by
    have hO8 : (0 : ℝ) < 840 * (2 ^ c.P) ^ 8 := by positivity
    rw [← mul_le_mul_iff_left₀ hO8]
    have e : (Lser y1 + 2 * y1 ^ 9) * 2 ^ c.P * (840 * (2 ^ c.P) ^ 8)
        = 840 * (2 ^ c.P) ^ 9 * Lser y1 + 1680 * (y1 * 2 ^ c.P) ^ 9 := by ring
    rw [e]; linarith
  have h4 : Real.log (1 + y) * 2 ^ c.P ≤ (Lser y1 + 2 * y1 ^ 9) * 2 ^ c.P :=
    mul_le_mul_of_nonneg_right (by linarith [hser.1]) hP.le
  linarith

/-! ## 2. the Dirichlet state: `psum t N` and `log N` -/

theorem dstate_inv (hv : Valid c t K) (hk : Checks5 c z) : Inv c t z.N (dstate c z) := by
  have h := run_sound c t K hv (z.N - 1) 1 (St.init c) (inv_init c t hv.one_eq)
  have hN := hk.hN
  rwa [show 1 + (z.N - 1) = z.N by omega] at h

theorem loga_lo (hv : Valid c t K) (hk : Checks5 c z) :
    ((dstate c z).llo : ℝ) + z.LG0 ≤ Real.log (RSInt.rsAlpha t) * 2 ^ c.P := by
  obtain ⟨_, _, h1, _, _, _⟩ := dstate_inv hv hk
  rw [log_alpha hv hk]
  have := lg_lo hv hk
  nlinarith

theorem loga_hi (hv : Valid c t K) (hk : Checks5 c z) :
    Real.log (RSInt.rsAlpha t) * 2 ^ c.P ≤ ((dstate c z).lhi : ℝ) + z.LG1 := by
  obtain ⟨_, _, _, h2, _, _⟩ := dstate_inv hv hk
  rw [log_alpha hv hk]
  have := lg_hi hv hk
  nlinarith

/-! ## 3. the phase ball -/

theorem thetaMain_eq (ht : 0 < t) :
    RSInt.rsThetaMain t = t * Real.log (RSInt.rsAlpha t) - t / 2 - π / 8 := by
  unfold RSInt.rsThetaMain RSInt.rsAlpha
  rw [Real.log_sqrt (by positivity), Real.log_div ht.ne' (by positivity)]
  ring

/-- The scaled phase identity used for both ends of the ball. -/
theorem phase_scaled (t T Q La O s : ℝ) (hT : 0 < T) (hQ : 0 < Q) (ht : t = T / Q) :
    (t * La - t / 2 - π / 8 + s / t) * O * (4 * T * Q)
      = 4 * T ^ 2 * (La * O) - 2 * T ^ 2 * O - (π / 2 * O) * T * Q + s * 4 * O * Q ^ 2 := by
  subst ht
  field_simp
  ring

theorem tn_pos (hk : Checks5 c z) : (0 : ℝ) < c.tn := by
  have h : ((509 * 2 ^ c.tq : ℕ) : ℝ) ≤ c.tn := by exact_mod_cast hk.ht
  push_cast at h
  have : (0 : ℝ) < 509 * 2 ^ c.tq := by positivity
  linarith

theorem phase_lo (hv : Valid c t K) (hk : Checks5 c z) {φ : ℝ}
    (hφ : |φ - RSInt.rsThetaMain t| ≤ 1 / t) : (z.TH0 : ℝ) ≤ φ * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hQ : (0 : ℝ) < 2 ^ c.tq := by positivity
  have hT := tn_pos hk
  have ht := t_pos hv hk
  have h : ((z.TH0 * (4 * c.tn * 2 ^ c.tq) + 2 * c.tn * c.tn * c.one + c.tn * 2 ^ c.tq * (c.hp + c.rp)
      + 4 * c.one * 2 ^ c.tq * 2 ^ c.tq : ℕ) : ℝ)
      ≤ ((4 * c.tn * c.tn * ((dstate c z).llo + z.LG0) : ℕ) : ℝ) := by exact_mod_cast hk.hTH0
  push_cast at h
  rw [oneR hv] at h
  have hL := loga_lo hv hk
  have hpi := pi_hi hv
  have hφ' : RSInt.rsThetaMain t + (-1) / t ≤ φ := by
    have := (abs_le.mp hφ).1; rw [neg_div]; linarith
  rw [thetaMain_eq ht] at hφ'
  have e := phase_scaled t c.tn (2 ^ c.tq) (Real.log (RSInt.rsAlpha t)) (2 ^ c.P) (-1) hT hQ hv.t_eq
  have hw : (0 : ℝ) < 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) := by positivity
  have h1 : (t * Real.log (RSInt.rsAlpha t) - t / 2 - π / 8 + (-1) / t) * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq)
      ≤ φ * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) := by
    rw [mul_assoc, mul_assoc φ]; exact mul_le_mul_of_nonneg_right hφ' hw.le
  have h2 : 4 * (c.tn : ℝ) ^ 2 * (((dstate c z).llo : ℝ) + z.LG0)
      ≤ 4 * (c.tn : ℝ) ^ 2 * (Real.log (RSInt.rsAlpha t) * 2 ^ c.P) :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have h3 : (π / 2 * 2 ^ c.P) * c.tn * 2 ^ c.tq ≤ ((c.hp : ℝ) + c.rp) * c.tn * 2 ^ c.tq := by
    apply mul_le_mul_of_nonneg_right _ hQ.le
    exact mul_le_mul_of_nonneg_right hpi hT.le
  have h4 : (z.TH0 : ℝ) * (4 * c.tn * 2 ^ c.tq) ≤ φ * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) := by
    nlinarith
  exact le_of_mul_le_mul_right h4 (by positivity)

theorem phase_hi (hv : Valid c t K) (hk : Checks5 c z) {φ : ℝ}
    (hφ : |φ - RSInt.rsThetaMain t| ≤ 1 / t) : φ * 2 ^ c.P ≤ (z.TH1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hQ : (0 : ℝ) < 2 ^ c.tq := by positivity
  have hT := tn_pos hk
  have ht := t_pos hv hk
  have h : ((4 * c.tn * c.tn * ((dstate c z).lhi + z.LG1) + 4 * c.one * 2 ^ c.tq * 2 ^ c.tq : ℕ) : ℝ)
      ≤ ((z.TH1 * (4 * c.tn * 2 ^ c.tq) + 2 * c.tn * c.tn * c.one
          + c.tn * 2 ^ c.tq * (c.hp - c.rp) : ℕ) : ℝ) := by exact_mod_cast hk.hTH1
  push_cast [Nat.cast_sub hk.hrp] at h
  rw [oneR hv] at h
  have hL := loga_hi hv hk
  have hpi := pi_lo hv
  have hφ' : φ ≤ RSInt.rsThetaMain t + 1 / t := by
    have := (abs_le.mp hφ).2; linarith
  rw [thetaMain_eq ht] at hφ'
  have e := phase_scaled t c.tn (2 ^ c.tq) (Real.log (RSInt.rsAlpha t)) (2 ^ c.P) 1 hT hQ hv.t_eq
  have hw : (0 : ℝ) < 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) := by positivity
  have h1 : φ * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq)
      ≤ (t * Real.log (RSInt.rsAlpha t) - t / 2 - π / 8 + 1 / t) * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) := by
    rw [mul_assoc, mul_assoc (t * Real.log (RSInt.rsAlpha t) - t / 2 - π / 8 + 1 / t)]
    exact mul_le_mul_of_nonneg_right hφ' hw.le
  have h2 : 4 * (c.tn : ℝ) ^ 2 * (Real.log (RSInt.rsAlpha t) * 2 ^ c.P)
      ≤ 4 * (c.tn : ℝ) ^ 2 * (((dstate c z).lhi : ℝ) + z.LG1) :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have h3 : ((c.hp : ℝ) - c.rp) * c.tn * 2 ^ c.tq ≤ (π / 2 * 2 ^ c.P) * c.tn * 2 ^ c.tq := by
    apply mul_le_mul_of_nonneg_right _ hQ.le
    exact mul_le_mul_of_nonneg_right hpi hT.le
  have h4 : φ * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) ≤ (z.TH1 : ℝ) * (4 * c.tn * 2 ^ c.tq) := by
    nlinarith
  exact le_of_mul_le_mul_right h4 (by positivity)

/-! ## 4. the C0 amplitude `(t/2pi)^(-1/4) = a^(-1/2)` -/

theorem alpha_pos (hv : Valid c t K) (hk : Checks5 c z) : 0 < RSInt.rsAlpha t := by
  have := N_lt_alpha hv hk; have := N_pos hk; linarith

theorem w_sq_alpha (ht : 0 < t) :
    ((t / (2 * π)) ^ (-(1 / 4 : ℝ))) ^ 2 * RSInt.rsAlpha t = 1 := by
  have hx : (0 : ℝ) < t / (2 * π) := by positivity
  have ha : 0 < RSInt.rsAlpha t := Real.sqrt_pos.mpr hx
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  unfold RSInt.rsAlpha
  field_simp

theorem w_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (z.Q0 : ℝ) ≤ (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have ht := t_pos hv hk
  have ha := alpha_pos hv hk
  have hwa := w_sq_alpha ht
  set w := (t / (2 * π)) ^ (-(1 / 4 : ℝ)) with hwdef
  have hw : 0 < w := Real.rpow_pos_of_pos (by positivity) _
  have h : ((z.Q0 * z.Q0 * z.A1 : ℕ) : ℝ) ≤ ((c.one * c.one * c.one : ℕ) : ℝ) := by
    exact_mod_cast hk.hQ0
  push_cast at h; rw [oneR hv] at h
  have hA1 := A1_ge hv hk
  have h1 : (z.Q0 : ℝ) ^ 2 * (RSInt.rsAlpha t * 2 ^ c.P) ≤ (z.Q0 : ℝ) ^ 2 * z.A1 :=
    mul_le_mul_of_nonneg_left hA1 (by positivity)
  have h2 : (z.Q0 : ℝ) ^ 2 * RSInt.rsAlpha t ≤ (w * 2 ^ c.P) ^ 2 * RSInt.rsAlpha t := by
    have e : (w * 2 ^ c.P) ^ 2 * RSInt.rsAlpha t = (2 ^ c.P) ^ 2 := by
      rw [mul_pow, mul_comm (w ^ 2), mul_assoc, hwa, mul_one]
    rw [e]
    have : (z.Q0 : ℝ) ^ 2 * RSInt.rsAlpha t * 2 ^ c.P ≤ (2 ^ c.P) ^ 2 * 2 ^ c.P := by nlinarith
    exact le_of_mul_le_mul_right this hP
  have h3 : (z.Q0 : ℝ) ^ 2 ≤ (w * 2 ^ c.P) ^ 2 := le_of_mul_le_mul_right h2 ha
  by_contra hc
  simp only [not_le] at hc
  have := pow_lt_pow_left₀ hc (by positivity) (by norm_num : (2 : ℕ) ≠ 0)
  linarith

theorem w_hi (hv : Valid c t K) (hk : Checks5 c z) :
    (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * 2 ^ c.P ≤ (z.Q1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have ht := t_pos hv hk
  have ha := alpha_pos hv hk
  have hwa := w_sq_alpha ht
  set w := (t / (2 * π)) ^ (-(1 / 4 : ℝ)) with hwdef
  have hw : 0 < w := Real.rpow_pos_of_pos (by positivity) _
  have h : ((c.one * c.one * c.one : ℕ) : ℝ) ≤ ((z.Q1 * z.Q1 * z.A0 : ℕ) : ℝ) := by
    exact_mod_cast hk.hQ1
  push_cast at h; rw [oneR hv] at h
  have hA0 := A0_le hv hk
  have h1 : (z.Q1 : ℝ) ^ 2 * z.A0 ≤ (z.Q1 : ℝ) ^ 2 * (RSInt.rsAlpha t * 2 ^ c.P) :=
    mul_le_mul_of_nonneg_left hA0 (by positivity)
  have h2 : (w * 2 ^ c.P) ^ 2 * RSInt.rsAlpha t ≤ (z.Q1 : ℝ) ^ 2 * RSInt.rsAlpha t := by
    have e : (w * 2 ^ c.P) ^ 2 * RSInt.rsAlpha t = (2 ^ c.P) ^ 2 := by
      rw [mul_pow, mul_comm (w ^ 2), mul_assoc, hwa, mul_one]
    rw [e]
    have : (2 ^ c.P) ^ 2 * 2 ^ c.P ≤ (z.Q1 : ℝ) ^ 2 * RSInt.rsAlpha t * 2 ^ c.P := by nlinarith
    exact le_of_mul_le_mul_right this hP
  have h3 : (w * 2 ^ c.P) ^ 2 ≤ (z.Q1 : ℝ) ^ 2 := le_of_mul_le_mul_right h2 ha
  by_contra hc
  simp only [not_le] at hc
  have := pow_lt_pow_left₀ hc (by positivity) (by norm_num : (2 : ℕ) ≠ 0)
  linarith

/-! ## 5. the angles `2 pi p` and `2 pi (p - p^2 + 1/16)` -/

theorem U_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (z.U0 : ℝ) ≤ 2 * π * RSInt.rsFrac t * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((z.U0 * c.one : ℕ) : ℝ) ≤ ((4 * (c.hp - c.rp) * (z.A0 - z.N * c.one) : ℕ) : ℝ) := by
    exact_mod_cast hk.hU0
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk.hrp, oneR hv] at h
  have hp := p_lo hv hk
  have hpi := pi_lo hv
  have hr : (0 : ℝ) ≤ (c.hp : ℝ) - c.rp := by
    have : (c.rp : ℝ) ≤ c.hp := by exact_mod_cast hk.hrp
    linarith
  have h1 : ((c.hp : ℝ) - c.rp) * ((z.A0 - z.N * c.one : ℕ) : ℝ)
      ≤ (π / 2 * 2 ^ c.P) * (RSInt.rsFrac t * 2 ^ c.P) :=
    mul_le_mul hpi hp (by positivity) (by positivity)
  have h2 : (z.U0 : ℝ) * 2 ^ c.P ≤ (2 * π * RSInt.rsFrac t * 2 ^ c.P) * 2 ^ c.P := by
    push_cast at h; nlinarith
  exact le_of_mul_le_mul_right h2 hP

theorem U_hi (hv : Valid c t K) (hk : Checks5 c z) :
    2 * π * RSInt.rsFrac t * 2 ^ c.P ≤ (z.U1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((4 * (c.hp + c.rp) * (z.A1 - z.N * c.one) : ℕ) : ℝ) ≤ ((z.U1 * c.one : ℕ) : ℝ) := by
    exact_mod_cast hk.hU1
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, oneR hv] at h
  have hp := p_hi hv hk
  have hpi := pi_hi hv
  have hf := frac_pos hv hk
  have h1 : (π / 2 * 2 ^ c.P) * (RSInt.rsFrac t * 2 ^ c.P)
      ≤ ((c.hp : ℝ) + c.rp) * ((z.A1 - z.N * c.one : ℕ) : ℝ) :=
    mul_le_mul hpi hp (by positivity) (by positivity)
  have h2 : (2 * π * RSInt.rsFrac t * 2 ^ c.P) * 2 ^ c.P ≤ (z.U1 : ℝ) * 2 ^ c.P := by
    push_cast at h; nlinarith
  exact le_of_mul_le_mul_right h2 hP



theorem G_bounds (hv : Valid c t K) (hk : Checks5 c z) :
    (((16 * (z.A0 - z.N * c.one) * c.one + c.one * c.one
        - 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one) : ℕ)) : ℝ)
      ≤ 16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2 ∧
    16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2
      ≤ 16 * ((z.A1 - z.N * c.one : ℕ) : ℝ) * 2 ^ c.P + (2 ^ c.P) ^ 2
        - 16 * ((z.A0 - z.N * c.one : ℕ) : ℝ) ^ 2 := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hlo := p_lo hv hk
  have hhi := p_hi hv hk
  have hf := frac_pos hv hk
  set x := RSInt.rsFrac t * 2 ^ c.P with hx
  have e : 16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2
      = 16 * x * 2 ^ c.P - 16 * x ^ 2 + (2 ^ c.P) ^ 2 := by rw [hx]; ring
  rw [e]
  have hx0 : 0 ≤ x := by positivity
  have hP0 : (0 : ℝ) ≤ ((z.A0 - z.N * c.one : ℕ) : ℝ) := by positivity
  constructor
  · rw [Nat.cast_sub hk.hG0]
    push_cast [Nat.cast_sub (NO_le_A0 hk), Nat.cast_sub (NO_le_A1 hv hk)]
    rw [oneR hv]
    push_cast [Nat.cast_sub (NO_le_A0 hk), Nat.cast_sub (NO_le_A1 hv hk), oneR hv] at hlo hhi
    nlinarith
  · have h1 : ((z.A0 - z.N * c.one : ℕ) : ℝ) ^ 2 ≤ x ^ 2 := by
      apply pow_le_pow_left₀ hP0 hlo
    nlinarith

theorem V_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (z.V0 : ℝ) ≤ vAng (RSInt.rsFrac t) * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  obtain ⟨hG, _⟩ := G_bounds hv hk
  have h : ((z.V0 * (4 * c.one * c.one) : ℕ) : ℝ) ≤ (((c.hp - c.rp) * (16 * (z.A0 - z.N * c.one) * c.one
      + c.one * c.one - 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one)) : ℕ) : ℝ) := by
    exact_mod_cast hk.hV0
  rw [Nat.cast_mul, Nat.cast_mul (c.hp - c.rp), Nat.cast_sub hk.hrp] at h
  have hpi := pi_lo hv
  have hr : (0 : ℝ) ≤ (c.hp : ℝ) - c.rp := by
    have : (c.rp : ℝ) ≤ c.hp := by exact_mod_cast hk.hrp
    linarith
  have hG0 : (0 : ℝ) ≤ (((16 * (z.A0 - z.N * c.one) * c.one + c.one * c.one
        - 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one) : ℕ)) : ℝ) := by positivity
  have h1 := mul_le_mul hpi hG hG0 (by positivity)
  have e : (π / 2 * 2 ^ c.P) * (16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2)
      = (vAng (RSInt.rsFrac t) * 2 ^ c.P) * (4 * 2 ^ c.P * 2 ^ c.P) := by unfold vAng; ring
  rw [e] at h1
  push_cast at h
  rw [oneR hv] at h
  have h2 : (z.V0 : ℝ) * (4 * 2 ^ c.P * 2 ^ c.P) ≤ (vAng (RSInt.rsFrac t) * 2 ^ c.P) * (4 * 2 ^ c.P * 2 ^ c.P) := by
    linarith
  exact le_of_mul_le_mul_right h2 (by positivity)

theorem V_hi (hv : Valid c t K) (hk : Checks5 c z) :
    vAng (RSInt.rsFrac t) * 2 ^ c.P ≤ (z.V1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  obtain ⟨hG, hG'⟩ := G_bounds hv hk
  have h : (((c.hp + c.rp) * (16 * (z.A1 - z.N * c.one) * c.one + c.one * c.one) : ℕ) : ℝ)
      ≤ ((z.V1 * (4 * c.one * c.one) + (c.hp + c.rp) * (16 * (z.A0 - z.N * c.one)
          * (z.A0 - z.N * c.one)) : ℕ) : ℝ) := by exact_mod_cast hk.hV1
  push_cast at h
  rw [oneR hv] at h
  have hpi := pi_hi hv
  have hG0 : (0 : ℝ) ≤ (((16 * (z.A0 - z.N * c.one) * c.one + c.one * c.one
        - 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one) : ℕ)) : ℝ) := by positivity
  have hg : 0 ≤ 16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2 := le_trans hG0 hG
  have h1 := mul_le_mul hpi hG' hg (by positivity)
  have e : (π / 2 * 2 ^ c.P) * (16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2)
      = (vAng (RSInt.rsFrac t) * 2 ^ c.P) * (4 * 2 ^ c.P * 2 ^ c.P) := by unfold vAng; ring
  rw [e] at h1
  have h2 : (vAng (RSInt.rsFrac t) * 2 ^ c.P) * (4 * 2 ^ c.P * 2 ^ c.P) ≤ (z.V1 : ℝ) * (4 * 2 ^ c.P * 2 ^ c.P) := by
    nlinarith
  exact le_of_mul_le_mul_right h2 (by positivity)

theorem psi_num_eq (p : ℝ) : Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) = Real.cos (vAng p) := by
  rw [← Real.cos_neg]; unfold vAng; congr 1; ring

end Facts

/-! ## 6. the quotient `Psi = cos v / cos 2 pi p` (denominator bounded away from 0) -/

theorem lin_le_max {F l u y : ℝ} (hl : l ≤ y) (hu : y ≤ u) : F * y ≤ F * l ∨ F * y ≤ F * u := by
  rcases le_total 0 F with hF | hF
  · exact Or.inr (mul_le_mul_of_nonneg_left hu hF)
  · exact Or.inl (mul_le_mul_of_nonpos_left hl hF)

theorem lin_ge_min {F l u y : ℝ} (hl : l ≤ y) (hu : y ≤ u) : F * l ≤ F * y ∨ F * u ≤ F * y := by
  rcases le_total 0 F with hF | hF
  · exact Or.inl (mul_le_mul_of_nonneg_left hl hF)
  · exact Or.inr (mul_le_mul_of_nonpos_left hu hF)

theorem quot_sound {o : ℕ} {O X Y : ℝ} {Nm D F0 F1 : ℤ} {rN rD : ℕ} (hO : (o : ℝ) = O)
    (hOp : 0 < O) (hX : |X * O - Nm| ≤ rN) (hY : |Y * O - D| ≤ rD)
    (hq : QuotOK o Nm rN D rD F0 F1) :
    Y ≠ 0 ∧ (F0 : ℝ) ≤ X / Y * O ∧ X / Y * O ≤ F1 := by
  rw [abs_le] at hX hY
  have eq : X / Y * O = (X * O) * O / (Y * O) := by
    by_cases hY0 : Y = 0
    · simp [hY0]
    · field_simp
  rcases hq with ⟨hD, a1, a2, a3, a4⟩ | ⟨hD, a1, a2, a3, a4⟩
  · have hD' : ((rD : ℤ) : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have a1' : ((F0 * (D - rD) : ℤ) : ℝ) ≤ (((Nm - rN) * o : ℤ) : ℝ) := by exact_mod_cast a1
    have a2' : ((F0 * (D + rD) : ℤ) : ℝ) ≤ (((Nm - rN) * o : ℤ) : ℝ) := by exact_mod_cast a2
    have a3' : (((Nm + rN) * o : ℤ) : ℝ) ≤ ((F1 * (D - rD) : ℤ) : ℝ) := by exact_mod_cast a3
    have a4' : (((Nm + rN) * o : ℤ) : ℝ) ≤ ((F1 * (D + rD) : ℤ) : ℝ) := by exact_mod_cast a4
    push_cast at hD' a1' a2' a3' a4'
    rw [hO] at a1' a2' a3' a4'
    have hYp : 0 < Y * O := by linarith
    have hY0 : Y ≠ 0 := by
      intro h; rw [h, zero_mul] at hYp; exact lt_irrefl _ hYp
    refine ⟨hY0, ?_, ?_⟩
    · rw [eq, le_div_iff₀ hYp]
      have hxo : ((Nm : ℝ) - rN) * O ≤ (X * O) * O := mul_le_mul_of_nonneg_right (by linarith [hX.1]) hOp.le
      rcases lin_le_max (F := (F0 : ℝ)) hY.1 hY.2 with h | h <;> nlinarith
    · rw [eq, div_le_iff₀ hYp]
      have hxo : (X * O) * O ≤ ((Nm : ℝ) + rN) * O := mul_le_mul_of_nonneg_right (by linarith [hX.2]) hOp.le
      rcases lin_ge_min (F := (F1 : ℝ)) hY.1 hY.2 with h | h <;> nlinarith
  · have hD' : (D : ℝ) + ((rD : ℤ) : ℝ) < 0 := by exact_mod_cast hD
    have a1' : (((Nm + rN) * o : ℤ) : ℝ) ≤ ((F0 * (D - rD) : ℤ) : ℝ) := by exact_mod_cast a1
    have a2' : (((Nm + rN) * o : ℤ) : ℝ) ≤ ((F0 * (D + rD) : ℤ) : ℝ) := by exact_mod_cast a2
    have a3' : ((F1 * (D - rD) : ℤ) : ℝ) ≤ (((Nm - rN) * o : ℤ) : ℝ) := by exact_mod_cast a3
    have a4' : ((F1 * (D + rD) : ℤ) : ℝ) ≤ (((Nm - rN) * o : ℤ) : ℝ) := by exact_mod_cast a4
    push_cast at hD' a1' a2' a3' a4'
    rw [hO] at a1' a2' a3' a4'
    have hYn : Y * O < 0 := by linarith
    have hY0 : Y ≠ 0 := by
      intro h; rw [h, zero_mul] at hYn; exact lt_irrefl _ hYn
    refine ⟨hY0, ?_, ?_⟩
    · rw [eq, le_div_iff_of_neg hYn]
      have hxo : (X * O) * O ≤ ((Nm : ℝ) + rN) * O := mul_le_mul_of_nonneg_right (by linarith [hX.2]) hOp.le
      rcases lin_ge_min (F := (F0 : ℝ)) hY.1 hY.2 with h | h <;> nlinarith
    · rw [eq, div_le_iff_of_neg hYn]
      have hxo : ((Nm : ℝ) - rN) * O ≤ (X * O) * O := mul_le_mul_of_nonneg_right (by linarith [hX.1]) hOp.le
      rcases lin_le_max (F := (F1 : ℝ)) hY.1 hY.2 with h | h <;> nlinarith

/-! ## 7. the main sum as `Re (e^{i phi} psum t N)` -/

theorem main_sum_eq (t φ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n)
      = Real.cos φ * (psum t N).re - Real.sin φ * (psum t N).im := by
  unfold psum
  rw [Complex.re_sum, Complex.im_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.Ico_add_one_right_eq_Icc]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 0 < n := (Finset.mem_Icc.mp hn).1
  obtain ⟨h1, h2⟩ := cpow_term n hn1 t
  rw [h1, h2, Real.cos_sub]
  have : (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt n := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.sqrt_eq_rpow, inv_eq_one_div]
  rw [this]
  ring

/-! ## 8. the DIntv assembly -/

section Assembly

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}

theorem mainBox_mem (hv : Valid c t K) (hk : Checks5 c z) {φ : ℝ}
    (hφ : |φ - RSInt.rsThetaMain t| ≤ 1 / t) :
    (mainBox c z).memR (2 * (Real.cos φ * (psum t z.N).re - Real.sin φ * (psum t z.N).im)) := by
  obtain ⟨_, _, _, _, hre, him⟩ := dstate_inv hv hk
  obtain ⟨hc, hs, _, _⟩ := trig_sound c t K hv φ z.TH0 z.TH1 (phase_lo hv hk hφ) (phase_hi hv hk hφ)
  unfold SBall at hc hs
  rw [← sgnI_cast] at hc hs
  have mre : (ballD c.P (((dstate c z).reP : ℤ) - (dstate c z).reN) (dstate c z).reR).memR
      (psum t z.N).re := ballD_mem (by push_cast; exact hre)
  have mim : (ballD c.P (((dstate c z).imP : ℤ) - (dstate c z).imN) (dstate c z).imR).memR
      (psum t z.N).im := ballD_mem (by push_cast; exact him)
  have mc : (ballD c.P (sgnI (phTrig c z).cs (phTrig c z).cm) (phTrig c z).cr).memR (Real.cos φ) :=
    ballD_mem hc
  have ms : (ballD c.P (sgnI (phTrig c z).ss (phTrig c z).sm) (phTrig c z).sr).memR (Real.sin φ) :=
    ballD_mem hs
  have m1 := DIntv.sub_sound (by rfl) (DIntv.mul_sound mc mre) (DIntv.mul_sound ms mim)
  have m2 := DIntv.add_sound (by rfl) m1 m1
  rw [show 2 * (Real.cos φ * (psum t z.N).re - Real.sin φ * (psum t z.N).im)
      = (Real.cos φ * (psum t z.N).re - Real.sin φ * (psum t z.N).im)
        + (Real.cos φ * (psum t z.N).re - Real.sin φ * (psum t z.N).im) by ring]
  exact m2

theorem neg_one_pow_eq (N : ℕ) :
    (-1 : ℝ) ^ (N + 1) = if (N % 2 == 1) = true then 1 else -1 := by
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · have hE : Even N := Nat.even_iff.mpr h
    rw [pow_succ, hE.neg_one_pow]
    simp [h]
  · have hO : Odd N := Nat.odd_iff.mpr h
    rw [pow_succ, hO.neg_one_pow]
    simp [h]

theorem c0Box_mem {w ψ : ℝ} (hw0 : (z.Q0 : ℝ) ≤ w * 2 ^ c.P) (hw1 : w * 2 ^ c.P ≤ z.Q1)
    (hψ0 : (z.F0 : ℝ) ≤ ψ * 2 ^ c.P) (hψ1 : ψ * 2 ^ c.P ≤ z.F1) :
    (c0Box c z).memR ((-1 : ℝ) ^ (z.N + 1) * w * ψ) := by
  have mw : DIntv.memR w ⟨(z.Q0 : ℤ), (z.Q1 : ℤ), -(c.P : ℤ)⟩ :=
    brD_mem (by exact_mod_cast hw0) (by exact_mod_cast hw1)
  have mψ : DIntv.memR ψ ⟨z.F0, z.F1, -(c.P : ℤ)⟩ := brD_mem hψ0 hψ1
  have m := negIf_mem (z.N % 2 == 1) (DIntv.mul_sound mw mψ)
  rw [neg_one_pow_eq]
  unfold c0Box
  split_ifs at m ⊢ with h
  · simpa using m
  · simpa using m

theorem zBox_e (c : Cfg) (z : Cert) : (zBox c z).e = -(c.P : ℤ) + -(c.P : ℤ) := rfl

end Assembly

/-! ## 9. THE SOUNDNESS THEOREM -/



end

end RS5


/-  RS5_Sound.lean -- lane B5: SOUNDNESS of the t >= 509 checker `RS5.check5`.

    This file is lane B4's `RS4_Sound` sections 1-9 (the checker's facts over the reals, the DIntv
    assembly and the soundness theorem) re-stated for `RS5.Checks5`, which differs from `RS4.Checks`
    ONLY in the height floor (`509 * 2^tq <= tn` instead of `10000 * 2^tq <= tn`).  The floor is used by
    exactly two facts, `t_ge` and `tn_pos`; every other proof is unchanged text.  The height-free
    helpers of `RS4_Sound` (`Zmain`, `Lser`, `log_one_add_near`, `lp_real`, `ballD_mem`, ...) and all
    computable definitions of `RS4_Eval` are REUSED (selective `open RS4 (...)`), not duplicated.

    ## The headline

      `RS5.check5_sound` : `Valid c t K` and `check5 c z = true` imply
        `509 <= t`, `rsNn t = z.N`, `0 < rsFrac t`, `cos (2 pi rsFrac t) ≠ 0`, and for EVERY phase
        `phi` with `|phi - rsThetaMain t| <= 1/t`:  `zlo / 2^(2P) <= RS4.Zmain t phi <= zhi / 2^(2P)`.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/



open Real Finset
open ArbEcon DIntvProd
open RS4 (Cert lpPos lpNeg sgnI ballD negIf dstate phTrig mainBox c0Box zBox QuotOK Zmain Lser
  log_one_add_near lp_real sgnI_cast two_zpow_negP ballD_mem brD_mem negIf_mem)

section
namespace RS5
end RS5
open RS5

noncomputable section

/-! ## 1. the checker's facts, over the reals -/

section Facts

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}























































/-! ## 2. the Dirichlet state: `psum t N` and `log N` -/







/-! ## 3. the phase ball -/











/-! ## 4. the C0 amplitude `(t/2pi)^(-1/4) = a^(-1/2)` -/









/-! ## 5. the angles `2 pi p` and `2 pi (p - p^2 + 1/16)` -/















end Facts

/-! ## 6. the quotient `Psi = cos v / cos 2 pi p` (denominator bounded away from 0) -/







/-! ## 7. the main sum as `Re (e^{i phi} psum t N)` -/



/-! ## 8. the DIntv assembly -/

section Assembly

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}









end Assembly

/-! ## 9. THE SOUNDNESS THEOREM -/


theorem solution {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert)
    (h : check5 c z = true) :
    509 ≤ t ∧ RSInt.rsNn t = z.N ∧ 0 < RSInt.rsFrac t ∧
      Real.cos (2 * π * RSInt.rsFrac t) ≠ 0 ∧
      ∀ φ : ℝ, |φ - RSInt.rsThetaMain t| ≤ 1 / t →
        (z.zlo : ℝ) / 2 ^ (2 * c.P) ≤ Zmain t φ ∧ Zmain t φ ≤ (z.zhi : ℝ) / 2 ^ (2 * c.P) := by
  have hk : Checks5 c z := checks5_of (of_decide_eq_true h)
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hN := N_eq hv hk
  -- the Psi quotient
  obtain ⟨hcU, _, _, _⟩ := trig_sound c t K hv (2 * π * RSInt.rsFrac t) z.U0 z.U1 (U_lo hv hk) (U_hi hv hk)
  obtain ⟨hcV, _, _, _⟩ := trig_sound c t K hv (vAng (RSInt.rsFrac t)) z.V0 z.V1 (V_lo hv hk) (V_hi hv hk)
  unfold SBall at hcU hcV
  rw [← sgnI_cast] at hcU hcV
  obtain ⟨hden, hψ0, hψ1⟩ := quot_sound (oneR hv) hP hcV hcU hk.hPsi
  refine ⟨t_ge hv hk, hN, frac_pos hv hk, hden, ?_⟩
  intro φ hφ
  have hm := mainBox_mem hv hk hφ
  have hc0 := c0Box_mem (c := c) (z := z) (w_lo hv hk) (w_hi hv hk) hψ0 hψ1
  have hz := DIntv.add_sound (by rfl) hm hc0
  have hZ : Zmain t φ = 2 * (Real.cos φ * (psum t z.N).re - Real.sin φ * (psum t z.N).im)
      + (-1 : ℝ) ^ (z.N + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ))
        * (Real.cos (vAng (RSInt.rsFrac t)) / Real.cos (2 * π * RSInt.rsFrac t)) := by
    unfold Zmain RSInt.rsPsi
    rw [hN, main_sum_eq, psi_num_eq]
  rw [hZ]
  change (zBox c z).memR _ at hz
  obtain ⟨hz0, hz1⟩ := hz
  rw [zBox_e] at hz0 hz1
  have e2 : (2 : ℝ) ^ (-(c.P : ℤ) + -(c.P : ℤ)) = 1 / 2 ^ (2 * c.P) := by
    rw [← neg_add, zpow_neg, ← two_mul, zpow_mul, zpow_natCast, one_div]
    norm_cast
    rw [← pow_mul, mul_comm]
  rw [e2] at hz0 hz1
  have hlo : (z.zlo : ℝ) ≤ ((zBox c z).lo : ℝ) := by exact_mod_cast hk.hzlo
  have hhi : ((zBox c z).hi : ℝ) ≤ (z.zhi : ℝ) := by exact_mod_cast hk.hzhi
  have hq : (0 : ℝ) < 1 / 2 ^ (2 * c.P) := by positivity
  constructor
  · calc (z.zlo : ℝ) / 2 ^ (2 * c.P) = (z.zlo : ℝ) * (1 / 2 ^ (2 * c.P)) := by ring
      _ ≤ ((zBox c z).lo : ℝ) * (1 / 2 ^ (2 * c.P)) := mul_le_mul_of_nonneg_right hlo hq.le
      _ ≤ _ := hz0
  · calc _ ≤ ((zBox c z).hi : ℝ) * (1 / 2 ^ (2 * c.P)) := hz1
      _ ≤ (z.zhi : ℝ) * (1 / 2 ^ (2 * c.P)) := mul_le_mul_of_nonneg_right hhi hq.le
      _ = (z.zhi : ℝ) / 2 ^ (2 * c.P) := by ring
