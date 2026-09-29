-- Prove2me | solution 1 for RealInequalities.loglog_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:12:28.420438+00:00
-- url     : https://prove2.me/submissions/5b561599-772c-416b-af1a-cb2d1ef03d68

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 2000000

-- ===== Salt.MR.USetPins =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# USetPins — the §8.3 pin arithmetic (U-9a)

The `hU` ladder's parameter page.  Nothing analytic lives here: every statement is an
inequality between the §8.3 parameters (`P₈₃`, `Q₈₃`, `H₈₃`, the `J`-cutoff, the balance
`θ = ρ/3`, the annulus height `Tann`), proved from explicit `X`-gates.  Scope pins:
`docs/exploration/hsup-design.md`'s ⟦V4⟧ block (the U-9a bullet) and
`docs/exploration/hu-scope-0724.md` (the ratified pins P-i/P-ii/P-iii).

Every gate is **in-statement** (law #253): no `X` is ever assumed "large enough" off-stage.
The five stones:

* **P-1 `QJ_sq_subpoly` / `QJ_sq_le_rpow`** — `Q_J² ≤ exp(3(log X)^{1/2}) = X^{o(1)}`.
  This is **`T`-free**: it comes from the *definition* of `J` (MR §2, p.6: `J` is the
  largest `j` with `Q_j ≤ exp((log X)^{1/2})`), NOT from `Uset_thin`'s `hκ30` binder
  (route (a) of the ⟦V4⟧ bullet).  `Uset_thin`'s union factor is `card 𝒫 ≤ (Q_Jb+1)²`
  (`USetThin.card_dyadicPairs_le`), so this is exactly the budget the U-9 assembly spends.

* **P-2 `pin_Pii`** — the ratified pin P-ii, `Q_j < P_L12` for every `j ≤ Jb`.  The whole
  content is `log Q_J ≤ (log X)^{1/2} < (log X)^{1−θ} = log P₈₃`, valid because `θ < 1/2`.
  Without it Lemma 12's `hcoef` is FALSE on the `𝒰` row (deviation D3 of HU-SCOPE).

* **P-3 `pin_P83_le_Q83`** — the §8.3 window is nonempty, `P₈₃ ≤ Q₈₃`, exactly when
  `loglog X ≤ (log X)^θ`; `loglog_le_rpow` discharges that gate from a *stated* threshold
  (`4/θ² ≤ (log X)^θ`), so the composite `pin_P83_le_Q83_of_gate` carries no hidden `X₀`.

* **P-4 `TannGate`** — THE NEW ONE.  `hU`'s exit must carry
  `Tann ≥ exp(30(log X)^{1/2})` **in-statement**: `Uset_thin`'s `hκ30`
  (`30 ≤ log T / log Q_Jb`) is an assumption about the row height, and at a polylog `Tann`
  it is FALSE — an exit that silently drops it is vacuous.  The pair supplied here is
  the named gate + its discharge at the live row height (`X/log X ≤ Tann`), plus the
  FAILS-protection (`TannGate_fails_polylog`: the gate genuinely refuses polylog heights).

* **P-5 the balance page** — `θ := ρ/3` is *defined* by making the two legs meet:
  `5θ − 2ρ = −θ`.  At the un-halved Halász grade `ρ = 1/(32e)` the exit exponent is
  `−1/(96e) < −1/261`, which clears the door's `c₀ ≥ 1/500` with margin `1.916×`
  (`exit_margin`); at the halved grade `ρ = 1/(64e)` it is `−1/(192e) > −1/500` and the
  page FAILS (`halved_fails` — the cliff, recorded in Lean).

Source pins (D5): MR arXiv v4 (`1501.04585v4`) p.6 (`S`, the `P_j/Q_j/J` definitions),
p.24 (the `α_j` exponents), p.27 (`P = exp((log X)^{1−1/48})`, `Q = exp(log X/loglog X)`,
`H = (log X)^{1/48}`), p.29 (`∫_𝒰 ≪ (T/X+1)(log X)^{−1/48+o(1)}`).
-/

namespace Salt.MR

/-! ## §0  The parameters -/

/-- **The §8.3 Lemma-12 window, lower endpoint**: `P = exp((log X)^{1−θ})` (MR p.27, with
MR's `1/48` written as the balance pin `θ`). -/
noncomputable def P83 (X θ : ℝ) : ℝ := Real.exp ((Real.log X) ^ (1 - θ))

/-- **The §8.3 Lemma-12 window, upper endpoint**: `Q = exp(log X/loglog X)` (MR p.27). -/
noncomputable def Q83 (X : ℝ) : ℝ := Real.exp (Real.log X / Real.log (Real.log X))

/-- **The §8.3 Ramaré width**: `H = (log X)^θ` (MR p.27). -/
noncomputable def H83 (X θ : ℝ) : ℝ := (Real.log X) ^ θ

/-- **The balance pin** `θ := ρ/3` — the exponent at which §8.3's main leg
`(log X)^{5θ−2ρ}` and remainder leg `(log X)^{−θ}` meet (`balance_exponent`).  At the
Halász grade `ρ = 1/16` this is MR's own `θ = 1/48`. -/
noncomputable def theta83 (ρ : ℝ) : ℝ := ρ / 3

/-- **The B4 Halász grade** `ρ = 1/(32e)` — the un-halved Halász-direct route (the ⟦V4⟧
cost discovery: the `1/2` of `rhsFbound` is a free monotone downgrade, so the balance page
runs at `1/e`, not `1/(2e)`). -/
noncomputable def rhoB4 : ℝ := 1 / (32 * Real.exp 1)

/-! ## §1  The arithmetic micro-bank

`(log X)^{1/2}` is written as an `rpow` in every statement (that is the form the design
block and the consumer use); `Real.sqrt` is the working form inside proofs. -/

/-- The statement form `x ^ (1/2 : ℝ)` and the working form `√x` agree. -/
theorem rpow_half_eq_sqrt (x : ℝ) : x ^ ((1 : ℝ) / 2) = Real.sqrt x :=
  (Real.sqrt_eq_rpow x).symm

/-- `e · log s ≤ s` for `s > 0` — the sharp `log s ≤ s/e` majorant, in the
division-free form (the `√`-form majorant `log s ≤ 2(√s − 1)` is too lossy in the
polylog-refusal step below). -/
theorem exp_one_mul_log_le {s : ℝ} (hs : 0 < s) : Real.exp 1 * Real.log s ≤ s := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < s / Real.exp 1 by positivity)
  rw [Real.log_div (ne_of_gt hs) (Real.exp_ne_zero 1), Real.log_exp] at h
  have h2 : Real.log s ≤ s / Real.exp 1 := by linarith
  calc Real.exp 1 * Real.log s ≤ Real.exp 1 * (s / Real.exp 1) :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt he)
    _ = s := by field_simp

/-- **The loglog absorption.**  `loglog X ≤ (log X)^θ` for any `θ > 0`, from the stated
threshold `4/θ² ≤ (log X)^θ` (which is the honest `X₀(θ)`: `log X ≥ (4/θ²)^{1/θ}`).
At `θ = 1/(96e)` this is what lets the `o(1)` of §8.3's exit be absorbed. -/
theorem loglog_le_rpow (X θ : ℝ) (hθ : 0 < θ) (hX : Real.exp 1 ≤ Real.log X)
    (hgate : 4 / θ ^ 2 ≤ (Real.log X) ^ θ) :
    Real.log (Real.log X) ≤ (Real.log X) ^ θ := by
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have hL1 : (1 : ℝ) < Real.log X := lt_of_lt_of_le he1 hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hu0 : (0 : ℝ) < (Real.log X) ^ θ := Real.rpow_pos_of_pos hL0 θ
  have hsu0 : (0 : ℝ) < Real.sqrt ((Real.log X) ^ θ) := Real.sqrt_pos.mpr hu0
  have hsu : Real.sqrt ((Real.log X) ^ θ) * Real.sqrt ((Real.log X) ^ θ) = (Real.log X) ^ θ :=
    Real.mul_self_sqrt (le_of_lt hu0)
  -- the gate, in `√`-form : `2/θ ≤ √u`
  have hgate' : 2 / θ ≤ Real.sqrt ((Real.log X) ^ θ) := by
    rw [Real.le_sqrt (by positivity) (le_of_lt hu0)]
    calc (2 / θ) ^ 2 = 4 / θ ^ 2 := by rw [div_pow]; norm_num
      _ ≤ (Real.log X) ^ θ := hgate
  have hgate2 : 2 ≤ θ * Real.sqrt ((Real.log X) ^ θ) := by
    rw [div_le_iff₀ hθ] at hgate'
    linarith
  -- `log u = θ log L`, and `log u ≤ 2√u ≤ θ u`
  have hlogu : Real.log ((Real.log X) ^ θ) = θ * Real.log (Real.log X) :=
    Real.log_rpow hL0 θ
  have hlog2 : Real.log ((Real.log X) ^ θ) ≤ 2 * Real.sqrt ((Real.log X) ^ θ) := by
    have hhalf : Real.log (Real.sqrt ((Real.log X) ^ θ))
        = Real.log ((Real.log X) ^ θ) / 2 := Real.log_sqrt (le_of_lt hu0)
    have := Real.log_le_sub_one_of_pos hsu0
    rw [hhalf] at this
    linarith
  have hprod : 2 * Real.sqrt ((Real.log X) ^ θ) ≤ θ * (Real.log X) ^ θ := by
    calc 2 * Real.sqrt ((Real.log X) ^ θ)
        ≤ θ * Real.sqrt ((Real.log X) ^ θ) * Real.sqrt ((Real.log X) ^ θ) :=
          mul_le_mul_of_nonneg_right hgate2 (le_of_lt hsu0)
      _ = θ * (Real.log X) ^ θ := by rw [mul_assoc, hsu]
  have hbound : Real.log ((Real.log X) ^ θ) ≤ θ * (Real.log X) ^ θ := le_trans hlog2 hprod
  rw [hlogu] at hbound
  exact le_of_mul_le_mul_left hbound hθ

/-! ## §2  P-1 — `Q_J² ≤ X^{o(1)}`, `T`-free (the definition of `J`) -/

/-- **P-1 (the `T`-free budget).**  `J` is defined (MR §2, p.6) as the largest `j` with
`Q_j ≤ exp((log X)^{1/2})`; that hypothesis alone gives `Q_J² ≤ exp(3(log X)^{1/2})`.

No coupling to `T`: `Uset_thin`'s `hκ30` binder (`30 ≤ log T/log Q_Jb`) is NOT used, and
must not be — it would make the union factor's budget hostage to the row height. -/
theorem QJ_sq_subpoly (X : ℝ) (Qseq : ℕ → ℕ) (J : ℕ) (hX : 1 ≤ X)
    (hJdef : ((Qseq J : ℕ) : ℝ) ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2))) :
    ((Qseq J : ℕ) : ℝ) ^ 2 ≤ Real.exp (3 * (Real.log X) ^ ((1 : ℝ) / 2)) := by
  have hL0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX
  have hs0 : (0 : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hL0 _
  calc ((Qseq J : ℕ) : ℝ) ^ 2 = ((Qseq J : ℕ) : ℝ) * ((Qseq J : ℕ) : ℝ) := pow_two _
    _ ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)) * Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)) :=
        mul_self_le_mul_self (Nat.cast_nonneg _) hJdef
    _ = Real.exp (2 * (Real.log X) ^ ((1 : ℝ) / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (3 * (Real.log X) ^ ((1 : ℝ) / 2)) := Real.exp_le_exp.mpr (by linarith)

/-- **P-1 (the `X^{o(1)}` form).**  `Q_J² ≤ X^ε` for every `ε > 0`, from the same `T`-free
`J`-definition, once `(log X)^{1/2} ≥ 3/ε` — the gate is in-statement. -/
theorem QJ_sq_le_rpow (X ε : ℝ) (Qseq : ℕ → ℕ) (J : ℕ) (hX : 1 ≤ X)
    (hgate : 3 ≤ ε * (Real.log X) ^ ((1 : ℝ) / 2))
    (hJdef : ((Qseq J : ℕ) : ℝ) ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2))) :
    ((Qseq J : ℕ) : ℝ) ^ 2 ≤ X ^ ε := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hL0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX
  refine le_trans (QJ_sq_subpoly X Qseq J hX hJdef) ?_
  rw [Real.rpow_def_of_pos hX0]
  refine Real.exp_le_exp.mpr ?_
  rw [rpow_half_eq_sqrt] at hgate ⊢
  have hsq : Real.sqrt (Real.log X) * Real.sqrt (Real.log X) = Real.log X :=
    Real.mul_self_sqrt hL0
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log X) := Real.sqrt_nonneg _
  calc 3 * Real.sqrt (Real.log X)
      ≤ ε * Real.sqrt (Real.log X) * Real.sqrt (Real.log X) :=
        mul_le_mul_of_nonneg_right hgate hs0
    _ = Real.log X * ε := by rw [mul_assoc, hsq, mul_comm]

/-- **P-1, in the shape the union factor actually has.**  `USetThin.card_dyadicPairs_le`
bounds `card 𝒫` by `(Q_Jb+1)²`, not `Q_Jb²`; the `+1` costs nothing (`4` in place of `3` in
the gate).  This is the budget line of the U-9 assembly. -/
theorem QJ_succ_sq_le_rpow (X ε : ℝ) (Qseq : ℕ → ℕ) (J : ℕ) (hX : Real.exp 1 ≤ X)
    (hgate : 4 ≤ ε * (Real.log X) ^ ((1 : ℝ) / 2))
    (hJdef : ((Qseq J : ℕ) : ℝ) ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2))) :
    ((Qseq J + 1 : ℕ) : ℝ) ^ 2 ≤ X ^ ε := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at h
  have hs1 : (1 : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) := by
    rw [rpow_half_eq_sqrt, Real.le_sqrt (by norm_num) (by linarith)]
    simpa using hL1
  have he2 : (2 : ℝ) ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)) := by
    have h1 : Real.exp 1 ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)) := Real.exp_le_exp.mpr hs1
    have h2 := Real.exp_one_gt_d9
    linarith
  have hstep : ((Qseq J + 1 : ℕ) : ℝ)
      ≤ Real.exp (2 * (Real.log X) ^ ((1 : ℝ) / 2)) := by
    have hcast : ((Qseq J + 1 : ℕ) : ℝ) = ((Qseq J : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast, show (2 : ℝ) * (Real.log X) ^ ((1 : ℝ) / 2)
        = (Real.log X) ^ ((1 : ℝ) / 2) + (Real.log X) ^ ((1 : ℝ) / 2) by ring, Real.exp_add]
    nlinarith [hJdef, he2]
  have hsq : ((Qseq J + 1 : ℕ) : ℝ) ^ 2
      ≤ Real.exp (4 * (Real.log X) ^ ((1 : ℝ) / 2)) := by
    calc ((Qseq J + 1 : ℕ) : ℝ) ^ 2 = ((Qseq J + 1 : ℕ) : ℝ) * ((Qseq J + 1 : ℕ) : ℝ) :=
          pow_two _
      _ ≤ Real.exp (2 * (Real.log X) ^ ((1 : ℝ) / 2))
            * Real.exp (2 * (Real.log X) ^ ((1 : ℝ) / 2)) :=
          mul_self_le_mul_self (Nat.cast_nonneg _) hstep
      _ = Real.exp (4 * (Real.log X) ^ ((1 : ℝ) / 2)) := by rw [← Real.exp_add]; congr 1; ring
  refine le_trans hsq ?_
  rw [Real.rpow_def_of_pos hX0]
  refine Real.exp_le_exp.mpr ?_
  rw [rpow_half_eq_sqrt] at hgate ⊢
  have hsq' : Real.sqrt (Real.log X) * Real.sqrt (Real.log X) = Real.log X :=
    Real.mul_self_sqrt (by linarith)
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log X) := Real.sqrt_nonneg _
  calc 4 * Real.sqrt (Real.log X)
      ≤ ε * Real.sqrt (Real.log X) * Real.sqrt (Real.log X) :=
        mul_le_mul_of_nonneg_right hgate hs0
    _ = Real.log X * ε := by rw [mul_assoc, hsq', mul_comm]

/-- The `J`-definition, in `log` form: `log Q_J ≤ (log X)^{1/2}`.  (`kappa30_of_TannGate`
consumes this shape.) -/
theorem log_le_of_Jdef (X : ℝ) (Q : ℕ) (hQ0 : 0 < Q)
    (hJdef : ((Q : ℕ) : ℝ) ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2))) :
    Real.log Q ≤ (Real.log X) ^ ((1 : ℝ) / 2) := by
  have hQpos : (0 : ℝ) < ((Q : ℕ) : ℝ) := by exact_mod_cast hQ0
  have h := Real.log_le_log hQpos hJdef
  rwa [Real.log_exp] at h

/-! ## §3  P-2 — the ratified pin `Q_j < P_L12` (`hcoef`'s guard) -/

/-- The `J`-cutoff exponent sits strictly below the §8.3 window exponent: `(log X)^{1/2} <
(log X)^{1−θ}` whenever `θ < 1/2` and `log X > 1`. -/
theorem sqrt_log_lt_rpow_one_sub (X θ : ℝ) (hX : 1 < Real.log X) (hθ : θ < 1 / 2) :
    (Real.log X) ^ ((1 : ℝ) / 2) < (Real.log X) ^ (1 - θ) :=
  Real.rpow_lt_rpow_of_exponent_lt hX (by linarith)

/-- **P-2 — the ratified pin P-ii**: every `𝒰`-block sits strictly below the §8.3 Lemma-12
window, `Q_j < P₈₃` for all `j ≤ Jb`.  Content: `Q_j ≤ Q_J ≤ exp((log X)^{1/2}) <
exp((log X)^{1−θ}) = P₈₃`.  This is the hypothesis that makes Lemma 12's `hcoef` true on
the `𝒰` row (HU-SCOPE's deviation D3). -/
theorem pin_Pii (X θ : ℝ) (Qseq : ℕ → ℕ) (J Jb : ℕ) (hθ : θ < 1 / 2) (hX : 1 < Real.log X)
    (hJdef : ((Qseq J : ℕ) : ℝ) ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)))
    (hQmono : ∀ i j : ℕ, i ≤ j → Qseq i ≤ Qseq j) (hJbJ : Jb ≤ J) :
    ∀ j : ℕ, j ≤ Jb → ((Qseq j : ℕ) : ℝ) < P83 X θ := by
  intro j hj
  have h1 : ((Qseq j : ℕ) : ℝ) ≤ ((Qseq J : ℕ) : ℝ) := by
    exact_mod_cast hQmono j J (le_trans hj hJbJ)
  refine lt_of_le_of_lt (le_trans h1 hJdef) ?_
  unfold P83
  exact Real.exp_lt_exp.mpr (sqrt_log_lt_rpow_one_sub X θ hX hθ)

/-- **P-2, in `ℕ` — the `hcoef` guard as Lemma 12 wants it.**  Lemma 12's window endpoint
`P` is a natural number; for any `P` at or above `P₈₃` the pin reads `Q_j < P` in `ℕ`. -/
theorem pin_Pii_nat (X θ : ℝ) (Qseq : ℕ → ℕ) (J Jb P : ℕ) (hθ : θ < 1 / 2)
    (hX : 1 < Real.log X)
    (hJdef : ((Qseq J : ℕ) : ℝ) ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)))
    (hQmono : ∀ i j : ℕ, i ≤ j → Qseq i ≤ Qseq j) (hJbJ : Jb ≤ J)
    (hP : P83 X θ ≤ (P : ℝ)) :
    ∀ j : ℕ, j ≤ Jb → Qseq j < P := by
  intro j hj
  have h := pin_Pii X θ Qseq J Jb hθ hX hJdef hQmono hJbJ j hj
  exact_mod_cast lt_of_lt_of_le h hP

/-! ## §4  P-3 — the §8.3 window is nonempty -/

/-- **P-3 — `P₈₃ ≤ Q₈₃`**, i.e. the §8.3 Lemma-12 window `[exp((log X)^{1−θ}),
exp(log X/loglog X)]` is nonempty.  The gate is exactly `loglog X ≤ (log X)^θ`, stated. -/
theorem pin_P83_le_Q83 (X θ : ℝ) (hX : Real.exp 1 ≤ Real.log X)
    (hloglog : Real.log (Real.log X) ≤ (Real.log X) ^ θ) :
    P83 X θ ≤ Q83 X := by
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have hL1 : (1 : ℝ) < Real.log X := lt_of_lt_of_le he1 hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at h
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  unfold P83 Q83
  refine Real.exp_le_exp.mpr ?_
  rw [le_div_iff₀ hLL0]
  calc (Real.log X) ^ (1 - θ) * Real.log (Real.log X)
      ≤ (Real.log X) ^ (1 - θ) * (Real.log X) ^ θ :=
        mul_le_mul_of_nonneg_left hloglog (Real.rpow_nonneg (le_of_lt hL0) _)
    _ = Real.log X := by
        rw [← Real.rpow_add hL0, show (1 : ℝ) - θ + θ = 1 by ring, Real.rpow_one]

/-- **P-3, gate discharged.**  `P₈₃ ≤ Q₈₃` from the stated threshold `4/θ² ≤ (log X)^θ`
alone (no hidden `X₀`). -/
theorem pin_P83_le_Q83_of_gate (X θ : ℝ) (hθ : 0 < θ) (hX : Real.exp 1 ≤ Real.log X)
    (hgate : 4 / θ ^ 2 ≤ (Real.log X) ^ θ) :
    P83 X θ ≤ Q83 X :=
  pin_P83_le_Q83 X θ hX (loglog_le_rpow X θ hθ hX hgate)

/-- **The Ramaré-width pin.**  Lemma 12 (`RamareErr.lemma12_meansq_sharp`) binds `2 ≤ H`;
at the §8.3 width `H₈₃ = (log X)^θ` that binder is exactly the stated gate
`exp(log 2/θ) ≤ log X`. -/
theorem two_le_H83 (X θ : ℝ) (hθ : 0 < θ) (hX : Real.exp (Real.log 2 / θ) ≤ Real.log X) :
    2 ≤ H83 X θ := by
  unfold H83
  have h1 : (0 : ℝ) < Real.exp (Real.log 2 / θ) := Real.exp_pos _
  have h2 : (Real.exp (Real.log 2 / θ)) ^ θ ≤ (Real.log X) ^ θ :=
    Real.rpow_le_rpow (le_of_lt h1) hX (le_of_lt hθ)
  have h3 : (Real.exp (Real.log 2 / θ)) ^ θ = 2 := by
    rw [Real.rpow_def_of_pos h1, Real.log_exp, div_mul_cancel₀ _ (ne_of_gt hθ)]
    exact Real.exp_log (by norm_num)
  rwa [h3] at h2

/-! ## §5  P-4 — THE `Tann` GATE (the new one)

`Uset_thin` (`Salt.MR.USetThin`) carries `hκ30 : 30 ≤ log T / log Q_Jb`.  Instantiated at
the `J`-block, `log Q_J ≤ (log X)^{1/2}`, that binder is *implied by* — and at the pin is
equivalent to — the height condition `T ≥ exp(30(log X)^{1/2})`.  It is FALSE at any
polylog height, so `hU`'s exit must carry it in-statement or the exit is vacuous. -/

/-- **The `Tann` gate**: the §8.3 row height must satisfy `Tann ≥ exp(30(log X)^{1/2})`.
This is `Uset_thin`'s `hκ30` at the `J`-block, in height form; `hU`'s exit MUST carry it
(a polylog `Tann` makes the thinness row vacuous — `TannGate_fails_polylog`). -/
def TannGate (X Tann : ℝ) : Prop := Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) ≤ Tann

/-- The gate is monotone in the height. -/
theorem TannGate_mono {X Tann Tann' : ℝ} (h : TannGate X Tann) (hle : Tann ≤ Tann') :
    TannGate X Tann' := le_trans h hle

/-- **The `hκ30` bridge**: at the pin `log Q_Jb ≤ (log X)^{1/2}` the height gate delivers
`Uset_thin`'s binder `30 ≤ log T/log Q_Jb` verbatim. -/
theorem kappa30_of_TannGate (X Tann : ℝ) (Q : ℕ) (hQ1 : 1 < (Q : ℝ))
    (hQpin : Real.log Q ≤ (Real.log X) ^ ((1 : ℝ) / 2))
    (hT : TannGate X Tann) :
    30 ≤ Real.log Tann / Real.log Q := by
  have hlogQ : (0 : ℝ) < Real.log Q := Real.log_pos hQ1
  have hTpos : (0 : ℝ) < Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) := Real.exp_pos _
  have hTann : (0 : ℝ) < Tann := lt_of_lt_of_le hTpos hT
  have hlog : 30 * (Real.log X) ^ ((1 : ℝ) / 2) ≤ Real.log Tann := by
    have h := Real.log_le_log hTpos hT
    rwa [Real.log_exp] at h
  rw [le_div_iff₀ hlogQ]
  calc 30 * Real.log Q ≤ 30 * (Real.log X) ^ ((1 : ℝ) / 2) := by linarith
    _ ≤ Real.log Tann := hlog

/-- **P-4 (the discharge) — the gate HOLDS at the live row height.**  The §8.3 annulus runs
to `Tann ≍ X/log X`; there `Tann ≥ exp(30(log X)^{1/2})` for every `X` with
`log X ≥ 1024`.  (`s := √log X ≥ 32` and `log X − loglog X ≥ s² − 2s ≥ 30s`.) -/
theorem TannGate_of_row_height (X Tann : ℝ) (hX0 : 0 < X) (hL : 1024 ≤ Real.log X)
    (hTann : X / Real.log X ≤ Tann) : TannGate X Tann := by
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have h1024 : Real.sqrt 1024 = 32 := by
    rw [show (1024 : ℝ) = 32 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hs32 : (32 : ℝ) ≤ Real.sqrt (Real.log X) := by
    rw [← h1024]; exact Real.sqrt_le_sqrt hL
  have hspos : (0 : ℝ) < Real.sqrt (Real.log X) := by linarith
  have hsq : Real.sqrt (Real.log X) * Real.sqrt (Real.log X) = Real.log X :=
    Real.mul_self_sqrt (le_of_lt hL0)
  have hlogL : Real.log (Real.log X)
      = Real.log (Real.sqrt (Real.log X)) + Real.log (Real.sqrt (Real.log X)) := by
    conv_lhs => rw [← hsq]
    exact Real.log_mul (ne_of_gt hspos) (ne_of_gt hspos)
  have hlog1 : Real.log (Real.sqrt (Real.log X)) ≤ Real.sqrt (Real.log X) - 1 :=
    Real.log_le_sub_one_of_pos hspos
  have hkey : 30 * Real.sqrt (Real.log X) ≤ Real.log X - Real.log (Real.log X) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt (Real.log X) - 32)
      (le_of_lt hspos)]
  have hXL : Real.exp (Real.log X - Real.log (Real.log X)) = X / Real.log X := by
    rw [← Real.log_div (ne_of_gt hX0) (ne_of_gt hL0), Real.exp_log (div_pos hX0 hL0)]
  unfold TannGate
  refine le_trans ?_ hTann
  rw [rpow_half_eq_sqrt, ← hXL]
  exact Real.exp_le_exp.mpr hkey

/-- **P-4 (FAILS-protection, the general form).**  Anything strictly below the gate height
refuses it — so an exit that drops the gate is not merely weaker, it is unsound. -/
theorem not_TannGate_of_lt (X Tann : ℝ)
    (h : Tann < Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2))) : ¬ TannGate X Tann :=
  not_le.mpr h

/-- **P-4 (FAILS-protection, the polylog instance).**  A polylog height `Tann = (log X)^k`
never meets the gate, whenever `k·loglog X < 30(log X)^{1/2}` (stated). -/
theorem TannGate_fails_polylog (X : ℝ) (k : ℕ) (hX : 1 < Real.log X)
    (hk : (k : ℝ) * Real.log (Real.log X) < 30 * (Real.log X) ^ ((1 : ℝ) / 2)) :
    ¬ TannGate X ((Real.log X) ^ k) := by
  refine not_TannGate_of_lt X _ ?_
  have hpos : (0 : ℝ) < (Real.log X) ^ k := by positivity
  have hlog : Real.log ((Real.log X) ^ k) = (k : ℝ) * Real.log (Real.log X) :=
    Real.log_pow (Real.log X) k
  calc (Real.log X) ^ k = Real.exp (Real.log ((Real.log X) ^ k)) := (Real.exp_log hpos).symm
    _ = Real.exp ((k : ℝ) * Real.log (Real.log X)) := by rw [hlog]
    _ < Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) := Real.exp_lt_exp.mpr hk

/-- **P-4 (FAILS-protection, unconditional in `X` up to degree 40).**  For any polylog
degree `k ≤ 40` the gate fails at `Tann = (log X)^k` for EVERY `X` with `log X > 1`: the
`log s ≤ s/e` majorant gives `k·loglog X ≤ (80/e)√log X < 30√log X`. -/
theorem TannGate_fails_polylog_deg (X : ℝ) (k : ℕ) (hk : k ≤ 40) (hX : 1 < Real.log X) :
    ¬ TannGate X ((Real.log X) ^ k) := by
  refine TannGate_fails_polylog X k hX ?_
  rw [rpow_half_eq_sqrt]
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hs1 : (1 : ℝ) < Real.sqrt (Real.log X) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hX
  have hsq : Real.sqrt (Real.log X) * Real.sqrt (Real.log X) = Real.log X :=
    Real.mul_self_sqrt (le_of_lt hL0)
  have hlogL : Real.log (Real.log X)
      = Real.log (Real.sqrt (Real.log X)) + Real.log (Real.sqrt (Real.log X)) := by
    conv_lhs => rw [← hsq]
    exact Real.log_mul (by linarith) (by linarith)
  have hmaj : Real.exp 1 * Real.log (Real.sqrt (Real.log X)) ≤ Real.sqrt (Real.log X) :=
    exp_one_mul_log_le (by linarith)
  have hlogs0 : (0 : ℝ) < Real.log (Real.sqrt (Real.log X)) := Real.log_pos hs1
  have hk40 : (k : ℝ) ≤ 40 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  nlinarith [hlogL, hmaj, hlogs0, hk40, hk0, he, hs1]

/-! ## §6  P-5 — the balance page (`θ = ρ/3`) and the exit -/

/-- **The balance identity.**  `θ := ρ/3` is exactly the pin at which §8.3's main leg
`(log X)^{5θ−2ρ}` and remainder leg `(log X)^{−θ}` have the same exponent. -/
theorem balance_exponent (ρ : ℝ) : 5 * theta83 ρ - 2 * ρ = -theta83 ρ := by
  unfold theta83; ring

/-- The balance identity, on the `(log X)`-powers themselves. -/
theorem balance_main_eq_rem (X ρ : ℝ) :
    (Real.log X) ^ (5 * theta83 ρ - 2 * ρ) = (Real.log X) ^ (-theta83 ρ) := by
  rw [balance_exponent]

/-- **P-5 (the exit shape).**  With the main leg at `(log X)^{5θ−2ρ}` and the remainder leg
at `(T/X+1)(log X)^{−θ+ε}`, the balance pin `θ = ρ/3` collapses both into the single
`(T/X+1)(log X)^{−θ+ε}` shape (constant `2`).  This is the arithmetic the U-9 assembly
consumes; `ε` is the `o(1)`. -/
theorem balance_exit (X T ρ ε M R : ℝ) (hε : 0 ≤ ε) (hL : 1 ≤ Real.log X)
    (hTX : 0 ≤ T / X)
    (hM : M ≤ (Real.log X) ^ (5 * theta83 ρ - 2 * ρ))
    (hR : R ≤ (T / X + 1) * (Real.log X) ^ (-theta83 ρ + ε)) :
    M + R ≤ 2 * ((T / X + 1) * (Real.log X) ^ (-theta83 ρ + ε)) := by
  have hstep : (Real.log X) ^ (-theta83 ρ) ≤ (Real.log X) ^ (-theta83 ρ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hpow0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta83 ρ + ε) :=
    Real.rpow_nonneg (by linarith) _
  have hM' : M ≤ (Real.log X) ^ (-theta83 ρ + ε) := by
    rw [balance_main_eq_rem] at hM; linarith
  have hM'' : M ≤ (T / X + 1) * (Real.log X) ^ (-theta83 ρ + ε) := by
    refine le_trans hM' ?_
    nlinarith [hpow0, hTX]
  linarith

/-! ### The numerics at the B4 grade `ρ = 1/(32e)` -/

/-- `θ(ρ_B4) = 1/(96e)`. -/
theorem theta83_rhoB4 : theta83 rhoB4 = 1 / (96 * Real.exp 1) := by
  unfold theta83 rhoB4
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  field_simp
  norm_num

/-- `θ(ρ_B4) > 0`. -/
theorem theta83_rhoB4_pos : 0 < theta83 rhoB4 := by
  rw [theta83_rhoB4]
  positivity

/-- **The exit exponent**: `1/261 ≤ 1/(96e) = θ(ρ_B4)` — the §8.3 exit is
`(T/X+1)(log X)^{−1/(96e)+o(1)}`, i.e. at worst `(log X)^{−1/261+o(1)}`. -/
theorem exit_exponent_ge : (1 : ℝ) / 261 ≤ theta83 rhoB4 := by
  rw [theta83_rhoB4, div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [Real.exp_one_lt_d9]

/-- **The door's floor is cleared**: `c₀ = 1/500 ≤ θ(ρ_B4)`. -/
theorem c0_le_exit_exponent : (1 : ℝ) / 500 ≤ theta83 rhoB4 := by
  rw [theta83_rhoB4, div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [Real.exp_one_lt_d9]

/-- **The margin — `1.916×`.**  `θ(ρ_B4) = 1/(96e) ≥ 1.916/500`: the §8.3 exit clears the
door's `c₀ ≥ 1/500` with the ⟦V4⟧ margin. -/
theorem exit_margin : (1.916 : ℝ) / 500 ≤ theta83 rhoB4 := by
  rw [theta83_rhoB4, div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [Real.exp_one_lt_d9]

/-- **The `o(1)` still clears the floor.**  Any `ε ≤ 1/1000` leaves `θ(ρ_B4) − ε ≥ 1/500`. -/
theorem exit_beats_c0 (ε : ℝ) (hε : ε ≤ 1 / 1000) : (1 : ℝ) / 500 ≤ theta83 rhoB4 - ε := by
  have h := exit_margin
  have h2 : (1.916 : ℝ) / 500 - 1 / 1000 ≥ 1 / 500 := by norm_num
  linarith

/-- **The cliff, in Lean.**  At the *halved* Halász grade `ρ = 1/(64e)` the balance exit is
`θ = 1/(192e) < 1/500` and the §8.3 page FAILS the door's floor (by ≈ 4.2%).  This is why
the un-halved route matters: the ⟦V4⟧ ruling, recorded as arithmetic. -/
theorem halved_fails : theta83 (1 / (64 * Real.exp 1)) < 1 / 500 := by
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hpos : (0 : ℝ) < 192 * Real.exp 1 := by positivity
  have hval : theta83 (1 / (64 * Real.exp 1)) = 1 / (192 * Real.exp 1) := by
    unfold theta83
    field_simp
    norm_num
  rw [hval, div_lt_div_iff₀ hpos (by norm_num)]
  nlinarith [Real.exp_one_gt_d9]

/-- **P-5 (the exit at the pin).**  The §8.3 balance exit in its concrete B4 form:
`main + remainder ≤ 2(T/X+1)(log X)^{−1/(96e)+o(1)}`. -/
theorem balance_exit_B4 (X T ε M R : ℝ) (hε : 0 ≤ ε) (hL : 1 ≤ Real.log X)
    (hTX : 0 ≤ T / X)
    (hM : M ≤ (Real.log X) ^ (5 * theta83 rhoB4 - 2 * rhoB4))
    (hR : R ≤ (T / X + 1) * (Real.log X) ^ (-(1 / (96 * Real.exp 1)) + ε)) :
    M + R ≤ 2 * ((T / X + 1) * (Real.log X) ^ (-(1 / (96 * Real.exp 1)) + ε)) := by
  have h := balance_exit X T rhoB4 ε M R hε hL hTX hM (by rwa [theta83_rhoB4])
  rwa [theta83_rhoB4] at h

/-- **The loglog absorption at the pin.**  `loglog X ≤ (log X)^{θ(ρ_B4)}` from the stated
threshold `4/θ² ≤ (log X)^θ` — the `o(1)` of §8.3's exit is absorbable at `ρ = 1/(32e)`
(it is NOT at `1/(64e)`, where the page has already failed by `halved_fails`). -/
theorem loglog_absorb_B4 (X : ℝ) (hX : Real.exp 1 ≤ Real.log X)
    (hgate : 4 / (theta83 rhoB4) ^ 2 ≤ (Real.log X) ^ (theta83 rhoB4)) :
    Real.log (Real.log X) ≤ (Real.log X) ^ (theta83 rhoB4) :=
  loglog_le_rpow X (theta83 rhoB4) theta83_rhoB4_pos hX hgate

end Salt.MR

end




theorem solution (X θ : ℝ) (hθ : 0 < θ) (hX : Real.exp 1 ≤ Real.log X)
    (hgate : 4 / θ ^ 2 ≤ (Real.log X) ^ θ) :
    Real.log (Real.log X) ≤ (Real.log X) ^ θ := by
  apply Salt.MR.loglog_le_rpow <;> assumption

