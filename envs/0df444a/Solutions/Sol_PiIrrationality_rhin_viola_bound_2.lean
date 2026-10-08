-- Prove2me | solution 2 for PiIrrationality.rhin_viola_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T06:22:14.38686+00:00
-- url     : https://prove2.me/submissions/f8b40609-9d0f-4021-875b-7fc4ba4dac78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PiIrrationality_UpperBound
import Theorems.Thm_RhinViola_zetaTwoIrrationalityBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

-- v4c: fresh immutable source after checker-implementation drift; proof term unchanged.
open Filter

private theorem zetaTransferProof (m : ℝ) (hm : 0 < m)
    (hz : ∀ ε : ℝ, 0 < ε →
      ∃ Q : ℕ, ∀ p : ℤ, ∀ q : ℕ, Q ≤ q → 0 < q →
        (q : ℝ) ^ (-(m + ε)) <
          |Real.pi ^ 2 / 6 - (p : ℝ) / (q : ℝ)|) :
    PiIrrationality.UpperBound (2 * m) := by
  change ∀ ε : ℝ, 0 < ε →
    ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), 0 < q → Q ≤ q →
      1 / (q : ℝ) ^ (2 * m + ε) < |Real.pi - (p : ℝ) / (q : ℝ)|
  intro ε hε
  have hd : 0 < ε / 4 := by linarith
  obtain ⟨N, hN⟩ := hz (ε / 4) hd
  let R : ℝ := 2 * Real.pi + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let C : ℝ := R * (6 : ℝ) ^ (m + ε / 4)
  have hC : 0 < C := by dsimp [C]; positivity
  have hlim : Tendsto (fun q : ℕ => (q : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < ε / 2)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_atTop.1 hlim) C)
  refine ⟨max (max N M) 2, ?_⟩
  intro p q hq hQ
  have hq2 : 2 ≤ q := (le_max_right (max N M) 2).trans hQ
  have hNq : N ≤ q := (le_max_left N M).trans ((le_max_left (max N M) 2).trans hQ)
  have hMq : M ≤ q := (le_max_right N M).trans ((le_max_left (max N M) 2).trans hQ)
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1 : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hqn : (q : ℝ) ≠ 0 := ne_of_gt hqr
  have hQden : N ≤ 6 * q * q := by nlinarith
  have hdenpos : 0 < 6 * q * q := by positivity
  have hzq := hN (p * p) (6 * q * q) hQden hdenpos
  have hpow6 : (6 : ℝ) ^ (m + ε / 4) * (6 : ℝ) ^ (-(m + ε / 4)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
    simp
  have h6invpos : 0 < (6 : ℝ) ^ (-(m + ε / 4)) := by positivity
  have hsmallpos : 0 < (q : ℝ) ^ (-(2 * m + ε)) := by positivity
  have hcomp : R ≤ (q : ℝ) ^ (ε / 2) * (6 : ℝ) ^ (-(m + ε / 4)) := by
    have hs := mul_le_mul_of_nonneg_right (hM q hMq) h6invpos.le
    calc
      R = C * (6 : ℝ) ^ (-(m + ε / 4)) := by
        dsimp [C]
        rw [mul_assoc, hpow6, mul_one]
      _ ≤ _ := hs
  have hpowq :
      ((q : ℝ) ^ 2) ^ (-(m + ε / 4)) =
        (q : ℝ) ^ (-(2 * m + ε / 2)) := by
    calc
      _ = ((q : ℝ) ^ (2 : ℝ)) ^ (-(m + ε / 4)) :=
        congrArg (fun z : ℝ => z ^ (-(m + ε / 4)))
          (Real.rpow_natCast (q : ℝ) 2).symm
      _ = (q : ℝ) ^ ((2 : ℝ) * (-(m + ε / 4))) :=
        (Real.rpow_mul hqr.le _ _).symm
      _ = _ := by congr 1; ring
  have hsplit :
      (q : ℝ) ^ (-(2 * m + ε / 2)) =
        (q : ℝ) ^ (-(2 * m + ε)) * (q : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hqr]
    congr 1
    ring
  have hpowprod :
      ((6 : ℝ) * (q : ℝ) ^ 2) ^ (-(m + ε / 4)) =
        (6 : ℝ) ^ (-(m + ε / 4)) *
          (q : ℝ) ^ (-(2 * m + ε / 2)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by positivity)]
    rw [hpowq]
  have hlower :
      R * (q : ℝ) ^ (-(2 * m + ε)) ≤
        ((6 : ℝ) * (q : ℝ) ^ 2) ^ (-(m + ε / 4)) := by
    rw [hpowprod, hsplit]
    calc
      R * (q : ℝ) ^ (-(2 * m + ε)) ≤
          ((q : ℝ) ^ (ε / 2) * (6 : ℝ) ^ (-(m + ε / 4))) *
            (q : ℝ) ^ (-(2 * m + ε)) :=
        mul_le_mul_of_nonneg_right hcomp hsmallpos.le
      _ = _ := by ring
  have hden_cast :
      ((6 * q * q : ℕ) : ℝ) = (6 : ℝ) * (q : ℝ) ^ 2 := by
    push_cast
    ring
  have hfrac :
      (Real.pi ^ 2 / 6 - ((p * p : ℤ) : ℝ) / ((6 * q * q : ℕ) : ℝ)) =
        ((Real.pi - (p : ℝ) / (q : ℝ)) *
            (Real.pi + (p : ℝ) / (q : ℝ))) / 6 := by
    rw [hden_cast]
    push_cast
    field_simp [hqn]
    ring
  rw [hfrac, hden_cast] at hzq
  rw [abs_div, abs_mul] at hzq
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)] at hzq
  have htarget : (q : ℝ) ^ (-(2 * m + ε)) <
      |Real.pi - (p : ℝ) / (q : ℝ)| := by
    by_cases hfar : 1 ≤ |Real.pi - (p : ℝ) / (q : ℝ)|
    · exact (Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)).trans_le hfar
    · have hnear : |Real.pi - (p : ℝ) / (q : ℝ)| < 1 :=
        lt_of_not_ge hfar
      have hRbound : |Real.pi + (p : ℝ) / (q : ℝ)| ≤ R := by
        have hrewrite :
            Real.pi + (p : ℝ) / (q : ℝ) =
              2 * Real.pi - (Real.pi - (p : ℝ) / (q : ℝ)) := by ring
        rw [hrewrite]
        calc
          _ = |2 * Real.pi + -(Real.pi - (p : ℝ) / (q : ℝ))| := by ring
          _ ≤ |2 * Real.pi| + |-(Real.pi - (p : ℝ) / (q : ℝ))| :=
            abs_add_le _ _
          _ = 2 * Real.pi + |Real.pi - (p : ℝ) / (q : ℝ)| := by
            rw [abs_neg, abs_of_nonneg (by positivity)]
          _ ≤ R := by dsimp [R]; linarith
      have hchain :
          R * (q : ℝ) ^ (-(2 * m + ε)) <
            |Real.pi - (p : ℝ) / (q : ℝ)| * R / 6 := by
        calc
          _ ≤ ((6 : ℝ) * (q : ℝ) ^ 2) ^ (-(m + ε / 4)) := hlower
          _ < |Real.pi - (p : ℝ) / (q : ℝ)| *
              |Real.pi + (p : ℝ) / (q : ℝ)| / 6 := hzq
          _ ≤ _ := by gcongr
      have hmult :
          (q : ℝ) ^ (-(2 * m + ε)) * R <
            (|Real.pi - (p : ℝ) / (q : ℝ)| / 6) * R := by
        nlinarith [hchain]
      have hconclude :=
        (mul_lt_mul_iff_left₀ hR).mp hmult
      have hnonneg : 0 ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := abs_nonneg _
      linarith
  simpa only [one_div, Real.rpow_neg hqr.le] using htarget

theorem solution :
    PiIrrationality.UpperBound (14.797074 : ℝ) := by
  have h : PiIrrationality.UpperBound (2 * ((7398537 : ℝ) / 1000000)) :=
    zetaTransferProof ((7398537 : ℝ) / 1000000)
      (by norm_num) RhinViola.zetaTwoIrrationalityBound
  convert h using 1 <;> norm_num
