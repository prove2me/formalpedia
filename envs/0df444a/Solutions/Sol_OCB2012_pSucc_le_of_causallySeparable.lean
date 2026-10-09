-- Prove2me | solution 1 for OCB2012.pSucc_le_of_causallySeparable
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:14:19.30259+00:00
-- url     : https://prove2.me/submissions/e1318575-e6b1-4a8b-aad9-41d72a84e65e

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Theorems.Thm_OCB2012_pSucc_le_of_noSignalBtoA
import Theorems.Thm_OCB2012_pSucc_le_of_noSignalAtoB

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol
open OCB2012

/-- `p_succ` is affine in the process matrix. -/
lemma pSucc_affine {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1] [Fintype b2]
    (W1 W2 : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (q : ℝ)
    (MA : Bool → Bool → Matrix (a1 × a2) (a1 × a2) ℂ)
    (MB : Bool → Bool → Bool → Matrix (b1 × b2) (b1 × b2) ℂ) :
    pSucc ((q : ℂ) • W1 + ((1 - q : ℝ) : ℂ) • W2) MA MB =
      q * pSucc W1 MA MB + (1 - q) * pSucc W2 MA MB := by
  have h : ∀ MA' MB', prob ((q : ℂ) • W1 + ((1 - q : ℝ) : ℂ) • W2) MA' MB' =
      (q : ℂ) * prob W1 MA' MB' + ((1 - q : ℝ) : ℂ) * prob W2 MA' MB' := by
    intro MA' MB'
    simp only [prob, Matrix.add_mul, Matrix.smul_mul, trace_add, trace_smul, smul_eq_mul]
  simp only [pSucc, h, Complex.add_re, Complex.re_ofReal_mul, Fintype.sum_bool]
  ring

end OCB2012Sol

open OCB2012 OCB2012Sol in
theorem solution {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (hW : IsCausallySeparable W)
    (MA : Bool → Bool → Matrix (a1 × a2) (a1 × a2) ℂ) (hMA : IsAliceInstrument MA)
    (MB : Bool → Bool → Bool → Matrix (b1 × b2) (b1 × b2) ℂ) (hMB : IsBobInstrument MB) :
    pSucc W MA MB ≤ 3 / 4 := by
  obtain ⟨q, hq0, hq1, WBA, WAB, hBA, hBAf, hAB, hABf, rfl⟩ := hW
  rw [pSucc_affine]
  have h1 := pSucc_le_of_noSignalBtoA WBA hBA hBAf MA hMA MB hMB
  have h2 := pSucc_le_of_noSignalAtoB WAB hAB hABf MA hMA MB hMB
  nlinarith
