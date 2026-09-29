-- Prove2me | solution 1 for PNTA.logDerivZeta_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-12T06:08:00.144601+00:00
-- url     : https://prove2.me/submissions/09be78d1-cb02-472f-9151-81930d8c3c7f

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Theorems.Thm_deriv_riemannZeta_conj
import Theorems.Thm_riemannZeta_conj

open scoped Complex ComplexConjugate

theorem solution (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]
