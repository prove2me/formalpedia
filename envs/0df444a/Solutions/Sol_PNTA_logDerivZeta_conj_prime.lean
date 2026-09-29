-- Prove2me | solution 1 for PNTA.logDerivZeta_conj_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-12T06:08:53.20711+00:00
-- url     : https://prove2.me/submissions/f47615ac-d76b-4c9c-9ed2-79214c75810e

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Theorems.Thm_PNTA_logDerivZeta_conj

open scoped Complex ComplexConjugate
open PNTA

theorem solution (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s
