-- Prove2me | solution 1 for Zeta23_conj_riemannZeta_conj_aux1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:40:47.971378+00:00
-- url     : https://prove2.me/submissions/30e5e6f9-80bd-48d5-8819-7f2216e81a17

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

-- from Zeta23.FromPNTPlus.ZetaConj
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaConj.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open scoped Complex ComplexConjugate


/- v4.30 port: Mathlib c5ea003 predates `riemannZeta_conj`, so we restore the local proof
from the v4.30-era PrimeNumberTheoremAnd/ZetaConj.lean (commit f55e855). -/






open scoped Complex ComplexConjugate

theorem solution (s : ℂ) (hs : 1 < s.re) :
    conj (riemannZeta (conj s)) = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa)]
  rw [Complex.conj_tsum]
  congr
  ext n
  have h1 : n + 1 ≠ 0 := by linarith
  have h2 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast h1
  rw [Complex.cpow_def_of_ne_zero h2, Complex.cpow_def_of_ne_zero h2, RCLike.conj_div, map_one,
    ← Complex.exp_conj, map_mul, Complex.conj_conj]
  congr 2
  rw [show (↑n + 1 : ℂ) = ↑((n + 1 : ℕ) : ℕ) from by push_cast; ring,
    ← Complex.natCast_log, Complex.conj_ofReal]
