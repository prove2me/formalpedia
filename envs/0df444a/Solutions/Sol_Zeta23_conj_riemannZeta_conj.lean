-- Prove2me | solution 1 for Zeta23_conj_riemannZeta_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:39:53.09646+00:00
-- url     : https://prove2.me/submissions/4f150f5f-9e75-4650-9a2b-c49f73f7979a

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Theorems.Thm_Zeta23_conj_riemannZeta_conj_aux1

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

theorem solution (s : ℂ) : conj (riemannZeta (conj s)) = riemannZeta s := by
  rw [riemannZeta_conj, Complex.conj_conj]
