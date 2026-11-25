-- Prove2me | solution 1 for SZ.digitReal_runY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:14:59.664699+00:00
-- url     : https://prove2.me/submissions/fc13599f-d1c7-4cfe-9b8a-b125c419e509

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_isDigits_run_snd
import Theorems.Thm_SZ_digitReal_compl


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    digitReal 3 (runY d) = 1 - digitReal 3 (fun i => (d i).2) := by
  have hfun : (fun i => ((3 : ℕ) : ℤ) - 1 - (d i).2) = runY d := by
    funext i; simp only [runY]; norm_num
  rw [← hfun, digitReal_compl (isDigits_run_snd hrun)]
end SZ
