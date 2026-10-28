-- Prove2me | solution 1 for SolarTariff.Fair.T3_threshold
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:24:45.299391+00:00
-- url     : https://prove2.me/submissions/9d82cf7c-1c4d-42fe-ae23-86637c9cb35a

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

open SolarTariff.Fair in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (τ : T3 ι) (i : ι) (hg : 0 < M.g i) :
    threshold M (τ.bills M) i = τ.pr - τ.f i / M.g i := by
  unfold threshold T3.bills gridUsage
  simp only
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hg.ne']
  ring
