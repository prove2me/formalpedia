-- Prove2me | solution 1 for WilliamsonShmoys.component_arithmetic__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:14:06.20017+00:00
-- url     : https://prove2.me/submissions/cdf067a4-5e13-46a5-b10b-fe2bfc32d38e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_arithmetic_large__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
import Theorems.Thm_WilliamsonShmoys_component_arithmetic_small__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1

set_option autoImplicit false

theorem solution
    (n E : Nat)
    (parts : List (Prod Nat Nat))
    (hvertices : (parts.map Prod.fst).sum = n)
    (hedges : (parts.map Prod.snd).sum = E)
    (hparts : forall p, List.Mem p parts ->
      (3 <= p.1 -> p.2 <= 3 * p.1 - 6) /\
      (p.1 < 3 -> p.2 <= p.1))
    (hcard : 3 <= n) :
    E <= 3 * n - 6 := by
  classical
  by_cases hlarge : Exists (fun p => And (List.Mem p parts) (3 <= p.1))
  case pos =>
    exact WilliamsonShmoys.component_arithmetic_large__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
      n E parts hvertices hedges hparts hlarge
  case neg =>
    apply WilliamsonShmoys.component_arithmetic_small__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
      n E parts hvertices hedges hparts hcard
    intro p hp
    have hpSmall : p.1 < 3 := by
      by_contra h
      have hpLarge : 3 <= p.1 := by omega
      exact hlarge (Exists.intro p (And.intro hp hpLarge))
    exact hpSmall