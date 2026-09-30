-- Prove2me | solution 1 for WeierstrassEllipticZeta.weierstrassZeta_add_period
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T01:30:08.749025+00:00
-- url     : https://prove2.me/submissions/1891f46d-0e68-451b-bf2c-1518e0f2cdcc

import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta

noncomputable section

open Filter
open scoped Topology

open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) (ω z : ℂ)
    (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hshift (w : ℂ) (hw : w ∉ L.lattice) : w + ω ∉ L.lattice :=
    fun h ↦ hw (by simpa using L.lattice.sub_mem h hω)
  have hd (w : ℂ) (hw : w ∉ L.lattice) :
      HasDerivAt (fun x ↦ weierstrassZeta L (x + ω) - weierstrassZeta L x) 0 w := by
    have hs : HasDerivAt (fun x ↦ weierstrassZeta L (x + ω))
        (-L.weierstrassP (w + ω)) w := by
      convert! (hasDerivAt_weierstrassZeta L (w + ω) (hshift w hw)).comp w
        ((hasDerivAt_id w).add_const ω) using 1
      simp
    convert! hs.sub (hasDerivAt_weierstrassZeta L w hw) using 1
    rw [L.weierstrassP_add_coe w ⟨ω, hω⟩]
    ring
  have heq := hopen.is_const_of_deriv_eq_zero
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
    (fun w hw ↦ (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd w hw).deriv) hz L.ω₁_div_two_notMem_lattice
  change weierstrassZeta L (z + ω) - weierstrassZeta L z = zetaQuasiPeriod L ω at heq
  linear_combination heq
