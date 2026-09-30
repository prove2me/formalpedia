-- Prove2me | solution 1 for WeierstrassEllipticZeta.hasDerivAt_weierstrassZeta
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T00:01:15.758258+00:00
-- url     : https://prove2.me/submissions/0fa44f18-de5e-4680-a68c-a774f650390c

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Theorems.Thm_WeierstrassEllipticZeta_hasSumLocallyUniformly_zetaSeries

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

private lemma hasDerivAt_zetaSummand (L : PeriodPair) (l : L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) :
    HasDerivAt (fun w : ℂ ↦ if l = 0 then 0 else
      1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2)
      (if l = 0 then 0 else -(1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)) z := by
  by_cases hl : l = 0
  · simpa only [if_pos hl] using hasDerivAt_const z (0 : ℂ)
  simp only [if_neg hl]
  have hzl : z - (l : ℂ) ≠ 0 := fun h ↦ hz (sub_eq_zero.mp h ▸ l.property)
  convert! ((((hasDerivAt_id z).sub_const (l : ℂ)).inv hzl).add_const
    (1 / (l : ℂ))).add ((hasDerivAt_id z).div_const ((l : ℂ) ^ 2)) using 1 <;>
    simp [funext_iff, Pi.add_apply, one_div, neg_div, sub_eq_add_neg, add_comm]

private lemma differentiableOn_zetaSeries (L : PeriodPair) :
    DifferentiableOn ℂ (fun z ↦ ∑' l : L.lattice, if l = 0 then 0 else
      1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) L.latticeᶜ := by
  exact (hasSumLocallyUniformly_zetaSeries L).tendstoLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun l _ z hz ↦
      (hasDerivAt_zetaSummand L l z hz).differentiableAt.differentiableWithinAt)
    L.isClosed_lattice.isOpen_compl

private lemma deriv_zetaSeries (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    deriv (fun w ↦ ∑' l : L.lattice, if l = 0 then 0 else
      1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) z =
      -L.weierstrassPExcept 0 z := by
  have hd := ((hasSumLocallyUniformly_zetaSeries L).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s ↦ .fun_sum fun l _ w hw ↦
      (hasDerivAt_zetaSummand L l w hw).differentiableAt.differentiableWithinAt)
    L.isClosed_lattice.isOpen_compl).tendsto_at hz
  have hsum : HasSum (fun l : L.lattice ↦ if l = 0 then 0 else
      -(1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)) (-L.weierstrassPExcept 0 z) := by
    convert! (L.hasSum_weierstrassPExcept 0 z).neg using 1
    ext l
    by_cases hl : l = 0
    · subst l
      simp
    · have hlc : (l : ℂ) ≠ 0 := fun h ↦ hl (Subtype.ext h)
      simp only [if_neg hl, if_neg hlc]
  apply HasSum.unique _ hsum
  change Tendsto _ atTop _
  convert! hd using 1
  funext s
  exact (HasDerivAt.fun_sum fun l _ ↦ hasDerivAt_zetaSummand L l z hz).deriv.symm

/-- The canonical zeta function is holomorphic away from the lattice. -/
theorem differentiableOn_weierstrassZeta (L : PeriodPair) :
    DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ := by
  refine DifferentiableOn.add ?_ (differentiableOn_zetaSeries L)
  intro z hz
  have hz0 : z ≠ 0 := fun h ↦ hz (h ▸ L.lattice.zero_mem)
  change DifferentiableWithinAt ℂ (fun w : ℂ ↦ 1 / w) L.latticeᶜ z
  simpa only [one_div] using (hasDerivAt_inv hz0).differentiableAt.differentiableWithinAt

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z := by
  have hz0 : z ≠ 0 := fun h ↦ hz (h ▸ L.lattice.zero_mem)
  have htail := ((differentiableOn_zetaSeries L).differentiableAt
    (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  rw [deriv_zetaSeries L z hz] at htail
  convert! (hasDerivAt_inv hz0).add htail using 1
  · ext w
    simp only [weierstrassZeta, one_div, Pi.add_apply]
  · have hP := L.weierstrassPExcept_add (0 : L.lattice) z
    simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero, sub_zero] at hP
    rw [← hP]
    simp only [one_div]
    ring
