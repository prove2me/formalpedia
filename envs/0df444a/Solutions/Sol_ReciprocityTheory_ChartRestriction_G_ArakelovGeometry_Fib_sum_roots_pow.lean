-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.sum_roots_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:15.093795+00:00
-- url     : https://prove2.me/submissions/b46ddd26-f3e7-49fb-8f87-c89ceb45d23a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_multiset_sum_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {K : Type*} [Field K] (p : Polynomial K) (hm : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) (k : ℕ) :
    (p.roots.map (· ^ k)).sum = psumC p p.natDegree k := by
  rw [multiset_sum_pow_eq p.roots hroots k, psumC]
  refine congrArg (fun F => aeval F (psumQ _ k)) (funext fun i => ?_)
  have hi : (i : ℕ) + 1 ≤ p.natDegree := i.isLt
  rw [Polynomial.coeff_eq_esymm_roots_of_card hroots (Nat.sub_le _ _), hm.leadingCoeff,
    Nat.sub_sub_self hi, one_mul, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
