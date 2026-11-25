-- Prove2me | solution 1 for ReciprocityTheory.PGsh.pderiv_linSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:31.650974+00:00
-- url     : https://prove2.me/submissions/a1814dbc-4cae-4fd6-affb-a048d7be7d1c

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_pderiv_linSub_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (g : Matrix (Fin n) (Fin n) R) (a b : Fin n)
    (q : MvPolynomial (Fin n × Fin n) R) :
    pderiv (a, b) (linSub g q) = ∑ i, C (g i a) * linSub g (pderiv (i, b) q) := by
  induction q using MvPolynomial.induction_on
  next c =>
    simp [linSub]
  next p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  next p v hp =>
    have hs : ∀ i, linSub g (Pi.single (M := fun _ : Fin n × Fin n => MvPolynomial (Fin n × Fin n) R) (i, b) 1 v) =
        if v = (i, b) then 1 else 0 := fun i => by
      rw [Pi.single_apply]; split_ifs <;> simp
    rw [map_mul, Derivation.leibniz, hp, pderiv_linSub_X]
    simp only [Derivation.leibniz, pderiv_X, map_add, map_mul, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · simp only [hs, mul_ite, mul_one, mul_zero]
      by_cases hb : v.2 = b
      · rw [if_pos hb, Finset.sum_eq_single v.1]
        · rw [if_pos (by ext <;> simp [hb])]; ring
        · intro i _ hi; rw [if_neg (fun h => hi (congrArg Prod.fst h).symm)]
        · simp
      · rw [if_neg hb]; symm
        exact Finset.sum_eq_zero fun i _ => if_neg (fun h => hb (congrArg Prod.snd h))
    · exact Finset.sum_congr rfl fun i _ => by ring
end ReciprocityTheory.PGsh
