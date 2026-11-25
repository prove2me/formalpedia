-- Prove2me | solution 1 for PI.SqfRootsInj.W.caseB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:49.365274+00:00
-- url     : https://prove2.me/submissions/2cb4be07-2494-4624-825e-d72685d2b514

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain
import Theorems.Thm_PI_SqfRootsInj_W_root_facts
import Theorems.Thm_PI_SqfRootsInj_W_orderOf_dvd_pow_sub_one
import Theorems.Thm_PI_SqfRootsInj_W_pow_card_minpoly
import Theorems.Thm_PI_SqfRootsInj_W_pow_eq_part_pow_of_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfRootsInj.W
theorem _root_.solution {r ℓ : ℕ} (hℓ : ℓ.Prime) {f : (ZMod g)[X]} (hf : IsLab g r f)
    {x y : Fbar g} (hx : x ∈ rootsBar f) (hy : y ∈ rootsBar f) (hxy : x ≠ y)
    (hp : primeToPart ℓ x = primeToPart ℓ y)
    (hne : minpoly (ZMod g) x ≠ minpoly (ZMod g) y)
    (hle : (minpoly (ZMod g) y).natDegree ≤ (minpoly (ZMod g) x).natDegree) :
    CaseB g r ℓ f := by
  obtain ⟨hx0, hxd, -, hx1⟩ := root_facts hf hx
  obtain ⟨hy0, hyd, -, hy1⟩ := root_facts hf hy
  have hxint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hyint : IsIntegral (ZMod g) y := Algebra.IsIntegral.isIntegral y
  have hcop : IsCoprime (minpoly (ZMod g) x) (minpoly (ZMod g) y) := by
    refine (Irreducible.coprime_iff_not_dvd (minpoly.irreducible hxint)).2 fun h => hne ?_
    exact eq_of_monic_of_associated (minpoly.monic hxint) (minpoly.monic hyint)
      ((minpoly.irreducible hxint).associated_of_dvd (minpoly.irreducible hyint) h)
  have hprod : minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f := hcop.mul_dvd hxd hyd
  have hdeg : (minpoly (ZMod g) x).natDegree + (minpoly (ZMod g) y).natDegree ≤ r := by
    rw [← hf.2.1, ← natDegree_mul (minpoly.ne_zero hxint) (minpoly.ne_zero hyint)]
    exact natDegree_le_of_dvd hprod hf.1.ne_zero
  obtain ⟨hNe, hox⟩ := orderOf_dvd_pow_sub_one hx0 rfl hx1
  obtain ⟨hNe', hoy⟩ := orderOf_dvd_pow_sub_one hy0 rfl hy1
  refine ⟨_, _, x, y, hy1, hle, hdeg, ?_, rfl, rfl, hprod, pow_card_minpoly y, ?_⟩
  · by_contra hnd
    have hv := padicValNat.eq_zero_of_not_dvd hnd
    have h1 := pow_eq_part_pow_of_dvd ℓ hℓ x _ (mul_ne_zero hNe hNe')
      (dvd_mul_of_dvd_left hox _)
    have h2 := pow_eq_part_pow_of_dvd ℓ hℓ y _ (mul_ne_zero hNe hNe')
      (dvd_mul_of_dvd_right hoy _)
    rw [hv, pow_zero, pow_one, pow_one] at h1 h2
    exact hxy (by rw [h1, h2, hp])
  · unfold Lp
    rw [← hp]
    exact pow_eq_part_pow_of_dvd ℓ hℓ x _ hNe hox
end PI.SqfRootsInj.W
