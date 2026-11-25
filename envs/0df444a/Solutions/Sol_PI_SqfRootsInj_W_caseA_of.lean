-- Prove2me | solution 1 for PI.SqfRootsInj.W.caseA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:42.303986+00:00
-- url     : https://prove2.me/submissions/91080b51-ea2c-44ff-af95-f39fd9deacd3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain
import Theorems.Thm_PI_SqfRootsInj_W_root_facts
import Theorems.Thm_P2M_PI_SqfRootsInj_W_pow_pred_eq_one__d29b6a46da77
import Theorems.Thm_PI_SqfRootsInj_W_two_mul_le_of_dvd_ne
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
    (heq : minpoly (ZMod g) x = minpoly (ZMod g) y) :
    CaseA g r ℓ f := by
  obtain ⟨hx0, hxd, hxr, hx1⟩ := root_facts hf hx
  obtain ⟨hy0, -, -, -⟩ := root_facts hf hy
  have hxint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  obtain ⟨hNe, hox⟩ := orderOf_dvd_pow_sub_one hx0 rfl hx1
  obtain ⟨-, hoy⟩ := orderOf_dvd_pow_sub_one hy0 (congrArg natDegree heq.symm) hx1
  have hxL := pow_eq_part_pow_of_dvd ℓ hℓ x _ hNe hox
  have hyL := pow_eq_part_pow_of_dvd ℓ hℓ y _ hNe hoy
  have htt : x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ =
      y ^ Lp g (minpoly (ZMod g) x).natDegree ℓ := by
    unfold Lp; rw [hxL, hyL, hp]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ZMod g) (E := Fbar g)).1 heq.symm
  replace hσ : σ x = y := hσ
  have hσt : σ (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ) =
      x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ := by
    rw [map_pow, hσ, htt]
  have hxnot : x ∉ IntermediateField.adjoin (ZMod g)
      {x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ} := by
    intro hmem
    obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff (ZMod g) x).1 hmem
    have hfix : σ x = x := by
      rw [hpq, map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, hσt]
    exact hxy (hfix.symm.trans hσ)
  have htint : IsIntegral (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ) :=
    Algebra.IsIntegral.isIntegral _
  have hle : IntermediateField.adjoin (ZMod g) {x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ} ≤
      IntermediateField.adjoin (ZMod g) {x} := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self (ZMod g) x) _
  haveI := IntermediateField.adjoin.finiteDimensional hxint
  have hdiv : (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ∣
      (minpoly (ZMod g) x).natDegree := by
    have h := IntermediateField.finrank_dvd_of_le_right hle
    rwa [IntermediateField.adjoin.finrank htint, IntermediateField.adjoin.finrank hxint] at h
  have hjne : (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ≠
      (minpoly (ZMod g) x).natDegree := by
    intro hEq
    apply hxnot
    have hEq2 := IntermediateField.eq_of_le_of_finrank_eq hle
      (by rw [IntermediateField.adjoin.finrank htint, IntermediateField.adjoin.finrank hxint, hEq])
    rw [hEq2]
    exact IntermediateField.mem_adjoin_simple_self _ x
  have hj1 := minpoly.natDegree_pos htint
  have h2j : 2 * (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ≤
      (minpoly (ZMod g) x).natDegree := by
    exact two_mul_le_of_dvd_ne hdiv hjne hx1
  have ht0 : x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ ≠ 0 := pow_ne_zero _ hx0
  have htj := pow_pred_eq_one' ht0 (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos)
    (pow_card_minpoly (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ))
  refine ⟨_, _, x, by omega, hxr, hj1, h2j, ?_, rfl, hxd, ?_⟩
  · by_contra hnd
    have hv := padicValNat.eq_zero_of_not_dvd hnd
    rw [hv, pow_zero, pow_one, pow_one] at hxL hyL
    exact hxy (by rw [hxL, hyL, hp])
  · rw [mul_comm, pow_mul]
    exact htj
end PI.SqfRootsInj.W
