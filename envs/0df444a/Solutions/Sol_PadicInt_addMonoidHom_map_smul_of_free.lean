-- Prove2me | solution 1 for PadicInt.addMonoidHom_map_smul_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b7aab54c-f634-581f-8324-5f096602c361

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_addMonoidHom_map_smul_of_free

set_option autoImplicit false

universe u v

namespace ZpLinAux

variable {p : ℕ} [Fact p.Prime]

theorem eq_zero_of_forall_mem_span_pow (z : ℤ_[p]) (hz : ∀ k : ℕ, z ∈ Ideal.span {(p : ℤ_[p]) ^ k}) : z = 0 := by
  by_contra hne
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h1 : ‖z‖ ≤ (p : ℝ) ^ (-((z.valuation + 1 : ℕ) : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow z _).mpr (hz _)
  rw [PadicInt.norm_eq_zpow_neg_valuation hne, zpow_le_zpow_iff_right₀ hp] at h1
  push_cast at h1
  omega

theorem apply_eq_smul_apply_one {M : Type v} [AddCommGroup M] [Module ℤ_[p] M] [Module.Free ℤ_[p] M]
    (g : ℤ_[p] →+ M) (c : ℤ_[p]) : g c = c • g 1 := by

  let h : ℤ_[p] →+ M := g - (AddMonoidHom.mk' (fun a : ℤ_[p] => a • g 1) (fun a b => add_smul a b _))
  have hh : ∀ a : ℤ_[p], h a = g a - a • g 1 := fun a => rfl
  have h_nat : ∀ n : ℕ, h (n : ℤ_[p]) = 0 := by
    intro n
    rw [hh, sub_eq_zero, ← nsmul_one, map_nsmul, nsmul_one, Nat.cast_smul_eq_nsmul]

  have hk : ∀ k : ℕ, ∃ m : M, h c = ((p : ℤ_[p]) ^ k) • m := by
    intro k
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k c)
    refine ⟨h d, ?_⟩
    have hc : c = (c.appr k : ℤ_[p]) + ((p ^ k : ℕ) : ℤ_[p]) * d := by
      push_cast; linear_combination (-1 : ℤ_[p]) * hd
    rw [hc, map_add, h_nat, zero_add, ← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p]]
    push_cast
    rfl

  suffices h0 : h c = 0 by
    rw [hh] at h0; exact sub_eq_zero.mp h0
  let b := Module.Free.chooseBasis ℤ_[p] M
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply eq_zero_of_forall_mem_span_pow
  intro k
  obtain ⟨m, hm⟩ := hk k
  rw [hm, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩

end ZpLinAux

theorem solution
    (p : ℕ) [Fact p.Prime] {N : Type u} {M : Type v}
    [AddCommGroup N] [Module ℤ_[p] N] [Module.Free ℤ_[p] N]
    [AddCommGroup M] [Module ℤ_[p] M] [Module.Free ℤ_[p] M]
    (f : N →+ M) (c : ℤ_[p]) (x : N) :
    f (c • x) = c • f x := by
  let b := Module.Free.chooseBasis ℤ_[p] N

  have key : ∀ (i : Module.Free.ChooseBasisIndex ℤ_[p] N) (a : ℤ_[p]), f (a • b i) = a • f (b i) := by
    intro i a
    have := ZpLinAux.apply_eq_smul_apply_one
      (AddMonoidHom.mk' (fun a : ℤ_[p] => f (a • b i)) (fun a a' => by simp only [add_smul, map_add])) a
    simpa using this

  conv_lhs => rw [← b.linearCombination_repr x]
  conv_rhs => rw [← b.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.smul_sum, map_finsuppSum, map_finsuppSum, Finsupp.smul_sum]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, key, key, smul_smul]

end S_PadicInt_addMonoidHom_map_smul_of_free
end P2MW
export P2MW.S_PadicInt_addMonoidHom_map_smul_of_free (solution)
