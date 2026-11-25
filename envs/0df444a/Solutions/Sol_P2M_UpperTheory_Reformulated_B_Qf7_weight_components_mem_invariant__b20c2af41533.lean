-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qf7_weight_components_mem_invariant__b20c2af41533
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:46.492982+00:00
-- url     : https://prove2.me/submissions/7a556131-e258-4687-9f41-071373ac7c04

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WeightComponentsMemInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qf7.apply_of_mem_weightSp {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V]
    [_root_.Module K V] {E : UpperTheory.Reformulated.B.Qf7.GLOps n K V} {mu : Fin n → ℤ} {x : V}
    (hx : x ∈ UpperTheory.Reformulated.B.Qf7.weightSp E mu) (a : Fin n) : E a a x = (mu a : K) • x := by
  unfold UpperTheory.Reformulated.B.Qf7.weightSp at hx
  have h := (Submodule.mem_iInf _).1 hx a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at h
  exact h
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf7
theorem _root_.solution.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      [CharZero K] (E : UpperTheory.Reformulated.B.Qf7.GLOps n K V) (W : Submodule K V),
      (∀ (a : Fin n), ∀ x ∈ W, (E a a : V → V) x ∈ W) →
        ∀ (s : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V),
          (∀ mu ∈ s, f mu ∈ UpperTheory.Reformulated.B.Qf7.weightSp E mu) → ∑ mu ∈ s, f mu ∈ W → ∀ mu ∈ s, f mu ∈ W := by
  intro n K V _ _ _ _ E W hW s
  classical
  induction s using Finset.induction_on with
  | empty => intro f _ _ mu hmu; simp at hmu
  | insert nu t hnu ih =>
    intro f hf hsum
    have ht : ∀ mu ∈ t, f mu ∈ W := by
      intro mu hmu
      have hne : mu ≠ nu := fun h => hnu (h ▸ hmu)
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
      have h1 : E a a (∑ l ∈ insert nu t, f l) - (nu a : K) • (∑ l ∈ insert nu t, f l) ∈ W :=
        W.sub_mem (hW a _ hsum) (W.smul_mem _ hsum)
      have h2 : E a a (∑ l ∈ insert nu t, f l) - (nu a : K) • (∑ l ∈ insert nu t, f l)
          = ∑ l ∈ insert nu t, ((l a : K) - (nu a : K)) • f l := by
        rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [UpperTheory.Reformulated.B.Qf7.apply_of_mem_weightSp (hf l hl) a, sub_smul]
      rw [h2, Finset.sum_insert hnu, sub_self, zero_smul, zero_add] at h1
      have h3 := ih (fun l => ((l a : K) - (nu a : K)) • f l)
        (fun l hl => Submodule.smul_mem _ _ (hf l (Finset.mem_insert_of_mem hl))) h1 mu hmu
      have hc : ((mu a : K) - (nu a : K)) ≠ 0 :=
        sub_ne_zero.2 (fun h => ha (Int.cast_injective h))
      exact (W.smul_mem_iff hc).1 h3
    intro mu hmu
    rcases Finset.mem_insert.1 hmu with rfl | hmu
    · rw [Finset.sum_insert hnu] at hsum
      exact (W.add_mem_iff_left (W.sum_mem ht)).1 hsum
    · exact ht mu hmu
end UpperTheory.Reformulated.B.Qf7
