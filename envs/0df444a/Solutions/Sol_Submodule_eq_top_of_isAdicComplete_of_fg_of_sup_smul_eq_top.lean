-- Prove2me | solution 1 for Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bbb6eea3-76f4-5636-b01d-3ee51b641e6b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top
set_option autoImplicit false

theorem solution
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) [IsAdicComplete I A] [IsHausdorff I M]
    (N : Submodule A M) (hN : N.FG) (h : N ⊔ I • ⊤ = ⊤) : N = ⊤ := by
  classical
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hN

  let φ : (Fin k → A) →ₗ[A] M :=
    { toFun := fun c => ∑ i, c i • s i
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp [Finset.smul_sum, mul_smul] }
  have hφ : ∀ c, φ c = ∑ i, c i • s i := fun c => rfl
  have hφN : ∀ c, φ c ∈ N := fun c => by
    rw [hφ, ← hs]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have h0 : ∀ m : M, ∃ c : Fin k → A, m - φ c ∈ (I • ⊤ : Submodule A M) := fun m => by
    have hm : m ∈ N ⊔ I • ⊤ := by rw [h]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hm
    rw [← hs, Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, rfl⟩ := hy
    exact ⟨c, by rw [hφ]; simpa using hz⟩

  have hstep : ∀ (n : ℕ) (y : M), y ∈ (I ^ n • ⊤ : Submodule A M) →
      ∃ c : Fin k → A, (∀ i, c i ∈ I ^ n) ∧ y - φ c ∈ (I ^ (n + 1) • ⊤ : Submodule A M) := by
    intro n y hy
    refine Submodule.smul_induction_on
      (p := fun y => ∃ c : Fin k → A, (∀ i, c i ∈ I ^ n) ∧ y - φ c ∈ (I ^ (n + 1) • ⊤ : Submodule A M))
      hy ?_ ?_
    · intro r hr m _
      obtain ⟨c, hc⟩ := h0 m
      refine ⟨r • c, fun i => Ideal.mul_mem_right _ _ hr, ?_⟩
      rw [map_smul, ← smul_sub, pow_succ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hr hc
    · rintro y₁ y₂ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
      refine ⟨c₁ + c₂, fun i => Ideal.add_mem _ (hc₁ i) (hc₂ i), ?_⟩
      rw [map_add]
      convert Submodule.add_mem _ h₁ h₂ using 1
      abel
  choose c hcI hcy using hstep
  refine eq_top_iff.mpr fun x _ => ?_

  let r : (n : ℕ) → {y : M // y ∈ (I ^ n • ⊤ : Submodule A M)} :=
    fun n => Nat.rec (motive := fun n => {y : M // y ∈ (I ^ n • ⊤ : Submodule A M)})
      ⟨x, by simp⟩ (fun n y => ⟨y.1 - φ (c n y.1 y.2), hcy n y.1 y.2⟩) n

  let a : ℕ → Fin k → A := fun n => c n (r n).1 (r n).2
  have haI : ∀ n i, a n i ∈ I ^ n := fun n i => hcI n (r n).1 (r n).2 i
  let S : ℕ → Fin k → A := fun n i => ∑ t ∈ Finset.range n, a t i
  have hS0 : S 0 = 0 := funext fun i => by simp [S]
  have hSsucc : ∀ n, S (n + 1) = S n + a n := fun n => funext fun i => by
    simp [S, Finset.sum_range_succ]
  have hr0 : (r 0).1 = x := rfl
  have hrsucc : ∀ n, (r (n + 1)).1 = (r n).1 - φ (a n) := fun n => rfl
  have hr : ∀ n, (r n).1 = x - φ (S n) := by
    intro n
    induction n with
    | zero => rw [hr0, hS0, map_zero, sub_zero]
    | succ n ih => rw [hrsucc, ih, hSsucc, map_add]; abel

  have hS : ∀ i m n, m ≤ n → S n i - S m i ∈ I ^ m := by
    intro i m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hSsucc, Pi.add_apply, add_sub_right_comm]
      exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right hmn (haI n i))
  have hL : ∀ i, ∃ L : A, ∀ n, S n i - L ∈ I ^ n := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I A) (f := fun n => S n i)
      (fun {m n} hmn => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, Ideal.neg_mem_iff]
        exact hS i m n hmn)
    exact ⟨L, fun n => by simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL n⟩
  choose L hL using hL

  suffices hx : x - φ L = 0 by rw [sub_eq_zero.mp hx]; exact hφN L
  refine IsHausdorff.haus (inferInstance : IsHausdorff I M) _ fun n => ?_
  rw [SModEq.zero]
  have : x - φ L = (r n).1 + φ (S n - L) := by rw [hr n, map_sub]; abel
  rw [this]
  refine Submodule.add_mem _ (r n).2 ?_
  rw [hφ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hL i n) Submodule.mem_top

end S_Submodule_eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top
end P2MW
export P2MW.S_Submodule_eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top (solution)
