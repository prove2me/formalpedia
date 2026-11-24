-- Prove2me | solution 1 for ValueEquivalence.ve_space_all_policies_all_functions
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:29:42.4558+00:00
-- url     : https://prove2.me/submissions/7888ac89-4242-40c0-8b6b-76aada09843a

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

set_option autoImplicit false

open Filter Topology

open ValueEquivalence

/-- Value equivalence for all policies and all functions forces equal rewards and kernels. -/
private lemma eq_of_ve {S A : Type*} [Fintype S] [Fintype A] (γ : ℝ) (hγ0 : 0 < γ)
    (m m' : Model S A) (h : IsValueEquivalent γ policies Set.univ m m') : m = m' := by
  classical
  -- the deterministic policy choosing `a`
  have hpol : ∀ a : A, (fun (_ : S) (a' : A) => if a' = a then (1 : ℝ) else 0) ∈ policies := by
    intro a
    refine ⟨fun s a' => by dsimp only; split_ifs <;> norm_num, fun s => ?_⟩
    simp
  have key : ∀ (a : A) (v : S → ℝ) (s : S),
      m.r s a + γ * ∑ s', m.p s a s' * v s' = m'.r s a + γ * ∑ s', m'.p s a s' * v s' := by
    intro a v s
    have := congrFun (h _ (hpol a) v (Set.mem_univ v)) s
    simpa [bellman] using this
  have hr : m.r = m'.r := by
    funext s a
    simpa using key a 0 s
  have hp : m.p = m'.p := by
    funext s a s'
    have h1 := key a (fun x => if x = s' then 1 else 0) s
    rw [congrFun (congrFun hr s) a] at h1
    have h2 := add_left_cancel h1
    have h3 := mul_left_cancel₀ hγ0.ne' h2
    simpa using h3
  cases m
  cases m'
  simp only at hr hp
  subst hr hp
  rfl

theorem solution {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (M : Set (Model S A)) (mstar : Model S A) :
    mstar ∈ veSpace γ M mstar policies Set.univ ∨
      veSpace γ M mstar policies Set.univ = ∅ := by
  by_cases hm : mstar ∈ M
  · exact Or.inl ⟨hm, fun _ _ _ _ => rfl⟩
  · right
    ext m'
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hm', hve⟩
    exact hm (eq_of_ve γ hγ0 mstar m' hve ▸ hm')
