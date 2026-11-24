-- Prove2me | solution 1 for ValueEquivalence.ve_space_pinned_by_spanning_sets
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:18:23.73041+00:00
-- url     : https://prove2.me/submissions/82d25566-9b7e-405b-afe1-d9f1e941ba5b

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

universe u v

namespace ValueEquivalence

theorem ve1_span_zero {X : Type*} [Fintype X] (d : X → ℝ) (H : Set (X → ℝ))
    (h : ∀ w ∈ H, ∑ x, w x * d x = 0) (w : X → ℝ) (hw : w ∈ Submodule.span ℝ H) :
    ∑ x, w x * d x = 0 := by
  let L : (X → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun w => ∑ x, w x * d x
      map_add' := by intro u v; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c u; simp [Finset.mul_sum, mul_assoc] }
  have hle : Submodule.span ℝ H ≤ LinearMap.ker L :=
    Submodule.span_le.mpr (fun u hu => by simpa [L] using h u hu)
  simpa [L] using hle hw

theorem ve1_diff {S A : Type*} [Fintype S] [Fintype A] (m m' : Model S A) (hr : m.r = m'.r)
    (γ : ℝ) (π : S → A → ℝ) (v : S → ℝ) (s : S) :
    bellman m γ π v s - bellman m' γ π v s =
      ∑ a, π s a * (γ * ∑ s', (m.p s a s' - m'.p s a s') * v s') := by
  simp only [bellman, hr, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem ve1_swap {S A : Type*} [Fintype S] [Fintype A] (w : A → ℝ) (γ : ℝ)
    (c : A → S → ℝ) (v : S → ℝ) :
    ∑ a, w a * (γ * ∑ s', c a s' * v s') = ∑ s', v s' * ∑ a, w a * (γ * c a s') := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem ve1_extend {S A : Type*} [Fintype S] [Fintype A] {γ : ℝ} {Pol : Set (S → A → ℝ)}
    {V : Set (S → ℝ)} {m m' : Model S A} (hr : m.r = m'.r)
    (h : IsValueEquivalent γ Pol V m m') :
    IsValueEquivalent γ (pspan Pol) (Submodule.span ℝ V : Set (S → ℝ)) m m' := by
  -- reformulate via differences
  have key : ∀ π ∈ Pol, ∀ v ∈ V, ∀ s,
      ∑ a, π s a * (γ * ∑ s', (m.p s a s' - m'.p s a s') * v s') = 0 := by
    intro π hπ v hv s
    rw [← ve1_diff m m' hr, h π hπ v hv, sub_self]
  -- step 1: extend in the policy
  have step1 : ∀ π' ∈ pspan Pol, ∀ v ∈ V, ∀ s,
      ∑ a, π' s a * (γ * ∑ s', (m.p s a s' - m'.p s a s') * v s') = 0 := by
    intro π' hπ' v hv s
    have hm : π' s ∈ Submodule.span ℝ ((fun h => h s) '' Pol) := hπ' s
    have hH : ∀ w ∈ ((fun h => h s) '' Pol),
        ∑ a, w a * (fun a => γ * ∑ s', (m.p s a s' - m'.p s a s') * v s') a = 0 := by
      rintro w ⟨π, hπ, rfl⟩
      exact key π hπ v hv s
    exact ve1_span_zero _ _ hH (π' s) hm
  -- step 2: extend in the function
  intro π' hπ' v hv
  funext s
  rw [← sub_eq_zero, ve1_diff m m' hr, ve1_swap]
  refine ve1_span_zero (fun s' => ∑ a, π' s a * (γ * (m.p s a s' - m'.p s a s'))) V ?_ v hv
  intro u hu
  rw [← ve1_swap]
  exact step1 π' hπ' u hu s

theorem ve1_det_policy {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A] (g : S → A) :
    (fun s a => if a = g s then (1 : ℝ) else 0) ∈ (policies : Set (S → A → ℝ)) := by
  refine ⟨fun s a => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs <;> norm_num
  · simp

theorem ve1_bellman_det {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A] (m : Model S A)
    (γ : ℝ) (g : S → A) (v : S → ℝ) (s : S) :
    bellman m γ (fun s a => if a = g s then (1 : ℝ) else 0) v s =
      m.r s (g s) + γ * ∑ s', m.p s (g s) s' * v s' := by
  simp [bellman, ite_mul]

theorem ve1_model_ext {S A : Type*} [Fintype S] [Fintype A] (m m' : Model S A)
    (hr : m.r = m'.r) (hp : m.p = m'.p) : m = m' := by
  obtain ⟨r, p, h⟩ := m
  obtain ⟨r', p', h'⟩ := m'
  simp only at hr hp
  subst hr
  subst hp
  rfl

end ValueEquivalence

open ValueEquivalence in
theorem solution {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (M : Set (Model S A)) (mstar : Model S A)
    (hM : ∀ m ∈ M, m.r = mstar.r)
    (Pol : Set (S → A → ℝ)) (V : Set (S → ℝ)) (hPol : Pol ⊆ policies)
    (hcover : policies ⊆ pspan Pol) (hV : Submodule.span ℝ V = ⊤) :
    veSpace γ M mstar Pol V = {mstar} ∨ veSpace γ M mstar Pol V = ∅ := by
  classical
  have key : ∀ m' ∈ veSpace γ M mstar Pol V, m' = mstar := by
    rintro m' ⟨hm', hve⟩
    have hr := hM m' hm'
    have hve2 := ve1_extend hr.symm hve
    rw [hV] at hve2
    have hp : ∀ s a s0, mstar.p s a s0 = m'.p s a s0 := by
      intro s a s0
      have h := congrFun (hve2 _ (hcover (ve1_det_policy (fun _ => a)))
        (fun s' => if s' = s0 then (1 : ℝ) else 0) Submodule.mem_top) s
      rw [ve1_bellman_det, ve1_bellman_det, hr] at h
      simp at h
      rcases h with h | h
      · exact h
      · exact absurd h hγ0.ne'
    exact ve1_model_ext _ _ hr (funext fun s => funext fun a => funext fun s0 => (hp s a s0).symm)
  by_cases hmem : mstar ∈ veSpace γ M mstar Pol V
  · left
    ext m'
    rw [Set.mem_singleton_iff]
    constructor
    · exact key m'
    · rintro rfl
      exact hmem
  · right
    ext m'
    simp only [Set.mem_empty_iff_false, iff_false]
    intro h
    exact hmem (key m' h ▸ h)
