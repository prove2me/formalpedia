-- Prove2me | solution 1 for ValueEquivalence.ve_space_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:16:49.352987+00:00
-- url     : https://prove2.me/submissions/39d34394-32af-44ee-9ab9-baf3ef6372c7

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

theorem ve1_mono {S A : Type*} [Fintype S] [Fintype A] {γ : ℝ} {Pol Pol' : Set (S → A → ℝ)}
    {V V' : Set (S → ℝ)} {m m' : Model S A} (hP : Pol' ⊆ Pol) (hV : V' ⊆ V)
    (h : IsValueEquivalent γ Pol V m m') : IsValueEquivalent γ Pol' V' m m' :=
  fun π hπ v hv => h π (hP hπ) v (hV hv)

end ValueEquivalence

open ValueEquivalence in
theorem solution {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (M : Set (Model S A)) (mstar : Model S A)
    (hM : ∀ m ∈ M, m.r = mstar.r)
    (Pol : Set (S → A → ℝ)) (V : Set (S → ℝ)) (hPolfin : Pol.Finite) (hVfin : V.Finite)
    (hPol : Pol ⊆ policies) :
    veSpace γ M mstar Pol V =
      veSpace γ M mstar (pspan Pol ∩ policies) (Submodule.span ℝ V : Set (S → ℝ)) := by
  ext m'
  constructor
  · rintro ⟨hm', hve⟩
    exact ⟨hm', ve1_mono Set.inter_subset_left subset_rfl (ve1_extend (hM m' hm').symm hve)⟩
  · rintro ⟨hm', hve⟩
    refine ⟨hm', ve1_mono ?_ Submodule.subset_span hve⟩
    intro π hπ
    exact ⟨fun s => Submodule.subset_span ⟨π, hπ, rfl⟩, hPol hπ⟩
