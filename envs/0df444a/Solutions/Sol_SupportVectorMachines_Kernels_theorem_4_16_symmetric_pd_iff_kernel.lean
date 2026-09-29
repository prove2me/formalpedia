-- Prove2me | solution 1 for SupportVectorMachines.Kernels.theorem_4_16_symmetric_pd_iff_kernel
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T01:45:53.266971+00:00
-- url     : https://prove2.me/submissions/bce6dfb0-8380-40c8-8019-9cf3a7fecdef

import Mathlib
import Definitions.Def_SupportVectorMachines_Kernels_IsKernel
import Definitions.Def_SupportVectorMachines_Kernels_PositiveDefinite

/-! Disproof of 787a70b3 `SupportVectorMachines.Kernels.theorem_4_16_symmetric_pd_iff_kernel`.

`IsKernel k` requires a feature space `H : Type` (universe 0), while `X : Type*` is arbitrary.
At `X = Ordinal.{0} : Type 1` the kernel `δ(a, b) = if a = b then 1 else 0` is symmetric and
positive definite: it is a Gram kernel in `lp (fun _ => ℝ) 2 : Type 1`. A feature map
`Φ : Ordinal.{0} → H` for `δ` would be injective, because `Φ a = Φ b` forces `δ a b = δ b b = 1`.
That gives `#Ordinal.{0} = univ.{0,1} ≤ lift #H < univ.{0,1}`, which is impossible. -/

set_option autoImplicit false

theorem svm_gram_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → E) :
    0 ≤ ∑ a ∈ s, ∑ b ∈ s, c a * c b * inner ℝ (v b) (v a) := by
  have h : ∑ a ∈ s, ∑ b ∈ s, c a * c b * inner ℝ (v b) (v a) =
      inner ℝ (∑ b ∈ s, c b • v b) (∑ a ∈ s, c a • v a) := by
    rw [sum_inner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [h]
  exact real_inner_self_nonneg

open SupportVectorMachines.Kernels in
theorem solution : ¬ (∀ {X : Type 1} [Nonempty X] (k : X → X → ℝ),
    IsKernel k ↔ Symmetric k ∧ PositiveDefinite k) := by
  intro h
  classical
  let k : Ordinal.{0} → Ordinal.{0} → ℝ := fun a b => if a = b then 1 else 0
  have hsym : Symmetric k := by
    intro a b
    simp only [k, eq_comm]
  have hpd : PositiveDefinite k := by
    intro n α x
    have hk : ∀ i j, k (x j) (x i) =
        inner ℝ (lp.single 2 (x j) (1 : ℝ) : lp (fun _ : Ordinal.{0} => ℝ) 2)
          (lp.single 2 (x i) (1 : ℝ)) := by
      intro i j
      rw [lp.inner_single_left]
      simp [k, Pi.single_apply]
    simp only [hk]
    exact svm_gram_nonneg Finset.univ α
      (fun i => (lp.single 2 (x i) (1 : ℝ) : lp (fun _ : Ordinal.{0} => ℝ) 2))
  obtain ⟨H, i1, i2, i3, Φ, hΦ⟩ := (h k).2 ⟨hsym, hpd⟩
  have hinj : Function.Injective Φ := by
    intro a b hab
    by_contra hne
    have h1 := hΦ a b
    have h2 := hΦ b b
    rw [hab, ← h2] at h1
    simp [k, hne] at h1
  have h1 := Cardinal.lift_mk_le_lift_mk_of_injective hinj
  have h2 := Cardinal.lift_lt_univ (Cardinal.mk H)
  rw [← Cardinal.mk_ordinal] at h2
  rw [Cardinal.lift_uzero] at h1
  exact absurd (h1.trans_lt h2) (lt_irrefl _)
