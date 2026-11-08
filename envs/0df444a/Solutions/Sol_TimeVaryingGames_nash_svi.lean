-- Prove2me | solution 1 for TimeVaryingGames.nash_svi
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:17:39.617572+00:00
-- url     : https://prove2.me/submissions/1318103f-2330-445e-8440-370e9b132803

import Mathlib
import Definitions.Def_TimeVaryingGames_ContinuousGame

open TimeVaryingGames in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    (K : ∀ i, Set (E i)) (hKc : ∀ i, IsCompact (K i)) (hKcv : ∀ i, Convex ℝ (K i))
    (U : Set (∀ j, E j)) (hU : IsOpen U) (hKU : profiles K ⊆ U)
    (u : ι → (∀ j, E j) → ℝ) (hu : ∀ i, ContDiffOn ℝ 1 (u i) U)
    (xs : ∀ i, E i) (hxs : IsNash K u xs) :
    ∀ x ∈ profiles K, ∑ i, partialGradient u i xs (x i - xs i) ≤ 0 := by
  intro x hx
  apply Finset.sum_nonpos
  intro i _
  have hxsK : xs ∈ profiles K := hxs.1
  have hxsi : xs i ∈ K i := hxsK i (Set.mem_univ i)
  have hxi : x i ∈ K i := hx i (Set.mem_univ i)
  have hdiff : DifferentiableAt ℝ (u i) xs :=
    ((hu i).differentiableOn (by norm_num) xs (hKU hxsK)).differentiableAt
      (hU.mem_nhds (hKU hxsK))
  set s : Set (∀ j, E j) := (fun y => Function.update xs i y) '' K i with hs
  have hmax : IsLocalMaxOn (u i) s xs := by
    apply IsMaxOn.localize
    rintro z ⟨y, hy, rfl⟩
    exact hxs.2 i y hy
  set x' : ∀ j, E j := Function.update xs i (x i) with hx'
  have hseg : segment ℝ xs x' ⊆ s := by
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨a • xs i + b • x i, (hKcv i) hxsi hxi ha hb hab, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hx']
    · simp only [hx', Pi.add_apply, Pi.smul_apply, Function.update_of_ne hj]
      rw [← add_smul, hab, one_smul]
  have hcone := IsLocalMaxOn.hasFDerivWithinAt_nonpos hmax
    hdiff.hasFDerivAt.hasFDerivWithinAt (sub_mem_posTangentConeAt_of_segment_subset hseg)
  have hdir : x' - xs = Pi.single i (x i - xs i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hx']
    · simp [hx', Function.update_of_ne hj, Pi.single_eq_of_ne hj]
  rw [hdir] at hcone
  exact hcone
