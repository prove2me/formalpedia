-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.exists_equivariant_hilbert_normalized_rooted_pair_realization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/6271de63-dc2e-47a0-a962-913fb3f809c1

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_exists_hyperfilter_diagonal_positive_pair_kernel_of_rooted_indicators
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_hilbertKernelRealization_pair_vector_add
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_exists_equivariantHilbertKernelRealization
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_equivariantPairCocycle_mul
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_norm_average_normalizedPairDisplacement_of_model
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_norm_smul_finset_sum_eq_one_of_gram

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {G ι : Type u} [Group G] [Fintype ι] [Nonempty ι]
    {V : ℕ → Type u} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (s : ι → G) (w : G → List ι)
    (hf : ∀ n x, f n x = 0 ∨ f n x = 1)
    (hdefect : ∀ n, permutationMarkov (p n) (indicatorVector (f n)) ≠
      indicatorVector (f n))
    (hw : ∀ n g, σ n g = ((w g).map (p n)).prod)
    (hone : ∀ n, σ n 1 = 1)
    (hgenerator : ∀ n i, σ n (s i) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x) :
    ∃ (K : Matrix (G × G) (G × G) ℂ)
      (R : EquivariantHilbertKernelRealization K),
      K.PosSemidef ∧
      (∀ a g h j k : G,
        K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) ∧
      (∀ a g h : G,
        R.representation a (R.realization.vector (g, h)) =
          R.realization.vector (a * g, a * h)) ∧
      (∀ g h j : G,
        R.realization.vector (g, h) +
          R.realization.vector (h, j) =
            R.realization.vector (g, j)) ∧
      (∀ a g : G,
        equivariantPairCocycle R (a * g) =
          equivariantPairCocycle R a +
            R.representation a (equivariantPairCocycle R g)) ∧
      ‖(Fintype.card ι : ℂ)⁻¹ •
        ∑ i, equivariantPairCocycle R (s i)‖ = 1 ∧
      ∀ q r,
        Tendsto
          (fun n =>
            ⟪normalizedPairDisplacement (p n) (f n) (σ n) q,
              normalizedPairDisplacement (p n) (f n) (σ n) r⟫_ℂ)
          (Filter.hyperfilter ℕ)
          (𝓝 ⟪R.realization.vector q,
            R.realization.vector r⟫_ℂ) := by
  obtain ⟨K, hpositive, hdiagonal, hadd, hconv⟩ :=
    exists_hyperfilter_diagonal_positive_pair_kernel_of_rooted_indicators
      p f σ w hf hdefect hw hroot
  obtain ⟨R⟩ :=
    exists_equivariantHilbertKernelRealization K hpositive hdiagonal
  refine ⟨K, R, hpositive, hdiagonal, R.equivariant, ?_, ?_, ?_, ?_⟩
  · exact hilbertKernelRealization_pair_vector_add
      K R.realization hadd
  · exact equivariantPairCocycle_mul K R hadd
  · apply norm_smul_finset_sum_eq_one_of_gram
      (Filter.hyperfilter ℕ)
      (fun n i => normalizedPairDisplacement (p n) (f n) (σ n)
        (s i, 1))
      (fun i => equivariantPairCocycle R (s i))
      (F := Finset.univ) (c := (Fintype.card ι : ℂ)⁻¹)
    · intro i j
      simpa only [equivariantPairCocycle, R.realization.gram] using
        hconv (s i, 1) (s j, 1)
    · intro n
      simpa using norm_average_normalizedPairDisplacement_of_model
        (p n) (f n) (σ n) s (hone n) (hgenerator n) (hdefect n)
  · intro q r
    simpa only [R.realization.gram] using hconv q r
end SoficGroups.KunRootedIndicatorCrossing
