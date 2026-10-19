-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.eventually_normalizedIndicatorDefect_markov_pow_lt_of_rooted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/091543d5-8ab1-4421-a559-1835babd14d9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_exists_equivariant_hilbert_normalized_rooted_pair_realization
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_inner_smul_cocycle_sum_eq_zero_of_invariant
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_unitaryFinsetMarkov_iterate_norm_le
import Theorems.Thm_SoficGroups_KunRootedWordPower_tendsto_norm_normalizedIndicatorDefect_markov_pow
import Theorems.Thm_SoficGroups_KunRootedWordPower_pairedDefectWordAverage_eq_unitaryFinsetMarkov_iterate

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    {V : ℕ → Type u} [∀ n, Fintype (V n)]
    (p : ∀ n, ↥S → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (w : G → List ↥S)
    (hf : ∀ n x, f n x = 0 ∨ f n x = 1)
    (hdefect : ∀ n,
      permutationMarkov (p n) (indicatorVector (f n)) ≠
        indicatorVector (f n))
    (hw : ∀ n g, σ n g = ((w g).map (p n)).prod)
    (hone : ∀ n, σ n 1 = 1)
    (hgenerator : ∀ n (i : ↥S), σ n (i : G) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ),
      ‖((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n))‖ <
        kazhdanMarkovContractionFactor P S ^ k + ε := by
  letI : Nonempty (↥S) := ⟨⟨1, honeS⟩⟩
  let s : ↥S → G := fun i => (i : G)
  obtain ⟨K, R, _hpositive, _hdiagonal, hequivariant,
      _hadd, hcocycle, hunit, hgram⟩ :=
    exists_equivariant_hilbert_normalized_rooted_pair_realization
      p f σ s w hf hdefect hw hone hgenerator hroot
  let z : R.realization.carrier :=
    pairedDefectWordAverage s R.realization.vector 0
  have hzone : ‖z‖ = 1 := by
    simpa only [z, pairedDefectWordAverage, pairedWordAverage,
      equivariantPairCocycle] using hunit
  have hzform :
      z = (S.card : ℂ)⁻¹ •
        ∑ g ∈ S, equivariantPairCocycle R g := by
    change
      (Fintype.card (↥S) : ℂ)⁻¹ •
        (∑ i : ↥S, R.realization.vector ((i : G), 1)) =
          (S.card : ℂ)⁻¹ •
            ∑ g ∈ S, equivariantPairCocycle R g
    rw [Fintype.card_coe, ← Finset.sum_coe_sort S]
    rfl
  have horth : ∀ y : R.realization.carrier,
      (∀ g : G, R.representation g y = y) →
        @inner ℂ R.realization.carrier _ y z = 0 := by
    intro y hy
    rw [hzform]
    exact inner_smul_cocycle_sum_eq_zero_of_invariant
      R.representation (equivariantPairCocycle R) hcocycle
      S hsymmetric (S.card : ℂ)⁻¹ y hy
  have hbound :
      ‖pairedDefectWordAverage s R.realization.vector k‖ ≤
        kazhdanMarkovContractionFactor P S ^ k := by
    rw [pairedDefectWordAverage_eq_unitaryFinsetMarkov_iterate
      R.representation S R.realization.vector hequivariant k]
    change ‖((unitaryFinsetMarkov R.representation S)^[k]) z‖ ≤ _
    calc
      ‖((unitaryFinsetMarkov R.representation S)^[k]) z‖ ≤
          kazhdanMarkovContractionFactor P S ^ k * ‖z‖ :=
        unitaryFinsetMarkov_iterate_norm_le
          P R.representation S honeS hcover z horth k
      _ = kazhdanMarkovContractionFactor P S ^ k := by
        rw [hzone, mul_one]
  have hstrict :
      ‖pairedDefectWordAverage s R.realization.vector k‖ <
        kazhdanMarkovContractionFactor P S ^ k + ε :=
    hbound.trans_lt (lt_add_of_pos_right _ hε)
  have hlimit := tendsto_norm_normalizedIndicatorDefect_markov_pow
    p f σ s R.realization.vector hone hgenerator hroot hgram k
  exact hlimit.eventually (Iio_mem_nhds hstrict)
end SoficGroups.KunRootedWordPower
