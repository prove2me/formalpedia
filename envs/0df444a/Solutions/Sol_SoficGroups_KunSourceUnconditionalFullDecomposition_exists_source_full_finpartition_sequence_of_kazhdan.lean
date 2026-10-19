-- Prove2me | solution 1 for SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_full_finpartition_sequence_of_kazhdan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/62755f34-0405-48a1-9f9e-39798e591554

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_diverging_radius_with_vanishing_diagonal_error
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdanMarkovContractionFactor_lt_one
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_symmetricGeneratorWord_prod
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenCayleyRadiusBad_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_exists_expanding_full_finpartition_sequence
import Theorems.Thm_SoficGroups_KunSourceUnconditionalFullDecomposition_exists_source_sparse_cut_at_radius

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSourceUnconditionalFullDecomposition
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunActualRootedModelBridge
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
namespace SoficGroups.KunSourceUnconditionalFullDecomposition
theorem _root_.solution
    {G : Type} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (P : SoficGroups.KazhdanPair.{0, 0} G)
    (S : Finset G) (hone : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    ∃ (γ : ℝ)
      (Q : (n : ℕ) →
        Finpartition
          (Finset.univ : Finset (Fin (A.model n).size))),
      0 < γ ∧
        (∀ n, ∀ C ∈ (Q n).parts,
          ∀ E : Finset (Fin (A.model n).size),
            E ⊆ C →
            2 * E.card ≤ C.card →
            γ * (E.card : ℝ) ≤
              (SoficGroups.boundary
                (fun i : ↥S =>
                  (A.model n).action (i : G)) E : ℝ)) ∧
        Tendsto
          (fun n =>
            (∑ C ∈ (Q n).parts,
              (SoficGroups.boundary
                (fun i : ↥S =>
                  (A.model n).action (i : G)) C : ℝ)) /
                  (A.model n).size)
          atTop (𝓝 0) := by
  classical
  letI : Nonempty (↥S) := ⟨⟨1, hone⟩⟩
  let q : ℝ := kazhdanMarkovContractionFactor P S
  let γ : ℝ := (S.card : ℝ) * (1 - q) ^ 2 / 288
  have hq : q < 1 :=
    kazhdanMarkovContractionFactor_lt_one P S ⟨1, hone⟩
  have hd : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  have hγ : 0 < γ := by
    dsimp [γ]
    positivity
  have hsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2 := by
    have hgap : 0 < (S.card : ℝ) * (1 - q) ^ 2 := by
      positivity
    dsimp [γ, q]
    nlinarith
  let α : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hα (j : ℕ) : 0 < α j := by
    dsimp [α]
    positivity
  have hαzero : Tendsto α atTop (𝓝 0) := by
    simpa [α] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsparse (j : ℕ) :=
    exists_source_sparse_cut_at_radius
      P S hone hcover hsymmetric hgenerates
      γ (α j) hγ (hα j) hsmall
  let radius : ℕ → ℕ := fun j => (hsparse j).choose
  let w : G → List ↥S :=
    symmetricGeneratorWord S hsymmetric hgenerates
  have hw : ∀ g : G,
      ((w g).map fun i : ↥S => (i : G)).prod = g := by
    intro g
    exact symmetricGeneratorWord_prod S hsymmetric hgenerates g
  let e : ℕ → ℕ → ℝ := fun n j =>
    ((chosenCayleyRadiusBad A S w n (radius j)).card : ℝ) /
      (A.model n).size
  have henonnegative : ∀ n j, 0 ≤ e n j := by
    intro n j
    dsimp [e]
    positivity
  have hezero (j : ℕ) :
      Tendsto (fun n => e n j) atTop (𝓝 0) := by
    simpa only [e] using
      chosenCayleyRadiusBad_density_tendsto_zero
        A S w hw (radius j)
  obtain ⟨m, hm, he⟩ :=
    SoficGroups.exists_diverging_radius_with_vanishing_diagonal_error
      e henonnegative hezero
  let B : (n : ℕ) → Finset (Fin (A.model n).size) :=
    fun n => chosenCayleyRadiusBad A S w n (radius (m n))
  let a : ℕ → ℝ := fun n => α (m n)
  let σ : (n : ℕ) → ↥S → Equiv.Perm (Fin (A.model n).size) :=
    fun n i => (A.model n).action (i : G)
  letI (n : ℕ) : Nonempty (Fin (A.model n).size) :=
    ⟨⟨0, (A.model n).size_pos⟩⟩
  have hazero : Tendsto a atTop (𝓝 0) := by
    exact hαzero.comp hm
  have hbad :
      Tendsto
        (fun n =>
          ((B n).card : ℝ) /
            Fintype.card (Fin (A.model n).size))
        atTop (𝓝 0) := by
    simpa only [B, e, Fintype.card_fin] using he
  have himprove :
      ∀ n (T : Finset (Fin (A.model n).size)),
        T ⊆ Finset.univ \ B n →
        (SoficGroups.boundary (σ n) T : ℝ) <
          γ * (T.card : ℝ) →
        ∃ U : Finset (Fin (A.model n).size),
          3 * (U ∆ T).card < T.card ∧
            (SoficGroups.boundary (σ n) U : ℝ) ≤
              a n * (U.card : ℝ) := by
    intro n T hT hboundary
    have hdisjoint : Disjoint T (B n) := by
      apply Finset.disjoint_left.mpr
      intro x hx hbadx
      exact (Finset.mem_sdiff.mp (hT hx)).2 hbadx
    have hgood :
        Disjoint T
          (chosenCayleyRadiusBad A S
            (symmetricGeneratorWord S hsymmetric hgenerates)
            n ((hsparse (m n)).choose)) := by
      simpa only [B, w, radius] using hdisjoint
    have hboundary' :
        (SoficGroups.boundary
          (fun i : ↥S => (A.model n).action (i : G)) T : ℝ) <
            γ * (T.card : ℝ) := by
      simpa only [σ] using hboundary
    obtain ⟨U, hclose, hcut⟩ :=
      (hsparse (m n)).choose_spec A n T hgood hboundary'
    refine ⟨U, hclose, ?_⟩
    simpa only [σ, a] using hcut
  obtain ⟨Q, hγ', hQ, hbudget⟩ :=
    SoficGroups.KunResidualExpanderDecomposition.exists_expanding_full_finpartition_sequence
        (↥S) (fun n => Fin (A.model n).size)
        σ B γ hγ a
        (fun n => (hα (m n)).le)
        hazero hbad himprove
  refine ⟨γ, Q, hγ', ?_, ?_⟩
  · simpa only [σ] using hQ
  · simpa only [σ, Fintype.card_fin] using hbudget
end SoficGroups.KunSourceUnconditionalFullDecomposition
