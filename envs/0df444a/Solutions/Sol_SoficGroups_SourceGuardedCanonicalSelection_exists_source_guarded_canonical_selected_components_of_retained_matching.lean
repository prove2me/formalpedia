-- Prove2me | solution 1 for SoficGroups.SourceGuardedCanonicalSelection.exists_source_guarded_canonical_selected_components_of_retained_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/8c4b60c5-916f-40c4-94e4-461d12d04e69

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualRetainedSelection_exists_matched_slow_diagonal_large_components_on_source_scale_tail
import Theorems.Thm_SoficGroups_KunActualCompressedSourceGroupFoundations_alphaZeroPrefixElementaryGroup_infinite
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_canonicalProductRadiusBad_density_tendsto_zero
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_canonical_source_matched_component_cayley_ball_realization
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_sourceCompressedGeneratingFinset_one_mem
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_source_canonical_product_radius_crossing_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGuardedCanonicalSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
namespace SoficGroups.SourceGuardedCanonicalSelection
theorem _root_.solution
    [DecidableEq SourceK] [DecidableEq SourceJ]
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hone : 1 ∈ SΓ)
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤)
    (P Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    {κ : Type*} [Fintype κ]
    (σ : (n : ℕ) → κ → Equiv.Perm (Fin (A.model n).size))
    (R : (n : ℕ) → Finset (Finset (Fin (A.model n).size)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : (n : ℕ) → Finset (Fin (A.model n).size) →
      Finset (Fin (A.model n).size))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (H eta : ℕ → ℝ)
    (hH : Tendsto H atTop (nhds 0))
    (heta : Tendsto eta atTop (nhds 0))
    (hmajor : ∀ n,
      eta n ≤ (1 : ℝ) / 2 →
      2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        ∀ C, C ∈ R n →
          (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n =>
        ((((Finset.univ : Finset (Fin (A.model n).size)) \
          SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
            (A.model n).size))
      atTop (nhds 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) /
          (A.model n).size)
      atTop (nhds 0))
    (F : Finset SourceJ)
    (E : (n : ℕ) → ℕ → Finset (Fin (A.model n).size))
    (hE : ∀ k, Tendsto
      (fun n => ((E n k).card : ℝ) / (A.model n).size)
      atTop (nhds 0))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                  i)) C : ℝ)) /
            (A.model n).size)
      atTop (nhds 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ)) /
          (A.model n).size)
      atTop (nhds 0))
    (N₀ : ℕ) :
    ∃ (N : ℕ) (r : ℕ → ℕ)
      (C : (n : ℕ) → Finset (Fin (A.model (n + N)).size)),
      N₀ ≤ N ∧
      (∀ n, eta (n + N) ≤ (1 : ℝ) / 2) ∧
      (∀ n,
        2 * (Real.exp (H (n + N)) - 1 +
          2 * eta (n + N)) < 1) ∧
      Tendsto r atTop atTop ∧
      (∀ n, C n ∈ R (n + N)) ∧
      Tendsto
        (fun n =>
          (SoficGroups.boundary (σ (n + N)) (C n) : ℝ) /
            (C n).card)
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (((C n ∩ SoficGroups.matchedRadiusBad
            (P (n + N))
            (SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
              (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset SΓ)
              F (r n))
            (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
              A).model (n + N)).action)
            (guardedCanonicalProductRadiusBad
              A SΓ hsymmetric hgenerates F E (n + N) (r n))).card : ℝ) /
                (C n).card))
        atTop (nhds 0) ∧
      Tendsto (fun n => (C n).card) atTop atTop := by
  classical
  letI : Infinite SourceK :=
    SoficGroups.KunActualCompressedSourceGroupFoundations.alphaZeroPrefixElementaryGroup_infinite
  have hnonempty (n : ℕ) : Nonempty (Fin (A.model n).size) :=
    Fin.pos_iff_nonempty.mp (A.model n).size_pos
  letI : ∀ n, Nonempty (Fin (A.model n).size) := hnonempty
  let SK : Finset SourceK :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset SΓ
  let Ap : SoficGroups.SoficApproximation (SourceK × SourceJ) :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A
  let I : ℕ → Finset (SourceK × SourceJ) := fun k =>
    SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
      SK F k
  let w : (n : ℕ) → SourceK × SourceJ →
      Equiv.Perm (Fin (A.model n).size) :=
    fun n z => (Ap.model n).action z
  let B : (n : ℕ) → ℕ → Finset (Fin (A.model n).size) :=
    fun n k => guardedCanonicalProductRadiusBad
      A SΓ hsymmetric hgenerates F E n k
  have hSKone : 1 ∈ SK :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_one_mem
      SΓ hone
  have hSKsym : ∀ g ∈ SK, g⁻¹ ∈ SK :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_inv_mem
      SΓ hsymmetric
  have hSKgen : Subgroup.closure (SK : Set SourceK) = ⊤ :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_closure
      SΓ hgenerates
  have hU (n : ℕ) :
      (Finset.univ : Finset (Fin (A.model n).size)).Nonempty :=
    Finset.univ_nonempty
  have hword (k : ℕ) : Tendsto
      (fun n =>
        ((∑ z ∈ I k,
          (SoficGroups.partitionWordCrossing
            (Q n) (w n z)).card : ℕ) : ℝ) /
            (Finset.univ : Finset (Fin (A.model n).size)).card)
      atTop (nhds 0) := by
    simpa only [I, w, Ap, SK, Finset.card_univ,
      Fintype.card_fin,
      SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation_model_size] using
      SoficGroups.SourceProductThroughAlpha.source_canonical_product_radius_crossing_density_tendsto_zero
        A SΓ hsymmetric hgenerates Q hsource F k
  have hbad (k : ℕ) : Tendsto
      (fun n =>
        ((((Finset.univ : Finset (Fin (A.model n).size)) ∩
          B n k).card : ℝ) /
            (Finset.univ : Finset (Fin (A.model n).size)).card))
      atTop (nhds 0) := by
    have hcanonical :=
      SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad_density_tendsto_zero
        Ap SK hSKsym hSKgen F k
    have hcanon' : Tendsto
        (fun n =>
          ((SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k).card : ℝ) /
              (A.model n).size)
        atTop (nhds 0) := by
      exact hcanonical
    have hlimit : Tendsto
        (fun n =>
          ((SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k).card : ℝ) /
              (A.model n).size +
            ((E n k).card : ℝ) / (A.model n).size)
        atTop (nhds 0) := by
      simpa using hcanon'.add (hE k)
    refine squeeze_zero (fun n => by positivity) ?_ hlimit
    intro n
    have hnat := Finset.card_union_le
      (SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
        Ap SK hSKsym hSKgen F n k) (E n k)
    have hreal :
        (((SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
          Ap SK hSKsym hSKgen F n k ∪ E n k).card : ℕ) : ℝ) ≤
        ((SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
          Ap SK hSKsym hSKgen F n k).card : ℝ) +
          ((E n k).card : ℝ) := by
      exact_mod_cast hnat
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin]
    change
      ((B n k).card : ℝ) / (A.model n).size ≤ _
    change
      ((SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
        Ap SK hSKsym hSKgen F n k ∪ E n k).card : ℝ) /
        (A.model n).size ≤ _
    calc
      ((SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
        Ap SK hSKsym hSKgen F n k ∪ E n k).card : ℝ) /
        (A.model n).size ≤
          (((SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k).card : ℝ) +
            ((E n k).card : ℝ)) /
            (A.model n).size :=
              div_le_div_of_nonneg_right hreal (by positivity)
      _ = ((SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k).card : ℝ) /
              (A.model n).size +
            ((E n k).card : ℝ) / (A.model n).size := by ring
  have hrealize :
      ∀ n k (C : Finset (Fin (A.model n).size)), C ∈ R n →
        ∀ x ∈ C,
          x ∉ SoficGroups.matchedRadiusBad
            (P n) (I k) (w n) (B n k) →
            ∃ f : SourceK → Fin (A.model n).size,
              Set.MapsTo f (↑(SK ^ (k / 2)) : Set SourceK)
                (↑C : Set (Fin (A.model n).size)) ∧
              Set.InjOn f (↑(SK ^ (k / 2)) : Set SourceK) := by
    intro n k C hCR x hx hgood
    have hgoodcanonical :
        x ∉ SoficGroups.matchedRadiusBad
          (P n) (I k) (w n)
          (SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k) := by
      intro hxcan
      apply hgood
      unfold SoficGroups.matchedRadiusBad at hxcan ⊢
      rcases Finset.mem_union.mp hxcan with hxB | hxW
      · apply Finset.mem_union_left
        change x ∈
          SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k ∪ E n k
        exact Finset.mem_union_left _ hxB
      · exact Finset.mem_union_right _ hxW
    exact
      SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonical_source_matched_component_cayley_ball_realization
        Ap SK hSKone hSKsym hSKgen F n k (P n) C
        (hR n hCR) x hx hgoodcanonical
  have hdiscard' : Tendsto
      (fun n =>
        ((((Finset.univ : Finset (Fin (A.model n).size)) \
          SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
            (Finset.univ : Finset (Fin (A.model n).size)).card))
      atTop (nhds 0) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hdiscard
  have hsymm' : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) /
          (Finset.univ : Finset (Fin (A.model n).size)).card)
      atTop (nhds 0) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hsymm
  have hboundary' : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ)) /
          (Finset.univ : Finset (Fin (A.model n).size)).card)
      atTop (nhds 0) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hboundary
  have hselected :=
    SoficGroups.KunResidualRetainedSelection.exists_matched_slow_diagonal_large_components_on_source_scale_tail
      SK hSKone hSKgen σ
      (fun n => (Finset.univ : Finset (Fin (A.model n).size))) hU
      P Q R hR D hD H eta hH heta hmajor hdiscard' hsymm'
      I w hword B hbad hboundary' hrealize N₀
  simpa only [I, w, Ap, SK, B] using hselected
end SoficGroups.SourceGuardedCanonicalSelection
