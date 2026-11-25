-- Prove2me | solution 1 for SNumbers.le_entropyNumber_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:42:29.72555+00:00
-- url     : https://prove2.me/submissions/da600702-6964-45db-894e-b6d5756a5a52

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_entropyNumber_def
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_entropySet_nonempty
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.entropyNumber_zero_op
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ} {δ : ℝ} {P : Finset Y}
    (hP : ↑P ⊆ ⇑S '' Metric.closedBall 0 1) (hcard : 2 ^ n < P.card)
    (hsep : ∀ z ∈ P, ∀ z' ∈ P, z ≠ z' → δ ≤ dist z z') :
    δ / 2 ≤ entropyNumber S n := by
  classical
  rw [entropyNumber_def]
  refine le_csInf (entropySet_nonempty S n) fun ε hε => ?_
  by_contra hcon
  have hlt : ε < δ / 2 := not_le.mp hcon
  obtain ⟨-, N, hN_card, hcov⟩ := hε
  -- Assign to every point of `P` a covering centre in `N`.
  have hchoice : ∀ z ∈ P, ∃ y ∈ N, dist z y ≤ ε := by
    intro z hz
    have hz' := hcov (hP (Finset.mem_coe.mpr hz))
    simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hz'
    obtain ⟨y, hy, hd⟩ := hz'
    exact ⟨y, by simpa using hy, hd⟩
  choose! g hg_mem hg_dist using hchoice
  -- Distinct points of `P` cannot share a centre.
  have hinj : ∀ z ∈ P, ∀ z' ∈ P, g z = g z' → z = z' := by
    intro z hz z' hz' hgg
    by_contra hne
    have h1 : dist z z' ≤ dist z (g z) + dist (g z) z' := dist_triangle _ _ _
    have h2 : dist (g z) z' = dist z' (g z') := by rw [hgg, dist_comm]
    have h3 := hsep z hz z' hz' hne
    have h4 := hg_dist z hz
    have h5 := hg_dist z' hz'
    rw [h2] at h1
    linarith
  have hcard' : P.card ≤ N.card :=
    Finset.card_le_card_of_injOn g (fun z hz => hg_mem z hz) hinj
  omega
end SNumbers
