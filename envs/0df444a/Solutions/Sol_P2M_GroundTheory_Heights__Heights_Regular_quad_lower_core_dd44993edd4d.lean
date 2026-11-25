-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_quad_lower_core_dd44993edd4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:17.532122+00:00
-- url     : https://prove2.me/submissions/0ddf4da1-1da4-4b9f-9e6b-a780cf11c096

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_dot_self_nonneg_b78618d375ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_isCompact_unitSphereDot_855e9264b529
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_exists_unit_of_ne_zero_01177db69549
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {Z : Type*} [TopologicalSpace Z] {g : ℕ} {K W : Set Z}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (M : Z → Matrix (Fin g) (Fin g) ℝ) (hM : ContinuousOn M W)
    (S : Matrix (Fin g) (Fin g) ℝ) (hS : S.PosSemidef)
    (hpos : ∀ z ∈ K, ∀ v : Fin g → ℝ, v ≠ 0 → S *ᵥ v = 0 → 0 < v ⬝ᵥ M z *ᵥ v) :
    ∃ L ε : ℝ, 0 < ε ∧ ∀ z ∈ K, ∀ v : Fin g → ℝ,
      ε * (v ⬝ᵥ v) ≤ L * (v ⬝ᵥ S *ᵥ v) + v ⬝ᵥ M z *ᵥ v := by
  have hSnn : ∀ v : Fin g → ℝ, 0 ≤ v ⬝ᵥ S *ᵥ v := fun v => by
    simpa using (posSemidef_iff_dotProduct_mulVec.mp hS).2 v
  have hΦ : Continuous fun q : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => q.2 ⬝ᵥ q.1 *ᵥ q.2 :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  let F : ℕ → Z × (Fin g → ℝ) → ℝ := fun m p =>
    (m : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + p.2 ⬝ᵥ M p.1 *ᵥ p.2
  have hFc : ∀ m, ContinuousOn (F m) (W ×ˢ Set.univ) := by
    intro m
    have hQ : ContinuousOn (fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ M p.1 *ᵥ p.2) (W ×ˢ Set.univ) :=
      hΦ.comp_continuousOn ((hM.comp continuous_fst.continuousOn fun p hp => hp.1).prodMk
        continuous_snd.continuousOn)
    have hS' : Continuous fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ S *ᵥ p.2 :=
      continuous_snd.dotProduct (continuous_const.matrix_mulVec continuous_snd)
    exact (continuous_const.mul hS').continuousOn.add hQ
  let U : ℕ → Set (Z × (Fin g → ℝ)) := fun m =>
    (W ×ˢ Set.univ) ∩ F m ⁻¹' Set.Ioi (1 / ((m : ℝ) + 1))
  have hUo : ∀ m, IsOpen (U m) := fun m =>
    (hFc m).isOpen_inter_preimage (hW.prod isOpen_univ) isOpen_Ioi
  have hmono : Monotone U := by
    intro m m' hmm' p hp
    refine ⟨hp.1, ?_⟩
    have hp2 : 1 / ((m : ℝ) + 1) < F m p := hp.2
    have hmm : (m : ℝ) ≤ m' := Nat.cast_le.mpr hmm'
    have h1 : F m p ≤ F m' p := by
      have := hSnn p.2
      show (m : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + _ ≤ (m' : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + _
      nlinarith
    have h2 : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by gcongr
    show 1 / ((m' : ℝ) + 1) < F m' p
    linarith
  have hcover : K ×ˢ unitSphereDot g ⊆ ⋃ m, U m := by
    rintro ⟨z, u⟩ ⟨hz, hu⟩
    have hu' : u ⬝ᵥ u = 1 := hu
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu'
    simp only [Set.mem_iUnion]
    have hm0 : ∀ m : ℕ, (0 : ℝ) ≤ m := fun m => Nat.cast_nonneg m
    by_cases hSu : S *ᵥ u = 0
    · have hQ := hpos z hz u hu0 hSu
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hQ
      refine ⟨m, ⟨⟨hKW hz, trivial⟩, ?_⟩⟩
      show 1 / ((m : ℝ) + 1) < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) + u ⬝ᵥ M z *ᵥ u
      have := hSnn u
      nlinarith [hm0 m]
    · have hs : 0 < u ⬝ᵥ S *ᵥ u := by
        refine lt_of_le_of_ne (hSnn u) (fun h => hSu ?_)
        have := (hS.dotProduct_mulVec_zero_iff u).mp
        simp only [star_trivial] at this
        exact this h.symm
      obtain ⟨m, hm⟩ := exists_nat_gt ((1 - u ⬝ᵥ M z *ᵥ u) / (u ⬝ᵥ S *ᵥ u))
      refine ⟨m, ⟨⟨hKW hz, trivial⟩, ?_⟩⟩
      show 1 / ((m : ℝ) + 1) < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) + u ⬝ᵥ M z *ᵥ u
      have h1 : 1 - u ⬝ᵥ M z *ᵥ u < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) := by rwa [div_lt_iff₀ hs] at hm
      have h2 : 1 / ((m : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [hm0 m]
      linarith
  obtain ⟨m, hm⟩ := (hK.prod (isCompact_unitSphereDot g)).elim_directed_cover U hUo hcover
    hmono.directed_le
  refine ⟨m, 1 / ((m : ℝ) + 1), by positivity, fun z hz v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  obtain ⟨u, hu, huM⟩ := exists_unit_of_ne_zero hv
  have hp : 1 / ((m : ℝ) + 1) < F m (z, u) := (hm ⟨hz, hu⟩).2
  have hvv := dot_self_nonneg v
  rw [huM S, huM (M z)]
  have h := mul_le_mul_of_nonneg_left hp.le hvv
  simp only [F] at h
  nlinarith [h]
end GroundTheory.Heights₂.Heights.Regular
