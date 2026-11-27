-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.lip_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:55.545085+00:00
-- url     : https://prove2.me/submissions/035dbba8-afc6-4ff8-acde-7ecb8a1e2ecc

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb
import Theorems.Thm_PositivityTheory_ThKEnd_Two_uni_dia
import Theorems.Thm_PositivityTheory_ThKEnd_Two_continuous_uni
import Theorems.Thm_PositivityTheory_ThKEnd_Two_diff_uni
import Theorems.Thm_PositivityTheory_ThKEnd_Two_nil_uni
import Theorems.Thm_PositivityTheory_ThKEnd_Two_bump_ex
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Bump_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain
open scoped Pointwise MatrixGroups
variable {R : Type} [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace PositivityTheory.ThKEnd.Two
theorem _root_.solution [T2Space R] {V Λ : Type} [NormedCommRing V] [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    (p : R →+* V) (q : R →+* Λ) (hp : Continuous p) (hq : Continuous q)
    (hc : ∀ (r : ℝ) (C : Set Λ), IsCompact C → IsCompact {x | ‖p x‖ ≤ r ∧ q x ∈ C})
    (hn : ∀ O ∈ 𝓝 (0 : R), ∃ ε > 0, ∃ U ∈ 𝓝 (0 : Λ), ∀ x, ‖p x‖ ≤ ε → q x ∈ U → x ∈ O) {Γ : Subgroup SL(2, R)}
    (hL : ∀ U ∈ 𝓝 (0 : Λ), ∃ L : AddSubgroup Λ, IsOpen (L : Set Λ) ∧ IsCompact (L : Set Λ) ∧ (L : Set Λ) ⊆ U ∧
      ∃ D : ℝ, ∀ x : R, ∃ ξ, uni (.ofAdd ξ) ∈ Γ ∧ ‖p (ξ + x)‖ ≤ D ∧ q (ξ + x) ∈ L)
    {u : Rˣ} (hu : ‖p (u⁻¹).1‖ ≤ 1 / 2) (hu' : q (u⁻¹).1 = 1) (W : Set SL(2, R)) (hW : W ∈ 𝓝 1) :
    ∃ η, Bump W η ∧ ∀ Ω : Set SL(2, R), IsCompact Ω → ∃ (D : ℝ) (Ω' : Set SL(2, R)), IsCompact Ω' ∧ ∀ x (k : ℕ),
      ∃ γ ∈ Γ, ∃ v ∈ Ω', γ * uni x * dia u ^ k = dia u ^ k * v ∧
        ∀ κ ∈ Ω, ∀ y, |η (κ⁻¹ * (v⁻¹ * y)) - η (κ⁻¹ * y)| ≤ D / 2 ^ k := by
  obtain ⟨η, hη, L, Lo, hlip⟩ := bump_ex p q hp hq hc hn (fun U hU => (hL U hU).imp fun L h => ⟨h.1, h.2.1, h.2.2.1⟩) hW
  refine ⟨η, hη, fun Ω hΩ => ?_⟩
  obtain ⟨T, hT0⟩ : ∃ T : SL(2, R) × SL(2, R) → Matrix (Fin 2) (Fin 2) R, ∀ z, T z = (z.1⁻¹).1 * !![0, 1; 0, 0] * (z.1 * z.2).1 :=
    ⟨_, fun _ => rfl⟩
  have Tc : Continuous T := by
    rw [funext hT0]
    have c : Continuous (Subtype.val : SL(2, R) → Matrix (Fin 2) (Fin 2) R) := continuous_subtype_val
    have c1 : Continuous fun z : SL(2, R) × SL(2, R) => (z.1⁻¹).1 := c.comp (continuous_inv (G := SL(2, R)) |>.comp continuous_fst)
    have c2 : Continuous fun z : SL(2, R) × SL(2, R) => (z.1 * z.2).1 := c.comp (continuous_mul (M := SL(2, R)))
    exact (c1.matrix_mul continuous_const).matrix_mul c2
  have hC : IsCompact (⋃ i, ⋃ j, (fun z => T z i j) '' Ω ×ˢ tsupport η) :=
    isCompact_iUnion fun i => isCompact_iUnion fun j => (hΩ.prod hη.cpt).image (Tc.matrix_elem i j)
  obtain ⟨D₁, hD₁⟩ := hC.exists_bound_of_continuousOn hp.continuousOn
  obtain ⟨L', -, Lc', LU', D, hD⟩ := hL _ (hC.eventually_forall_of_forall_eventually (x₀ := (0 : Λ)) (P := fun z t => z * q t ∈ L)
    fun t _ => (continuous_fst.mul (hq.comp continuous_snd)).continuousAt.preimage_mem_nhds (Lo.mem_nhds (by simp)))
  refine ⟨4 * (D * max D₁ 0), uni '' (Multiplicative.ofAdd '' {x | ‖p x‖ ≤ D ∧ q x ∈ L'}),
    ((hc D L' Lc').image continuous_ofAdd).image continuous_uni, fun x k => ?_⟩
  obtain ⟨ξ, h1, h2, h3⟩ := hD x.toAdd
  have D0 : 0 ≤ D := (norm_nonneg _).trans h2
  obtain ⟨w, hw⟩ : ∃ w, w = ((u ^ k)⁻¹).1 * ((u ^ k)⁻¹).1 * (ξ + x.toAdd) := ⟨_, rfl⟩
  have w1 : ‖p w‖ ≤ D / 2 ^ k := by
    have a : ∀ z : V, ‖p ((u ^ k)⁻¹).1 * z‖ ≤ ‖z‖ / 2 ^ k := fun z => by
      rw [← inv_pow, Units.val_pow_eq_pow_val, map_pow]
      clear hw
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', mul_assoc, pow_succ', ← div_div, div_right_comm, div_eq_inv_mul]
        exact (norm_mul_le _ _).trans (mul_le_mul (hu.trans_eq (one_div _)) ih (norm_nonneg _) (by positivity))
    rw [hw, map_mul, map_mul, mul_assoc]
    refine (a _).trans (div_le_div_of_nonneg_right ((a _).trans ((div_le_self (norm_nonneg _) (one_le_pow₀ one_le_two)).trans h2))
      (by positivity))
  have w2 : q w ∈ L' := by
    rwa [hw, map_mul, map_mul, ← inv_pow, Units.val_pow_eq_pow_val, map_pow, hu', one_pow, one_mul, one_mul]
  refine ⟨_, h1, _, ⟨_, ⟨w, ⟨w1.trans (div_le_self D0 (one_le_pow₀ one_le_two)), w2⟩, rfl⟩, rfl⟩, ?_, fun κ hκ y => ?_⟩
  · rw [← map_mul, ← map_pow, hw, ← uni_dia]; rfl
  have key : ∀ z ∈ tsupport η, T (κ, z) = (κ⁻¹).1 * !![0, 1; 0, 0] * y.1 →
      |η (κ⁻¹ * ((uni (.ofAdd w))⁻¹ * y)) - η (κ⁻¹ * y)| ≤ 4 * (D * max D₁ 0) / 2 ^ k := fun z hz hT => by
    refine (hlip _ _ (D / 2 ^ k * max D₁ 0) fun i j => ?_).trans_eq (by ring)
    have m : T (κ, z) i j ∈ ⋃ i, ⋃ j, (fun z => T z i j) '' Ω ×ˢ tsupport η := Set.mem_iUnion₂.2 ⟨i, j, (κ, z), ⟨hκ, hz⟩, rfl⟩
    rw [diff_uni, ← hT, Matrix.smul_apply, smul_eq_mul, map_mul, map_mul]
    exact ⟨LU' w2 _ m, (norm_mul_le _ _).trans (mul_le_mul w1 ((hD₁ _ m).trans (le_max_left _ _)) (norm_nonneg _) (by positivity))⟩
  by_cases a1 : κ⁻¹ * y ∈ tsupport η
  · exact key _ a1 (by simp only [hT0, mul_inv_cancel_left])
  by_cases a2 : κ⁻¹ * ((uni (.ofAdd w))⁻¹ * y) ∈ tsupport η
  · exact key _ a2 (by simp only [hT0, mul_inv_cancel_left]; rw [Matrix.mul_assoc, nil_uni, Matrix.mul_assoc])
  · have b1 := image_eq_zero_of_notMem_tsupport a1
    have b2 := image_eq_zero_of_notMem_tsupport a2
    simp only [b1, b2, sub_self, abs_zero]
    positivity
end PositivityTheory.ThKEnd.Two
