-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitDegree_full_f938816fbbe2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:43.389065+00:00
-- url     : https://prove2.me/submissions/1b8325c7-7a86-4337-8670-d0e05e1d40d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_homogForm_9c410c1834c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_homog_sum_eq_99e15293109e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_homog_sum_zero_e8577340b774
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_homogForm_mem_orbitIdeal_fdc7dade412e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_relation_bf34191512a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_conj_eq_zero_be975f9d4692
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace OrbitDegree
theorem _root_.solution : OrbitDegree.Statement := by
  intro ι _ _ n x hx
  set W := orbitIdeal x
  set Q := Quot fun z z' : Geo.mcPts (ι := blockIdx n) W ↦
    ∃ c : ι → ℂ, (∀ k, c k ≠ 0) ∧ (z' : Coord n → ℂ) = fun p ↦ c p.1 * (z : Coord n → ℂ) p
  show 0 < Nat.card Q
  rw [Nat.card_pos_iff]

  let _ : Algebra.IsAlgebraic ℤ (AlgebraicClosure ℚ) := ⟨fun r ↦
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic r)⟩
  let σ : AlgebraicClosure ℚ →+* ℂ :=
    (IsAlgClosed.lift (R := ℤ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom
  have hσ : (fun p ↦ σ (flatCone x p)) ∈ Geo.mcPts (ι := blockIdx n) W := by
    refine ⟨fun k ↦ ?_, fun f hf ↦ eval_conj_eq_zero x σ hf⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
    exact ⟨i, (map_ne_zero σ).mpr hi⟩
  refine ⟨⟨Quot.mk _ ⟨_, hσ⟩⟩, ?_⟩

  obtain ⟨c, hc⟩ := exists_chart hx
  let q : Coord n → Coord n := fun p ↦ ⟨p.1, c p.1⟩
  have hq : ∀ p, flatCone x (q p) ≠ 0 := fun p ↦ hc p.1
  choose g hg0 hg using fun p ↦ exists_int_relation (flatCone x p / flatCone x (q p))
  have hmem : ∀ p, homogForm (g p) p (q p) ∈ W := fun p ↦
    homogForm_mem_orbitIdeal x (g p) p (q p) rfl (hq p) (hg p)
  have hform : ∀ z ∈ Geo.mcPts (ι := blockIdx n) W, ∀ p,
      ∑ j ∈ Finset.range ((g p).natDegree + 1),
        ((g p).coeff j : ℂ) * z p ^ j * z (q p) ^ ((g p).natDegree - j) = 0 := fun z hz p ↦ by
    rw [← eval_homogForm]; exact hz.2 _ (hmem p)

  have hz0 : ∀ z ∈ Geo.mcPts (ι := blockIdx n) W, ∀ k, z ⟨k, c k⟩ ≠ 0 := by
    intro z hz k h0
    obtain ⟨i, hi⟩ := hz.1 k
    have := hform z hz ⟨k, i⟩
    simp only [q] at this
    rw [h0, homog_sum_zero] at this
    exact mul_ne_zero (Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (hg0 _)))
      (pow_ne_zero _ hi) this

  let T : Set (Coord n → ℂ) := Set.pi Set.univ fun p ↦ {t | ((g p).map (Int.castRingHom ℂ)).IsRoot t}
  have hT : T.Finite := Set.Finite.pi fun p ↦
    Polynomial.finite_setOfPred_isRoot ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr (hg0 p))
  have hrat : ∀ z ∈ Geo.mcPts (ι := blockIdx n) W, (fun p ↦ z p / z (q p)) ∈ T := by
    intro z hz p _
    have h := hform z hz p
    rw [homog_sum_eq _ _ _ (hz0 z hz p.1)] at h
    have h' := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (hz0 z hz p.1))
    rw [Polynomial.aeval_def, algebraMap_int_eq] at h'
    simpa [Polynomial.IsRoot, Polynomial.eval_map] using h'
  let F : Q → T := Quot.lift (fun z ↦ ⟨_, hrat z.1 z.2⟩) (by
    rintro z z' ⟨a, ha, e⟩
    apply Subtype.ext
    funext p
    simp only [e, q]
    rw [mul_div_mul_left _ _ (ha p.1)])
  have hF : Function.Injective F := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
    have h' := fun p ↦ congrFun (congrArg Subtype.val h) p
    simp only [F] at h'
    refine Quot.sound ⟨fun k ↦ z' ⟨k, c k⟩ / z ⟨k, c k⟩,
      fun k ↦ div_ne_zero (hz0 z' hz' k) (hz0 z hz k), ?_⟩
    funext p
    have hp := h' p
    simp only [q] at hp
    have h1 := hz0 z hz p.1
    have h2 := hz0 z' hz' p.1
    have e : z' p = z p / z ⟨p.1, c p.1⟩ * z' ⟨p.1, c p.1⟩ := by
      rw [hp, div_mul_cancel₀ _ h2]
    show z' p = z' ⟨p.1, c p.1⟩ / z ⟨p.1, c p.1⟩ * z p
    rw [e]
    field_simp
  have : Finite T := hT.to_subtype
  exact Finite.of_injective F hF
end OrbitDegree
end GroundTheory.Heights₂.Heights
