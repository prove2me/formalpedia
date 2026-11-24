-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointChowForm_proof_efe26cd777c2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:45.360639+00:00
-- url     : https://prove2.me/submissions/5b94ac13-029d-4837-ad4c-fcb0bf128587

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointChowForm

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace PointChowForm
theorem _root_.solution : PointChowForm.Statement := by
  intro n W g y hg hy hW
  obtain ⟨hg0, hgdiv⟩ := hg
  set φ := algebraMap ℂ (AlgebraicClosure ℂ) with hφ
  have hbij : Function.Bijective φ := IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hinj : Function.Injective φ := hbij.1
  set L : MvPolynomial (Fin 1 × Fin n) ℂ := ∑ j, C (y j) * X ((0 : Fin 1), j) with hL
  have hLu : ∀ u : Fin 1 × Fin n → AlgebraicClosure ℂ, aeval u L = ∑ j, φ (y j) * u (0, j) := by
    intro u; simp [hL, map_sum, hφ]

  have hvan : ∀ u ∈ incidence W 1, aeval u L = 0 := by
    rintro u ⟨x, hx0, hxW, hxu⟩
    choose x' hx' using fun j => hbij.2 (x j)
    have hxe : x = φ ∘ x' := funext fun j => (hx' j).symm
    have hW' : ∀ q ∈ W, eval x' q = 0 := by
      intro q hq
      have := hxW q hq
      rw [hxe, aeval_algebraMap_apply] at this
      exact hinj (by simpa using this)
    obtain ⟨t, ht⟩ := (hW x').1 hW'
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hx0
      rw [hxe, ht]
      ext j; simp
    have hsum := hxu 0
    have : ∑ j, u (0, j) * x j = φ t * aeval u L := by
      rw [hLu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hxe, ht]
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    rw [this] at hsum
    exact (mul_eq_zero.1 hsum).resolve_left ((map_ne_zero φ).2 ht0)

  have h0inc : (0 : Fin 1 × Fin n → AlgebraicClosure ℂ) ∈ incidence W 1 := by
    refine ⟨φ ∘ y, ?_, ?_, ?_⟩
    · intro h
      apply hy
      ext j
      exact hinj (by simpa using congrFun h j)
    · intro q hq
      have : eval y q = 0 := (hW y).2 ⟨1, by simp⟩ q hq
      rw [aeval_algebraMap_apply]
      simp [this]
    · intro i; simp
  have hg_at0 : aeval (0 : Fin 1 × Fin n → AlgebraicClosure ℂ) g = 0 :=
    (hgdiv g).2 dvd_rfl 0 h0inc
  obtain ⟨k, hk⟩ := (hgdiv L).1 hvan

  have hL0 : L ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
    intro h
    apply hj
    have := congrArg (coeff (Finsupp.single ((0 : Fin 1), j) 1)) h
    simpa [hL, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_left_inj, Prod.ext_iff] using this
  have hk0 : k ≠ 0 := by rintro rfl; exact hL0 (by rw [hk, mul_zero])
  have hLdeg : L.totalDegree ≤ 1 := by
    rw [hL]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  have hgdeg : 1 ≤ g.totalDegree := by
    by_contra hlt
    have hgC := totalDegree_eq_zero_iff_eq_C.1 (by omega : g.totalDegree = 0)
    rw [hgC, aeval_C] at hg_at0
    apply hg0
    rw [hgC, (map_eq_zero_iff _ hinj).1 hg_at0, C_0]
  have hkdeg : k.totalDegree = 0 := by
    have := totalDegree_mul_of_isDomain hg0 hk0
    rw [← hk] at this
    omega
  obtain ⟨d, hd⟩ : ∃ d : ℂ, k = C d := ⟨_, totalDegree_eq_zero_iff_eq_C.1 hkdeg⟩
  have hd0 : d ≠ 0 := by rintro rfl; exact hk0 (by rw [hd, C_0])
  refine ⟨d⁻¹, inv_ne_zero hd0, ?_⟩
  rw [hk, hd, mul_comm g, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hd0, C_1, one_mul]
end PointChowForm
end GroundTheory.Heights₂.Heights
