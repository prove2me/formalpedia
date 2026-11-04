-- Prove2me | solution 1 for SpikedWishart.SoftEdge.eq_109_111
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T05:52:21.057342+00:00
-- url     : https://prove2.me/submissions/4c9d3839-043b-4085-bd56-5c63017f69b4

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex

set_option autoImplicit false

namespace SWEq109
open SpikedWishart.SoftEdge

/-- The open domain on which both principal logarithms in `fFn` are holomorphic. -/
def Ud : Set ℂ := {z | z ∈ slitPlane ∧ 1 - z ∈ slitPlane}

theorem Ud_open : IsOpen Ud :=
  isOpen_slitPlane.inter (isOpen_slitPlane.preimage (continuous_const.sub continuous_id))

noncomputable def g1 (γ : ℝ) (z : ℂ) : ℂ := -(mu γ : ℂ) + z⁻¹ + (1 / (γ : ℂ) ^ 2) * (1 - z)⁻¹

noncomputable def g2 (γ : ℝ) (z : ℂ) : ℂ := -(z ^ 2)⁻¹ + (1 / (γ : ℂ) ^ 2) * ((1 - z) ^ 2)⁻¹

theorem hasDerivAt_f (γ q : ℝ) (z : ℂ) (hz : z ∈ Ud) : HasDerivAt (fFn γ q) (g1 γ z) z := by
  obtain ⟨h0, h1⟩ := hz
  have hA : HasDerivAt (fun w : ℂ => -(mu γ : ℂ) * (w - q)) (-(mu γ : ℂ) * 1) z :=
    ((hasDerivAt_id z).sub_const (q : ℂ)).const_mul (-(mu γ : ℂ))
  have hB : HasDerivAt Complex.log z⁻¹ z := Complex.hasDerivAt_log h0
  have hC : HasDerivAt (fun w : ℂ => Complex.log (1 - w)) (-1 / (1 - z)) z :=
    ((hasDerivAt_id z).const_sub (1 : ℂ)).clog h1
  have := (hA.add hB).sub (hC.const_mul (1 / (γ : ℂ) ^ 2))
  show HasDerivAt (fun w : ℂ => -(mu γ : ℂ) * (w - q) + Complex.log w
    - (1 / (γ : ℂ) ^ 2) * Complex.log (1 - w)) _ z
  refine this.congr_deriv ?_
  unfold g1
  ring

theorem hasDerivAt_g1 (γ : ℝ) (z : ℂ) (hz : z ∈ Ud) : HasDerivAt (g1 γ) (g2 γ z) z := by
  obtain ⟨h0, h1⟩ := hz
  have hz0 : z ≠ 0 := slitPlane_ne_zero h0
  have hz1 : (1 : ℂ) - z ≠ 0 := slitPlane_ne_zero h1
  have hB : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz0
  have hC : HasDerivAt (fun w : ℂ => (1 - w)⁻¹) (-(-1) / (1 - z) ^ 2) z :=
    ((hasDerivAt_id z).const_sub (1 : ℂ)).inv hz1
  have := ((hasDerivAt_const z (-(mu γ : ℂ))).add hB).add (hC.const_mul (1 / (γ : ℂ) ^ 2))
  refine this.congr_deriv ?_
  unfold g2
  ring

theorem hasDerivAt_g2 (γ : ℝ) (hγ : (γ : ℂ) ≠ 0) (z : ℂ) (hz : z ∈ Ud) :
    HasDerivAt (g2 γ) (2 / z ^ 3 - 2 / ((γ : ℂ) ^ 2 * (z - 1) ^ 3)) z := by
  obtain ⟨h0, h1⟩ := hz
  have hz0 : z ≠ 0 := slitPlane_ne_zero h0
  have hz1 : (1 : ℂ) - z ≠ 0 := slitPlane_ne_zero h1
  have hz1' : z - 1 ≠ 0 := by
    intro h; apply hz1; linear_combination -h
  have hB : HasDerivAt (fun w : ℂ => (w ^ 2)⁻¹) (-((2 : ℕ) * z ^ (2 - 1) * 1) / (z ^ 2) ^ 2) z :=
    ((hasDerivAt_id z).pow 2).inv (pow_ne_zero 2 hz0)
  have hC : HasDerivAt (fun w : ℂ => ((1 - w) ^ 2)⁻¹)
      (-((2 : ℕ) * (1 - z) ^ (2 - 1) * (-1)) / ((1 - z) ^ 2) ^ 2) z :=
    (((hasDerivAt_id z).const_sub (1 : ℂ)).pow 2).inv (pow_ne_zero 2 hz1)
  have := hB.neg.add (hC.const_mul (1 / (γ : ℂ) ^ 2))
  refine this.congr_deriv ?_
  have e1 : (1 : ℂ) - z = -(z - 1) := by ring
  rw [e1]
  field_simp
  ring

theorem deriv_eq (γ q : ℝ) (z : ℂ) (hz : z ∈ Ud) : deriv (fFn γ q) z = g1 γ z :=
  (hasDerivAt_f γ q z hz).deriv

theorem iter2_eq (γ q : ℝ) (z : ℂ) (hz : z ∈ Ud) : iteratedDeriv 2 (fFn γ q) z = g2 γ z := by
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    (Filter.eventuallyEq_of_mem (Ud_open.mem_nhds hz) (fun w hw => deriv_eq γ q w hw)).deriv_eq]
  exact (hasDerivAt_g1 γ z hz).deriv

theorem iter3_eq (γ q : ℝ) (hγ : (γ : ℂ) ≠ 0) (z : ℂ) (hz : z ∈ Ud) :
    iteratedDeriv 3 (fFn γ q) z = 2 / z ^ 3 - 2 / ((γ : ℂ) ^ 2 * (z - 1) ^ 3) := by
  rw [iteratedDeriv_succ,
    (Filter.eventuallyEq_of_mem (Ud_open.mem_nhds hz) (fun w hw => iter2_eq γ q w hw)).deriv_eq]
  exact (hasDerivAt_g2 γ hγ z hz).deriv

theorem pc_mem (γ : ℝ) (hγ : 1 ≤ γ) : ((pc γ : ℝ) : ℂ) ∈ Ud := by
  have hp : 0 < γ + 1 := by linarith
  refine ⟨Complex.ofReal_mem_slitPlane.mpr (div_pos (by linarith) hp), ?_⟩
  have : (1 : ℂ) - ((pc γ : ℝ) : ℂ) = ((1 - pc γ : ℝ) : ℂ) := by push_cast; ring
  rw [this]
  apply Complex.ofReal_mem_slitPlane.mpr
  unfold pc
  rw [sub_pos, div_lt_one hp]
  linarith

theorem main (γ q : ℝ) (hγ : 1 ≤ γ) :
    deriv (fFn γ q) (pc γ) = 0 ∧
      iteratedDeriv 2 (fFn γ q) (pc γ) = 0 ∧
      (∀ z : ℂ, z ∈ slitPlane → 1 - z ∈ slitPlane →
        iteratedDeriv 3 (fFn γ q) z = 2 / z ^ 3 - 2 / ((γ : ℂ) ^ 2 * (z - 1) ^ 3)) ∧
      iteratedDeriv 3 (fFn γ q) (pc γ) = ((2 * (γ + 1) ^ 4 / γ ^ 3 : ℝ) : ℂ) ∧
      2 * (γ + 1) ^ 4 / γ ^ 3 = 2 * nu γ ^ 3 := by
  have hγ0 : (γ : ℂ) ≠ 0 := by
    have : (0 : ℝ) < γ := by linarith
    exact_mod_cast this.ne'
  have hγ1 : (γ : ℂ) + 1 ≠ 0 := by
    have : (0 : ℝ) < γ + 1 := by linarith
    exact_mod_cast this.ne'
  have hpc : ((pc γ : ℝ) : ℂ) = (γ : ℂ) / ((γ : ℂ) + 1) := by unfold pc; push_cast; ring
  have hmu : ((mu γ : ℝ) : ℂ) = ((1 + (γ : ℂ)) / (γ : ℂ)) ^ 2 := by unfold mu; push_cast; ring
  have hm := pc_mem γ hγ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [deriv_eq γ q _ hm]
    unfold g1
    rw [hpc, hmu]
    have e : (1 : ℂ) - (γ : ℂ) / ((γ : ℂ) + 1) = 1 / ((γ : ℂ) + 1) := by field_simp; ring
    rw [e]
    field_simp
    ring
  · rw [iter2_eq γ q _ hm]
    unfold g2
    rw [hpc]
    have e : (1 : ℂ) - (γ : ℂ) / ((γ : ℂ) + 1) = 1 / ((γ : ℂ) + 1) := by field_simp; ring
    rw [e]
    field_simp
    ring
  · intro z h0 h1
    exact iter3_eq γ q hγ0 z ⟨h0, h1⟩
  · rw [iter3_eq γ q hγ0 _ hm, hpc]
    have e : (γ : ℂ) / ((γ : ℂ) + 1) - 1 = -1 / ((γ : ℂ) + 1) := by field_simp; ring
    rw [e]
    push_cast
    field_simp
    ring
  · have hb : (0 : ℝ) ≤ 1 + γ := by linarith
    have : nu γ ^ 3 = (1 + γ) ^ 4 / γ ^ 3 := by
      unfold nu
      rw [div_pow, ← Real.rpow_natCast ((1 + γ) ^ (4 / 3 : ℝ)) 3, ← Real.rpow_mul hb]
      norm_num
    rw [this]
    ring

end SWEq109

open Complex SpikedWishart.SoftEdge in
theorem solution (γ q : ℝ) (hγ : 1 ≤ γ) :
    deriv (fFn γ q) (pc γ) = 0 ∧
      iteratedDeriv 2 (fFn γ q) (pc γ) = 0 ∧
      (∀ z : ℂ, z ∈ slitPlane → 1 - z ∈ slitPlane →
        iteratedDeriv 3 (fFn γ q) z = 2 / z ^ 3 - 2 / ((γ : ℂ) ^ 2 * (z - 1) ^ 3)) ∧
      iteratedDeriv 3 (fFn γ q) (pc γ) = ((2 * (γ + 1) ^ 4 / γ ^ 3 : ℝ) : ℂ) ∧
      2 * (γ + 1) ^ 4 / γ ^ 3 = 2 * nu γ ^ 3 := by
  exact SWEq109.main γ q hγ
