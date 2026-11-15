-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.fine_sector_rayleigh_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:36:43.490538+00:00
-- url     : https://prove2.me/submissions/c17715ca-9533-47b3-b111-8d100f617071

import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_projector_coordinate_equiv
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

set_option autoImplicit false

theorem solution {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ} (D : Data G A n) (r : Row D)
    (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (w : (Fin n × Fin n) → ℂ)
    (hfix : (fineMatrix D.U D.F r.1.val r.2).mulVec w = w)
    (hnorm : (∑ p, conj (w p) * w p) = 1)
    (hcomm : M * fineMatrix D.U D.F r.1.val r.2 = fineMatrix D.U D.F r.1.val r.2 * M) :
    M.mulVec w = (∑ p, conj (w p) * M.mulVec w p) • w := by
  classical
  obtain ⟨C,hC⟩ := fine_projector_coordinate_equiv D
  have hc : C w = Pi.single r (C w r) := by
    have h := hC r w
    rw [hfix] at h
    exact h
  have hmfix : (fineMatrix D.U D.F r.1.val r.2).mulVec (M.mulVec w) = M.mulVec w := by
    rw [Matrix.mulVec_mulVec,← hcomm,← Matrix.mulVec_mulVec,hfix]
  have hmc : C (M.mulVec w) = Pi.single r (C (M.mulVec w) r) := by
    have h := hC r (M.mulVec w)
    rw [hmfix] at h
    exact h
  have hn : C w r ≠ 0 := by
    intro hz
    have hcz : C w = 0 := by rw [hc,hz]; simp
    have hw : w = 0 := C.injective (by simpa using hcz)
    simp [hw] at hnorm
  let c : ℂ := C (M.mulVec w) r / C w r
  have he : M.mulVec w = c • w := by
    apply C.injective
    rw [map_smul,hc,hmc]
    funext s
    by_cases hs : s = r
    · subst s; simp [c,hn]
    · simp [Pi.single_apply,hs]
  have hl : (∑ p, conj (w p) * M.mulVec w p) = c := by
    rw [he]
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = c * (∑ p, conj (w p) * w p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = c := by rw [hnorm,mul_one]
  rw [hl]
  exact he