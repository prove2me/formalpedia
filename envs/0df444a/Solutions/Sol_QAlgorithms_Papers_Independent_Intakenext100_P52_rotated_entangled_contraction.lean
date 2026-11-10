-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.rotated_entangled_contraction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:47:09.739627+00:00
-- url     : https://prove2.me/submissions/a2186911-e784-464b-bb2e-e5c3ebab1b36

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52
  QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (alpha : Vec I) (halpha : IsState alpha) :
    teleportContraction alpha (finiteMaxEntangled I) (rotatedEntangledKet U) =
      ((Fintype.card I : ℂ)⁻¹) • act U alpha := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((Real.sqrt (Fintype.card I))⁻¹ : ℂ) := ⟨_, rfl⟩
  have hphi : ∀ p : I × I, finiteMaxEntangled I p = if p.1 = p.2 then c else 0 := by
    intro p
    rw [hc]
    rfl
  have hcc : conj c = c := by
    rw [hc]
    simp
  have hs : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) * ((Real.sqrt (Fintype.card I) : ℝ) : ℂ)
      = (Fintype.card I : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have hc2 : c * c = (Fintype.card I : ℂ)⁻¹ := by
    rw [hc]
    push_cast
    rw [← mul_inv, hs]
  have hrot : ∀ i j, rotatedEntangledKet U (i, j) = star (U j i) * c := by
    intro i j
    unfold rotatedEntangledKet act
    rw [PiLp.toLp_apply]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
      Matrix.one_apply, Matrix.conjTranspose_apply, hphi]
    simp
    rw [Finset.sum_eq_single j]
    · simp [Matrix.one_apply]
    · intro b _ hb
      simp [Matrix.one_apply, Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  ext k
  unfold teleportContraction
  rw [PiLp.toLp_apply]
  simp only [hrot, hphi]
  unfold act
  rw [PiLp.smul_apply, PiLp.toLp_apply]
  simp only [Matrix.mulVec, dotProduct, map_mul, Complex.star_def, Complex.conj_conj, hcc]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← hc2]
  ring
