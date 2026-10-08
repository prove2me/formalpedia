-- Prove2me | solution 1 for UncoupledDyn.Continuum.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:28:53.227977+00:00
-- url     : https://prove2.me/submissions/33598706-e38a-49eb-ab23-687726bbd988

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

open UncoupledDyn.Continuum

set_option maxHeartbeats 800000

private theorem trace_re_nonpos {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : ∀ z ∈ spectrum ℂ A, z.re ≤ 0) :
    A.trace.re ≤ 0 := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  have he : A.charpoly.roots.sum.re = (A.charpoly.roots.map Complex.re).sum :=
    Complex.reAddGroupHom.map_multiset_sum _
  rw [he]
  have hb := Multiset.sum_map_le_sum_map Complex.re (fun _ : ℂ => (0 : ℝ)) (fun z hz =>
    h z (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
      ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mp hz)))
  simpa using hb

private theorem trace_re_neg {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (h : ∀ z ∈ spectrum ℂ A, z.re < 0) :
    A.trace.re < 0 := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  have he : A.charpoly.roots.sum.re = (A.charpoly.roots.map Complex.re).sum :=
    Complex.reAddGroupHom.map_multiset_sum _
  rw [he]
  have hne : A.charpoly.roots ≠ 0 := by
    intro hz
    have hc := (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots
    rw [hz, Multiset.card_zero, Matrix.charpoly_natDegree_eq_dim] at hc
    exact (Fintype.card_pos.ne' hc)
  have hb := Multiset.sum_lt_sum_of_nonempty hne (fun z hz =>
    h z (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
      ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mp hz)))
  simpa using hb

private theorem unit_of_hurwitz {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : ∀ z ∈ spectrum ℂ A, z.re < 0) : IsUnit A := by
  apply spectrum.isUnit_of_zero_notMem (R := ℂ)
  intro hz
  have := h 0 hz
  simp at this

private theorem inv_trace_neg {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (u : (Matrix n n ℂ)ˣ) (h : ∀ z ∈ spectrum ℂ (u : Matrix n n ℂ), z.re < 0) :
    (↑u⁻¹ : Matrix n n ℂ).trace.re < 0 := by
  apply trace_re_neg
  intro z hz
  have hi := h z⁻¹ (spectrum.inv₀_mem_iff.mpr hz)
  have hne : z ≠ 0 := by
    intro he
    subst z
    exact spectrum.zero_notMem (R := ℂ) u⁻¹.isUnit hz
  rw [Complex.inv_re] at hi
  simpa using (div_lt_iff₀ (Complex.normSq_pos.mpr hne)).mp hi

private theorem inv_trace_nonpos {n : Type} [Fintype n] [DecidableEq n]
    (u : (Matrix n n ℂ)ˣ) (h : ∀ z ∈ spectrum ℂ (u : Matrix n n ℂ), z.re ≤ 0) :
    (↑u⁻¹ : Matrix n n ℂ).trace.re ≤ 0 := by
  apply trace_re_nonpos
  intro z hz
  have hi := h z⁻¹ (spectrum.inv₀_mem_iff.mpr hz)
  have hne : z ≠ 0 := by
    intro he
    subst z
    exact spectrum.zero_notMem (R := ℂ) u⁻¹.isUnit hz
  rw [Complex.inv_re] at hi
  simpa using (div_le_iff₀ (Complex.normSq_pos.mpr hne)).mp hi

private def cblock (A1 A2 : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if q.1 = p.1 then ![A1,A2] p.1 p.2 q.2 else -2 * ![A1,A2] p.1 p.2 q.2

private noncomputable def cinverse (u1 u2 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if q.1 = p.1 then (-1/3 : ℂ) * ![(↑u1⁻¹ : Matrix (Fin 2) (Fin 2) ℂ),
      (↑u2⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)] q.1 p.2 q.2
    else (-2/3 : ℂ) * ![(↑u1⁻¹ : Matrix (Fin 2) (Fin 2) ℂ),
      (↑u2⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)] q.1 p.2 q.2

private theorem block_inverse (u1 u2 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) :
    cblock u1 u2 * cinverse u1 u2 = 1 := by
  ext ⟨p,k⟩ ⟨q,l⟩
  have h1 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A k l) u1.mul_inv
  have h2 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A k l) u2.mul_inv
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.coe_units_inv, Matrix.one_apply] at h1 h2
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, cblock, cinverse,
      Matrix.one_apply] <;>
    first | linear_combination h1 | linear_combination h2 | ring

private theorem inverse_trace (u1 u2 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) :
    (cinverse u1 u2).trace = (-1/3 : ℂ) *
      ((↑u1⁻¹ : Matrix (Fin 2) (Fin 2) ℂ).trace +
        (↑u2⁻¹ : Matrix (Fin 2) (Fin 2) ℂ).trace) := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, cinverse]
  ring

theorem UncoupledDyn.Continuum.lemma_3 (J1 J2 : Matrix (Fin 2) (Fin 2) ℝ)
    (h1 : FatkhullinPolyak.Discrete.IsHurwitz J1)
    (h2 : FatkhullinPolyak.Discrete.IsHurwitz J2) :
    ∃ z ∈ spectrum ℂ ((blockJ J1 J2).map (algebraMap ℝ ℂ)), 0 < z.re := by
  classical
  let A1 := J1.map (algebraMap ℝ ℂ)
  let A2 := J2.map (algebraMap ℝ ℂ)
  let u1 := (unit_of_hurwitz A1 h1).unit
  let u2 := (unit_of_hurwitz A2 h2).unit
  have hu1 : (u1 : Matrix (Fin 2) (Fin 2) ℂ) = A1 := (unit_of_hurwitz A1 h1).unit_spec
  have hu2 : (u2 : Matrix (Fin 2) (Fin 2) ℂ) = A2 := (unit_of_hurwitz A2 h2).unit_spec
  have hm := block_inverse u1 u2
  let u : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)ˣ :=
    ⟨cblock u1 u2, cinverse u1 u2, hm, mul_eq_one_comm.mp hm⟩
  have hu : (u : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      (blockJ J1 J2).map (algebraMap ℝ ℂ) := by
    ext ⟨p,k⟩ ⟨q,l⟩
    fin_cases p <;> fin_cases q <;>
      simp [u, cblock, blockJ, hu1, hu2, A1, A2]
  have ht1 := inv_trace_neg u1 (by rw [hu1]; exact h1)
  have ht2 := inv_trace_neg u2 (by rw [hu2]; exact h2)
  by_contra hn
  have hs : ∀ z ∈ spectrum ℂ (u : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), z.re ≤ 0 := by
    intro z hz
    exact le_of_not_gt (fun hp => hn ⟨z, hu ▸ hz, hp⟩)
  have ht := inv_trace_nonpos u hs
  change (cinverse u1 u2).trace.re ≤ 0 at ht
  rw [inverse_trace] at ht
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at ht
  norm_num at ht
  simp only [Matrix.coe_units_inv] at ht1 ht2
  linarith

theorem solution (J1 J2 : Matrix (Fin 2) (Fin 2) ℝ)
    (h1 : FatkhullinPolyak.Discrete.IsHurwitz J1)
    (h2 : FatkhullinPolyak.Discrete.IsHurwitz J2) :
    ∃ z ∈ spectrum ℂ ((blockJ J1 J2).map (algebraMap ℝ ℂ)), 0 < z.re :=
  UncoupledDyn.Continuum.lemma_3 J1 J2 h1 h2

#print axioms solution
