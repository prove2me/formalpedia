-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P17.exists_jordan_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T10:48:26.150662+00:00
-- url     : https://prove2.me/submissions/e001f74f-48d6-47fc-9fa7-b57aca23418a

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section
open scoped Matrix ComplexOrder

namespace P17Aux

open Matrix

lemma cfcCont {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact Set.Finite.continuousOn (Set.finite_range hA.eigenvalues) f

lemma psdCfc {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (cfc f A).PosSemidef := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have hd : (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues : I → ℂ)).PosSemidef := by
    rw [posSemidef_diagonal_iff]; intro i
    simpa using hf i
  simpa [star_eq_conjTranspose] using hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix I I ℂ)

lemma traceCfc {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  rfl

lemma minEig_le {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (i : I) : QAlgorithms.minEigenvalue A ≤ hA.eigenvalues i := by
  have h : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  simp only [QAlgorithms.minEigenvalue, dif_pos h, QAlgorithms.ascEigenvalues, dif_pos hA,
    IsHermitian.eigenvalues]
  apply hA.eigenvalues₀_antitone
  rw [Fin.le_def]; simp; omega


lemma specFin {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) : (spectrum ℝ A).Finite := by
  rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _

theorem jd_main {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : QAlgorithms.IsDensityMatrix sigma) :
    ∃ Xp Xm : Matrix I I ℂ, Xp.PosSemidef ∧ Xm.PosSemidef ∧ rho - sigma = Xp - Xm ∧
      Xp.trace = ((QAlgorithms.traceDistance rho sigma : ℝ) : ℂ) ∧
      Xm.trace = ((QAlgorithms.traceDistance rho sigma : ℝ) : ℂ) ∧
      (((QAlgorithms.traceDistance rho sigma : ℝ) : ℂ) • (1 : Matrix I I ℂ) - (Xp + Xm)).PosSemidef := by
  set D := rho - sigma with hDdef
  have hD : D.IsHermitian := hrho.1.isHermitian.sub hsigma.1.isHermitian
  have hsa : IsSelfAdjoint D := hD
  set l := hD.eigenvalues
  set P := ∑ i, max (l i) 0
  set M := ∑ i, max (-l i) 0
  have hsum : ∑ i, l i = 0 := by
    have h1 : D.trace = 0 := by rw [hDdef, Matrix.trace_sub, hrho.2, hsigma.2, sub_self]
    rw [hD.trace_eq_sum_eigenvalues] at h1
    have h2 : ((∑ i, l i : ℝ) : ℂ) = 0 := by push_cast; exact h1
    exact_mod_cast h2
  have hPM : P = M := by
    have : P - M = ∑ i, l i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases le_total (l i) 0 with h | h
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    linarith
  have htd : QAlgorithms.traceDistance rho sigma = P := by
    have hn : QAlgorithms.traceNorm D = ∑ i, |l i| := by
      unfold QAlgorithms.traceNorm
      have hmul : Dᴴ * D = cfc (fun x : ℝ => x * x) D := by
        rw [hD.eq, cfc_mul (f := fun x => x) (g := fun x => x) (a := D) (hf := cfcCont hD _)
          (hg := cfcCont hD _), cfc_id' ℝ D]
      rw [hmul, ← cfc_comp Real.sqrt (fun x : ℝ => x * x) D (hg := Set.Finite.continuousOn
        ((specFin hD).image _) _) (hf := cfcCont hD _), traceCfc hD, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Complex.ofReal_re, Function.comp_apply, Real.sqrt_mul_self_eq_abs]
      rfl
    have habs : ∑ i, |l i| = P + M := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases le_total (l i) 0 with h | h
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]; ring
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]; ring
    unfold QAlgorithms.traceDistance
    rw [← hDdef, hn, habs, ← hPM]; ring
  refine ⟨cfc (fun x : ℝ => max x 0) D, cfc (fun x : ℝ => max (-x) 0) D,
    psdCfc hD _ (fun i => le_max_right _ _), psdCfc hD _ (fun i => le_max_right _ _), ?_, ?_, ?_, ?_⟩
  · rw [← cfc_sub (f := fun x : ℝ => max x 0) (g := fun x : ℝ => max (-x) 0) (a := D)
      (hf := cfcCont hD _) (hg := cfcCont hD _)]
    have : (fun x : ℝ => max x 0 - max (-x) 0) = fun x => x := by
      funext x
      rcases le_total x 0 with h | h
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    rw [this, cfc_id' ℝ D]
  · rw [traceCfc hD, htd]; show _ = ((∑ i, max (l i) 0 : ℝ) : ℂ); push_cast; rfl
  · rw [traceCfc hD, htd, hPM]; show _ = ((∑ i, max (-l i) 0 : ℝ) : ℂ); push_cast; rfl
  · rw [htd]
    have e : ((P : ℝ) : ℂ) • (1 : Matrix I I ℂ) -
        (cfc (fun x : ℝ => max x 0) D + cfc (fun x : ℝ => max (-x) 0) D) =
        cfc (fun x : ℝ => P - (max x 0 + max (-x) 0)) D := by
      rw [cfc_sub (f := fun _ : ℝ => P) (g := fun x : ℝ => max x 0 + max (-x) 0) (a := D)
        (hf := cfcCont hD _) (hg := cfcCont hD _),
        cfc_add (f := fun x : ℝ => max x 0) (g := fun x : ℝ => max (-x) 0) (a := D)
        (hf := cfcCont hD _) (hg := cfcCont hD _), cfc_const P D]
      simp [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
    rw [e]
    refine psdCfc hD _ fun j => ?_
    have hp : max (l j) 0 ≤ P :=
      Finset.single_le_sum (f := fun i => max (l i) 0) (fun i _ => le_max_right _ _) (Finset.mem_univ j)
    have hm : max (-l j) 0 ≤ M :=
      Finset.single_le_sum (f := fun i => max (-l i) 0) (fun i _ => le_max_right _ _) (Finset.mem_univ j)
    show 0 ≤ P - (max (l j) 0 + max (-l j) 0)
    rcases le_total (l j) 0 with h | h
    · rw [max_eq_right h] at hp ⊢; linarith
    · rw [max_eq_right (neg_nonpos.mpr h)] at hm ⊢; linarith

end P17Aux

theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : QAlgorithms.IsDensityMatrix sigma) :
    ∃ Xp Xm : Matrix I I ℂ, Xp.PosSemidef ∧ Xm.PosSemidef ∧ rho - sigma = Xp - Xm ∧
      Xp.trace = ((QAlgorithms.traceDistance rho sigma : ℝ) : ℂ) ∧
      Xm.trace = ((QAlgorithms.traceDistance rho sigma : ℝ) : ℂ) ∧
      (((QAlgorithms.traceDistance rho sigma : ℝ) : ℂ) • (1 : Matrix I I ℂ) - (Xp + Xm)).PosSemidef :=
  P17Aux.jd_main rho sigma hrho hsigma

end
