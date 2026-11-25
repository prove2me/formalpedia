-- Prove2me | solution 1 for PI.SlopeSteps.gram_matrix_duality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:35.187658+00:00
-- url     : https://prove2.me/submissions/85fe0ae5-f78e-4838-ad17-03d8f2ba308e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Theorems.Thm_PI_SlopeSteps_fqB_apply
import Theorems.Thm_PI_SlopeSteps_fqB_symm
import Theorems.Thm_PI_SlopeSteps_fqB_self_eq_zero
import Theorems.Thm_PI_SlopeSteps_linIndep_Q
import Theorems.Thm_PI_SlopeSteps_expand
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual
import Theorems.Thm_Formalism_L2_DIV_we_nabla_le
import Theorems.Thm_Formalism_L2_DIV_weyl_eq_dual_nabla_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV
namespace PI.SlopeSteps
theorem _root_.solution : GramDual := by
  intro N ν r r' e e' hν
  classical
  set h := fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) with hh
  have hpos : 0 < h := (fockQPos _ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)).2 (hwNe ℚ N N le_rfl ν)
  have hne : h ≠ 0 := hpos.ne'
  set B := fqB (σ := Fin N × Fin N) h with hB
  set w : Fin r → MvPolynomial (Fin N × Fin N) ℚ := fun i => intQ N N (e i : MvPolynomial (Fin N × Fin N) ℤ)
    with hw_def
  set u : Fin r' → MvPolynomial (Fin N × Fin N) ℚ := fun k => intQ N N (e' k : MvPolynomial (Fin N × Fin N) ℤ)
    with hu_def
  have hWE := weyl_eq_dual_nabla_holds N N le_rfl ν hν
  have hu_mem : ∀ k, u k ∈ (dualWeyl ℤ N N ν).map (intQ N N) := fun k => ⟨e' k, (e' k).2, rfl⟩
  have hw_mem : ∀ i, w i ∈ (weyl ℤ N N le_rfl ν).map (intQ N N) := fun i => ⟨e i, (e i).2, rfl⟩

  have hMex0 : ∀ i k, ∃ z : ℤ, B (w i) (u k) = z := by
    intro i k
    have hm := hw_mem i
    rw [hWE] at hm
    obtain ⟨z, hz⟩ := hm.2 (u k) (hu_mem k)
    exact ⟨z, by rw [hB, fqB_apply, hz, mul_div_assoc, div_self hne, mul_one]⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin r) (Fin r') ℤ, ∀ i k, B (w i) (u k) = M i k :=
    ⟨Matrix.of fun i k => Classical.choose (hMex0 i k), fun i k => Classical.choose_spec (hMex0 i k)⟩
  have hu_ind : LinearIndependent ℚ u := linIndep_Q e'
  have hw_ind : LinearIndependent ℚ w := linIndep_Q e

  set G' : Matrix (Fin r') (Fin r') ℚ := Matrix.of fun k l => B (u k) (u l) with hG'_def
  have hG'det : G'.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    obtain ⟨y, hy⟩ : ∃ y, y = ∑ l, v l • u l := ⟨_, rfl⟩
    have hx : ∀ k, B (u k) y = 0 := by
      intro k
      have hk := congrFun hv k
      simp only [Matrix.mulVec, dotProduct, hG'_def, Matrix.of_apply, Pi.zero_apply] at hk
      rw [hy, map_sum]
      rw [← hk]
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul, mul_comm]
    have e2 : ∀ l, B y (u l) = 0 := fun l => by rw [hB, fqB_symm, ← hB]; exact hx l
    have hxx : B y y = 0 := by
      calc B y y = B y (∑ l, v l • u l) := by rw [← hy]
        _ = ∑ l, v l * B y (u l) := by
            rw [map_sum]; exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
        _ = 0 := by simp [e2]
    have hy0 : ∑ l, v l • u l = 0 := by rw [← hy]; exact fqB_self_eq_zero hne _ hxx
    exact hv0 (funext (Fintype.linearIndependent_iff.mp hu_ind v hy0))
  set Gi := G'⁻¹ with hGi_def
  have hGiG : Gi * G' = 1 := Matrix.nonsing_inv_mul G' (isUnit_iff_ne_zero.mpr hG'det)

  set f : Fin r' → MvPolynomial (Fin N × Fin N) ℚ := fun j => ∑ k, Gi j k • u k with hf_def
  have hfu : ∀ j l, B (f j) (u l) = if j = l then 1 else 0 := by
    intro j l
    have hjl := congrFun (congrFun hGiG j) l
    rw [Matrix.mul_apply, Matrix.one_apply] at hjl
    rw [← hjl, hf_def, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hG'_def, Matrix.of_apply]
  have hf_mem : ∀ j, f j ∈ (weyl ℤ N N le_rfl ν).map (intQ N N) := by
    intro j
    rw [hWE]
    refine ⟨Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (we_nabla_le ν (u k) (hu_mem k)), ?_⟩
    rintro Q ⟨p, hp, rfl⟩
    refine ⟨e'.repr ⟨p, hp⟩ j, ?_⟩
    have hB1 : B (f j) (∑ l, ((e'.repr ⟨p, hp⟩ l : ℤ) : ℚ) • u l) = (e'.repr ⟨p, hp⟩ j : ℚ) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, hfu, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [hB, fqB_apply, div_eq_iff hne] at hB1
    rw [expand e' p hp]
    exact hB1
  have hNex0 : ∀ j, ∃ c : Fin r → ℤ, f j = ∑ i, (c i : ℚ) • w i := by
    intro j
    obtain ⟨p, hp, hpf⟩ := hf_mem j
    exact ⟨fun i => e.repr ⟨p, hp⟩ i, by rw [← hpf]; exact expand e p hp⟩
  obtain ⟨Nm, hNm⟩ : ∃ Nm : Matrix (Fin r') (Fin r) ℤ, ∀ j, f j = ∑ i, (Nm j i : ℚ) • w i :=
    ⟨Matrix.of fun j => Classical.choose (hNex0 j), fun j => Classical.choose_spec (hNex0 j)⟩

  have hNM : Nm * M = 1 := by
    ext j l
    have h1 := hfu j l
    rw [hNm j, map_sum, LinearMap.sum_apply] at h1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hM] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact_mod_cast h1

  have hspan_zero : ∀ y ∈ Submodule.span ℚ (Set.range u), (∀ l, B y (u l) = 0) → y = 0 := by
    intro y hy hyl
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hy
    apply fqB_self_eq_zero hne
    calc B y y = B y (∑ l, d l • u l) := by rw [hd]
      _ = ∑ l, d l * B y (u l) := by
          rw [map_sum]; exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
      _ = 0 := by simp [hyl]
  have hw_span : ∀ i, w i ∈ Submodule.span ℚ (Set.range u) := by
    intro i
    have hei : (e i : MvPolynomial (Fin N × Fin N) ℤ) ∈ dualWeyl ℤ N N ν :=
      weylLeDual ℤ N N le_rfl ν hν (e i).2
    rw [show w i = _ from expand e' _ hei]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hf_span : ∀ j, f j ∈ Submodule.span ℚ (Set.range u) := fun j =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hwf : ∀ i, w i = ∑ j, (M i j : ℚ) • f j := by
    intro i
    rw [← sub_eq_zero]
    apply hspan_zero
    · exact Submodule.sub_mem _ (hw_span i)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hf_span j))
    · intro l
      rw [map_sub, LinearMap.sub_apply, hM, map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hfu, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  have hMN : M * Nm = 1 := by
    ext i k
    have h2 : ∑ k, (((M * Nm : Matrix (Fin r) (Fin r) ℤ) i k : ℤ) : ℚ) • w k = w i := by
      conv_rhs => rw [hwf i]
      simp only [hNm, Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Finset.smul_sum, smul_smul,
        Finset.sum_smul]
      rw [Finset.sum_comm]
    have hsum : ∑ k, ((((M * Nm : Matrix (Fin r) (Fin r) ℤ) i k : ℤ) : ℚ) -
        (((1 : Matrix (Fin r) (Fin r) ℤ) i k : ℤ) : ℚ)) • w k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h2, Matrix.one_apply, Int.cast_ite, Int.cast_one,
        Int.cast_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    have hk := Fintype.linearIndependent_iff.mp hw_ind _ hsum k
    exact_mod_cast sub_eq_zero.mp hk

  have hrr : r = r' := by
    apply le_antisymm
    · have hle := Matrix.rank_mul_le_left M Nm
      rw [hMN, Matrix.rank_one, Fintype.card_fin] at hle
      exact hle.trans (Matrix.rank_le_width _)
    · have hle := Matrix.rank_mul_le_left Nm M
      rw [hNM, Matrix.rank_one, Fintype.card_fin] at hle
      exact hle.trans (Matrix.rank_le_width _)
  subst hrr
  refine ⟨rfl, ?_⟩

  have hBwf : ∀ i j, B (w i) (f j) = ∑ k, Gi j k * (M i k : ℚ) := by
    intro i j
    rw [hf_def, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_eq_mul, hM]
  set Mq : Matrix (Fin r) (Fin r) ℚ := M.map (Int.castRingHom ℚ) with hMq
  have hGw : gramOf ν (fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)) = Mq * Matrix.transpose Gi * Matrix.transpose Mq := by
    ext i i'
    have e1 : gramOf ν (fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)) i i' = B (w i) (w i') := rfl
    rw [e1]
    conv_lhs => rw [hwf i']
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, hBwf, Matrix.mul_apply, Matrix.transpose_apply, hMq, Matrix.map_apply,
      eq_intCast, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hGu : gramOf ν (fun i => (e' i : MvPolynomial (Fin N × Fin N) ℤ)) = G' := by
    ext k l
    rfl
  have hdetM : M.det ^ 2 = 1 := by
    have h1 : M.det * Nm.det = 1 := by
      rw [← Matrix.det_mul, hMN, Matrix.det_one]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h2 | h2 <;> simp [h2]
  have hdetMq : Mq.det ^ 2 = 1 := by
    have h3 : (M.map (Int.castRingHom ℚ)).det = ((M.det : ℤ) : ℚ) :=
      (RingHom.map_det (Int.castRingHom ℚ) M).symm
    rw [hMq, h3]
    exact_mod_cast hdetM
  rw [hGw, hGu, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose]
  have hinv : Gi.det * G'.det = 1 := Matrix.det_nonsing_inv_mul_det G' (isUnit_iff_ne_zero.mpr hG'det)
  calc Mq.det * Gi.det * Mq.det * G'.det = Mq.det ^ 2 * (Gi.det * G'.det) := by ring
    _ = 1 := by rw [hdetMq, hinv, one_mul]
end PI.SlopeSteps
