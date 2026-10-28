-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.normComparisonE
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:11:57.541+00:00
-- url     : https://prove2.me/submissions/54eebba0-f526-43a1-a8ae-eb039be20431

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator
open Matrix
open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace X4P40N

variable {d : ℕ}

/-- A unit vector is the `i0`-th column of a unitary matrix. -/
lemma ext_unit (i0 : Fin d) (u : EuclideanSpace ℂ (Fin d)) (hu : ‖u‖ = 1) :
    ∃ U ∈ unitaryGroup (Fin d) ℂ, ∀ a, U a i0 = u a := by
  have hv : Orthonormal ℂ (({i0} : Set (Fin d)).restrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have : i = j := Subsingleton.elim _ _
    simp only [this, if_true]
    rw [inner_self_eq_norm_sq_to_K]
    show ((‖u‖ : ℝ) : ℂ) ^ 2 = 1
    rw [hu]; simp
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨Matrix.of fun a j => b j a, ?_, fun a => by simp [hb i0 rfl]⟩
  rw [mem_unitaryGroup_iff']
  ext i j
  have h := orthonormal_iff_ite.mp b.orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [mul_apply, star_apply, of_apply, one_apply]
  rw [← h, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_comm]

variable (N : Mat d → ℝ)

lemma N_zero (hN : QAlgorithms.Papers.Independent.Information100.P50.IsUINorm N) :
    N 0 = 0 := by
  have := hN.2.2.2.1 0 0
  simpa using this

lemma N_ui (hN : QAlgorithms.Papers.Independent.Information100.P50.IsUINorm N)
    (U V : Mat d) (hU : U ∈ unitaryGroup (Fin d) ℂ) (hV : V ∈ unitaryGroup (Fin d) ℂ)
    (A : Mat d) : N (U * A * V) = N A :=
  hN.2.2.2.2 ⟨U, hU⟩ ⟨V, hV⟩ A

lemma E_def (hd : 0 < d) :
    QAlgorithms.Papers.Independent.Gap48.P40.matrixE d =
      Matrix.of fun a b => if a = ⟨0, hd⟩ ∧ b = ⟨0, hd⟩ then (1 : ℂ) else 0 := by
  ext a b
  simp only [QAlgorithms.Papers.Independent.Gap48.P40.matrixE, diagonal_apply, of_apply]
  by_cases h : a = b
  · subst h; simp [Fin.ext_iff]
  · simp only [h, if_false]
    rw [if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl

/-- Rank-one matrices: `N (c w^*) = ‖c‖ ‖w‖ N(E)`. -/
lemma rank_one (hN : QAlgorithms.Papers.Independent.Information100.P50.IsUINorm N) (hd : 0 < d)
    (c w : EuclideanSpace ℂ (Fin d)) :
    N (Matrix.of fun a b => c a * conj (w b)) =
      ‖c‖ * ‖w‖ * N (QAlgorithms.Papers.Independent.Gap48.P40.matrixE d) := by
  by_cases hc : c = 0
  · subst hc; simp [N_zero N hN]
    have : (Matrix.of fun (a b : Fin d) => (0 : ℂ)) = 0 := rfl
    rw [this, N_zero N hN]
  by_cases hw : w = 0
  · subst hw; simp
    have : (Matrix.of fun (a b : Fin d) => (0 : ℂ)) = 0 := rfl
    rw [this, N_zero N hN]
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set i0 : Fin d := ⟨0, hd⟩
  obtain ⟨U, hU, hUc⟩ := ext_unit i0 ((‖c‖⁻¹ : ℂ) • c) (by
    rw [norm_smul]; simp [hc'.ne'])
  obtain ⟨V, hV, hVc⟩ := ext_unit i0 ((‖w‖⁻¹ : ℂ) • w) (by
    rw [norm_smul]; simp [hw'.ne'])
  have key : (Matrix.of fun a b => c a * conj (w b)) =
      ((‖c‖ * ‖w‖ : ℝ) : ℂ) • (U * QAlgorithms.Papers.Independent.Gap48.P40.matrixE d * Vᴴ) := by
    ext a b
    have hE : (U * QAlgorithms.Papers.Independent.Gap48.P40.matrixE d * Vᴴ) a b =
        U a i0 * conj (V b i0) := by
      simp only [QAlgorithms.Papers.Independent.Gap48.P40.matrixE]
      rw [mul_apply]
      simp only [mul_diagonal, conjTranspose_apply]
      rw [Finset.sum_eq_single i0]
      · simp [i0]
      · intro k _ hk
        have : k.val ≠ 0 := fun h => hk (Fin.ext h)
        simp [this]
      · simp
    rw [Matrix.smul_apply, hE, hUc, hVc]
    simp only [PiLp.smul_apply, smul_eq_mul, map_mul, map_inv₀, Complex.conj_ofReal]
    have : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
    have : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hw'.ne'
    push_cast
    field_simp
    rfl
  rw [key, hN.2.2.2.1, N_ui N hN U Vᴴ hU (by
    simpa [star_eq_conjTranspose] using Unitary.star_mem (show V ∈ unitary (Matrix (Fin d) (Fin d) ℂ) from hV))]
  simp [abs_of_pos hc', abs_of_pos hw']

lemma N_sum (hN : QAlgorithms.Papers.Independent.Information100.P50.IsUINorm N)
    {ι : Type*} (s : Finset ι) (f : ι → Mat d) : N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [N_zero N hN]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hN.2.2.1 _ _).trans (by linarith)

lemma upper (hN : QAlgorithms.Papers.Independent.Information100.P50.IsUINorm N) (hd : 0 < d)
    (A : Mat d) : N A ≤ QAlgorithms.traceNorm A *
      N (QAlgorithms.Papers.Independent.Gap48.P40.matrixE d) := by
  have hH : (Aᴴ * A).IsHermitian := isHermitian_conjTranspose_mul_self A
  set Q : Mat d := (hH.eigenvectorUnitary : Mat d) with hQdef
  have hQ : Q ∈ unitaryGroup (Fin d) ℂ := hH.eigenvectorUnitary.2
  set lam := hH.eigenvalues
  have hdiag : star Q * (Aᴴ * A) * Q = diagonal (RCLike.ofReal ∘ lam) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this
  -- trace norm = Σ √λ
  have htn : QAlgorithms.traceNorm A = ∑ j, Real.sqrt (lam j) := by
    unfold QAlgorithms.traceNorm
    rw [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_comm,
      ← mul_assoc]
    have : (star (hH.eigenvectorUnitary : Mat d)) * (hH.eigenvectorUnitary : Mat d) = 1 :=
      Unitary.coe_star_mul_self _
    rw [this, one_mul, trace_diagonal, Complex.re_sum]
    simp [lam]
  -- columns of A * Q
  set A' := A * Q
  let col : Fin d → EuclideanSpace ℂ (Fin d) := fun j => WithLp.toLp 2 (fun a => A' a j)
  have hcol : ∀ j, ‖col j‖ = Real.sqrt (lam j) := by
    intro j
    rw [EuclideanSpace.norm_eq]
    congr 1
    have h := congrFun (congrFun hdiag j) j
    have h2 : star Q * (Aᴴ * A) * Q = A'ᴴ * A' := by
      simp only [A', conjTranspose_mul, star_eq_conjTranspose]; simp only [Matrix.mul_assoc]
    rw [h2, mul_apply, diagonal_apply_eq] at h
    have h3 := congrArg Complex.re h
    simp only [Function.comp_apply, RCLike.ofReal_re, Complex.re_sum, conjTranspose_apply] at h3
    rw [← (h3.trans (by simp) : _ = lam j)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [col]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re]
  have hsplit : A' = ∑ j, Matrix.of fun a b => col j a * conj ((EuclideanSpace.single j (1 : ℂ)) b) := by
    ext a b
    rw [Matrix.sum_apply]
    simp only [of_apply, col, PiLp.single_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have hNA : N A = N A' := by
    have := N_ui N hN 1 Q (one_mem _) hQ A
    rw [one_mul] at this; exact this.symm
  rw [hNA, hsplit, htn, Finset.sum_mul]
  refine (N_sum N hN _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [rank_one N hN hd, hcol]
  simp

lemma corner (hd : 0 < d) (M : Mat d) :
    QAlgorithms.Papers.Independent.Gap48.P40.matrixE d * M *
      QAlgorithms.Papers.Independent.Gap48.P40.matrixE d =
    M ⟨0, hd⟩ ⟨0, hd⟩ • QAlgorithms.Papers.Independent.Gap48.P40.matrixE d := by
  ext a b
  simp only [QAlgorithms.Papers.Independent.Gap48.P40.matrixE, diagonal_mul, mul_diagonal,
    Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
  · have h1 : a = ⟨0, hd⟩ := Fin.ext ha
    have h2 : b = ⟨0, hd⟩ := Fin.ext hb
    subst h1 h2; simp
  · have : a ≠ b := fun h => hb (h ▸ ha)
    simp [ha, hb, this]
  · simp [ha]
  · simp [ha]

lemma pinch (hN : QAlgorithms.Papers.Independent.Information100.P50.IsUINorm N) (M : Mat d) :
    N (QAlgorithms.Papers.Independent.Gap48.P40.matrixE d * M *
      QAlgorithms.Papers.Independent.Gap48.P40.matrixE d) ≤ N M := by
  set D : Mat d := diagonal fun i => if i.val = 0 then 1 else -1
  have hD : D ∈ unitaryGroup (Fin d) ℂ := by
    rw [mem_unitaryGroup_iff']
    simp only [D, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
    rw [← diagonal_one]; congr 1; funext i
    by_cases h : i.val = 0 <;> simp [h]
  have hE : QAlgorithms.Papers.Independent.Gap48.P40.matrixE d = (1 / 2 : ℂ) • (1 + D) := by
    ext a b
    simp only [QAlgorithms.Papers.Independent.Gap48.P40.matrixE, D, Matrix.smul_apply,
      Matrix.add_apply, one_apply, diagonal_apply, smul_eq_mul]
    split_ifs <;> norm_num
  have hEME : QAlgorithms.Papers.Independent.Gap48.P40.matrixE d * M *
      QAlgorithms.Papers.Independent.Gap48.P40.matrixE d =
      (1 / 4 : ℂ) • (M + (D * M * 1) + (1 * M * D) + D * M * D) := by
    rw [hE]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, smul_smul]
    module
  have h1 := N_ui N hN D 1 hD (one_mem _) M
  have h2 := N_ui N hN 1 D (one_mem _) hD M
  have h3 := N_ui N hN D D hD hD M
  rw [hEME, hN.2.2.2.1]
  have t1 := hN.2.2.1 (M + D * M * 1 + 1 * M * D) (D * M * D)
  have t2 := hN.2.2.1 (M + D * M * 1) (1 * M * D)
  have t3 := hN.2.2.1 M (D * M * 1)
  have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [this]
  linarith

lemma lower (hN : QAlgorithms.Papers.Independent.Information100.P50.IsUINorm N) (hd : 0 < d)
    (A : Mat d) : QAlgorithms.specNorm A *
      N (QAlgorithms.Papers.Independent.Gap48.P40.matrixE d) ≤ N A := by
  set i0 : Fin d := ⟨0, hd⟩
  set L := (toEuclideanLin (𝕜 := ℂ) (m := Fin d) (n := Fin d)).trans
    LinearMap.toContinuousLinearMap A
  have hspec : QAlgorithms.specNorm A = ‖L‖ := rfl
  have hS : IsCompact (Metric.sphere (0 : EuclideanSpace ℂ (Fin d)) 1) := isCompact_sphere _ _
  have hne : (Metric.sphere (0 : EuclideanSpace ℂ (Fin d)) 1).Nonempty :=
    ⟨EuclideanSpace.single i0 1, by simp⟩
  obtain ⟨v, hv, hmax⟩ := hS.exists_isMaxOn hne
    (continuous_norm.comp L.continuous).continuousOn
  have hv1 : ‖v‖ = 1 := by simpa using hv
  have hLv : ‖L‖ = ‖L v‖ := by
    apply le_antisymm
    · refine L.opNorm_le_bound (norm_nonneg _) fun x => ?_
      by_cases hx : x = 0
      · simp [hx]
      have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hm := hmax (show (‖x‖⁻¹ : ℂ) • x ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin d)) 1 by
        simp [norm_smul, hx'.ne'])
      simp only [Set.mem_setOf_eq, Function.comp_apply, map_smul, norm_smul] at hm
      simp at hm
      rw [inv_mul_le_iff₀ hx'] at hm
      linarith
    · simpa [hv1] using L.le_opNorm v
  have hEn : 0 ≤ N (QAlgorithms.Papers.Independent.Gap48.P40.matrixE d) := hN.1 _
  rw [hspec, hLv]
  set w := L v
  by_cases hw : w = 0
  · rw [hw, norm_zero, zero_mul]; exact hN.1 _
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨U, hU, hUc⟩ := ext_unit i0 ((‖w‖⁻¹ : ℂ) • w) (by rw [norm_smul]; simp [hw'.ne'])
  obtain ⟨V, hV, hVc⟩ := ext_unit i0 v hv1
  set M := star U * A * V
  have hU' : star U ∈ unitaryGroup (Fin d) ℂ :=
    Unitary.star_mem (show U ∈ unitary (Matrix (Fin d) (Fin d) ℂ) from hU)
  have hNM : N M = N A := N_ui N hN _ _ hU' hV A
  have hwa : ∀ a, w a = ∑ k, A a k * v k := by
    intro a; simp [w, L, toEuclideanLin, mulVec, dotProduct]
  have hMii : M i0 i0 = (‖w‖ : ℂ) := by
    simp only [M, mul_apply, star_apply, hUc, hVc]
    simp only [PiLp.smul_apply, smul_eq_mul, star_mul', map_inv₀, RCLike.star_def,
      Complex.conj_ofReal, Finset.sum_mul, mul_assoc, ← Finset.mul_sum]
    have : ∑ x, (starRingEnd ℂ) (w x) * ∑ x_1, A x x_1 * v x_1 = (‖w‖ : ℂ) ^ 2 := by
      simp_rw [← hwa]
      rw [EuclideanSpace.norm_eq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [this]
    have : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hw'.ne'
    field_simp
  have key : ((‖w‖ : ℝ) : ℂ) • QAlgorithms.Papers.Independent.Gap48.P40.matrixE d =
      QAlgorithms.Papers.Independent.Gap48.P40.matrixE d * M *
        QAlgorithms.Papers.Independent.Gap48.P40.matrixE d := by
    rw [corner hd, ← hMii]
  have := pinch N hN M
  rw [← key, hN.2.2.2.1, hNM] at this
  simpa using this

end X4P40N

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)
open QAlgorithms.Papers.Independent.Gap48.P40

theorem solution {d : ℕ} (hd : 0 < d) (N : Mat d → ℝ)
    (hN : IsUINorm N) (A : Mat d) :
    specNorm A ≤ N A / N (matrixE d) ∧ N A / N (matrixE d) ≤ traceNorm A := by
  have hE : matrixE d ≠ 0 := by
    intro h
    have := congrFun (congrFun h ⟨0, hd⟩) ⟨0, hd⟩
    simp [matrixE] at this
  have hpos : 0 < N (matrixE d) := lt_of_le_of_ne (hN.1 _) (fun h => hE ((hN.2.1 _).mp h.symm))
  constructor
  · rw [le_div_iff₀ hpos]; exact X4P40N.lower N hN hd A
  · rw [div_le_iff₀ hpos]; exact X4P40N.upper N hN hd A

