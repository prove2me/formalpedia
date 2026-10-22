-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P10.geometricMinimum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T00:12:12.123888+00:00
-- url     : https://prove2.me/submissions/c64cb394-68d3-4eba-89a1-9aaabb4bd4d8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

set_option autoImplicit false

namespace QAlgorithms.Papers.Independent.Information100.P10.GMx

open scoped ComplexConjugate Matrix

lemma kronAll_mul {n : ℕ} (A B : Fin n → Matrix Bool Bool ℂ) :
    kronAll A * kronAll B = kronAll (fun j => A j * B j) := by
  ext y z
  simp only [kronAll, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

lemma kronAll_conjTranspose {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ) :
    (kronAll A)ᴴ = kronAll (fun j => (A j)ᴴ) := by
  ext y z
  simp [kronAll, Matrix.conjTranspose_apply]

lemma kronAll_one {n : ℕ} : kronAll (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext y z
  simp only [kronAll, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

/-- the single-qubit directional Pauli matrix -/
noncomputable def S (v : Direction) : Matrix Bool Bool ℂ := ∑ a, (v a : ℂ) • pauli a

lemma S_herm (v : Direction) : (S v)ᴴ = S v := by
  ext i j
  cases i <;> cases j <;>
    simp [S, pauli, pauliX, pauliY, pauliZ, Fin.sum_univ_three, Matrix.conjTranspose_apply] <;>
    ring

lemma S_sq (v : Direction) (hv : ‖v‖ = 1) : S v * S v = 1 := by
  have h2 : ‖v‖ ^ 2 = 1 := by rw [hv]; norm_num
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three] at h2
  simp only [Real.norm_eq_abs, sq_abs] at h2
  have hC : ((v 0 : ℂ)) ^ 2 + (v 1 : ℂ) ^ 2 + (v 2 : ℂ) ^ 2 = 1 := by exact_mod_cast h2
  ext i j
  cases i <;> cases j <;>
    simp [S, pauli, pauliX, pauliY, pauliZ, Fin.sum_univ_three, Matrix.mul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> linear_combination hC

lemma directionalPauli_eq {M : ℕ} (q : Fin M) (v : Direction) :
    directionalPauli q v = kronAll (fun j => if j = q then S v else 1) := by
  have key : ∀ (F : Matrix Bool Bool ℂ) (y z : Qubits M),
      (∏ j, (if j = q then F else 1) (y j) (z j)) =
        F (y q) (z q) * ∏ j ∈ ({q}ᶜ : Finset (Fin M)), (1 : Matrix Bool Bool ℂ) (y j) (z j) := by
    intro F y z
    rw [Fintype.prod_eq_mul_prod_compl q]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro j hj
      simp only [Finset.mem_compl, Finset.mem_singleton] at hj
      simp [hj]
  ext y z
  simp only [directionalPauli, localPauli, kronAll, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, key]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1

lemma dP_herm {M : ℕ} (q : Fin M) (v : Direction) : (directionalPauli q v)ᴴ = directionalPauli q v := by
  rw [directionalPauli_eq, kronAll_conjTranspose]
  congr 1
  funext j
  split_ifs
  · exact S_herm v
  · simp

lemma dP_sq {M : ℕ} (q : Fin M) (v : Direction) (hv : ‖v‖ = 1) :
    directionalPauli q v * directionalPauli q v = 1 := by
  rw [directionalPauli_eq, kronAll_mul]
  rw [← kronAll_one]
  congr 1
  funext j
  split_ifs
  · exact S_sq v hv
  · simp

lemma act_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    act A x = Matrix.toEuclideanLin A x := by
  simp [act, Matrix.toEuclideanLin_apply]

lemma inner_act_left {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x y : EuclideanSpace ℂ ι) : inner ℂ (act A x) y = inner ℂ x (act Aᴴ y) := by
  rw [act_eq, act_eq, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

lemma act_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) : act A (act B x) = act (A * B) x := by
  simp [act, Matrix.mulVec_mulVec]

lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (x : EuclideanSpace ℂ ι) :
    act 1 x = x := by
  simp [act]

/-- key facts for a unit direction -/
lemma norm_sq_act {M : ℕ} (psi : Ket M) (hpsi : IsState psi) (q : Fin M) (v : Direction)
    (hv : ‖v‖ = 1) :
    inner ℂ (act (directionalPauli q v) psi) (act (directionalPauli q v) psi) = 1 := by
  rw [inner_act_left, dP_herm, act_mul, dP_sq q v hv, act_one, inner_self_eq_norm_sq_to_K]
  unfold IsState at hpsi
  rw [hpsi]; simp

lemma expect_eq {M : ℕ} (psi : Ket M) (q : Fin M) (v : Direction) :
    inner ℂ psi (act (directionalPauli q v) psi) = ((inner ℝ v (bloch psi q) : ℝ) : ℂ) := by
  set z := inner ℂ psi (act (directionalPauli q v) psi) with hz
  have hreal : conj z = z := by
    rw [hz, inner_conj_symm, inner_act_left, dP_herm]
  have him : z.im = 0 := by
    have := congrArg Complex.im hreal
    simp at this
    linarith
  have hre : z.re = inner ℝ v (bloch psi q) := by
    rw [hz]
    simp only [directionalPauli, act_eq, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right]
    simp only [← act_eq]
    simp [bloch, PiLp.inner_apply, Fin.sum_univ_three, Complex.re_sum]
    ring
  apply Complex.ext
  · simp [hre]
  · simp [him]

lemma tangent_term {M : ℕ} (psi : Ket M) (hpsi : IsState psi) (q : Fin M) (v : Direction)
    (hv : ‖v‖ = 1) :
    (fsForm psi (orbitTangent psi q v) (orbitTangent psi q v)).re =
      1 - (inner ℝ v (bloch psi q)) ^ 2 := by
  have h1 := norm_sq_act psi hpsi q v hv
  have h2 := expect_eq psi q v
  have h3 : inner ℂ (act (directionalPauli q v) psi) psi = ((inner ℝ v (bloch psi q) : ℝ) : ℂ) := by
    rw [← inner_conj_symm, h2]; simp
  simp only [fsForm, orbitTangent, inner_smul_left, inner_smul_right, h1, h2, h3]
  simp [Complex.conj_I, sq]
  ring_nf

lemma dist_term {M : ℕ} (psi : Ket M) (q : Fin M) (v : Direction) :
    fsSquared psi (act (directionalPauli q v) psi) = 1 - (inner ℝ v (bloch psi q)) ^ 2 := by
  rw [fsSquared, expect_eq]
  simp [sq_abs]

lemma trace_formula {M : ℕ} (psi : Ket M) (hpsi : IsState psi) (v : Fin M → Direction)
    (hv : v ∈ directionDomain M) :
    traceObjective psi v = ∑ q, (1 - (inner ℝ (v q) (bloch psi q)) ^ 2) := by
  simp only [traceObjective, Matrix.trace, Matrix.diag, orbitMetric, Complex.re_sum]
  exact Finset.sum_congr rfl (fun q _ => tangent_term psi hpsi q (v q) (hv q))

lemma dist_formula {M : ℕ} (psi : Ket M) (v : Fin M → Direction) :
    distanceObjective psi v = ∑ q, (1 - (inner ℝ (v q) (bloch psi q)) ^ 2) := by
  simp only [distanceObjective]
  exact Finset.sum_congr rfl (fun q _ => dist_term psi q (v q))

lemma inner_sq_le (v b : Direction) (hv : ‖v‖ = 1) : (inner ℝ v b) ^ 2 ≤ ‖b‖ ^ 2 := by
  have h := abs_real_inner_le_norm v b
  rw [hv, one_mul] at h
  have := sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
  exact this

lemma inner_sq_eq_iff (v b : Direction) (hv : ‖v‖ = 1) :
    (inner ℝ v b) ^ 2 = ‖b‖ ^ 2 ↔
      b = 0 ∨ v = (‖b‖⁻¹ : ℝ) • b ∨ v = -((‖b‖⁻¹ : ℝ) • b) := by
  by_cases hb : b = 0
  · subst hb; simp
  have hbn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  constructor
  · intro h
    right
    have hcases : inner ℝ v b = ‖b‖ ∨ inner ℝ v b = -‖b‖ := by
      have : (inner ℝ v b - ‖b‖) * (inner ℝ v b + ‖b‖) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp this with h' | h'
      · left; linarith
      · right; linarith
    rcases hcases with h' | h'
    · left
      have : inner ℝ v b = ‖v‖ * ‖b‖ := by rw [hv, one_mul]; exact h'
      rw [inner_eq_norm_mul_iff_real, hv, one_smul] at this
      calc v = (‖b‖⁻¹ * ‖b‖) • v := by rw [inv_mul_cancel₀ hbn, one_smul]
        _ = ‖b‖⁻¹ • (‖b‖ • v) := by rw [smul_smul]
        _ = ‖b‖⁻¹ • b := by rw [this]
    · right
      have : inner ℝ (-v) b = ‖-v‖ * ‖b‖ := by rw [inner_neg_left, norm_neg, hv, one_mul, h']; ring
      rw [inner_eq_norm_mul_iff_real, norm_neg, hv, one_smul] at this
      calc v = -((‖b‖⁻¹ * ‖b‖) • -v) := by rw [inv_mul_cancel₀ hbn, one_smul, neg_neg]
        _ = -(‖b‖⁻¹ • (‖b‖ • -v)) := by rw [smul_smul]
        _ = -(‖b‖⁻¹ • b) := by rw [this]
  · rintro (h | h | h)
    · exact absurd h hb
    · rw [h, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    · rw [h, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp

/-- the optimal direction -/
noncomputable def vstar {M : ℕ} (psi : Ket M) (q : Fin M) : Direction :=
  if bloch psi q = 0 then EuclideanSpace.single 0 1 else (‖bloch psi q‖⁻¹ : ℝ) • bloch psi q

lemma vstar_mem {M : ℕ} (psi : Ket M) : vstar psi ∈ directionDomain M := by
  intro q
  unfold vstar
  split_ifs with h
  · simp
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)

lemma vstar_inner {M : ℕ} (psi : Ket M) (q : Fin M) :
    (inner ℝ (vstar psi q) (bloch psi q)) ^ 2 = ‖bloch psi q‖ ^ 2 := by
  unfold vstar
  split_ifs with h
  · simp [h]
  · have hm : ‖(‖bloch psi q‖⁻¹ : ℝ) • bloch psi q‖ = 1 := by
      have := vstar_mem psi q
      unfold vstar at this
      rwa [if_neg h] at this
    exact (inner_sq_eq_iff _ _ hm).mpr (Or.inr (Or.inl rfl))

end QAlgorithms.Papers.Independent.Information100.P10.GMx

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P10 in
theorem solution {M : ℕ} (psi : Ket M) (hpsi : IsState psi) :
    (directionDomain M).Nonempty ∧ IsCompact (directionDomain M) ∧
    ContinuousOn (traceObjective psi) (directionDomain M) ∧
    BddBelow (traceObjective psi '' directionDomain M) ∧
    entanglementDistance psi = (M : ℝ) - ∑ q, ‖bloch psi q‖ ^ 2 ∧
    entanglementDistance psi = ∑ q, localED psi q ∧
    entanglementDistance psi = sInf (distanceObjective psi '' directionDomain M) ∧
    (∀ v ∈ directionDomain M, traceObjective psi v = distanceObjective psi v) ∧
    (∃ v ∈ directionDomain M, traceObjective psi v = entanglementDistance psi ∧
      distanceObjective psi v = entanglementDistance psi ∧
      ∀ q, bloch psi q ≠ 0 → v q = (‖bloch psi q‖⁻¹ : ℝ) • bloch psi q) ∧
    (∀ v ∈ directionDomain M,
      traceObjective psi v = entanglementDistance psi ↔
      ∀ q, bloch psi q = 0 ∨
        v q = (‖bloch psi q‖⁻¹ : ℝ) • bloch psi q ∨
        v q = -( (‖bloch psi q‖⁻¹ : ℝ) • bloch psi q)) := by
  set b := bloch psi with hbdef
  set f : (Fin M → Direction) → ℝ := fun v => ∑ q, (1 - (inner ℝ (v q) (b q)) ^ 2) with hf
  set L : ℝ := ∑ q, (1 - ‖b q‖ ^ 2) with hL
  have htr : ∀ v ∈ directionDomain M, traceObjective psi v = f v :=
    fun v hv => GMx.trace_formula psi hpsi v hv
  have hdist : ∀ v, distanceObjective psi v = f v := fun v => GMx.dist_formula psi v
  have hlow : ∀ v ∈ directionDomain M, L ≤ f v := by
    intro v hv
    apply Finset.sum_le_sum
    intro q _
    have := GMx.inner_sq_le (v q) (b q) (hv q)
    linarith
  have hfstar : f (GMx.vstar psi) = L := by
    apply Finset.sum_congr rfl
    intro q _
    rw [GMx.vstar_inner]
  have himg : traceObjective psi '' directionDomain M = f '' directionDomain M :=
    Set.image_congr htr
  have hleast : IsLeast (f '' directionDomain M) L :=
    ⟨⟨GMx.vstar psi, GMx.vstar_mem psi, hfstar⟩, by rintro _ ⟨v, hv, rfl⟩; exact hlow v hv⟩
  have hED : entanglementDistance psi = L := by
    rw [entanglementDistance, himg, hleast.csInf_eq]
  have hLM : L = (M : ℝ) - ∑ q, ‖b q‖ ^ 2 := by
    rw [hL, Finset.sum_sub_distrib]; simp
  have hDom : directionDomain M = Set.pi Set.univ (fun _ => Metric.sphere (0 : Direction) 1) := by
    ext v; simp [directionDomain, Set.mem_pi]
  have hfcont : Continuous f := by
    rw [hf]
    fun_prop
  refine ⟨⟨GMx.vstar psi, GMx.vstar_mem psi⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hDom]; exact isCompact_univ_pi (fun _ => isCompact_sphere 0 1)
  · exact hfcont.continuousOn.congr htr
  · exact ⟨L, by rw [himg]; exact hleast.2⟩
  · rw [hED, hLM]
  · rw [hED, hL]; rfl
  · rw [hED, Set.image_congr (fun v _ => hdist v), hleast.csInf_eq]
  · intro v hv; rw [htr v hv, hdist v]
  · refine ⟨GMx.vstar psi, GMx.vstar_mem psi, by rw [htr _ (GMx.vstar_mem psi), hfstar, hED],
      by rw [hdist, hfstar, hED], ?_⟩
    intro q hq
    show GMx.vstar psi q = _
    unfold GMx.vstar
    rw [if_neg (show ¬ bloch psi q = 0 from hq)]
  · intro v hv
    rw [htr v hv, hED]
    have hterm : ∀ q ∈ Finset.univ, 1 - ‖b q‖ ^ 2 ≤ 1 - (inner ℝ (v q) (b q)) ^ 2 := by
      intro q _
      have := GMx.inner_sq_le (v q) (b q) (hv q)
      linarith
    rw [eq_comm, hL, hf]
    simp only
    rw [Finset.sum_eq_sum_iff_of_le hterm]
    apply forall_congr'
    intro q
    rw [← GMx.inner_sq_eq_iff (v q) (b q) (hv q)]
    simp only [Finset.mem_univ, true_implies]
    constructor <;> intro h <;> linarith
