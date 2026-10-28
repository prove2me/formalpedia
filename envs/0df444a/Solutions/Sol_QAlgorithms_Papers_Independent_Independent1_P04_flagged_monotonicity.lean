-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.flagged_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:00:18.399675+00:00
-- url     : https://prove2.me/submissions/a58bd285-b861-4e37-ad4f-8ee30f59ce27

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_l1_monotonicity
import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_relative_entropy_axioms
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def p04s204_blk {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ) :
    Matrix (Fin a × Fin e) (Fin a × Fin e) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then X p.1 p.2 q.2 else 0

def p04s204_fl {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ) : CoherenceMatrix (a*e) :=
  (p04s204_blk X).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

lemma p04s204_flagged_eq {d e a : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    (rho : CoherenceMatrix d) :
    flaggedOutput K rho = p04s204_fl (fun i => conjSuperop (K i) rho) := rfl

lemma p04s204_blk_pow {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ) (n : ℕ) :
    (p04s204_blk X) ^ n = p04s204_blk (fun i => X i ^ n) := by
  induction n with
  | zero =>
    ext p q
    simp only [pow_zero, p04s204_blk, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff]
    by_cases h1 : p.1 = q.1 <;> simp [h1]
  | succ n ih =>
    rw [pow_succ, ih]
    ext ⟨i0, k0⟩ ⟨j0, l0⟩
    simp only [p04s204_blk, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, ite_mul,
      mul_ite, zero_mul, mul_zero, pow_succ]
    by_cases h1 : i0 = j0
    · subst h1
      simp [Finset.sum_ite_eq']
    · simp only [h1, if_false]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
      by_cases h2 : i0 = i
      · subst h2; simp [h1]
      · simp [h2]

lemma p04s204_blk_trace {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ) :
    (p04s204_blk X).trace = ∑ i, (X i).trace := by
  simp [Matrix.trace, p04s204_blk, Fintype.sum_prod_type]

lemma p04s204_fl_eq {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ) :
    p04s204_fl X = Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv (p04s204_blk X) := rfl

lemma p04s204_fl_trace {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ) :
    (p04s204_fl X).trace = ∑ i, (X i).trace := by
  rw [← p04s204_blk_trace]
  unfold p04s204_fl Matrix.trace
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finProdFinEquiv.symm (fun p => p04s204_blk X p p)

lemma p04s204_fl_pow {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ) (n : ℕ) :
    (p04s204_fl X) ^ n = p04s204_fl (fun i => X i ^ n) := by
  rw [p04s204_fl_eq, p04s204_fl_eq, ← map_pow, p04s204_blk_pow]

lemma p04s204_trace_aeval {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ) (p : Polynomial ℝ) :
    (Polynomial.aeval (p04s204_fl X) p).trace = ∑ i, (Polynomial.aeval (X i) p).trace := by
  simp only [Polynomial.aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_smul, p04s204_fl_pow,
    p04s204_fl_trace]
  rw [Finset.sum_comm]
  simp [Finset.smul_sum]

lemma p04s204_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma p04s204_cfc_poly {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (f : ℝ → ℝ) (p : Polynomial ℝ)
    (hp : ∀ i, p.eval (hY.eigenvalues i) = f (hY.eigenvalues i)) :
    (cfc f Y).trace = (Polynomial.aeval Y p).trace := by
  rw [← cfc_polynomial p Y (show IsSelfAdjoint Y from hY), p04s204_cfc_trace hY, p04s204_cfc_trace hY]
  simp [hp]

lemma p04s204_blk_herm {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ)
    (hX : ∀ i, (X i).IsHermitian) : (p04s204_fl X).IsHermitian := by
  unfold p04s204_fl
  refine Matrix.IsHermitian.submatrix ?_ _
  ext p q
  simp only [p04s204_blk, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : q.1 = p.1
  · rw [if_pos h, if_pos h.symm, h]
    have := congrFun (congrFun (hX p.1) p.2) q.2
    simpa [Matrix.conjTranspose_apply] using this
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

lemma p04s204_trace_cfc_fl {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ)
    (hX : ∀ i, (X i).IsHermitian) (f : ℝ → ℝ) :
    (cfc f (p04s204_fl X)).trace = ∑ i, (cfc f (X i)).trace := by
  have hF := p04s204_blk_herm X hX
  set T : Finset ℝ := Finset.univ.image hF.eigenvalues ∪
    Finset.univ.biUnion (fun i => Finset.univ.image (hX i).eigenvalues) with hT
  set p := Lagrange.interpolate T id f
  have hp : ∀ x ∈ T, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) hx
  rw [p04s204_cfc_poly hF f p (fun i => hp _ (by simp [hT])), p04s204_trace_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [p04s204_cfc_poly (hX i) f p (fun k => hp _ ?_)]
  simp only [hT, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, k, rfl⟩

lemma p04s204_ent_fl {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ)
    (hX : ∀ i, (X i).IsHermitian) :
    naturalEntropy (p04s204_fl X) = ∑ i, naturalEntropy (X i) := by
  unfold naturalEntropy vnEntropy
  rw [p04s204_trace_cfc_fl X hX, Complex.re_sum, ← Finset.sum_neg_distrib, Finset.mul_sum]

lemma p04s204_deph_fl {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ) :
    dephasedMatrix (p04s204_fl X) = p04s204_fl (fun i => dephasedMatrix (X i)) := by
  ext m n
  simp only [dephasedMatrix, p04s204_fl, p04s204_blk, Matrix.diagonal_apply,
    Matrix.submatrix_apply, Matrix.of_apply]
  by_cases h : m = n
  · subst h; simp
  · have h' : finProdFinEquiv.symm m ≠ finProdFinEquiv.symm n := fun hh => h (finProdFinEquiv.symm.injective hh)
    rw [if_neg h]
    split_ifs with h1 h2
    · exact absurd (Prod.ext h1 h2) h'
    · rfl
    · rfl

lemma p04s204_cont : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
  have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (x * Real.log x) / Real.log 2 := by
    funext x; simp [Real.logb, mul_div_assoc]
  rw [this]
  exact Real.continuous_mul_log.div_const _

lemma p04s204_ent_smul {e : ℕ} (Y : CoherenceMatrix e) (hY : Y.IsHermitian) {c : ℝ} (hc : 0 < c) :
    naturalEntropy ((c : ℂ) • Y) = c * naturalEntropy Y - c * Real.log c * Y.trace.re := by
  unfold naturalEntropy vnEntropy
  rw [Complex.coe_smul]
  rw [← cfc_comp_smul c (fun x : ℝ => x * Real.logb 2 x) Y (p04s204_cont.continuousOn) (show IsSelfAdjoint Y from hY)]
  have hfun : (fun x : ℝ => (c • x) * Real.logb 2 (c • x)) =
      fun x => c * (x * Real.logb 2 x) + (c * Real.logb 2 c) * x := by
    funext x
    simp only [smul_eq_mul]
    by_cases hx : x = 0
    · subst hx; simp
    · rw [Real.logb, Real.log_mul hc.ne' hx, Real.logb, Real.logb]; ring
  have hsa : IsSelfAdjoint Y := hY
  rw [hfun, cfc_add (a := Y) (fun x => c * (x * Real.logb 2 x)) (fun x => (c * Real.logb 2 c) * x)
      (p04s204_cont.continuousOn.const_smul c) (by fun_prop),
    cfc_const_mul c (fun x : ℝ => x * Real.logb 2 x) Y (p04s204_cont.continuousOn),
    cfc_const_mul _ (fun x : ℝ => x) Y, cfc_id' ℝ Y hsa]
  simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul,
    Complex.re_ofReal_mul]
  have h2 : Real.log 2 ≠ 0 := by positivity
  rw [Real.logb]
  field_simp
  ring

lemma p04s204_deph_smul {e : ℕ} (Y : CoherenceMatrix e) (c : ℂ) :
    dephasedMatrix (c • Y) = c • dephasedMatrix Y := by
  ext i j
  simp only [dephasedMatrix, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma p04s204_deph_herm {e : ℕ} (Y : CoherenceMatrix e) (hY : Y.IsHermitian) :
    (dephasedMatrix Y).IsHermitian := by
  ext i j
  simp only [dephasedMatrix, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases h : j = i
  · subst h
    have := congrFun (congrFun hY j) j
    simpa [Matrix.conjTranspose_apply] using this
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

lemma p04s204_deph_trace {e : ℕ} (Y : CoherenceMatrix e) :
    (dephasedMatrix Y).trace = Y.trace := by
  simp [dephasedMatrix, Matrix.trace]

lemma p04s204_psd_zero {e : ℕ} (Y : CoherenceMatrix e) (hY : Y.PosSemidef) :
    0 ≤ Y.trace.re ∧ (Y.trace.re = 0 → Y = 0) := by
  have h := hY.trace_nonneg
  rw [Complex.nonneg_iff] at h
  refine ⟨by simpa using h.1, fun h0 => ?_⟩
  apply (hY.trace_eq_zero_iff).1
  apply Complex.ext
  · simpa using h0
  · simpa using h.2.symm

lemma p04s204_sel_ent {d e : ℕ} (K : Matrix (Fin e) (Fin d) ℂ) (rho : CoherenceMatrix d)
    (hrho : rho.PosSemidef) :
    selectiveContribution entropyCoherence K rho =
      naturalEntropy (dephasedMatrix (conjSuperop K rho)) - naturalEntropy (conjSuperop K rho) := by
  set Y := conjSuperop K rho with hYdef
  have hY : Y.PosSemidef := hrho.mul_mul_conjTranspose_same K
  obtain ⟨hp0, hpz⟩ := p04s204_psd_zero Y hY
  unfold selectiveContribution branchProbability
  rw [← hYdef]
  dsimp only
  split_ifs with hp
  · have hc : 0 < (Y.trace.re)⁻¹ := inv_pos.2 hp
    have hcast : ((Y.trace.re : ℂ))⁻¹ = (((Y.trace.re)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    unfold entropyCoherence
    rw [hcast, p04s204_deph_smul, p04s204_ent_smul _ (p04s204_deph_herm Y hY.1) hc,
      p04s204_ent_smul _ hY.1 hc, p04s204_deph_trace]
    field_simp
    ring
  · have : Y.trace.re = 0 := le_antisymm (not_lt.1 hp) hp0
    rw [hpz this]
    simp [dephasedMatrix]

lemma p04s204_l1_smul {e : ℕ} (Y : CoherenceMatrix e) (c : ℂ) :
    Coherence.l1Coherence (c • Y) = ‖c‖ * Coherence.l1Coherence Y := by
  unfold Coherence.l1Coherence
  simp [Finset.mul_sum]

lemma p04s204_sel_l1 {d e : ℕ} (K : Matrix (Fin e) (Fin d) ℂ) (rho : CoherenceMatrix d)
    (hrho : rho.PosSemidef) :
    selectiveContribution (fun _ rho => Coherence.l1Coherence rho) K rho =
      Coherence.l1Coherence (conjSuperop K rho) := by
  set Y := conjSuperop K rho with hYdef
  have hY : Y.PosSemidef := hrho.mul_mul_conjTranspose_same K
  obtain ⟨hp0, hpz⟩ := p04s204_psd_zero Y hY
  unfold selectiveContribution branchProbability
  rw [← hYdef]
  dsimp only
  split_ifs with hp
  · rw [p04s204_l1_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    field_simp
  · have : Y.trace.re = 0 := le_antisymm (not_lt.1 hp) hp0
    rw [hpz this]
    simp [Coherence.l1Coherence]

lemma p04s204_l1_fl {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ) :
    Coherence.l1Coherence (p04s204_fl X) = ∑ i, Coherence.l1Coherence (X i) := by
  unfold Coherence.l1Coherence
  simp only [Finset.sum_filter]
  set u : Fin (a*e) ≃ Fin a × Fin e := finProdFinEquiv.symm
  have step : (∑ m : Fin (a*e), ∑ n : Fin (a*e), if m ≠ n then ‖p04s204_fl X m n‖ else 0) =
      ∑ P : Fin a × Fin e, ∑ Q : Fin a × Fin e, if P ≠ Q then ‖p04s204_blk X P Q‖ else 0 := by
    refine Fintype.sum_equiv u _ _ fun m => ?_
    refine Fintype.sum_equiv u _ _ fun n => ?_
    simp only [ne_eq, u.injective.eq_iff]
    rfl
  rw [step, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp [p04s204_blk]
  · intro j _ hj
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [p04s204_blk, Ne.symm hj]
  · simp

lemma p04s204_blk_psd {a e : ℕ} (X : Fin a → Matrix (Fin e) (Fin e) ℂ)
    (hX : ∀ i, (X i).PosSemidef) : (p04s204_blk X).PosSemidef := by
  let B : Fin a → Matrix (Fin a × Fin e) (Fin e) ℂ := fun i =>
    Matrix.of fun p k => if p.1 = i ∧ p.2 = k then 1 else 0
  have hEq : p04s204_blk X = ∑ i, B i * X i * (B i)ᴴ := by
    ext p q
    simp only [p04s204_blk, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, B]
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, apply_ite star,
      star_one, star_zero]
    by_cases h : p.1 = q.1
    · rw [if_pos h, Finset.sum_eq_single p.1]
      · simp [h]
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    · rw [if_neg h]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      by_cases hj : p.1 = j
      · subst hj
        simp [Ne.symm h, h]
      · simp [hj]
  rw [hEq]
  exact Matrix.posSemidef_sum _ fun i _ => (hX i).mul_mul_conjTranspose_same (B i)

end QAlgorithms.Papers.Independent.Independent1.P04

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P04 in
/-- PDF pp.7–8, (C2c), (D.1)–(D.4): flagged monotonicity of the two concrete measures. -/
theorem solution (d e a : ℕ) (hd : 0 < d) (he : 0 < e)
    (K : Fin a → Matrix (Fin e) (Fin d) ℂ) (hK : IncoherentInstrument (fun _ => e) K)
    (rho : CoherenceMatrix d) (hrho : IsDensityMatrix rho) :
    IsDensityMatrix (flaggedOutput K rho) ∧
    entropyCoherence (a*e) (flaggedOutput K rho) ≤ entropyCoherence d rho ∧
    Coherence.l1Coherence (flaggedOutput K rho) ≤ Coherence.l1Coherence rho := by
  classical
  set Y : Fin a → CoherenceMatrix e := fun i => conjSuperop (K i) rho with hYdef
  have hYpsd : ∀ i, (Y i).PosSemidef := fun i => hrho.1.mul_mul_conjTranspose_same (K i)
  have hYh : ∀ i, (Y i).IsHermitian := fun i => (hYpsd i).1
  rw [p04s204_flagged_eq]
  refine ⟨⟨(p04s204_blk_psd Y hYpsd).submatrix _, ?_⟩, ?_, ?_⟩
  · rw [p04s204_fl_trace]
    have : ∀ i, (Y i).trace = ((K i)ᴴ * K i * rho).trace := by
      intro i
      show (K i * rho * (K i)ᴴ).trace = _
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun i _ => this i, ← Matrix.trace_sum, ← Finset.sum_mul, hK.1,
      Matrix.one_mul]
    exact hrho.2
  · have hsel := relative_entropy_axioms.2.2.2.1 d hd a (fun _ => e) (fun _ => he) K hK rho hrho
    refine le_trans (le_of_eq ?_) hsel
    rw [Finset.sum_congr rfl fun i _ => p04s204_sel_ent (K i) rho hrho.1]
    unfold entropyCoherence
    rw [p04s204_deph_fl, p04s204_ent_fl _ (fun i => p04s204_deph_herm _ (hYh i)),
      p04s204_ent_fl _ hYh, ← Finset.sum_sub_distrib]
  · have hsel := l1_monotonicity.1 d hd a (fun _ => e) (fun _ => he) K hK rho hrho
    refine le_trans (le_of_eq ?_) hsel
    rw [Finset.sum_congr rfl fun i _ => p04s204_sel_l1 (K i) rho hrho.1, p04s204_l1_fl]

