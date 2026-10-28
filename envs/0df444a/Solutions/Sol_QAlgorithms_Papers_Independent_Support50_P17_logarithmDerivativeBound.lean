-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P17.logarithmDerivativeBound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:54:28.832528+00:00
-- url     : https://prove2.me/submissions/13568e33-2eec-4082-9c99-4dbafe3143b4

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section
open MeasureTheory
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P17

namespace P17LDB

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma spec_eq {b : Matrix I I ℂ} (hb : b.IsHermitian) :
    b = (hb.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun k => ((hb.eigenvalues k : ℝ) : ℂ)) * star (hb.eigenvectorUnitary : Matrix I I ℂ) := by
  conv_lhs => rw [hb.spectral_theorem]
  simp [Function.comp_def]

lemma res_inv {b : Matrix I I ℂ} (hb : b.PosDef) (s : ℝ) (hs : 0 ≤ s) :
    (b + (s : ℂ) • (1 : Matrix I I ℂ))⁻¹ =
      (hb.1.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun k => (((hb.1.eigenvalues k + s)⁻¹ : ℝ) : ℂ)) *
      star (hb.1.eigenvectorUnitary : Matrix I I ℂ) := by
  set U : Matrix I I ℂ := (hb.1.eigenvectorUnitary : Matrix I I ℂ) with hU
  have h1 : U * star U = 1 := Unitary.coe_mul_star_self _
  have h2 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hsum : b + (s : ℂ) • (1 : Matrix I I ℂ) =
      U * Matrix.diagonal (fun k => ((hb.1.eigenvalues k + s : ℝ) : ℂ)) * star U := by
    have : Matrix.diagonal (fun k => ((hb.1.eigenvalues k + s : ℝ) : ℂ)) =
        Matrix.diagonal (fun k => ((hb.1.eigenvalues k : ℝ) : ℂ)) + (s : ℂ) • (1 : Matrix I I ℂ) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h]
    rw [this, Matrix.mul_add, Matrix.add_mul, ← spec_eq hb.1, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, h1]
  rw [hsum]
  apply Matrix.inv_eq_right_inv
  have hd : Matrix.diagonal (fun k => ((hb.1.eigenvalues k + s : ℝ) : ℂ)) *
      Matrix.diagonal (fun k => (((hb.1.eigenvalues k + s)⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext k
    have : 0 < hb.1.eigenvalues k + s := by have := hb.eigenvalues_pos k; linarith
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ this.ne', Complex.ofReal_one]
  calc U * Matrix.diagonal (fun k => ((hb.1.eigenvalues k + s : ℝ) : ℂ)) * star U *
        (U * Matrix.diagonal (fun k => (((hb.1.eigenvalues k + s)⁻¹ : ℝ) : ℂ)) * star U)
      = U * (Matrix.diagonal (fun k => ((hb.1.eigenvalues k + s : ℝ) : ℂ)) * (star U * U) *
        Matrix.diagonal (fun k => (((hb.1.eigenvalues k + s)⁻¹ : ℝ) : ℂ))) * star U := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h2, Matrix.mul_one, hd, Matrix.mul_one, h1]

lemma entry_formula (P Q M : Matrix I I ℂ) (r : I → ℝ) (i j : I) :
    (P * Matrix.diagonal (fun k => (r k : ℂ)) * M * Matrix.diagonal (fun k => (r k : ℂ)) * Q) i j =
      ∑ k, ∑ l, (P i k * M k l * Q l j) * ((r k * r l : ℝ) : ℂ) := by
  have hN : ∀ k l, (Matrix.diagonal (fun k => (r k : ℂ)) * M * Matrix.diagonal (fun k => (r k : ℂ))) k l
      = (r k : ℂ) * M k l * (r l : ℂ) := by
    intro k l; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have : P * Matrix.diagonal (fun k => (r k : ℂ)) * M * Matrix.diagonal (fun k => (r k : ℂ)) * Q =
      P * (Matrix.diagonal (fun k => (r k : ℂ)) * M * Matrix.diagonal (fun k => (r k : ℂ))) * Q := by
    simp only [Matrix.mul_assoc]
  rw [this, Matrix.mul_apply]
  simp only [Matrix.mul_apply, hN, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  push_cast; ring


open Filter Topology Set in
lemma sq_deriv (m : ℝ) (hm : 0 < m) :
    (∀ x ∈ Ici (0:ℝ), HasDerivAt (fun s : ℝ => -(m + s)⁻¹) ((m + x)⁻¹ * (m + x)⁻¹) x) ∧
    (∀ x ∈ Ioi (0:ℝ), 0 ≤ (m + x)⁻¹ * (m + x)⁻¹) ∧
    Tendsto (fun s : ℝ => -(m + s)⁻¹) atTop (𝓝 0) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
  · have hx' : (0:ℝ) ≤ x := hx
    have hne : m + x ≠ 0 := by linarith
    have h : HasDerivAt (fun s : ℝ => -(m + s)⁻¹) (-(-1 / (m + x) ^ 2)) x :=
      (((hasDerivAt_id' x).const_add m).inv hne).neg
    refine h.congr_deriv ?_
    field_simp
  · have : 0 < m + x := by have : (0:ℝ) < x := hx; linarith
    positivity
  · have : Tendsto (fun s : ℝ => (m + s)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ m tendsto_id)
    simpa using this.neg

lemma integ_sq (m : ℝ) (hm : 0 < m) :
    IntegrableOn (fun s : ℝ => (m + s)⁻¹ * (m + s)⁻¹) (Set.Ioi 0) ∧
    ∫ s in Set.Ioi (0:ℝ), (m + s)⁻¹ * (m + s)⁻¹ = m⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := sq_deriv m hm
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' h1 h2 h3, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' h1 h2 h3]
  simp

lemma integ_pair (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ => (p + s)⁻¹ * (q + s)⁻¹) (Set.Ioi 0) := by
  set m := min p q with hmdef
  have hm : 0 < m := lt_min hp hq
  refine (integ_sq m hm).1.mono' ?_ ?_
  · exact (((measurable_const.add measurable_id).inv).mul
      ((measurable_const.add measurable_id).inv)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hs' : (0:ℝ) < s := hs
    have hmp : m ≤ p := min_le_left _ _
    have hmq : m ≤ q := min_le_right _ _
    have a1 : 0 < m + s := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have e1 : (p + s)⁻¹ ≤ (m + s)⁻¹ := inv_anti₀ a1 (by linarith)
    have e2 : (q + s)⁻¹ ≤ (m + s)⁻¹ := inv_anti₀ a1 (by linarith)
    have : 0 < q + s := by linarith
    exact mul_le_mul e1 e2 (by positivity) (by positivity)


lemma resolvent_entry {b : Matrix I I ℂ} (hb : b.PosDef) (D : Matrix I I ℂ) (s : ℝ) (hs : 0 ≤ s)
    (i j : I) :
    resolventIntegrand b D s i j =
      ∑ k, ∑ l, ((hb.1.eigenvectorUnitary : Matrix I I ℂ) i k *
        (star (hb.1.eigenvectorUnitary : Matrix I I ℂ) * D * (hb.1.eigenvectorUnitary : Matrix I I ℂ)) k l *
        star (hb.1.eigenvectorUnitary : Matrix I I ℂ) l j) *
        (((hb.1.eigenvalues k + s)⁻¹ * (hb.1.eigenvalues l + s)⁻¹ : ℝ) : ℂ) := by
  unfold resolventIntegrand
  rw [res_inv hb s hs]
  rw [← entry_formula]
  simp only [Matrix.mul_assoc]

lemma resolvent_integrable {b : Matrix I I ℂ} (hb : b.PosDef) (D : Matrix I I ℂ) (i j : I) :
    IntegrableOn (fun s => resolventIntegrand b D s i j) (Set.Ioi (0 : ℝ)) := by
  refine IntegrableOn.congr_fun ?_ (fun s hs => (resolvent_entry hb D s (le_of_lt hs) i j).symm)
    measurableSet_Ioi
  refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ?_
  exact ((integ_pair _ _ (hb.eigenvalues_pos k) (hb.eigenvalues_pos l)).ofReal).const_mul _

lemma ldm_formula {b : Matrix I I ℂ} (hb : b.PosDef) (D : Matrix I I ℂ) (i j : I) :
    logarithmDerivativeMap b D i j =
      ∑ k, ∑ l, ((hb.1.eigenvectorUnitary : Matrix I I ℂ) i k *
        (star (hb.1.eigenvectorUnitary : Matrix I I ℂ) * D * (hb.1.eigenvectorUnitary : Matrix I I ℂ)) k l *
        star (hb.1.eigenvectorUnitary : Matrix I I ℂ) l j) *
        ((∫ s in Set.Ioi (0:ℝ), (hb.1.eigenvalues k + s)⁻¹ * (hb.1.eigenvalues l + s)⁻¹ : ℝ) : ℂ) := by
  unfold logarithmDerivativeMap
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => resolvent_entry hb D s (le_of_lt hs) i j)]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    ((integ_pair _ _ (hb.eigenvalues_pos k) (hb.eigenvalues_pos l)).ofReal).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ =>
    ((integ_pair _ _ (hb.eigenvalues_pos k) (hb.eigenvalues_pos l)).ofReal).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]
  congr 1
  exact integral_complex_ofReal

lemma conj_diag (U X Dg : Matrix I I ℂ) (h2 : star U * U = 1) (hX : X = U * Dg * star U) :
    star U * X * U = Dg := by
  rw [hX]
  calc star U * (U * Dg * star U) * U = (star U * U) * Dg * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = Dg := by rw [h2, Matrix.one_mul, Matrix.mul_one]

lemma ldm_self {b : Matrix I I ℂ} (hb : b.PosDef) : logarithmDerivativeMap b b = 1 := by
  ext i j
  rw [ldm_formula hb]
  rw [conj_diag _ _ _ (Unitary.coe_star_mul_self _) (spec_eq hb.1)]
  have hK : ∀ k, (∫ s in Set.Ioi (0:ℝ), (hb.1.eigenvalues k + s)⁻¹ * (hb.1.eigenvalues k + s)⁻¹)
      = (hb.1.eigenvalues k)⁻¹ := fun k => (integ_sq _ (hb.eigenvalues_pos k)).2
  have h1 : (hb.1.eigenvectorUnitary : Matrix I I ℂ) * star (hb.1.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  rw [← h1, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq, hK]
    have hne : ((hb.1.eigenvalues k : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (hb.eigenvalues_pos k).ne'
    push_cast
    field_simp
  · intro l _ hl
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hl)]
    simp
  · simp


lemma ldm_lin {b : Matrix I I ℂ} (hb : b.PosDef) (c d : ℂ) (X Y : Matrix I I ℂ) :
    logarithmDerivativeMap b (c • X + d • Y) =
      c • logarithmDerivativeMap b X + d • logarithmDerivativeMap b Y := by
  ext i j
  unfold logarithmDerivativeMap
  simp only [Matrix.add_apply]
  have h : ∀ s, resolventIntegrand b (c • X + d • Y) s i j =
      c * resolventIntegrand b X s i j + d * resolventIntegrand b Y s i j := by
    intro s
    simp [resolventIntegrand, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp_rw [h]
  rw [integral_add ((resolvent_integrable hb X i j).const_mul c)
    ((resolvent_integrable hb Y i j).const_mul d), integral_const_mul, integral_const_mul]
  rfl

lemma res_herm {b : Matrix I I ℂ} (hb : b.PosDef) (s : ℝ) :
    ((b + (s : ℂ) • (1 : Matrix I I ℂ))⁻¹)ᴴ = (b + (s : ℂ) • (1 : Matrix I I ℂ))⁻¹ := by
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_add, hb.1.eq,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

lemma cplx_integral_nonneg {f : ℝ → ℂ} (hf : ∀ s, 0 ≤ f s) :
    0 ≤ ∫ s in Set.Ioi (0:ℝ), f s := by
  have hfe : f = fun s => ((f s).re : ℂ) := by
    funext s
    have := (Complex.le_def.1 (hf s)).2
    apply Complex.ext
    · simp
    · simp [← this]
  rw [hfe, integral_complex_ofReal]
  exact Complex.zero_le_real.2 (setIntegral_nonneg measurableSet_Ioi
    (fun s _ => (Complex.le_def.1 (hf s)).1))

lemma ldm_psd {b : Matrix I I ℂ} (hb : b.PosDef) {Y : Matrix I I ℂ} (hY : Y.PosSemidef) :
    (logarithmDerivativeMap b Y).PosSemidef := by
  have hR : ∀ s, resolventIntegrand b Y s =
      ((b + (s : ℂ) • (1 : Matrix I I ℂ))⁻¹)ᴴ * Y * (b + (s : ℂ) • (1 : Matrix I I ℂ))⁻¹ := by
    intro s; rw [res_herm hb s]; rfl
  have hRpsd : ∀ s, (resolventIntegrand b Y s).PosSemidef := by
    intro s; rw [hR s]; exact hY.conjTranspose_mul_mul_same _
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    rw [Matrix.conjTranspose_apply]
    unfold logarithmDerivativeMap
    change (starRingEnd ℂ) (∫ s in Set.Ioi (0:ℝ), resolventIntegrand b Y s j i) = _
    rw [← integral_conj]
    congr 1; funext s
    have := congrFun (congrFun (hRpsd s).1 i) j
    rw [Matrix.conjTranspose_apply] at this
    exact this
  · intro x
    have hq : star x ⬝ᵥ (logarithmDerivativeMap b Y *ᵥ x) =
        ∫ s in Set.Ioi (0:ℝ), star x ⬝ᵥ (resolventIntegrand b Y s *ᵥ x) := by
      simp only [dotProduct, Matrix.mulVec]
      rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum _ fun j _ =>
        (resolvent_integrable hb Y i j).mul_const _).const_mul _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
        (resolvent_integrable hb Y i j).mul_const _)]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const]
      rfl
    rw [hq]
    exact cplx_integral_nonneg fun s => (hRpsd s).dotProduct_mulVec_nonneg x


lemma traceNorm_herm {Δ : Matrix I I ℂ} (hΔ : Δ.IsHermitian) :
    traceNorm Δ = ∑ i, |hΔ.eigenvalues i| := by
  have hsa : IsSelfAdjoint Δ := hΔ
  unfold traceNorm
  have h1 : Δᴴ * Δ = cfc (fun x : ℝ => x ^ 2) Δ := by
    rw [cfc_pow (fun x : ℝ => x) 2 Δ, cfc_id' ℝ Δ, hΔ.eq, pow_two]
  rw [h1, ← cfc_comp Real.sqrt (fun x : ℝ => x ^ 2) Δ]
  have h2 : (Real.sqrt ∘ fun x : ℝ => x ^ 2) = fun x => |x| := by
    funext x; simp [Real.sqrt_sq_eq_abs]
  rw [h2, hΔ.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp

lemma eig_le_half_traceNorm {Δ : Matrix I I ℂ} (hΔ : Δ.IsHermitian) (htr : Δ.trace = 0) (i : I) :
    hΔ.eigenvalues i ≤ 2⁻¹ * traceNorm Δ := by
  rw [traceNorm_herm hΔ]
  have hsum : ∑ j, hΔ.eigenvalues j = 0 := by
    have := congrArg Complex.re (hΔ.trace_eq_sum_eigenvalues)
    rw [htr] at this
    simpa using this.symm
  have key : hΔ.eigenvalues i ≤ ∑ j, (|hΔ.eigenvalues j| + hΔ.eigenvalues j) / 2 := by
    have h := Finset.single_le_sum (f := fun j => (|hΔ.eigenvalues j| + hΔ.eigenvalues j) / 2)
      (fun j _ => by have := neg_abs_le (hΔ.eigenvalues j); linarith)
      (Finset.mem_univ i)
    have : hΔ.eigenvalues i ≤ (|hΔ.eigenvalues i| + hΔ.eigenvalues i) / 2 := by
      have := le_abs_self (hΔ.eigenvalues i); linarith
    linarith
  rw [← Finset.sum_div, Finset.sum_add_distrib, hsum] at key
  linarith

lemma shift_psd {Δ : Matrix I I ℂ} (hΔ : Δ.IsHermitian) (t : ℝ) (ht : ∀ i, hΔ.eigenvalues i ≤ t) :
    ((t : ℂ) • (1 : Matrix I I ℂ) - Δ).PosSemidef := by
  set U : Matrix I I ℂ := (hΔ.eigenvectorUnitary : Matrix I I ℂ)
  have h1 : U * star U = 1 := Unitary.coe_mul_star_self _
  have heq : (t : ℂ) • (1 : Matrix I I ℂ) - Δ =
      U * Matrix.diagonal (fun k => ((t - hΔ.eigenvalues k : ℝ) : ℂ)) * star U := by
    have hd : Matrix.diagonal (fun k => ((t - hΔ.eigenvalues k : ℝ) : ℂ)) =
        (t : ℂ) • (1 : Matrix I I ℂ) - Matrix.diagonal (fun k => ((hΔ.eigenvalues k : ℝ) : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h]
    rw [hd, Matrix.mul_sub, Matrix.sub_mul, ← spec_eq hΔ, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, h1]
  rw [heq, Matrix.star_eq_conjTranspose]
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ _
  refine Matrix.PosSemidef.diagonal fun k => ?_
  exact Complex.zero_le_real.2 (by linarith [ht k])

end P17LDB

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (a b : Matrix I I ℂ) (ha : a.PosDef) (hb : b.PosDef)
    (htrace : a.trace = b.trace) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hlower : (a - (gamma : ℂ) • (1 : Matrix I I ℂ)).PosSemidef) :
    let t := traceDistance b a
    (∀ i j : I, IntegrableOn (fun s => resolventIntegrand b (b - a) s i j)
      (Set.Ioi (0 : ℝ))) ∧
    (((t / (gamma + t) : ℝ) : ℂ) • (1 : Matrix I I ℂ) -
      logarithmDerivativeMap b (b - a)).PosSemidef := by
  intro t
  refine ⟨fun i j => P17LDB.resolvent_integrable hb _ i j, ?_⟩
  have hΔ : (b - a).IsHermitian := hb.1.sub ha.1
  have htr : (b - a).trace = 0 := by rw [Matrix.trace_sub, htrace, sub_self]
  have ht_def : t = 2⁻¹ * traceNorm (b - a) := rfl
  have hteig : ∀ i, hΔ.eigenvalues i ≤ t := fun i => by
    rw [ht_def]; exact P17LDB.eig_le_half_traceNorm hΔ htr i
  have hpsd1 := P17LDB.shift_psd hΔ t hteig
  have ht0 : 0 ≤ t := by
    rw [ht_def, P17LDB.traceNorm_herm hΔ]
    have : 0 ≤ ∑ i, |hΔ.eigenvalues i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hTΔ : logarithmDerivativeMap b (b - a) =
      (1 : Matrix I I ℂ) - logarithmDerivativeMap b a := by
    have := P17LDB.ldm_lin hb 1 (-1) b a
    rw [one_smul, neg_one_smul, one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg,
      P17LDB.ldm_self hb] at this
    exact this
  rcases eq_or_lt_of_le (add_nonneg hgamma ht0) with h0 | hpos
  · have hg0 : gamma = 0 := by linarith
    have ht00 : t = 0 := by linarith
    have hlin := P17LDB.ldm_lin hb (t : ℂ) (-1) 1 (b - a)
    rw [neg_one_smul, ← sub_eq_add_neg, neg_one_smul, ← sub_eq_add_neg] at hlin
    have hP := P17LDB.ldm_psd hb hpsd1
    rw [hlin] at hP
    rw [← h0, ht00] at *
    simpa using hP
  · set Y : Matrix I I ℂ := (t : ℂ) • (a - (gamma : ℂ) • (1 : Matrix I I ℂ)) +
      (gamma : ℂ) • ((t : ℂ) • (1 : Matrix I I ℂ) - (b - a)) with hYdef
    have hY : Y.PosSemidef :=
      (hlower.smul (Complex.zero_le_real.2 ht0)).add (hpsd1.smul (Complex.zero_le_real.2 hgamma))
    have hY2 : Y = ((gamma + t : ℝ) : ℂ) • a + (-(gamma : ℂ)) • b := by
      rw [hYdef]; push_cast
      rw [smul_sub, smul_sub, smul_sub, smul_smul, smul_smul, mul_comm (gamma : ℂ) (t : ℂ), add_smul,
        neg_smul]
      abel
    have hTY := P17LDB.ldm_lin hb ((gamma + t : ℝ) : ℂ) (-(gamma : ℂ)) a b
    rw [← hY2, P17LDB.ldm_self hb] at hTY
    have hfin := (P17LDB.ldm_psd hb hY).smul
      (Complex.zero_le_real.2 (inv_nonneg.2 hpos.le) : (0 : ℂ) ≤ (((gamma + t)⁻¹ : ℝ) : ℂ))
    convert hfin using 1
    rw [hTY, hTΔ]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Matrix.one_apply]
    have hne : ((gamma + t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast at hne ⊢
    field_simp
    split_ifs <;> ring
