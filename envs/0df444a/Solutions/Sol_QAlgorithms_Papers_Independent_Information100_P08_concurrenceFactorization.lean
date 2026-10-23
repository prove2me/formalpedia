-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P08.concurrenceFactorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:59:56.003092+00:00
-- url     : https://prove2.me/submissions/5a6ce2ec-a918-412c-b6c6-74b9b23c9cb4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev X8V := EuclideanSpace ℂ (Fin 2 × Fin 2)
abbrev X8M := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

def x8act (M : Matrix (Fin 2) (Fin 2) ℂ) (w : X8V) : X8V :=
  WithLp.toLp 2 fun p => ∑ s, M p.1 s * w (s, p.2)

def x8L (M : Matrix (Fin 2) (Fin 2) ℂ) (X : X8M) : X8M :=
  Matrix.of fun p q => ∑ s, ∑ s', M p.1 s * X (s, p.2) (s', q.2) * conj (M q.1 s')

def x8S (X : X8M) : Set ℝ :=
  {r | ∃ e : PureEnsemble (Fin 2 × Fin 2), pureAverage e = X ∧
    r = ∑ x, e.prob x * pureConcurrence (e.vector x)}

lemma x8_conc (X : X8M) : concurrence X = sInf (x8S X) := rfl

lemma x8_pc_act (M : Matrix (Fin 2) (Fin 2) ℂ) (w : X8V) :
    pureConcurrence (x8act M w) = ‖M.det‖ * pureConcurrence w := by
  unfold pureConcurrence
  have : (Matrix.of fun i j => (x8act M w) (i, j)) = M * Matrix.of fun i j => w (i, j) := by
    ext i j; simp [x8act, Matrix.mul_apply]
  rw [this, Matrix.det_mul, norm_mul]; ring

lemma x8_pc_smul (c : ℂ) (w : X8V) :
    pureConcurrence (c • w) = ‖c‖ ^ 2 * pureConcurrence w := by
  unfold pureConcurrence
  have : (Matrix.of fun i j => (c • w) (i, j)) = c • Matrix.of fun i j => w (i, j) := by
    ext i j; simp
  rw [this, Matrix.det_smul]; simp [norm_mul, norm_pow]; ring

lemma x8_pc_nonneg (w : X8V) : 0 ≤ pureConcurrence w := by
  unfold pureConcurrence; positivity

lemma x8_pD_smul (c : ℂ) (w : X8V) :
    pureDensity (c • w) = ((‖c‖ ^ 2 : ℝ) : ℂ) • pureDensity w := by
  ext a b
  simp only [pureDensity, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, PiLp.smul_apply, map_mul]
  have : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [this]; ring

lemma x8_pD_act (M : Matrix (Fin 2) (Fin 2) ℂ) (w : X8V) :
    pureDensity (x8act M w) = x8L M (pureDensity w) := by
  ext p q
  rw [x8L, pureDensity, pureDensity, Matrix.of_apply, Matrix.of_apply]
  simp [x8act, Fin.sum_univ_two]
  ring

lemma x8_L_sum {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℂ) (X : Fin n → X8M) :
    x8L M (∑ x, X x) = ∑ x, x8L M (X x) := by
  ext p q
  simp only [x8L, Matrix.of_apply, Matrix.sum_apply, Fin.sum_univ_two, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib]

lemma x8_L_comp (A B : Matrix (Fin 2) (Fin 2) ℂ) (X : X8M) :
    x8L A (x8L B X) = x8L (A * B) X := by
  ext p q
  simp only [x8L, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
  ring

lemma x8_L_one (X : X8M) : x8L 1 X = X := by
  ext p q
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  fin_cases a <;> fin_cases c <;> simp [x8L, Fin.sum_univ_two, Matrix.one_apply]

lemma x8_tr_pD (w : X8V) : (pureDensity w).trace = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

lemma x8_mk {n : ℕ} (w : Fin n → X8V) (X : X8M) (hX : ∑ x, pureDensity (w x) = X)
    (htr : X.trace = 1) : ∑ x, pureConcurrence (w x) ∈ x8S X := by
  have htot : ∑ x, ‖w x‖ ^ 2 = 1 := by
    have h := congrArg Matrix.trace hX
    rw [Matrix.trace_sum, htr] at h
    simp only [x8_tr_pD] at h
    exact_mod_cast h
  let u0 : X8V := EuclideanSpace.single (0, 0) 1
  have hu0 : ‖u0‖ = 1 := by simp [u0]
  let v : Fin n → X8V := fun x => if w x = 0 then u0 else ((‖w x‖ : ℂ)⁻¹) • w x
  have key : ∀ x, w x ≠ 0 → (‖w x‖ ^ 2 : ℝ) * ‖((‖w x‖ : ℂ)⁻¹)‖ ^ 2 = 1 := by
    intro x hx
    have : ‖w x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]; field_simp
  refine ⟨⟨n, fun x => ‖w x‖ ^ 2, v, fun x => by positivity, htot, fun x => ?_⟩, ?_, ?_⟩
  · by_cases hx : w x = 0
    · simp [v, hx, hu0]
    · simp only [v, hx, if_false, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)
  · rw [← hX]; unfold pureAverage
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : w x = 0
    · simp [hx]
      ext a b; simp [pureDensity]
    · simp only [v, hx, if_false, x8_pD_smul, smul_smul]
      rw [← Complex.coe_smul, ← smul_assoc]
      ext a b
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← Complex.ofReal_mul, key x hx, Complex.ofReal_one, one_mul]
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : w x = 0
    · have h0 : (Matrix.of fun _ _ => (0 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by ext; simp
      simp [hx, pureConcurrence, h0]
    · simp only [v, hx, if_false, x8_pc_smul]
      rw [← mul_assoc, key x hx, one_mul]

lemma x8_S_nonneg (X : X8M) : ∀ r ∈ x8S X, 0 ≤ r := by
  rintro r ⟨e, -, rfl⟩
  exact Finset.sum_nonneg fun x _ => mul_nonneg (e.nonneg x) (x8_pc_nonneg _)

lemma x8_transfer (A : Matrix (Fin 2) (Fin 2) ℂ) (Y Z : X8M) (hZ : Z = x8L A Y)
    (htr : Z.trace = 1) : ∀ r ∈ x8S Y, ‖A.det‖ * r ∈ x8S Z := by
  rintro r ⟨e, he, rfl⟩
  let w : Fin e.size → X8V := fun x => x8act A (((Real.sqrt (e.prob x) : ℝ) : ℂ) • e.vector x)
  have h := x8_mk w Z ?_ htr
  · convert h using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [w, x8_pc_act, x8_pc_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (e.nonneg x)]
  · simp only [w, x8_pD_act, x8_pD_smul]
    rw [← x8_L_sum, hZ, ← he]
    congr 1
    unfold pureAverage
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (e.nonneg x), Complex.coe_smul]

lemma x8_id_L {m : ℕ} (E : Fin m → Matrix (Fin 2) (Fin 2) ℂ) (N : Superop (Fin 2) (Fin 2))
    (hN : ∀ ρ, N ρ = krausApply E ρ) (M : Matrix (Fin 2) (Fin 2) ℂ) (X : X8M) :
    idTensorSuperop N (x8L M X) = x8L M (idTensorSuperop N X) := by
  ext p q
  simp only [idTensorSuperop, x8L, Matrix.of_apply, hN, krausApply, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul, Fin.sum_univ_two, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring

lemma x8_kraus_trace {m : ℕ} (E : Fin m → Matrix (Fin 2) (Fin 2) ℂ) (hE : IsKrausFamily E)
    (B : Matrix (Fin 2) (Fin 2) ℂ) : (krausApply E B).trace = B.trace := by
  unfold krausApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_comm _ (E _)ᴴ, ← mul_assoc]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hE, one_mul]

lemma x8_id_trace {m : ℕ} (E : Fin m → Matrix (Fin 2) (Fin 2) ℂ) (hE : IsKrausFamily E)
    (N : Superop (Fin 2) (Fin 2)) (hN : ∀ ρ, N ρ = krausApply E ρ) (X : X8M) :
    (idTensorSuperop N X).trace = X.trace := by
  have h : ∀ r, (N (Matrix.of fun i i' => X (r, i) (r, i'))).trace =
      (Matrix.of fun i i' => X (r, i) (r, i')).trace := fun r => by
    rw [hN, x8_kraus_trace E hE]
  simp only [Matrix.trace, Matrix.diag] at h ⊢
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  have := h r; simp only [Matrix.of_apply] at this; exact this

lemma x8_choi_decomp {m : ℕ} (E : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (N : Superop (Fin 2) (Fin 2)) (hN : ∀ ρ, N ρ = krausApply E ρ) :
    ∑ j, pureDensity (WithLp.toLp 2 fun p : Fin 2 × Fin 2 =>
      ∑ i, E j p.2 i * bellVector 2 (p.1, i) : X8V) = choi N := by
  ext p q
  simp only [choi, idTensorSuperop, Matrix.of_apply, hN, krausApply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, PiLp.toLp_apply, map_add, map_mul]
  simp only [RCLike.star_def]
  ring

lemma x8_bell_trace : (pureDensity (bellVector 2)).trace = 1 := by
  simp [Matrix.trace, pureDensity, bellVector, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; norm_num

lemma x8_purif (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    canonicalPurification ρ = x8act ((Real.sqrt 2 : ℂ) • (cfc Real.sqrt ρ)ᵀ) (bellVector 2) := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  ext p
  obtain ⟨a, b⟩ := p
  fin_cases b <;>
    simp [canonicalPurification, x8act, bellVector, Fin.sum_univ_two] <;> field_simp

lemma x8_sqrt (ρ : Matrix (Fin 2) (Fin 2) ℂ) (h : ρ.PosSemidef) :
    cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ ∧ (cfc Real.sqrt ρ).PosSemidef := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ ρ := Matrix.nonneg_iff_posSemidef.2 h
  constructor
  · rw [← cfc_mul (fun x => Real.sqrt x) (fun x => Real.sqrt x) ρ]
    conv_rhs => rw [← cfc_id' ℝ ρ]
    apply cfc_congr
    intro x hx
    exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 hx)
  · open scoped MatrixOrder in
    exact Matrix.nonneg_iff_posSemidef.1 (cfc_nonneg (fun x _ => Real.sqrt_nonneg x))

lemma x8_det (ρ : Matrix (Fin 2) (Fin 2) ℂ) (h : ρ.PosSemidef) :
    ‖((Real.sqrt 2 : ℂ) • (cfc Real.sqrt ρ)ᵀ).det‖ = 2 * Real.sqrt ρ.det.re := by
  obtain ⟨hsq, hpsd⟩ := x8_sqrt ρ h
  set R := cfc Real.sqrt ρ
  have hnn : 0 ≤ R.det := hpsd.det_nonneg
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 hnn
  have hR : R.det = (R.det.re : ℂ) := by
    apply Complex.ext <;> simp [him.symm]
  have hd : ρ.det.re = R.det.re ^ 2 := by
    rw [← hsq, Matrix.det_mul, hR]; norm_cast; ring
  rw [Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin, hd, Real.sqrt_sq hre, hR]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num), norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hre]
  norm_num

lemma x8_purif_trace (ρ : Matrix (Fin 2) (Fin 2) ℂ) (h : IsDensityMatrix ρ) :
    (pureDensity (canonicalPurification ρ)).trace = 1 := by
  obtain ⟨hsq, hpsd⟩ := x8_sqrt ρ h.1
  set R := cfc Real.sqrt ρ
  have hH := hpsd.1
  rw [← h.2]; conv_rhs => rw [← hsq]
  simp only [Matrix.trace, Matrix.diag, pureDensity, canonicalPurification, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
  rw [← hH.apply r i]; simp [R]

theorem x8_main (N : Superop (Fin 2) (Fin 2)) (hN : IsChannel N)
    (rho : Matrix (Fin 2) (Fin 2) ℂ) (hrho : IsDensityMatrix rho) :
    concurrence (idTensorSuperop N (pureDensity (canonicalPurification rho))) =
      2 * Real.sqrt rho.det.re * concurrence (choi N) := by
  obtain ⟨m, E, hE, hNE⟩ := hN
  set M : Matrix (Fin 2) (Fin 2) ℂ := (Real.sqrt 2 : ℂ) • (cfc Real.sqrt rho)ᵀ with hMdef
  set T := idTensorSuperop N (pureDensity (canonicalPurification rho)) with hTdef
  set X := choi N with hXdef
  have hT : T = x8L M X := by
    rw [hTdef, x8_purif, x8_pD_act, x8_id_L E N hNE]; rfl
  have htrT : T.trace = 1 := by
    rw [hTdef, x8_id_trace E hE N hNE, x8_purif_trace rho hrho]
  have htrX : X.trace = 1 := by
    rw [hXdef, choi, x8_id_trace E hE N hNE, x8_bell_trace]
  have hneX : (x8S X).Nonempty := ⟨_, x8_mk _ X (x8_choi_decomp E N hNE) htrX⟩
  have hbX : BddBelow (x8S X) := ⟨0, fun r hr => x8_S_nonneg X r hr⟩
  have hbT : BddBelow (x8S T) := ⟨0, fun r hr => x8_S_nonneg T r hr⟩
  rw [x8_conc, x8_conc, ← x8_det rho hrho.1]
  set d := ‖M.det‖
  obtain ⟨r0, hr0⟩ := hneX
  by_cases hd : d = 0
  · rw [hd, zero_mul]
    apply le_antisymm
    · have := csInf_le hbT (x8_transfer M X T hT htrT r0 hr0)
      change sInf (x8S T) ≤ d * r0 at this
      rwa [hd, zero_mul] at this
    · exact Real.sInf_nonneg (x8_S_nonneg T)
  · have hdpos : 0 < d := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have hdet : M.det ≠ 0 := fun h0 => hd (by simp [d, h0])
    have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (Ne.isUnit hdet)
    have hX : X = x8L M⁻¹ T := by rw [hT, x8_L_comp, hinv, x8_L_one]
    have hdinv : ‖M⁻¹.det‖ = d⁻¹ := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv]
    have hneT : (x8S T).Nonempty := ⟨_, x8_transfer M X T hT htrT r0 hr0⟩
    apply le_antisymm
    · rw [← div_le_iff₀' hdpos]
      refine le_csInf ⟨r0, hr0⟩ fun r hr => ?_
      rw [div_le_iff₀' hdpos]
      exact csInf_le hbT (x8_transfer M X T hT htrT r hr)
    · refine le_csInf hneT fun r hr => ?_
      have := csInf_le hbX (x8_transfer M⁻¹ T X hX htrX r hr)
      rw [hdinv] at this
      rw [← le_div_iff₀' hdpos]
      calc sInf (x8S X) ≤ d⁻¹ * r := this
        _ = r / d := by ring

end

end QAlgorithms.Papers.Independent.Information100.P08

open QAlgorithms.Papers.Independent.Information100.P08 in
theorem solution (N : QAlgorithms.Superop (Fin 2) (Fin 2)) (hN : QAlgorithms.IsChannel N)
    (rho : Matrix (Fin 2) (Fin 2) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    concurrence (QAlgorithms.idTensorSuperop N
      (QAlgorithms.pureDensity (canonicalPurification rho))) =
      2 * Real.sqrt rho.det.re * concurrence (choi N) := x8_main N hN rho hrho
