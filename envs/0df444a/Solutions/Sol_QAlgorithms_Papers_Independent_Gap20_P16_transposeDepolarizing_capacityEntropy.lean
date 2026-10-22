-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P16.transposeDepolarizing_capacityEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:31:51.130822+00:00
-- url     : https://prove2.me/submissions/7be776f4-a35f-44b0-8ba8-22e71de2e016

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder


lemma g73f_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g73f_affine {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℂ} (hB : B.IsHermitian)
    (c : ℝ) : (c : ℂ) • (1 - B) = cfc (fun x : ℝ => c * (1 - x)) B := by
  have hfin := (Matrix.finite_real_spectrum (A := B))
  rw [cfc_const_mul c (fun x : ℝ => 1 - x) B (hfin.continuousOn _),
    cfc_sub (fun _ : ℝ => (1:ℝ)) (fun x : ℝ => x) B (hfin.continuousOn _) (hfin.continuousOn _),
    cfc_const_one ℝ B, cfc_id' ℝ (a := B) (show IsSelfAdjoint B from hB)]
  rw [← Complex.coe_smul]

lemma g73f_ent_affine {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℂ} (hB : B.IsHermitian)
    (c : ℝ) : vnEntropy ((c : ℂ) • (1 - B)) =
      -∑ i, (c * (1 - hB.eigenvalues i)) * Real.logb 2 (c * (1 - hB.eigenvalues i)) := by
  unfold vnEntropy
  have hfin := (Matrix.finite_real_spectrum (A := B))
  have hc := cfc_comp (fun x : ℝ => x * Real.logb 2 x) (fun x : ℝ => c * (1 - x)) B hB
    ((hfin.image _).continuousOn _) (hfin.continuousOn _)
  rw [g73f_affine hB c, ← hc, g73f_cfc_trace hB]
  simp

lemma g73f_term_le (D μ : ℝ) (hD : 0 < D) (hμ : 0 ≤ μ) :
    -(μ * Real.log μ) - μ * Real.log D ≤ 1 / D - μ := by
  rcases hμ.eq_or_lt with h | h
  · subst h; simp; positivity
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (D * μ) by positivity)
    rw [one_div, Real.log_inv, Real.log_mul hD.ne' h.ne'] at h1
    have h2 : μ * ((D * μ)⁻¹ - 1) = 1 / D - μ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 h.le]

lemma g73f_ent_le_log {n : Type*} [Fintype n] (μ : n → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hs : ∑ i, μ i = 1) (hn : 0 < Fintype.card n) :
    -∑ i, μ i * Real.logb 2 (μ i) ≤ Real.logb 2 (Fintype.card n) := by
  have hD : (0:ℝ) < Fintype.card n := by exact_mod_cast hn
  have key : ∑ i, (-(μ i * Real.log (μ i)) - μ i * Real.log (Fintype.card n)) ≤
      ∑ _i : n, (1 / (Fintype.card n : ℝ)) - ∑ i, μ i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => g73f_term_le _ _ hD (hμ i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at key
  rw [mul_one_div_cancel hD.ne'] at key
  simp only [Real.logb, ← Finset.sum_neg_distrib]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : ∑ i, -(μ i * (Real.log (μ i) / Real.log 2)) = (∑ i, -(μ i * Real.log (μ i))) / Real.log 2 := by
    rw [Finset.sum_div]; congr 1; ext i; ring
  rw [this, div_le_div_iff_of_pos_right hl]
  linarith

lemma g73f_ent_ge_log {n : Type*} [Fintype n] (c : ℝ) (hc : 0 < c) (μ : n → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hμc : ∀ i, μ i ≤ c) (hs : ∑ i, μ i = 1) :
    Real.logb 2 c⁻¹ ≤ -∑ i, μ i * Real.logb 2 (μ i) := by
  have key : ∀ i, μ i * Real.logb 2 c⁻¹ ≤ -(μ i * Real.logb 2 (μ i)) := by
    intro i
    rcases (hμ i).eq_or_lt with h | h
    · rw [← h]; simp
    · have : Real.logb 2 (μ i) ≤ Real.logb 2 c := Real.logb_le_logb_of_le (by norm_num) h (hμc i)
      rw [Real.logb_inv]
      nlinarith
  calc Real.logb 2 c⁻¹ = ∑ i, μ i * Real.logb 2 c⁻¹ := by rw [← Finset.sum_mul, hs, one_mul]
    _ ≤ ∑ i, -(μ i * Real.logb 2 (μ i)) := Finset.sum_le_sum fun i _ => key i
    _ = _ := by rw [Finset.sum_neg_distrib]

lemma g73f_wh_eq {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.trace = 1) :
    QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d σ =
      ((((d:ℝ) - 1)⁻¹ : ℝ) : ℂ) • (1 - σ.transpose) := by
  unfold QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo
  rw [hσ, one_smul]; push_cast; rfl

lemma g73f_wh_ent {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : IsDensityMatrix σ) :
    ∃ μ : Fin d → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, μ i ≤ ((d:ℝ) - 1)⁻¹) ∧
      (2 ≤ d → ∑ i, μ i = 1) ∧
      vnEntropy (QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d σ) =
        -∑ i, μ i * Real.logb 2 (μ i) := by
  have hT : σ.transpose.PosSemidef := hσ.1.transpose
  set lam := hT.1.eigenvalues with hlam
  have hnn : ∀ i, 0 ≤ lam i := fun i => hT.eigenvalues_nonneg i
  have hsum : ∑ i, lam i = 1 := by
    have h := hT.1.trace_eq_sum_eigenvalues
    rw [Matrix.trace_transpose, hσ.2] at h
    have h2 := congrArg Complex.re h
    simp at h2
    exact h2.symm
  have hle : ∀ i, lam i ≤ 1 := fun i => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  refine ⟨fun i => ((d:ℝ) - 1)⁻¹ * (1 - lam i), ?_, ?_, ?_, ?_⟩
  · intro i
    rcases le_or_gt (d:ℝ) 1 with h | h
    · rcases Nat.lt_or_ge d 1 with h0 | h0
      · exact absurd i.2 (by omega)
      · have : (d:ℝ) = 1 := le_antisymm h (by exact_mod_cast h0)
        simp [this]
    · exact mul_nonneg (inv_nonneg.2 (by linarith)) (by linarith [hle i])
  · intro i
    rcases le_or_gt (d:ℝ) 1 with h | h
    · rcases Nat.lt_or_ge d 1 with h0 | h0
      · exact absurd i.2 (by omega)
      · have : (d:ℝ) = 1 := le_antisymm h (by exact_mod_cast h0)
        simp [this]
    · have : 0 ≤ ((d:ℝ) - 1)⁻¹ := inv_nonneg.2 (by linarith)
      nlinarith [hnn i]
  · intro hd
    have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
    simp
    exact inv_mul_cancel₀ (show (d:ℝ) - 1 ≠ 0 by linarith)
  · rw [g73f_wh_eq σ hσ.2, g73f_ent_affine hT.1]

lemma g73f_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma g73f_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := g73f_diag_herm d
  rw [g73f_cfc_trace hD]
  have h1 := hD.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma g73f_vn_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [g73f_trace_cfc_diag]
  simp

lemma g73f_wh_diag {d : ℕ} (r : Fin d → ℝ) (hr : ∑ i, r i = 1) :
    QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d
      (Matrix.diagonal (fun i => (r i : ℂ))) =
      Matrix.diagonal (fun i => ((((d:ℝ) - 1)⁻¹ * (1 - r i) : ℝ) : ℂ)) := by
  rw [g73f_wh_eq _ (by rw [Matrix.trace_diagonal]; exact_mod_cast hr)]
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply, h]

lemma g73f_isChannel_of {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Fintype K]
    (Φ : Superop ι ι) (E : K → Matrix ι ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1)
    (hΦ : ∀ ρ, Φ ρ = ∑ k, E k * ρ * (E k)ᴴ) : IsChannel Φ := by
  refine ⟨Fintype.card K, fun k => E ((Fintype.equivFin K).symm k), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← hE]
    exact Equiv.sum_comp (Fintype.equivFin K).symm (fun k => (E k)ᴴ * E k)
  · intro ρ
    rw [hΦ, krausApply]
    exact (Equiv.sum_comp (Fintype.equivFin K).symm (fun k => E k * ρ * (E k)ᴴ)).symm

lemma g73f_wh_channel {d : ℕ} (hd : 2 ≤ d) :
    IsChannel (QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d) := by
  set s : ℂ := ((Real.sqrt (1 / (2 * ((d:ℝ) - 1))) : ℝ) : ℂ) with hs
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hss : s * conj s = (((1 / (2 * ((d:ℝ) - 1))) : ℝ) : ℂ) := by
    rw [hs, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by
      have : (0:ℝ) < 2 * ((d:ℝ) - 1) := by linarith
      positivity)]
  have hdC : ((d:ℂ) - 1) ≠ 0 := by
    have : ((d:ℂ) - 1) = (((d:ℝ)-1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_ne_zero]; linarith
  have hss' : conj s * s = (((1 / (2 * ((d:ℝ) - 1))) : ℝ) : ℂ) := by rw [mul_comm]; exact hss
  apply g73f_isChannel_of _ (fun p : Fin d × Fin d =>
    s • (Matrix.single p.1 p.2 (1:ℂ) - Matrix.single p.2 p.1 1))
  · ext a b
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.single_apply, Fintype.sum_prod_type, Matrix.one_apply]
    simp only [smul_eq_mul, star_mul', star_sub, mul_sub, sub_mul, Finset.sum_sub_distrib]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ← mul_assoc, hss']
    by_cases h : a = b
    · subst h
      simp [apply_ite (starRingEnd ℂ), hss']
      field_simp
      ring
    · simp [h, Ne.symm h, apply_ite (starRingEnd ℂ)]
  · intro ρ
    ext a b
    simp only [QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo, Matrix.trace,
      Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.single_apply, Fintype.sum_prod_type, Matrix.one_apply,
      Matrix.transpose_apply, Matrix.diag_apply]
    simp only [smul_eq_mul, star_mul', star_sub, mul_sub, sub_mul, Finset.sum_sub_distrib,
      Finset.sum_mul, Finset.mul_sum]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ)]
    have key : ∀ X : ℂ, s * X * conj s = X * (((1 / (2 * ((d:ℝ) - 1))) : ℝ) : ℂ) := by
      intro X; rw [← hss]; ring
    have hK : ((d:ℂ) - 1)⁻¹ = 2 * (((1 / (2 * ((d:ℝ) - 1))) : ℝ) : ℂ) := by
      push_cast; field_simp
    simp only [key, ← Finset.sum_mul, ← Finset.mul_sum]
    by_cases h : a = b
    · subst h; simp only [if_true]; linear_combination (∑ x, ρ x x - ρ a a) * hK
    · simp only [if_neg h, if_neg (Ne.symm h)]; linear_combination (- ρ b a) * hK

lemma g73f_avg_dens {d : ℕ} (m : ℕ) (q : Fin m → ℝ) (ρ : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hq : ∀ j, 0 ≤ q j) (hs : ∑ j, q j = 1) (hρ : ∀ j, IsDensityMatrix (ρ j)) :
    IsDensityMatrix (∑ j, (q j : ℂ) • ρ j) := by
  refine ⟨Matrix.posSemidef_sum _ (fun j _ => (hρ j).1.smul (by exact_mod_cast hq j)), ?_⟩
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, (hρ _).2, smul_eq_mul, mul_one]
  exact_mod_cast hs

theorem g73f_main {d : ℕ} (hd : 2 ≤ d) :
    IsChannel (QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d) ∧
    CapacityEntropyIdentity
      (QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d) := by
  refine ⟨g73f_wh_channel hd, ?_⟩
  set W := QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d with hW
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have h1 : ((d:ℝ) - 1) ≠ 0 := by linarith
  have h1' : (-1 + (d:ℝ)) ≠ 0 := by linarith
  have hdne : (d:ℝ) ≠ 0 := by linarith
  have hc0 : 0 < ((d:ℝ) - 1)⁻¹ := inv_pos.2 (by linarith)
  have hlow : ∀ σ, IsDensityMatrix σ → Real.logb 2 ((d:ℝ) - 1) ≤ vnEntropy (W σ) := by
    intro σ hσ
    obtain ⟨μ, h0, h1, h2, h3⟩ := g73f_wh_ent σ hσ
    rw [h3]
    have := g73f_ent_ge_log _ hc0 μ h0 h1 (h2 hd)
    rwa [inv_inv] at this
  have hup : ∀ σ, IsDensityMatrix σ → vnEntropy (W σ) ≤ Real.logb 2 d := by
    intro σ hσ
    obtain ⟨μ, h0, h1, h2, h3⟩ := g73f_wh_ent σ hσ
    rw [h3]
    have := g73f_ent_le_log μ h0 (h2 hd) (by simp; omega)
    simpa using this
  let e : Fin d → Matrix (Fin d) (Fin d) ℂ := fun j =>
    Matrix.diagonal (fun i => ((if i = j then 1 else 0 : ℝ) : ℂ))
  have he_dens : ∀ j, IsDensityMatrix (e j) := by
    intro j
    refine ⟨Matrix.PosSemidef.diagonal ?_, ?_⟩
    · intro i; simp only [Pi.zero_apply]; split_ifs <;> simp
    · simp only [e, Matrix.trace_diagonal, apply_ite Complex.ofReal, Complex.ofReal_one,
        Complex.ofReal_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have he_ent : ∀ j, vnEntropy (W (e j)) = Real.logb 2 ((d:ℝ) - 1) := by
    intro j
    rw [hW, g73f_wh_diag _ (by simp), g73f_vn_diag]
    have : ∀ i, (((d:ℝ) - 1)⁻¹ * (1 - (if i = j then (1:ℝ) else 0))) *
        Real.logb 2 (((d:ℝ) - 1)⁻¹ * (1 - if i = j then 1 else 0)) =
        if i = j then 0 else ((d:ℝ) - 1)⁻¹ * Real.logb 2 (((d:ℝ) - 1)⁻¹) := by
      intro i; split_ifs <;> simp
    simp_rw [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
      Finset.filter_ne' Finset.univ j, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin, Nat.cast_sub (by omega), Nat.cast_one, Real.logb_inv]
    field_simp
  have havg : ∀ (q : ℝ), q = 1 / d → W (∑ j : Fin d, (q : ℂ) • e j) =
      Matrix.diagonal (fun _ => ((1 / d : ℝ) : ℂ)) := by
    intro q hq
    have : ∑ j : Fin d, (q : ℂ) • e j = Matrix.diagonal (fun _ => ((1 / d : ℝ) : ℂ)) := by
      ext a b
      simp only [e, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply]
      by_cases h : a = b
      · subst h
        simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero,
          smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hq]
      · simp [h]
    rw [this, hW, g73f_wh_diag _ (by simp; field_simp)]
    congr 1; funext i; congr 1
    field_simp
  have havg_ent : vnEntropy (Matrix.diagonal (fun _ : Fin d => ((1 / d : ℝ) : ℂ))) =
      Real.logb 2 d := by
    rw [g73f_vn_diag]
    simp [Real.logb_inv]
    field_simp
  let q : Fin d → ℝ := fun _ => 1 / d
  have hq0 : ∀ j, 0 ≤ q j := fun _ => by positivity
  have hq1 : ∑ j, q j = 1 := by simp [q]; field_simp
  have hval : vnEntropy (W (∑ j, (q j : ℂ) • e j)) - ∑ j, q j * vnEntropy (W (e j)) =
      Real.logb 2 d - Real.logb 2 ((d:ℝ) - 1) := by
    rw [havg (1 / d) rfl, havg_ent]
    simp only [he_ent]
    rw [← Finset.sum_mul, hq1, one_mul]
  have hgreat : IsGreatest {v | ∃ (m : ℕ) (q : Fin m → ℝ) (rho : Fin m → Matrix (Fin d) (Fin d) ℂ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j = 1) ∧ (∀ j, IsDensityMatrix (rho j)) ∧
      v = vnEntropy (W (∑ j, (q j : ℂ) • rho j)) - ∑ j, q j * vnEntropy (W (rho j))}
      (Real.logb 2 d - Real.logb 2 ((d:ℝ) - 1)) := by
    refine ⟨⟨d, q, e, hq0, hq1, he_dens, hval.symm⟩, ?_⟩
    rintro v ⟨m, q', ρ, h0, h1, h2, rfl⟩
    have ha := hup _ (g73f_avg_dens m q' ρ h0 h1 h2)
    have hb : ∑ j, q' j * Real.logb 2 ((d:ℝ) - 1) ≤ ∑ j, q' j * vnEntropy (W (ρ j)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hlow _ (h2 j)) (h0 j)
    rw [← Finset.sum_mul, h1, one_mul] at hb
    linarith
  have hcap : QAlgorithms.Papers.Independent.Dependency50.P45.holevoCapacity W =
      Real.logb 2 d - Real.logb 2 ((d:ℝ) - 1) := hgreat.csSup_eq
  refine ⟨e ⟨0, by omega⟩, he_dens _, fun σ hσ => (he_ent _).trans_le (hlow σ hσ), ?_, ?_⟩
  · rw [hcap, he_ent]
  · refine ⟨⟨d, q, e, hq0, hq1, he_dens⟩, ?_⟩
    rw [hcap]
    unfold QAlgorithms.Papers.Independent.Information100.P08.outputHolevo
      QAlgorithms.Papers.Independent.Information100.P08.ensembleAverage
    simp only [← Complex.coe_smul]
    exact hval


attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

/-- PDF p.2, (5): the transpose-depolarizing channel satisfies (2).
The accepted map is (Tr(X) I - transpose(X))/(d-1), so on trace-one states
it is exactly the printed formula. The denominator requires d >= 2;
the earlier accepted definition's use at d >= 3 is not imposed here. -/
theorem solution {d : ℕ} (hd : 2 ≤ d) :
    IsChannel (QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d) ∧
    CapacityEntropyIdentity
      (QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d) := by
  exact g73f_main hd


end
