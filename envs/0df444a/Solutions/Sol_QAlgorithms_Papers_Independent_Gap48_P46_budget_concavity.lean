-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P46.budget_concavity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:52:13.816215+00:00
-- url     : https://prove2.me/submissions/4b1cd7f9-8675-4bf0-b3d0-baf8ae67f853

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P46
noncomputable section

open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X7C14

lemma cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

/-- diagonal entries of a unitary conjugate of a Hermitian matrix are convex combinations
of its eigenvalues -/
lemma diag_conj {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (V : Matrix n n ℂ) (j : n) :
    ((star V * ρ * V) j j).re =
      ∑ i, Complex.normSq ((star V * (hρ.eigenvectorUnitary : Matrix n n ℂ)) j i) *
        hρ.eigenvalues i := by
  set W : Matrix n n ℂ := (hρ.eigenvectorUnitary : Matrix n n ℂ)
  have hs := hρ.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set P := star V * W
  have : star V * ρ * V = P * Matrix.diagonal (RCLike.ofReal ∘ hρ.eigenvalues) * star P := by
    conv_lhs => rw [hs]
    simp only [P, StarMul.star_mul, star_star]
    simp only [Matrix.mul_assoc]
    rfl
  rw [this]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, mul_right_comm, Complex.mul_conj]
  have e : ((RCLike.ofReal (hρ.eigenvalues i) : ℂ)) = ((hρ.eigenvalues i : ℝ) : ℂ) := rfl
  rw [e, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma unitary_row {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP : P ∈ Matrix.unitaryGroup n ℂ) (j : n) : ∑ i, Complex.normSq (P j i) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hP) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  simpa [Complex.mul_conj, Complex.normSq_apply] using h2

lemma unitary_col {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP : P ∈ Matrix.unitaryGroup n ℂ) (i : n) : ∑ j, Complex.normSq (P j i) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hP) i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  simpa [Complex.conj_mul', Complex.normSq_apply, mul_comm] using h2

/-- Peierls inequality -/
lemma peierls {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (V : Matrix n n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (hs : ∀ i, hρ.eigenvalues i ∈ s) :
    ∑ j, f ((star V * ρ * V) j j).re ≤ ∑ i, f (hρ.eigenvalues i) := by
  set P := star V * (hρ.eigenvectorUnitary : Matrix n n ℂ)
  have hP : P ∈ Matrix.unitaryGroup n ℂ :=
    Submonoid.mul_mem _ (Unitary.star_mem hV) hρ.eigenvectorUnitary.2
  calc ∑ j, f ((star V * ρ * V) j j).re
      ≤ ∑ j, ∑ i, Complex.normSq (P j i) * f (hρ.eigenvalues i) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [diag_conj hρ V j]
        have := hf.map_sum_le (t := Finset.univ) (w := fun i => Complex.normSq (P j i))
          (p := hρ.eigenvalues) (fun i _ => Complex.normSq_nonneg _) (unitary_row P hP j)
          (fun i _ => hs i)
        simpa [smul_eq_mul] using this
    _ = ∑ i, f (hρ.eigenvalues i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, unitary_col P hP i, one_mul]

lemma convex_g : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun x : ℝ => x * Real.logb 2 x) := by
  have h := Real.convexOn_mul_log.smul (c := (Real.log 2)⁻¹) (by positivity)
  have e : (fun x : ℝ => x * Real.logb 2 x) = (Real.log 2)⁻¹ • (fun x : ℝ => x * Real.log x) := by
    funext x; simp only [Real.logb, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]; exact h

lemma vn_eq {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    vnEntropy ρ = -∑ i, hρ.eigenvalues i * Real.logb 2 (hρ.eigenvalues i) := by
  unfold vnEntropy; rw [cfc_trace hρ]; simp

lemma diag_eig {n : Type*} [Fintype n] [DecidableEq n] {σ : Matrix n n ℂ} (hσ : σ.IsHermitian)
    (j : n) : ((star (hσ.eigenvectorUnitary : Matrix n n ℂ) * σ *
      (hσ.eigenvectorUnitary : Matrix n n ℂ)) j j).re = hσ.eigenvalues j := by
  have h := hσ.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply] at h
  have h2 := congrFun (congrFun h j) j
  simp only [Unitary.coe_star, star_star] at h2
  rw [h2, Matrix.diagonal_apply_eq]
  rfl

lemma diag_nonneg {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (V : Matrix n n ℂ) (j : n) : 0 ≤ ((star V * ρ * V) j j).re := by
  rw [diag_conj hρ.isHermitian V j]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Complex.normSq_nonneg _) (hρ.eigenvalues_nonneg i)

/-- concavity of von Neumann entropy on PSD matrices -/
lemma vn_concave {n : Type*} [Fintype n] [DecidableEq n] {ρ₁ ρ₂ : Matrix n n ℂ}
    (h₁ : ρ₁.PosSemidef) (h₂ : ρ₂.PosSemidef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * vnEntropy ρ₁ + b * vnEntropy ρ₂ ≤ vnEntropy ((a : ℂ) • ρ₁ + (b : ℂ) • ρ₂) := by
  have hσ : ((a : ℂ) • ρ₁ + (b : ℂ) • ρ₂).IsHermitian := by
    have := ((h₁.smul (show (0:ℂ) ≤ (a:ℂ) by exact_mod_cast ha)).add
      (h₂.smul (show (0:ℂ) ≤ (b:ℂ) by exact_mod_cast hb)))
    exact this.isHermitian
  set V : Matrix n n ℂ := (hσ.eigenvectorUnitary : Matrix n n ℂ)
  have hV : V ∈ Matrix.unitaryGroup n ℂ := hσ.eigenvectorUnitary.2
  set g : ℝ → ℝ := fun x => x * Real.logb 2 x
  rw [vn_eq h₁.isHermitian, vn_eq h₂.isHermitian, vn_eq hσ]
  have hsplit : ∀ j, hσ.eigenvalues j = a * ((star V * ρ₁ * V) j j).re + b * ((star V * ρ₂ * V) j j).re := by
    intro j
    rw [← diag_eig hσ j]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
    rfl
  have key : ∑ j, g (hσ.eigenvalues j) ≤
      a * ∑ i, g (h₁.isHermitian.eigenvalues i) + b * ∑ i, g (h₂.isHermitian.eigenvalues i) := by
    calc ∑ j, g (hσ.eigenvalues j)
        ≤ ∑ j, (a * g ((star V * ρ₁ * V) j j).re + b * g ((star V * ρ₂ * V) j j).re) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hsplit j]
          have := convex_g.2 (show ((star V * ρ₁ * V) j j).re ∈ Set.Ici (0:ℝ) from diag_nonneg h₁ V j)
            (show ((star V * ρ₂ * V) j j).re ∈ Set.Ici (0:ℝ) from diag_nonneg h₂ V j) ha hb hab
          simpa [smul_eq_mul, g] using this
      _ = a * ∑ j, g ((star V * ρ₁ * V) j j).re + b * ∑ j, g ((star V * ρ₂ * V) j j).re := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (peierls h₁.isHermitian V hV convex_g (fun i => h₁.eigenvalues_nonneg i)) ha)
            (mul_le_mul_of_nonneg_left (peierls h₂.isHermitian V hV convex_g (fun i => h₂.eigenvalues_nonneg i)) hb)
  simp only [g] at key
  linarith

lemma term_le (D μ : ℝ) (hD : 0 < D) (hμ : 0 ≤ μ) :
    -(μ * Real.log μ) - μ * Real.log D ≤ 1 / D - μ := by
  rcases hμ.eq_or_lt with h | h
  · subst h; simp; positivity
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (D * μ) by positivity)
    rw [one_div, Real.log_inv, Real.log_mul hD.ne' h.ne'] at h1
    have h2 : μ * ((D * μ)⁻¹ - 1) = 1 / D - μ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 h.le]

lemma ent_le_log {n : Type*} [Fintype n] (μ : n → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hs : ∑ i, μ i = 1) (hn : 0 < Fintype.card n) :
    -∑ i, μ i * Real.logb 2 (μ i) ≤ Real.logb 2 (Fintype.card n) := by
  have hD : (0:ℝ) < Fintype.card n := by exact_mod_cast hn
  have key : ∑ i, (-(μ i * Real.log (μ i)) - μ i * Real.log (Fintype.card n)) ≤
      ∑ _i : n, (1 / (Fintype.card n : ℝ)) - ∑ i, μ i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => term_le _ _ hD (hμ i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at key
  rw [mul_one_div_cancel hD.ne'] at key
  simp only [Real.logb, ← Finset.sum_neg_distrib]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : ∑ i, -(μ i * (Real.log (μ i) / Real.log 2)) = (∑ i, -(μ i * Real.log (μ i))) / Real.log 2 := by
    rw [Finset.sum_div]; congr 1; ext i; ring
  rw [this, div_le_div_iff_of_pos_right hl]
  linarith

lemma ent_bounds {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : Matrix n n ℂ) (h : IsDensityMatrix ρ) :
    0 ≤ vnEntropy ρ ∧ vnEntropy ρ ≤ Real.logb 2 (Fintype.card n) := by
  have hH := h.1.isHermitian
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [h.2] at this
    have h2 := congrArg Complex.re this
    simp at h2
    exact_mod_cast h2.symm
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => h.1.eigenvalues_nonneg i
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := fun i => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  rw [vn_eq hH]
  constructor
  · rw [neg_nonneg]; apply Finset.sum_nonpos; intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (hnn i) (Real.logb_nonpos (by norm_num) (hnn i) (hle i))
  · exact ent_le_log _ hnn hsum Fintype.card_pos

lemma kraus_density {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] {m : ℕ}
    (E : Fin m → Matrix κ ι ℂ) (hE : IsKrausFamily E) (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (krausApply E ρ) := by
  refine ⟨Matrix.posSemidef_sum _ fun j _ => hρ.1.mul_mul_conjTranspose_same (E j), ?_⟩
  unfold krausApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) ρ]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  rw [show (∑ j, (E j)ᴴ * E j) = 1 from hE, one_mul, hρ.2]

lemma kraus_lin {ι κ : Type*} [Fintype ι] {m : ℕ} (E : Fin m → Matrix κ ι ℂ) (a b : ℝ)
    (X Y : Matrix ι ι ℂ) :
    krausApply E (a • X + b • Y) = a • krausApply E X + b • krausApply E Y := by
  unfold krausApply
  simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, Finset.smul_sum,
    Matrix.mul_smul, Matrix.smul_mul]

lemma sup2 {S T : Set ℝ} (hS : S.Nonempty) (hT : T.Nonempty) (hSb : BddAbove S) (hTb : BddAbove T)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (h : ∀ x ∈ S, ∀ y ∈ T, a * x + b * y ≤ c) :
    a * sSup S + b * sSup T ≤ c := by
  have h1 : ∀ y ∈ T, a * sSup S + b * y ≤ c := by
    intro y hy
    have : sSup S ≤ (c - b * y) / a := csSup_le hS fun x hx => by
      rw [le_div_iff₀ ha]; linarith [h x hx y hy]
    rw [le_div_iff₀ ha] at this; linarith
  have : sSup T ≤ (c - a * sSup S) / b := csSup_le hT fun y hy => by
    rw [le_div_iff₀ hb]; linarith [h1 y hy]
  rw [le_div_iff₀ hb] at this; linarith

end X7C14

end

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo mixedRoof)

namespace X7C14B

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P46 X7C14

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

lemma avg_density (e : Ensemble I) : IsDensityMatrix (ensembleAverage e) := by
  unfold ensembleAverage
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  refine ⟨Matrix.posSemidef_sum _ (fun j _ => (e.density j).1.smul (Complex.zero_le_real.mpr (e.nonneg j))), ?_⟩
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, (e.density _).2, smul_eq_mul, mul_one]
  have h := congrArg (fun r : ℝ => (r : ℂ)) e.total
  simp only [Complex.ofReal_sum, Complex.ofReal_one] at h
  exact h

lemma chan_density [Nonempty O] (Phi : Superop I O) (hPhi : IsChannel Phi) (ρ : Matrix I I ℂ)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (Phi ρ) := by
  obtain ⟨m, E, hE, hPhiE⟩ := hPhi
  rw [hPhiE]; exact kraus_density E hE ρ hρ

lemma holevo_le [Nonempty O] (Phi : Superop I O) (hPhi : IsChannel Phi) (e : Ensemble I) :
    outputHolevo Phi e ≤ Real.logb 2 (Fintype.card O) := by
  unfold outputHolevo
  have h1 := (ent_bounds _ (chan_density Phi hPhi _ (avg_density e))).2
  have h2 : 0 ≤ ∑ x, e.prob x * vnEntropy (Phi (e.state x)) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (e.nonneg x)
      (ent_bounds _ (chan_density Phi hPhi _ (e.density x))).1
  linarith

lemma log_nonneg' [Nonempty O] : 0 ≤ Real.logb 2 (Fintype.card O) :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos)

lemma fmc_le [Nonempty O] (Phi : Superop I O) (hPhi : IsChannel Phi) (ρ : Matrix I I ℂ) :
    fixedMeanChi Phi ρ ≤ Real.logb 2 (Fintype.card O) := by
  unfold fixedMeanChi
  refine Real.sSup_le ?_ log_nonneg'
  rintro v ⟨e, -, rfl⟩
  exact holevo_le Phi hPhi e

lemma le_fmc [Nonempty O] (Phi : Superop I O) (hPhi : IsChannel Phi) (e : Ensemble I) :
    outputHolevo Phi e ≤ fixedMeanChi Phi (ensembleAverage e) := by
  unfold fixedMeanChi
  refine le_csSup ⟨Real.logb 2 (Fintype.card O), ?_⟩ ⟨e, rfl, rfl⟩
  rintro v ⟨e', -, rfl⟩
  exact holevo_le Phi hPhi e'

lemma single_avg (ρ : Matrix I I ℂ) (hρ : IsDensityMatrix ρ) :
    ensembleAverage (singletonMixedEnsemble ρ hρ) = ρ := by
  change (∑ _ : Fin 1, (1 : ℝ) • ρ) = ρ
  simp

/-- mixing two ensembles -/
lemma holevo_mix [Nonempty O] (Phi : Superop I O) (hPhi : IsChannel Phi) (e1 e2 : Ensemble I)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∃ e : Ensemble I, ensembleAverage e = a • ensembleAverage e1 + b • ensembleAverage e2 ∧
      a * outputHolevo Phi e1 + b * outputHolevo Phi e2 ≤ outputHolevo Phi e := by
  let e : Ensemble I :=
    { size := e1.size + e2.size
      prob := Fin.append (fun x => a * e1.prob x) (fun x => b * e2.prob x)
      state := Fin.append e1.state e2.state
      nonneg := by
        intro x
        refine Fin.addCases (fun i => ?_) (fun i => ?_) x
        · simp only [Fin.append_left]; exact mul_nonneg ha (e1.nonneg i)
        · simp only [Fin.append_right]; exact mul_nonneg hb (e2.nonneg i)
      total := by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right, ← Finset.mul_sum, e1.total, e2.total]
        linarith
      density := by
        intro x
        refine Fin.addCases (fun i => ?_) (fun i => ?_) x
        · simp only [Fin.append_left]; exact e1.density i
        · simp only [Fin.append_right]; exact e2.density i }
  have havg : ensembleAverage e = a • ensembleAverage e1 + b • ensembleAverage e2 := by
    unfold ensembleAverage
    show ∑ x, (Fin.append (fun x => a * e1.prob x) (fun x => b * e2.prob x) x) •
      (Fin.append e1.state e2.state x) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.smul_sum, smul_smul]
  refine ⟨e, havg, ?_⟩
  obtain ⟨m, E, hE, hPhiE⟩ := hPhi
  have hd1 := chan_density Phi ⟨m, E, hE, hPhiE⟩ _ (avg_density e1)
  have hd2 := chan_density Phi ⟨m, E, hE, hPhiE⟩ _ (avg_density e2)
  have hconc := vn_concave hd1.1 hd2.1 ha hb hab
  have hlin : Phi (ensembleAverage e) = (a : ℂ) • Phi (ensembleAverage e1) + (b : ℂ) • Phi (ensembleAverage e2) := by
    rw [havg, hPhiE, hPhiE, hPhiE, kraus_lin, RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.real_smul_eq_coe_smul (K := ℂ) b]
    rfl
  unfold outputHolevo
  rw [hlin]
  have hsum : ∑ x, e.prob x * vnEntropy (Phi (e.state x)) =
      a * ∑ x, e1.prob x * vnEntropy (Phi (e1.state x)) +
      b * ∑ x, e2.prob x * vnEntropy (Phi (e2.state x)) := by
    show ∑ x, (Fin.append (fun x => a * e1.prob x) (fun x => b * e2.prob x) x) *
      vnEntropy (Phi (Fin.append e1.state e2.state x)) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.mul_sum, mul_assoc]
  rw [hsum]
  nlinarith [hconc]

lemma fmc_concave [Nonempty O] (Phi : Superop I O) (hPhi : IsChannel Phi) (ρ1 ρ2 : Matrix I I ℂ)
    (h1 : IsDensityMatrix ρ1) (h2 : IsDensityMatrix ρ2) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) :
    a * fixedMeanChi Phi ρ1 + b * fixedMeanChi Phi ρ2 ≤ fixedMeanChi Phi (a • ρ1 + b • ρ2) := by
  unfold fixedMeanChi
  have bdd : ∀ ρ : Matrix I I ℂ, BddAbove {v | ∃ e : Ensemble I, ensembleAverage e = ρ ∧ v = outputHolevo Phi e} :=
    fun ρ => ⟨Real.logb 2 (Fintype.card O), by rintro v ⟨e', -, rfl⟩; exact holevo_le Phi hPhi e'⟩
  have ne : ∀ ρ : Matrix I I ℂ, IsDensityMatrix ρ →
      Set.Nonempty {v | ∃ e : Ensemble I, ensembleAverage e = ρ ∧ v = outputHolevo Phi e} :=
    fun ρ hρ => ⟨outputHolevo Phi (singletonMixedEnsemble ρ hρ), singletonMixedEnsemble ρ hρ,
      single_avg ρ hρ, rfl⟩
  refine sup2 (ne ρ1 h1) (ne ρ2 h2) (bdd _) (bdd _) ha hb ?_
  rintro x ⟨e1, he1, rfl⟩ y ⟨e2, he2, rfl⟩
  obtain ⟨e, hea, hle⟩ := holevo_mix Phi hPhi e1 e2 ha.le hb.le hab
  refine hle.trans (le_csSup (bdd _) ⟨e, ?_, rfl⟩)
  rw [hea, he1, he2]

lemma lin_mono (A : Matrix I I ℂ) {α β : ℝ} (h : α ≤ β) : linearConstraint A α ⊆ linearConstraint A β :=
  fun _ hρ => ⟨hρ.1, hρ.2.trans h⟩

lemma density_mix {ρ1 ρ2 : Matrix I I ℂ} (h1 : IsDensityMatrix ρ1) (h2 : IsDensityMatrix ρ2)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : IsDensityMatrix (a • ρ1 + b • ρ2) := by
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  refine ⟨(h1.1.smul (Complex.zero_le_real.mpr ha)).add (h2.1.smul (Complex.zero_le_real.mpr hb)), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, h1.2, h2.2]
  simp only [smul_eq_mul, mul_one]
  have h := congrArg (fun r : ℝ => (r : ℂ)) hab
  simp only [Complex.ofReal_add, Complex.ofReal_one] at h
  exact h

lemma effect_mix (A ρ1 ρ2 : Matrix I I ℂ) (a b : ℝ) :
    effectProb A (a • ρ1 + b • ρ2) = a * effectProb A ρ1 + b * effectProb A ρ2 := by
  unfold effectProb
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]

lemma lin_mix (A : Matrix I I ℂ) {α β : ℝ} {ρ1 ρ2 : Matrix I I ℂ} (h1 : ρ1 ∈ linearConstraint A α)
    (h2 : ρ2 ∈ linearConstraint A β) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • ρ1 + b • ρ2 ∈ linearConstraint A (a * α + b * β) := by
  refine ⟨density_mix h1.1 h2.1 ha hb hab, ?_⟩
  rw [effect_mix]
  have := h1.2; have := h2.2
  nlinarith [mul_le_mul_of_nonneg_left h1.2 ha, mul_le_mul_of_nonneg_left h2.2 hb]

lemma bddF [Nonempty O] (Phi : Superop I O) (hPhi : IsChannel Phi) (S : Set (Matrix I I ℂ)) :
    BddAbove (fixedMeanChi Phi '' S) :=
  ⟨Real.logb 2 (Fintype.card O), by rintro v ⟨ρ, -, rfl⟩; exact fmc_le Phi hPhi ρ⟩

lemma main [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    let f := fun alpha => constrainedChiCapacity Phi (linearConstraint A alpha)
    MonotoneOn f (budgetDomain A) ∧ ConcaveOn ℝ (budgetDomain A) f ∧
      ∀ n : ℕ, 1 ≤ n → ∀ alpha ∈ budgetDomain A,
        (fun _ : Fin n => alpha) ∈ blockAllocations A n alpha ∧
        (∑ i : Fin n, f alpha) = (n : ℝ) * f alpha ∧
        MaximizesValue (blockAllocations A n alpha) (fun a => ∑ i, f (a i)) ((n : ℝ) * f alpha) := by
  intro f
  have hmono : MonotoneOn f (budgetDomain A) := by
    intro α hα β hβ hle
    exact csSup_le_csSup (bddF Phi hPhi _) (hα.2.image _) (Set.image_mono (lin_mono A hle))
  have hconvex : Convex ℝ (budgetDomain A) := by
    intro α hα β hβ a b ha hb hab
    obtain ⟨ρ1, h1⟩ := hα.2
    obtain ⟨ρ2, h2⟩ := hβ.2
    refine ⟨?_, _, lin_mix A h1 h2 ha hb hab⟩
    simp only [smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hα.1) (mul_nonneg hb hβ.1)
  have hconc : ConcaveOn ℝ (budgetDomain A) f := by
    refine ⟨hconvex, ?_⟩
    intro α hα β hβ a b ha hb hab
    simp only [smul_eq_mul]
    rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0
      have : b = 1 := by linarith
      subst this; simp
    rcases hb.eq_or_lt with hb0 | hb0
    · subst hb0
      have : a = 1 := by linarith
      subst this; simp
    show a * sSup _ + b * sSup _ ≤ sSup _
    refine sup2 (hα.2.image _) (hβ.2.image _) (bddF Phi hPhi _) (bddF Phi hPhi _) ha0 hb0 ?_
    rintro x ⟨ρ1, h1, rfl⟩ y ⟨ρ2, h2, rfl⟩
    refine (fmc_concave Phi hPhi ρ1 ρ2 h1.1 h2.1 ha0 hb0 hab).trans ?_
    exact le_csSup (bddF Phi hPhi _) ⟨_, lin_mix A h1 h2 ha hb hab, rfl⟩
  refine ⟨hmono, hconc, ?_⟩
  intro n hn α hα
  have hmem : (fun _ : Fin n => α) ∈ blockAllocations A n α := ⟨fun _ => hα, by simp⟩
  refine ⟨hmem, by simp, ⟨fun _ => α, hmem, by simp⟩, ?_⟩
  rintro v ⟨a, ha, rfl⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hj := hconc.le_map_sum (t := Finset.univ) (w := fun _ : Fin n => (1 / (n : ℝ)))
    (p := a) (fun _ _ => by positivity) (by simp; field_simp) (fun i _ => ha.1 i)
  have hs : ∑ i, (1 / (n : ℝ)) • a i = α := by
    rw [← Finset.smul_sum, ha.2, smul_eq_mul]; field_simp
  rw [hs] at hj
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hnpos] at hj
  linarith

end X7C14B

end

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo mixedRoof)

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P46 in
theorem solution [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    let f := fun alpha => constrainedChiCapacity Phi (linearConstraint A alpha)
    MonotoneOn f (budgetDomain A) ∧ ConcaveOn ℝ (budgetDomain A) f ∧
      ∀ n : ℕ, 1 ≤ n → ∀ alpha ∈ budgetDomain A,
        (fun _ : Fin n => alpha) ∈ blockAllocations A n alpha ∧
        (∑ i : Fin n, f alpha) = (n : ℝ) * f alpha ∧
        MaximizesValue (blockAllocations A n alpha) (fun a => ∑ i, f (a i)) ((n : ℝ) * f alpha) :=
  X7C14B.main Phi hPhi A hA

end
