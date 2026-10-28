-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P01.cloner_capacity_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:34:08.636594+00:00
-- url     : https://prove2.me/submissions/a0e99a84-7370-4f31-8c3c-bb530b9402ce

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace S197cap
open Matrix QAlgorithms Polynomial Finset
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel dilationPower)
open QAlgorithms.Papers.Independent.Information100.P22
  (coherentInformation densityPurification)
open QAlgorithms.Papers.Independent.Support50.P01 (clonerDilation cloningCoefficient)

/-! ### Entropy toolkit -/

lemma vn_eig {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    vnEntropy X = -∑ i, hX.eigenvalues i * Real.logb 2 (hX.eigenvalues i) := by
  unfold vnEntropy
  rw [hX.cfc_eq, IsHermitian.cfc]
  have hU := hX.eigenvectorUnitary.2
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.one_mul, trace_diagonal]
  simp

lemma ent_bounds {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (X : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (ht : X.trace = 1) : 0 ≤ vnEntropy X ∧ vnEntropy X ≤ Real.logb 2 (Fintype.card ι) := by
  rw [vn_eig X hX.1]
  set l := hX.1.eigenvalues with hldef
  have hl0 : ∀ i, 0 ≤ l i := hX.eigenvalues_nonneg
  have hl1 : ∑ i, l i = 1 := by
    have h := hX.1.trace_eq_sum_eigenvalues
    rw [ht] at h
    have h' : ((∑ i, l i : ℝ) : ℂ) = 1 := by push_cast; exact h.symm
    exact_mod_cast h'
  have hle : ∀ i, l i ≤ 1 := fun i => by
    rw [← hl1]; exact Finset.single_le_sum (fun j _ => hl0 j) (Finset.mem_univ i)
  have hrw : -∑ i, l i * Real.logb 2 (l i) = (∑ i, Real.negMulLog (l i)) / Real.log 2 := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.negMulLog, Real.logb]; ring
  rw [hrw]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (hl0 i) (hle i)) hlog2.le
  · rw [Real.logb, div_le_div_iff_of_pos_right hlog2]
    have hne : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hl1
    have hd : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun _ => (Fintype.card ι : ℝ)⁻¹)
      (p := l) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
      (fun i _ => Set.mem_Ici.mpr (hl0 i))
    simp only [smul_eq_mul, ← Finset.mul_sum, hl1, mul_one] at hJ
    rw [Real.negMulLog, Real.log_inv] at hJ
    have := mul_le_mul_of_nonneg_left hJ hd.le
    have h2 : (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, Real.negMulLog (l i)) =
        ∑ i, Real.negMulLog (l i) := by field_simp
    have h3 : (Fintype.card ι : ℝ) * (-(Fintype.card ι : ℝ)⁻¹ * -Real.log (Fintype.card ι)) =
        Real.log (Fintype.card ι) := by field_simp
    linarith

lemma vn_scalar {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (c : ℝ) (hc : c * Fintype.card ι = 1) :
    vnEntropy ((c : ℂ) • (1 : Matrix ι ι ℂ)) = Real.logb 2 (Fintype.card ι) := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hc; exact zero_ne_one hc
  have hc' : c = (Fintype.card ι : ℝ)⁻¹ := eq_inv_of_mul_eq_one_left hc
  have e : ((c : ℂ) • (1 : Matrix ι ι ℂ)) = algebraMap ℝ (Matrix ι ι ℂ) c := by
    rw [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
  unfold vnEntropy
  rw [e, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, trace_smul, trace_one]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  rw [hc', Real.logb_inv]
  field_simp

lemma S197C_spec_finite {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (spectrum ℝ A).Finite := by
  rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _

lemma S197C_vn_poly {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (p : ℝ[X])
    (hp : ∀ x ∈ spectrum ℝ A, p.eval x = x * Real.logb 2 x) :
    QAlgorithms.vnEntropy A = -(aeval A p).trace.re := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x hx).symm),
    cfc_polynomial p A hA.isSelfAdjoint]

def S197C_interp (s : Finset ℝ) : ℝ[X] :=
  Lagrange.interpolate s id (fun x => x * Real.logb 2 x)

lemma S197C_interp_eval (s : Finset ℝ) {x : ℝ} (hx : x ∈ s) :
    (S197C_interp s).eval x = x * Real.logb 2 x :=
  Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx

lemma S197C_vn_conj {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy (A.map (starRingEnd ℂ)) = QAlgorithms.vnEntropy A := by
  set s := (S197C_spec_finite A hA).toFinset
  set φ : Matrix ι ι ℂ ≃ₐ[ℝ] Matrix ι ι ℂ := AlgEquiv.mapMatrix Complex.conjAe
  have hφ : A.map (starRingEnd ℂ) = φ A := rfl
  have hspec : spectrum ℝ (A.map (starRingEnd ℂ)) = spectrum ℝ A := by
    rw [hφ]; exact AlgEquiv.spectrum_eq _ _
  have hH : (A.map (starRingEnd ℂ)).IsHermitian := by
    ext i j; have := congrFun (congrFun hA i) j
    simp only [conjTranspose_apply, map_apply] at this ⊢
    rw [← this]; simp
  rw [S197C_vn_poly A hA (S197C_interp s) (fun x hx => S197C_interp_eval s (by simpa [s] using hx)),
    S197C_vn_poly _ hH (S197C_interp s)
      (fun x hx => S197C_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hφ, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  have htr : ∀ X : Matrix ι ι ℂ, (φ X).trace = starRingEnd ℂ X.trace := by
    intro X
    simp only [φ, AlgEquiv.mapMatrix_apply, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    rfl
  simp only [AlgEquiv.coe_toAlgHom]
  rw [htr, Complex.conj_re]

lemma S197C_pow_mul {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (N : Matrix ι κ ℂ) (k : ℕ) :
    (M * N) ^ (k + 1) = M * (N * M) ^ k * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]

lemma S197C_tr_pow {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (N : Matrix ι κ ℂ) (k : ℕ) :
    ((M * N) ^ (k + 1)).trace = ((N * M) ^ (k + 1)).trace := by
  rw [S197C_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, pow_succ]

lemma S197C_vn_mul_comm {κ ι : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (M : Matrix κ ι ℂ) :
    QAlgorithms.vnEntropy (M * Mᴴ) = QAlgorithms.vnEntropy (Mᴴ * M) := by
  have h1 : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  have h2 : (Mᴴ * M).IsHermitian := isHermitian_conjTranspose_mul_self M
  set s : Finset ℝ := insert 0 ((S197C_spec_finite (inst := inst') _ h1).toFinset ∪
    (S197C_spec_finite (inst := inst) _ h2).toFinset)
  set p := S197C_interp s
  rw [S197C_vn_poly _ h1 p (fun x hx => S197C_interp_eval s (by simp [s, hx])),
    S197C_vn_poly _ h2 p (fun x hx => S197C_interp_eval s (by simp [s, hx]))]
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, S197C_interp_eval s (by simp [s])]; simp
  congr 2
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.trace_sum,
    Matrix.trace_sum, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [h0, zero_smul, Matrix.trace_zero, add_zero, Matrix.trace_smul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [S197C_tr_pow]

/-! ### Partial traces -/

lemma tR_psd {α β : Type*} [Fintype α] [Fintype β] (X : Matrix (α × β) (α × β) ℂ)
    (h : X.PosSemidef) : (traceRight X).PosSemidef := by
  have : traceRight X = ∑ e : β, X.submatrix (fun a => (a, e)) (fun a => (a, e)) := by
    ext i j; simp [traceRight, Matrix.sum_apply]
  rw [this]; exact posSemidef_sum _ fun e _ => h.submatrix _

lemma tL_psd {α β : Type*} [Fintype α] [Fintype β] (X : Matrix (α × β) (α × β) ℂ)
    (h : X.PosSemidef) : (traceLeft X).PosSemidef := by
  have : traceLeft X = ∑ a : α, X.submatrix (fun b => (a, b)) (fun b => (a, b)) := by
    ext i j; simp [traceLeft, Matrix.sum_apply]
  rw [this]; exact posSemidef_sum _ fun e _ => h.submatrix _

lemma tR_trace {α β : Type*} [Fintype α] [Fintype β] (X : Matrix (α × β) (α × β) ℂ) :
    (traceRight X).trace = X.trace := by
  simp [Matrix.trace, traceRight, Fintype.sum_prod_type]

lemma tL_trace {α β : Type*} [Fintype α] [Fintype β] (X : Matrix (α × β) (α × β) ℂ) :
    (traceLeft X).trace = X.trace := by
  simp only [Matrix.trace, traceLeft, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-! ### Channels from isometries -/

section chan
variable {A B E : Type*} [Fintype A] {iA : DecidableEq A} [Fintype B] {iB : DecidableEq B}
  [Fintype E] {iE : DecidableEq E}

lemma recv_density (W : Matrix (B × E) A ℂ) (hW : Wᴴ * W = 1) (ρ : Matrix A A ℂ)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (receiverChannel W ρ) := by
  refine ⟨tR_psd _ (hρ.1.mul_mul_conjTranspose_same W), ?_⟩
  show (traceRight (W * ρ * Wᴴ)).trace = 1
  rw [tR_trace, Matrix.trace_mul_cycle, hW, Matrix.one_mul, hρ.2]

lemma compl_density (W : Matrix (B × E) A ℂ) (hW : Wᴴ * W = 1) (ρ : Matrix A A ℂ)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (complementaryChannel W ρ) := by
  refine ⟨tL_psd _ (hρ.1.mul_mul_conjTranspose_same W), ?_⟩
  show (traceLeft (W * ρ * Wᴴ)).trace = 1
  rw [tL_trace, Matrix.trace_mul_cycle, hW, Matrix.one_mul, hρ.2]

lemma sqrt_facts (ρ : Matrix A A ℂ) (hρ : ρ.PosSemidef) :
    (cfc Real.sqrt ρ)ᴴ = cfc Real.sqrt ρ ∧ cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ := by
  refine ⟨(cfc_predicate Real.sqrt ρ : IsSelfAdjoint _), ?_⟩
  rw [← cfc_mul Real.sqrt Real.sqrt ρ]
  have : cfc (fun x => Real.sqrt x * Real.sqrt x) ρ = cfc (id : ℝ → ℝ) ρ := by
    apply cfc_congr
    intro x hx
    rw [hρ.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Real.mul_self_sqrt (hρ.eigenvalues_nonneg i)
  rw [this, cfc_id ℝ ρ hρ.1.isSelfAdjoint]

def Cm (W : Matrix (B × E) A ℂ) (S : Matrix A A ℂ) : Matrix (A × B) E ℂ :=
  Matrix.of fun p e => ∑ a, W (p.2, e) a * S a p.1

lemma joint_eq (W : Matrix (B × E) A ℂ) (ρ : Matrix A A ℂ) :
    idTensorSuperop (R := A) (receiverChannel W) (pureDensity (densityPurification ρ)) =
      Cm W (cfc Real.sqrt ρ) * (Cm W (cfc Real.sqrt ρ))ᴴ := by
  ext p q
  simp only [idTensorSuperop, receiverChannel, traceRight, pureDensity, densityPurification,
    Matrix.of_apply, Matrix.mul_apply, conjTranspose_apply, Cm, PiLp.toLp_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, Complex.star_def, map_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma compl_eq (W : Matrix (B × E) A ℂ) (ρ : Matrix A A ℂ) (hρ : ρ.PosSemidef) :
    complementaryChannel W ρ =
      ((Cm W (cfc Real.sqrt ρ))ᴴ * Cm W (cfc Real.sqrt ρ)).map (starRingEnd ℂ) := by
  have hS := sqrt_facts (iA := iA) ρ hρ
  set S := cfc Real.sqrt ρ with hSdef
  have e : ρ = S * Sᴴ := by rw [hS.1, hS.2]
  rw [show complementaryChannel W ρ = complementaryChannel W (S * Sᴴ) by rw [← e]]
  ext u v
  simp only [complementaryChannel, traceLeft, Cm, Matrix.of_apply, Matrix.mul_apply,
    conjTranspose_apply, Matrix.map_apply, Fintype.sum_prod_type]
  simp only [star_sum, map_sum, Finset.sum_mul, Finset.mul_sum, Complex.star_def, map_mul,
    Complex.conj_conj]
  conv_lhs => enter [2, b, 2, a']; rw [Finset.sum_comm]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun a _ => by ring

lemma coh_eq (W : Matrix (B × E) A ℂ) (ρ : Matrix A A ℂ) (hρ : ρ.PosSemidef) :
    coherentInformation (receiverChannel W) ρ =
      vnEntropy (receiverChannel W ρ) - vnEntropy (complementaryChannel W ρ) := by
  unfold coherentInformation
  rw [joint_eq, compl_eq W ρ hρ, S197C_vn_conj _ (isHermitian_conjTranspose_mul_self _),
    S197C_vn_mul_comm]

lemma coh_le (W : Matrix (B × E) A ℂ) (hW : Wᴴ * W = 1) (ρ : Matrix A A ℂ)
    (hρ : IsDensityMatrix ρ) :
    coherentInformation (receiverChannel W) ρ ≤ Real.logb 2 (Fintype.card B) := by
  let iE : DecidableEq E := Classical.decEq E
  rw [coh_eq (iE := iE) W ρ hρ.1]
  have h1 : vnEntropy (receiverChannel W ρ) ≤ Real.logb 2 (Fintype.card B) :=
    (ent_bounds _ (recv_density W hW ρ hρ).1 (recv_density W hW ρ hρ).2).2
  have h2 : 0 ≤ vnEntropy (complementaryChannel W ρ) :=
    (ent_bounds _ (compl_density W hW ρ hρ).1 (compl_density W hW ρ hρ).2).1
  linarith

lemma dil_iso (U : Matrix (B × E) A ℂ) (hU : Uᴴ * U = 1) (n : ℕ) :
    (dilationPower U n)ᴴ * dilationPower U n = 1 := by
  ext x x'
  rw [mul_apply]
  simp only [conjTranspose_apply, dilationPower]
  have key : ∀ i, ∑ q : B × E, star (U q (x i)) * U q (x' i) = (1 : Matrix A A ℂ) (x i) (x' i) :=
    fun i => by rw [← hU, mul_apply]; rfl
  calc ∑ p : (Fin n → B) × (Fin n → E),
        star (∏ i, U (p.1 i, p.2 i) (x i)) * ∏ i, U (p.1 i, p.2 i) (x' i)
      = ∑ f : Fin n → B × E, ∏ i, (star (U (f i) (x i)) * U (f i) (x' i)) := by
        rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => B) (fun _ => E)).sum_comp]
        refine Finset.sum_congr rfl fun f _ => ?_
        simp only [Complex.star_def, map_prod, Finset.prod_mul_distrib]
        rfl
    _ = ∏ i, ∑ q : B × E, star (U q (x i)) * U q (x' i) := (Fintype.prod_sum (fun i (q : B × E) => star (U q (x i)) * U q (x' i))).symm
    _ = ∏ i, (1 : Matrix A A ℂ) (x i) (x' i) := by simp_rw [key]
    _ = (1 : Matrix (Fin n → A) (Fin n → A) ℂ) x x' := by
        by_cases h : x = x'
        · subst h; simp
        · obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
            by_contra hc; push Not at hc; exact h (funext hc)
          rw [one_apply_ne h]; exact Finset.prod_eq_zero (Finset.mem_univ i) (one_apply_ne hi)

lemma pi_recv (U : Matrix (B × E) A ℂ) (n : ℕ) :
    piSuperop (fun _ : Fin n => receiverChannel U) = receiverChannel (dilationPower U n) := by
  funext X; ext y y'
  have hs : ∀ (a a' : A) (b b' : B), receiverChannel U (Matrix.single a a' 1) b b' =
      ∑ e, U (b, e) a * star (U (b', e) a') := by
    intro a a' b b'
    simp [receiverChannel, traceRight, mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq,
      ite_mul, zero_mul]
  simp only [piSuperop, Matrix.of_apply, hs, Fintype.prod_sum]
  simp only [receiverChannel, traceRight, Matrix.of_apply, mul_apply, conjTranspose_apply,
    dilationPower, Finset.mul_sum, Finset.sum_mul, Finset.prod_mul_distrib, Complex.star_def,
    map_prod]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, e]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun x' _ =>
    Finset.sum_congr rfl fun x _ => by ring

lemma sum_fin1 {T : Type*} [Fintype T] (g : (Fin 1 → T) → ℂ) :
    ∑ f, g f = ∑ t, g (fun _ => t) :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) T) _ _
    (fun f => congrArg g (funext fun i => by rw [Subsingleton.elim i default]; rfl))

lemma dil1 (U : Matrix (B × E) A ℂ) (X : Matrix A A ℂ) :
    receiverChannel (dilationPower U 1)
        (X.submatrix (Equiv.funUnique (Fin 1) A) (Equiv.funUnique (Fin 1) A)) =
      (receiverChannel U X).submatrix (Equiv.funUnique (Fin 1) B) (Equiv.funUnique (Fin 1) B) := by
  ext y y'
  simp only [receiverChannel, traceRight, Matrix.of_apply, mul_apply, conjTranspose_apply,
    dilationPower, Matrix.submatrix_apply, Equiv.funUnique_apply, Fin.prod_univ_one, sum_fin1,
    Fin.default_eq_zero]

end chan

/-! ### Combinatorics of the cloner -/

lemma upper_vand (a b L : ℕ) :
    ∑ ij ∈ antidiagonal L, (a + ij.1).choose a * (b + ij.2).choose b =
      (a + b + 1 + L).choose (a + b + 1) := by
  have h := PowerSeries.invOneSubPow_add ℤ (a + 1) (b + 1)
  rw [show a + 1 + (b + 1) = (a + b + 1) + 1 by ring] at h
  have h2 := congrArg (fun u : (PowerSeries ℤ)ˣ => PowerSeries.coeff L (u : PowerSeries ℤ)) h
  simp only [Units.val_mul, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.coeff_mul, PowerSeries.coeff_mk] at h2
  exact_mod_cast h2.symm

lemma cc_formula {N M k j : ℕ} (hk : k ≤ N) (hj : j ≤ M - N) (hNM : N ≤ M) :
    cloningCoefficient N M k j * ((M + 1).choose (N + 1) : ℝ) =
      ((k + j).choose k : ℝ) * ((M - k - j).choose (N - k) : ℝ) := by
  obtain ⟨p, rfl⟩ : ∃ p, N = k + p := ⟨N - k, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, M = k + p + j + q := ⟨M - (k + p) - j, by omega⟩
  have e1 : k + p + j + q - (k + p) = j + q := by omega
  have e2 : k + p + j + q - k - j = p + q := by omega
  have e3 : k + p - k = p := by omega
  have e4 : k + p + j + q - (k + p) - j = q := by omega
  unfold cloningCoefficient
  rw [e4, e1, e2, e3]
  have h1 : ((k + j).choose k : ℝ) * k.factorial * j.factorial = (k + j).factorial := by
    have := Nat.add_choose_mul_factorial_mul_factorial j k
    rw [add_comm j k] at this
    rw [mul_assoc, mul_comm (k.factorial : ℝ), ← mul_assoc]; exact_mod_cast this
  have h2 : ((p + q).choose p : ℝ) * p.factorial * q.factorial = (p + q).factorial := by
    have := Nat.add_choose_mul_factorial_mul_factorial q p
    rw [add_comm q p] at this
    rw [mul_assoc, mul_comm (p.factorial : ℝ), ← mul_assoc]; exact_mod_cast this
  have h3 : ((k + p + j + q + 1).choose (k + p + 1) : ℝ) * (k + p + 1).factorial *
      (j + q).factorial = (k + p + j + q + 1).factorial := by
    have := Nat.add_choose_mul_factorial_mul_factorial (j + q) (k + p + 1)
    rw [show j + q + (k + p + 1) = k + p + j + q + 1 by ring,
      show k + p + j + q + 1 = (k + p + 1) + (j + q) by ring] at this
    rw [show k + p + j + q + 1 = (k + p + 1) + (j + q) by ring]
    rw [mul_assoc, mul_comm ((k + p + 1).factorial : ℝ), ← mul_assoc]; exact_mod_cast this
  rw [← h1, ← h2, ← h3]
  have : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos _
  have : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos _
  have : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos _
  have : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos _
  have : (0 : ℝ) < (j + q).factorial := by exact_mod_cast Nat.factorial_pos _
  have : (0 : ℝ) < (k + p + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have : (0 : ℝ) < ((k + p + j + q + 1).choose (k + p + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  field_simp


lemma smul_one_sub {m l : Type*} [Fintype m] [Fintype l] {im : DecidableEq m}
    {il : DecidableEq l} (c : ℂ) (e : m ≃ l) :
    (c • (1 : Matrix l l ℂ)).submatrix e e = c • (1 : Matrix m m ℂ) := by
  rw [show (c • (1 : Matrix l l ℂ)).submatrix e e = c • ((1 : Matrix l l ℂ).submatrix e e) from rfl,
    Matrix.submatrix_one_equiv]

lemma sum_fin_ite' {m : ℕ} (t : ℕ) (x : ℝ) :
    ∑ b : Fin m, (if (b : ℕ) = t then x else 0) = if t < m then x else 0 := by
  split_ifs with ht
  · rw [Finset.sum_eq_single ⟨t, ht⟩]
    · simp
    · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h)
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun b _ => if_neg ?_
    intro h; exact ht (h ▸ b.isLt)

lemma cc_nonneg (N M k j : ℕ) : 0 ≤ cloningCoefficient N M k j := by
  unfold cloningCoefficient; positivity

lemma sum_cc {N M k : ℕ} (hk : k ≤ N) (hNM : N ≤ M) :
    ∑ j : Fin (M - N + 1), cloningCoefficient N M k j = 1 := by
  have hC : (0:ℝ) < ((M+1).choose (N+1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hnat : ∑ i ∈ range (M - N + 1), (k + i).choose k * (M - k - i).choose (N - k) =
      (M + 1).choose (N + 1) := by
    have h := upper_vand k (N - k) (M - N)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    rw [show k + (N - k) + 1 + (M - N) = M + 1 by omega,
      show k + (N - k) + 1 = N + 1 by omega] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    congr 2; omega
  have key : (∑ j : Fin (M - N + 1), cloningCoefficient N M k j) *
      ((M+1).choose (N+1) : ℝ) = ((M+1).choose (N+1) : ℝ) := by
    rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl fun (j : Fin (M-N+1)) _ =>
      cc_formula hk (Nat.lt_succ_iff.mp j.isLt) hNM]
    rw [show (∑ j : Fin (M - N + 1), ((k + (j:ℕ)).choose k : ℝ) *
        ((M - k - (j:ℕ)).choose (N - k) : ℝ)) =
        ∑ j ∈ range (M - N + 1), ((k + j).choose k : ℝ) * ((M - k - j).choose (N - k) : ℝ) from
      Fin.sum_univ_eq_sum_range (fun j => ((k + j).choose k : ℝ) *
        ((M - k - j).choose (N - k) : ℝ)) _]
    exact_mod_cast hnat
  exact (mul_eq_right₀ hC.ne').mp key

lemma iso_U {N M : ℕ} (hNM : N ≤ M) {i1 : DecidableEq (Fin (N + 1))} :
    (clonerDilation N M)ᴴ * clonerDilation N M = 1 := by
  ext k k'
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [conjTranspose_apply, clonerDilation]
  by_cases hkk : k = k'
  · subst hkk
    rw [one_apply_eq]
    have : ∀ j : Fin (M - N + 1), ∑ b : Fin (M + 1),
        star (if (b:ℕ) = k + j then (Real.sqrt (cloningCoefficient N M k j) : ℂ) else 0) *
        (if (b:ℕ) = k + j then (Real.sqrt (cloningCoefficient N M k j) : ℂ) else 0) =
        (cloningCoefficient N M k j : ℂ) := by
      intro j
      have hlt : (k:ℕ) + j < M + 1 := by have := k.isLt; have := j.isLt; omega
      have e2 : ∀ b : Fin (M + 1),
          star (if (b:ℕ) = k + j then (Real.sqrt (cloningCoefficient N M k j) : ℂ) else 0) *
          (if (b:ℕ) = k + j then (Real.sqrt (cloningCoefficient N M k j) : ℂ) else 0) =
          ((if (b:ℕ) = k + j then cloningCoefficient N M k j else 0 : ℝ) : ℂ) := by
        intro b
        split_ifs
        · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
            Real.mul_self_sqrt (cc_nonneg _ _ _ _)]
        · simp
      rw [Finset.sum_congr rfl fun b _ => e2 b, ← Complex.ofReal_sum, sum_fin_ite', if_pos hlt]
    rw [Finset.sum_congr rfl fun j _ => this j]
    exact_mod_cast sum_cc (Nat.lt_succ_iff.mp k.isLt) hNM
  · rw [one_apply_ne hkk]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h1 h2
    · exact absurd (Fin.ext (by omega)) hkk
    · simp
    · simp
    · simp

lemma diag_sum {N M : ℕ} (hNM : N ≤ M) (b : ℕ) (hb : b ≤ M) :
    (∑ k : Fin (N+1), ∑ j : Fin (M-N+1),
      if b = (k:ℕ) + j then cloningCoefficient N M k j else 0) = ((N:ℝ)+1)/((M:ℝ)+1) := by
  have hC : (0:ℝ) < ((M+1).choose (N+1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have inner : ∀ k : Fin (N+1), (∑ j : Fin (M-N+1),
      if b = (k:ℕ) + j then cloningCoefficient N M k j else 0) * ((M+1).choose (N+1) : ℝ) =
      ((b.choose k : ℕ) : ℝ) * ((M-b).choose (N-k) : ℕ) := by
    intro k
    have hk := k.isLt
    by_cases hcond : (k:ℕ) ≤ b ∧ b - k ≤ M - N
    · rw [Finset.sum_eq_single ⟨b - k, by omega⟩]
      · rw [if_pos (by simp only; omega),
          cc_formula (by omega) (by simp only; omega) hNM]
        simp only
        rw [show (k:ℕ) + (b - k) = b by omega, show M - k - (b - k) = M - b by omega]
      · intro j _ hj; rw [if_neg]; intro h; exact hj (Fin.ext (by simp only; omega))
      · simp
    · rw [Finset.sum_eq_zero (fun j _ => if_neg (by
          intro h; apply hcond; have := j.isLt; omega)), zero_mul]
      by_cases hkb : (k:ℕ) ≤ b
      · have : M - b < N - k := by omega
        rw [Nat.choose_eq_zero_of_lt this]; simp
      · rw [Nat.choose_eq_zero_of_lt (by omega : b < k)]; simp
  have vand : ∑ k : Fin (N+1), ((b.choose k : ℕ) : ℝ) * ((M-b).choose (N-k) : ℕ) =
      (M.choose N : ℝ) := by
    have := Nat.add_choose_eq b (M - b) N
    rw [Nat.add_sub_cancel' hb, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    rw [show (∑ k : Fin (N+1), ((b.choose k : ℕ) : ℝ) * ((M-b).choose (N-(k:ℕ)) : ℕ)) =
        ∑ k ∈ range (N+1), ((b.choose k : ℕ) : ℝ) * ((M-b).choose (N-k) : ℕ) from
      Fin.sum_univ_eq_sum_range (fun k => ((b.choose k : ℕ) : ℝ) * ((M-b).choose (N-k) : ℕ)) _]
    exact_mod_cast this.symm
  have hsucc : ((N:ℝ)+1) * (M+1).choose (N+1) = ((M:ℝ)+1) * M.choose N := by
    have := Nat.add_one_mul_choose_eq M N
    have h : (((M+1) * M.choose N : ℕ) : ℝ) = (((M+1).choose (N+1) * (N+1) : ℕ) : ℝ) := by
      rw [this]
    push_cast at h; linarith
  set D := ∑ k : Fin (N+1), ∑ j : Fin (M-N+1),
      if b = (k:ℕ) + j then cloningCoefficient N M k j else 0
  have hD : D * ((M+1).choose (N+1) : ℝ) = M.choose N := by
    rw [Finset.sum_mul, Finset.sum_congr rfl fun k _ => inner k, vand]
  rw [eq_div_iff (by positivity)]
  apply mul_right_cancel₀ hC.ne'
  linear_combination ((M:ℝ)+1) * hD - hsucc

lemma recv_mixed {N M : ℕ} (hNM : N ≤ M) {i1 : DecidableEq (Fin (N + 1))}
    {i2 : DecidableEq (Fin (M + 1))} :
    receiverChannel (clonerDilation N M) ((((((N:ℝ)+1)⁻¹ : ℝ)) : ℂ) • 1) =
      ((((M:ℝ)+1)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin (M+1)) (Fin (M+1)) ℂ) := by
  show traceRight (_ * (_ • 1) * _) = _
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  ext b b'
  simp only [traceRight, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply,
    conjTranspose_apply, smul_eq_mul, Matrix.one_apply, clonerDilation]
  rw [← Finset.mul_sum]
  by_cases hb : b = b'
  · subst hb
    rw [if_pos rfl, mul_one]
    have hterm : ∀ (j : Fin (M - N + 1)) (k : Fin (N + 1)),
        (if (b:ℕ) = k + j then (Real.sqrt (cloningCoefficient N M k j) : ℂ) else 0) *
        star (if (b:ℕ) = k + j then (Real.sqrt (cloningCoefficient N M k j) : ℂ) else 0) =
        ((if (b:ℕ) = k + j then cloningCoefficient N M k j else 0 : ℝ) : ℂ) := by
      intro j k
      split_ifs
      · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
          Real.mul_self_sqrt (cc_nonneg _ _ _ _)]
      · simp
    simp only [hterm]
    rw [Finset.sum_comm]
    have := diag_sum hNM b (Nat.lt_succ_iff.mp b.isLt)
    simp only [← Complex.ofReal_sum, this, ← Complex.ofReal_mul]
    congr 1
    field_simp
  · rw [if_neg hb, mul_zero]
    rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h1 h2
    · exact absurd (Fin.ext (by omega)) hb
    · simp
    · simp
    · simp

end S197cap

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter
open QAlgorithms.Papers.Independent.Support50.P01
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)
open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation quantumCapacity)
open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)
open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)
open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

theorem solution (N M : ℕ) (hN : 1≤N) (hNM : N≤M) :
    0 < quantumCapacity (receiverChannel (clonerDilation N M)) := by
  have hU := S197cap.iso_U hNM (i1 := inferInstance)
  have hlog : 0 ≤ Real.logb 2 ((M:ℝ) + 1) := Real.logb_nonneg one_lt_two (by linarith)
  have cardB : ∀ n : ℕ, Real.logb 2 (Fintype.card (Fin n → Fin (M + 1)) : ℝ) =
      n * Real.logb 2 ((M:ℝ) + 1) := by
    intro n
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rw [Real.logb_pow]
  unfold quantumCapacity
  refine lt_of_lt_of_le ?_ (le_csSup ?_ ⟨1, one_pos, rfl⟩)
  swap
  · refine ⟨Real.logb 2 ((M:ℝ) + 1), ?_⟩
    rintro _ ⟨n, hn, rfl⟩
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    unfold QAlgorithms.Papers.Independent.Information100.P22.singleUseInformation
    apply Real.sSup_le
    · rintro _ ⟨ρ, hρ, rfl⟩
      rw [S197cap.pi_recv]
      refine (S197cap.coh_le _ (S197cap.dil_iso _ hU n) ρ hρ).trans (le_of_eq ?_)
      rw [cardB]; ring
    · positivity
  rw [Nat.cast_one, div_one]
  unfold QAlgorithms.Papers.Independent.Information100.P22.singleUseInformation
  set ρ1 : Matrix (Fin 1 → Fin (N + 1)) (Fin 1 → Fin (N + 1)) ℂ :=
    ((((N:ℝ)+1)⁻¹ : ℝ) : ℂ) • 1 with hρ1def
  have hρ1 : QAlgorithms.IsDensityMatrix ρ1 := by
    refine ⟨Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by positivity)), ?_⟩
    rw [hρ1def, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin]
    push_cast
    rw [pow_one, smul_eq_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero N)
  refine lt_of_lt_of_le ?_ (le_csSup ?_ ⟨ρ1, hρ1, rfl⟩)
  swap
  · refine ⟨1 * Real.logb 2 ((M:ℝ) + 1), ?_⟩
    rintro _ ⟨ρ, hρ, rfl⟩
    rw [S197cap.pi_recv]
    refine (S197cap.coh_le _ (S197cap.dil_iso _ hU 1) ρ hρ).trans (le_of_eq ?_)
    rw [cardB]; push_cast; ring
  rw [S197cap.pi_recv, S197cap.coh_eq (iE := inferInstance) _ _ hρ1.1]
  have hsub : ρ1 = (((((N:ℝ)+1)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)).submatrix
      (Equiv.funUnique (Fin 1) (Fin (N + 1))) (Equiv.funUnique (Fin 1) (Fin (N + 1))) := by
    rw [S197cap.smul_one_sub]
  have hB : receiverChannel (dilationPower (clonerDilation N M) 1) ρ1 =
      ((((M:ℝ)+1)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin 1 → Fin (M+1)) (Fin 1 → Fin (M+1)) ℂ) := by
    rw [hsub, S197cap.dil1, S197cap.recv_mixed hNM (i2 := inferInstance), S197cap.smul_one_sub]
  rw [hB, S197cap.vn_scalar]
  · have hc := S197cap.compl_density _ (S197cap.dil_iso _ hU 1) ρ1 hρ1
    have hE := (S197cap.ent_bounds (inst := inferInstance) _ hc.1 hc.2).2
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_one] at hE
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_one]
    have hlt : Real.logb 2 ((M - N + 1 : ℕ) : ℝ) < Real.logb 2 ((M + 1 : ℕ) : ℝ) := by
      apply Real.logb_lt_logb one_lt_two
      · exact_mod_cast Nat.succ_pos _
      · exact_mod_cast (by omega : M - N + 1 < M + 1)
    linarith
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_one]
    push_cast
    field_simp
