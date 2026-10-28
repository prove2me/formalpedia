-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P11.optimal_fidelity_primal_sdp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:52.898098+00:00
-- url     : https://prove2.me/submissions/40c0366e-90d6-4b9c-bfaf-741ec3500663

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_primal_feasibility_iff
import Mathlib

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)
open QAlgorithms.Papers.Independent.Information100.P21 (pt)
open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)
open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)
open QAlgorithms.Papers.Independent.Information100.P69 (replacer)
open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section S192OFPS
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma S192OFPS_ch_trace {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) (X : Matrix ι ι ℂ) : (Φ X).trace = X.trace := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ]
  unfold krausApply
  calc (∑ j, E j * X * (E j)ᴴ).trace = ∑ j, ((E j)ᴴ * E j * X).trace := by
        rw [Matrix.trace_sum]; congr 1; ext j; rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = ((∑ j, (E j)ᴴ * E j) * X).trace := by rw [Finset.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [show (∑ j, (E j)ᴴ * E j) = 1 from hE, Matrix.one_mul]

lemma S192OFPS_ch_psd {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) {M : Matrix ι ι ℂ} (hM : M.PosSemidef) : (Φ M).PosSemidef := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ]
  exact Matrix.posSemidef_sum _ fun j _ => hM.mul_mul_conjTranspose_same (E j)

lemma S192OFPS_choi_psd {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) : (choi Φ).PosSemidef := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  have : choi Φ = ∑ j, Matrix.vecMulVec (fun p : ι × κ => E j p.2 p.1)
      (star (fun p : ι × κ => E j p.2 p.1)) := by
    ext ⟨p, r⟩ ⟨q, s⟩
    simp [choi, hΦ, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.vecMulVec_apply, ite_and, Finset.sum_ite_eq, ite_mul]
  rw [this]
  exact Matrix.posSemidef_sum _ fun j _ => Matrix.posSemidef_vecMulVec_self_star _

lemma S192OFPS_contract {U X : Type*} [Fintype U] [Fintype X] {P : Matrix X X ℂ}
    {Q : Matrix (U × X) (U × X) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (Matrix.of fun u v => ∑ x, ∑ y, P x y * Q (u, x) (v, y)).PosSemidef := by
  have hH := (hP.submatrix (Prod.snd : U × X → X)).hadamard hQ
  let A : Matrix (U × X) U ℂ := Matrix.of fun p u => if p.1 = u then 1 else 0
  have := hH.conjTranspose_mul_mul_same A
  have key : (Matrix.of fun u v => ∑ x, ∑ y, P x y * Q (u, x) (v, y)) =
      Aᴴ * (P.submatrix Prod.snd Prod.snd ⊙ Q) * A := by
    ext u v
    simp [A, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.hadamard_apply]
    exact Finset.sum_comm
  rw [key]; exact this

lemma S192OFPS_trR_trace {A B : Type*} [Fintype A] [Fintype B] (X : Matrix (A × B) (A × B) ℂ) :
    (traceRight X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, traceRight, Matrix.of_apply, Fintype.sum_prod_type]

lemma S192OFPS_trR_psd {A B : Type*} [Fintype A] [Fintype B] {X : Matrix (A × B) (A × B) ℂ}
    (hX : X.PosSemidef) : (traceRight X).PosSemidef := by
  have h := S192OFPS_contract (U := A) (Matrix.PosSemidef.one (n := B) (R := ℂ)) hX
  convert h using 1
  ext u v
  simp [traceRight, Matrix.one_apply]

lemma S192OFPS_avg_dens {I O : Type} [Fintype I] [Fintype O] [Nonempty O] (K : ℕ) (hK : 0 < K)
    (c : CodeAssistance) (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsForwardCode K c Z) :
    IsDensityMatrix (codeAverageInput K Z) := by
  have hZc : IsChannel Z := by convert hZ.1
  have h0 : ((K * Fintype.card O : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hK.ne' Fintype.card_ne_zero)
  have hc : (0 : ℂ) ≤ ((K * Fintype.card O : ℕ) : ℂ)⁻¹ := by
    rw [show ((K * Fintype.card O : ℕ) : ℂ)⁻¹ = ((((K * Fintype.card O : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by
      push_cast; rfl]
    exact Complex.zero_le_real.mpr (by positivity)
  refine ⟨S192OFPS_trR_psd (S192OFPS_ch_psd hZc (Matrix.PosSemidef.one.smul hc)), ?_⟩
  unfold codeAverageInput
  rw [S192OFPS_trR_trace, S192OFPS_ch_trace hZc, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  push_cast at h0 ⊢
  exact inv_mul_cancel₀ h0

lemma S192OFPS_tr_psd {n : Type*} [Fintype n] {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have h := (hA.hadamard hB.transpose).dotProduct_mulVec_nonneg (fun _ => 1)
  have e : star (fun _ : n => (1:ℂ)) ⬝ᵥ ((A ⊙ Bᵀ) *ᵥ fun _ => 1) = (A * B).trace := by
    simp [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.mul_apply, Matrix.hadamard_apply]
  rw [e] at h
  simpa using (Complex.le_def.mp h).1

lemma S192OFPS_tr_kron {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (X : Matrix (A × B) (A × B) ℂ) (rho : Matrix A A ℂ) :
    (X * Matrix.kronecker rho (1 : Matrix B B ℂ)).trace = (traceRight X * rho).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceRight, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma S192OFPS_trR_choiT {I O : Type} [Fintype I] [Fintype O] (N : Superop I O)
    (hN : IsChannel N) : traceRight ((choi N)ᵀ) = 1 := by
  ext i j
  calc traceRight ((choi N)ᵀ) i j = (N (Matrix.single j i 1)).trace := rfl
    _ = _ := by
      rw [S192OFPS_ch_trace hN]
      by_cases h : i = j
      · subst h; simp [Matrix.trace, Matrix.single_apply]
      · simp [Matrix.trace, Matrix.single_apply, h, Ne.symm h]

lemma S192OFPS_obj_le_one {I O : Type} [Fintype I] [Fintype O] (N : Superop I O)
    (hN : IsChannel N) (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (L : Matrix (I × O) (I × O) ℂ) (hL : Loewner L (Matrix.kronecker rho 1)) :
    primalObjective N L ≤ 1 := by
  have h := S192OFPS_tr_psd (S192OFPS_choi_psd hN).transpose hL
  have e : ((choi N)ᵀ * Matrix.kronecker rho 1).trace = 1 := by
    rw [S192OFPS_tr_kron, S192OFPS_trR_choiT N hN, Matrix.one_mul, hrho.2]
  unfold primalObjective
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, e] at h
  simp only [Complex.one_re] at h
  linarith

lemma S192OFPS_psd_scal {n : Type*} [Fintype n] [DecidableEq n] (c : ℝ) (hc : 0 ≤ c) :
    ((c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
  Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hc)

lemma S192OFPS_pt_one {A B : Type*} [DecidableEq A] [DecidableEq B] (c : ℂ) :
    pt (c • (1 : Matrix (A × B) (A × B) ℂ)) = c • 1 := by
  ext p q
  simp only [pt, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff, eq_comm]

lemma S192OFPS_loew_scal {n : Type*} [Fintype n] [DecidableEq n] (a b : ℝ) (h : a ≤ b) :
    Loewner ((a : ℂ) • (1 : Matrix n n ℂ)) ((b : ℂ) • 1) := by
  unfold Loewner
  rw [← sub_smul, ← Complex.ofReal_sub]
  exact S192OFPS_psd_scal _ (by linarith)

/-! ### Topology -/

lemma S192OFPS_psd_closed (n : Type*) [Fintype n] :
    IsClosed {M : Matrix n n ℂ | M.PosSemidef} := by
  have : {M : Matrix n n ℂ | M.PosSemidef} =
      {M | Mᴴ = M} ∩ ⋂ x : n → ℂ, {M | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

lemma S192OFPS_box_compact (n : Type*) [Fintype n] (r : ℝ) :
    IsCompact {M : Matrix n n ℂ | ∀ i j, ‖M i j‖ ≤ r} := by
  have : IsCompact (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n => Metric.closedBall (0:ℂ) r) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {M : Matrix n n ℂ | ∀ i j, ‖M i j‖ ≤ r} =
      (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n => Metric.closedBall (0:ℂ) r) := by
    ext M
    show _ ↔ ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, M i j ∈ Metric.closedBall (0:ℂ) r
    simp
  rw [e]
  exact this

lemma S192OFPS_entry {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) (x y : n) :
    ‖M x y‖ ≤ (M x x).re + (M y y).re := by
  have hyx : M y x = star (M x y) := by
    have := congrFun (congrFun hM.1 y) x
    simpa [Matrix.conjTranspose_apply] using this.symm
  have h1 := (hM.submatrix ![x, y]).re_dotProduct_nonneg ![1, -1]
  have h2 := (hM.submatrix ![x, y]).re_dotProduct_nonneg ![1, 1]
  have h3 := (hM.submatrix ![x, y]).re_dotProduct_nonneg ![1, Complex.I]
  have h4 := (hM.submatrix ![x, y]).re_dotProduct_nonneg ![1, -Complex.I]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, hyx] at h1 h2 h3 h4
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have a : |(M x y).re| ≤ ((M x x).re + (M y y).re) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have b : |(M x y).im| ≤ ((M x x).re + (M y y).re) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

lemma S192OFPS_imp {α : Type*} [TopologicalSpace α] (q : Prop) {S : Set α} (h : IsClosed S) :
    IsClosed {x | q → x ∈ S} := by
  by_cases hq : q
  · simpa [hq] using h
  · simp [hq]

lemma S192OFPS_closed {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (s p : Bool) :
    IsClosed {x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ | Primal K s p x.1 x.2} := by
  have hk : Continuous (fun x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ =>
      Matrix.kronecker x.1 (1 : Matrix O O ℂ)) :=
    continuous_matrix fun a b => by
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
      exact (continuous_fst.matrix_elem _ _).mul continuous_const
  have hpt : Continuous (fun x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ => pt x.2) :=
    continuous_matrix fun a b => continuous_snd.matrix_elem _ _
  have htl : Continuous (fun x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ => traceLeft x.2) :=
    continuous_matrix fun a b => by
      simp only [traceLeft, Matrix.of_apply]
      exact continuous_finsetSum _ fun k _ => continuous_snd.matrix_elem _ _
  have P : ∀ {n : Type} [Fintype n] (f : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ → Matrix n n ℂ),
      Continuous f → IsClosed {x | (f x).PosSemidef} :=
    fun f hf => (S192OFPS_psd_closed _).preimage hf
  have hD : IsClosed {x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ | IsDensityMatrix x.1} :=
    (P _ continuous_fst).inter (isClosed_eq continuous_fst.matrix_trace continuous_const)
  have hL : IsClosed {x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ | x.2.PosSemidef} :=
    P _ continuous_snd
  have hLw : IsClosed {x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ |
      Loewner x.2 (Matrix.kronecker x.1 1)} := P _ (hk.sub continuous_snd)
  have hS : IsClosed {x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ |
      s = true → traceLeft x.2 = ((K : ℂ)^2)⁻¹ • 1} :=
    S192OFPS_imp (s = true) (isClosed_eq htl continuous_const)
  have hA : IsClosed {x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ |
      Loewner (-((K : ℂ)⁻¹ • Matrix.kronecker x.1 1)) (pt x.2)} :=
    P _ (hpt.sub (show Continuous (fun x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ =>
      -((K : ℂ)⁻¹ • Matrix.kronecker x.1 (1 : Matrix O O ℂ))) from
        continuous_neg.comp (hk.const_smul ((K : ℂ)⁻¹))))
  have hB : IsClosed {x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ |
      Loewner (pt x.2) ((K : ℂ)⁻¹ • Matrix.kronecker x.1 1)} :=
    P _ ((show Continuous (fun x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ =>
      ((K : ℂ)⁻¹ • Matrix.kronecker x.1 (1 : Matrix O O ℂ))) from
        hk.const_smul ((K : ℂ)⁻¹)).sub hpt)
  have hPp : IsClosed {x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ |
      p = true → Loewner (-((K : ℂ)⁻¹ • Matrix.kronecker x.1 1)) (pt x.2) ∧
        Loewner (pt x.2) ((K : ℂ)⁻¹ • Matrix.kronecker x.1 1)} :=
    S192OFPS_imp (p = true) (hA.inter hB)
  exact hD.inter (hL.inter (hLw.inter (hS.inter hPp)))

lemma S192OFPS_diag_le {n : Type*} [Fintype n] {rho : Matrix n n ℂ} (hrho : IsDensityMatrix rho)
    (i : n) : (rho i i).re ≤ 1 := by
  have hn : ∀ k, 0 ≤ (rho k k).re := fun k => (Complex.le_def.mp (hrho.1.diag_nonneg (i := k))).1
  calc (rho i i).re ≤ ∑ k, (rho k k).re := Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ i)
    _ = (rho.trace).re := by simp [Matrix.trace, Complex.re_sum]
    _ = 1 := by rw [hrho.2]; simp

lemma S192OFPS_compact {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (s p : Bool) :
    IsCompact {x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ | Primal K s p x.1 x.2} := by
  refine ((S192OFPS_box_compact I 2).prod (S192OFPS_box_compact (I × O) 2)).of_isClosed_subset
    (S192OFPS_closed K s p) ?_
  rintro ⟨rho, L⟩ ⟨hrho, hL, hLr, -, -⟩
  have hd : ∀ u : I × O, (L u u).re ≤ 1 := by
    intro u
    have h1 := (Complex.le_def.mp (hLr.diag_nonneg (i := u))).1
    have h2 := S192OFPS_diag_le hrho u.1
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply] at h1
    linarith
  refine ⟨fun i j => ?_, fun u v => ?_⟩
  · have := S192OFPS_entry hrho.1 i j
    linarith [S192OFPS_diag_le hrho i, S192OFPS_diag_le hrho j]
  · have := S192OFPS_entry hL u v
    linarith [hd u, hd v]

/-- feasible point -/
def S192OFPS_rho0 (I : Type) [Fintype I] : Matrix I I ℂ :=
  (((Fintype.card I : ℝ)⁻¹ : ℝ) : ℂ) • 1

def S192OFPS_L0 (I O : Type) [Fintype I] [Fintype O] (K : ℕ) : Matrix (I × O) (I × O) ℂ :=
  ((K : ℂ)^2)⁻¹ • Matrix.kronecker (S192OFPS_rho0 I) 1

lemma S192OFPS_rho0_dens (I : Type) [Fintype I] [Nonempty I] :
    IsDensityMatrix (S192OFPS_rho0 I) := by
  refine ⟨S192OFPS_psd_scal _ (by positivity), ?_⟩
  have : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [S192OFPS_rho0, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  push_cast
  exact inv_mul_cancel₀ this

lemma S192OFPS_kron0 (I O : Type) [Fintype I] [Fintype O] :
    Matrix.kronecker (S192OFPS_rho0 I) (1 : Matrix O O ℂ) =
      (((Fintype.card I : ℝ)⁻¹ : ℝ) : ℂ) • 1 := by
  rw [S192OFPS_rho0, Matrix.kronecker, Matrix.smul_kronecker, Matrix.one_kronecker_one]

lemma S192OFPS_feas (I O : Type) [Fintype I] [Nonempty I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (s p : Bool) : Primal K s p (S192OFPS_rho0 I) (S192OFPS_L0 I O K) := by
  set d : ℝ := (Fintype.card I : ℝ)⁻¹ with hd
  have hd0 : 0 ≤ d := by positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hL0 : S192OFPS_L0 I O K = ((d / (K:ℝ)^2 : ℝ) : ℂ) • 1 := by
    rw [S192OFPS_L0, S192OFPS_kron0, smul_smul]
    congr 1
    rw [hd]
    push_cast; ring
  have hk := S192OFPS_kron0 I O
  have hle : d / (K:ℝ)^2 ≤ d / K := div_le_div_of_nonneg_left hd0 hK0 (by nlinarith)
  have hle' : d / K ≤ d := div_le_self hd0 hK1
  refine ⟨S192OFPS_rho0_dens I, ?_, ?_, fun _ => ?_, fun _ => ⟨?_, ?_⟩⟩
  · rw [hL0]; exact S192OFPS_psd_scal _ (by positivity)
  · rw [hL0, hk]; exact S192OFPS_loew_scal _ _ (by linarith)
  · rw [hL0]
    ext o o'
    have hc : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    by_cases h : o = o'
    · subst h
      simp [traceLeft, hd]
      field_simp
    · simp [traceLeft, h]
  · rw [hL0, S192OFPS_pt_one, hk, smul_smul,
      show -((((K:ℂ)⁻¹ * ((d:ℝ):ℂ)) • (1 : Matrix (I × O) (I × O) ℂ))) =
        ((-(d / K) : ℝ) : ℂ) • 1 by rw [← neg_smul]; congr 1; push_cast; ring]
    exact S192OFPS_loew_scal _ _ (by linarith [div_nonneg hd0 (sq_nonneg (K:ℝ)), div_nonneg hd0 hK0.le])
  · rw [hL0, S192OFPS_pt_one, hk, smul_smul,
      show ((K:ℂ)⁻¹ * ((d:ℝ):ℂ)) = ((d / K : ℝ) : ℂ) by push_cast; ring]
    exact S192OFPS_loew_scal _ _ hle

lemma S192OFPS_obj0 (I O : Type) [Fintype I] [Nonempty I] [Fintype O] (N : Superop I O)
    (hN : IsChannel N) : primalObjective N (S192OFPS_L0 I O 1) = 1 := by
  unfold primalObjective S192OFPS_L0
  rw [Matrix.mul_smul, Matrix.trace_smul, S192OFPS_tr_kron, S192OFPS_trR_choiT N hN,
    Matrix.one_mul, (S192OFPS_rho0_dens I).2]
  simp

lemma S192OFPS_max {I O : Type} [Fintype I] [Nonempty I] [Fintype O] (N : Superop I O)
    (K : ℕ) (hK : 0 < K) (s p : Bool) :
    ∃ rho L, Primal K s p rho L ∧
      ∀ rho2 L2, Primal K s p rho2 L2 → primalObjective N L2 ≤ primalObjective N L := by
  have hc : Continuous (fun x : Matrix I I ℂ × Matrix (I × O) (I × O) ℂ =>
      primalObjective N x.2) :=
    Complex.continuous_re.comp ((continuous_const.matrix_mul continuous_snd).matrix_trace)
  obtain ⟨x, hx, hmax⟩ := (S192OFPS_compact (O := O) K s p).exists_isMaxOn
    ⟨(S192OFPS_rho0 I, S192OFPS_L0 I O K), S192OFPS_feas I O K hK s p⟩ hc.continuousOn
  exact ⟨x.1, x.2, hx, fun r2 L2 h2 => isMaxOn_iff.mp hmax (r2, L2) h2⟩

end S192OFPS
end QAlgorithms.Papers.Independent.Support50.P11

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P11 in
theorem solution {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]
    (N : Superop I O) (hN : IsChannel N) (K : ℕ) (hK : 0 < K)
    (s p : Bool) (hflags : s = true ∨ p = true) :
    ∃ rho : Matrix I I ℂ, ∃ L : Matrix (I × O) (I × O) ℂ,
      Primal K s p rho L ∧ optimalCodeFidelity (flagsClass s p) N K = primalObjective N L ∧
      (∀ rho2 L2, Primal K s p rho2 L2 → primalObjective N L2 ≤ primalObjective N L) ∧
      (∃ Z : Superop (Fin K × O) (I × Fin K),
        IsForwardCode K (flagsClass s p) Z ∧
        channelFidelity K (link K N Z) = primalObjective N L) := by
  obtain ⟨rho, L, hP, hmax⟩ := S192OFPS_max N K hK s p
  have hobj1 : K = 1 → primalObjective N L = 1 := by
    rintro rfl
    refine le_antisymm (S192OFPS_obj_le_one N hN rho hP.1 L hP.2.2.1) ?_
    have := hmax _ _ (S192OFPS_feas I O 1 one_pos s p)
    rwa [S192OFPS_obj0 I O N hN] at this
  have hmem : ∃ Z : Superop (Fin K × O) (I × Fin K), IsForwardCode K (flagsClass s p) Z ∧
      channelFidelity K (link K N Z) = primalObjective N L := by
    obtain ⟨Z, hZ, -, hf⟩ := (primal_feasibility_iff N hN K hK s p hflags rho hP.1
      (primalObjective N L)).2 (by
        split_ifs with h
        · exact hobj1 h
        · exact ⟨L, hP, rfl⟩)
    exact ⟨Z, hZ, hf⟩
  have hub : ∀ Z : Superop (Fin K × O) (I × Fin K), IsForwardCode K (flagsClass s p) Z →
      channelFidelity K (link K N Z) ≤ primalObjective N L := by
    intro Z hZ
    have := (primal_feasibility_iff N hN K hK s p hflags _ (S192OFPS_avg_dens K hK _ Z hZ)
      (channelFidelity K (link K N Z))).1 ⟨Z, hZ, rfl, rfl⟩
    split_ifs at this with h
    · rw [this, hobj1 h]
    · obtain ⟨L2, hP2, he⟩ := this
      rw [he]
      exact hmax _ _ hP2
  refine ⟨rho, L, hP, ?_, hmax, hmem⟩
  unfold optimalCodeFidelity
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · obtain ⟨Z, hZ, hf⟩ := hmem
    exact ⟨Z, hZ, hf.symm⟩
  · rintro f ⟨Z, hZ, rfl⟩
    exact hub Z hZ
