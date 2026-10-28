-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P11.nonSignalling_le_matthewsWehner
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:31:36.455852+00:00
-- url     : https://prove2.me/submissions/3d1c1ac5-d8aa-4eb8-a0a7-6aebd7da7840

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11
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

section S191P11b
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma S191P11b_ch_trace {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) (X : Matrix ι ι ℂ) : (Φ X).trace = X.trace := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ]
  unfold krausApply
  calc (∑ j, E j * X * (E j)ᴴ).trace = ∑ j, ((E j)ᴴ * E j * X).trace := by
        rw [Matrix.trace_sum]; congr 1; ext j; rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = ((∑ j, (E j)ᴴ * E j) * X).trace := by rw [Finset.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [show (∑ j, (E j)ᴴ * E j) = 1 from hE, Matrix.one_mul]

lemma S191P11b_ch_smul {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) (c : ℂ) (X : Matrix ι ι ℂ) : Φ (c • X) = c • Φ X := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ, hΦ]
  unfold krausApply
  simp [Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

lemma S191P11b_choi_psd {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) : (choi Φ).PosSemidef := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  have : choi Φ = ∑ j, Matrix.vecMulVec (fun p : ι × κ => E j p.2 p.1)
      (star (fun p : ι × κ => E j p.2 p.1)) := by
    ext ⟨p, r⟩ ⟨q, s⟩
    simp [choi, hΦ, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.vecMulVec_apply, ite_and, Finset.sum_ite_eq, ite_mul]
  rw [this]
  exact Matrix.posSemidef_sum _ fun j _ => Matrix.posSemidef_vecMulVec_self_star _

lemma S191P11b_pt_single {A B : Type*} [DecidableEq A] [DecidableEq B] (a b : A) (β γ : B) :
    pt (Matrix.single (a, β) (b, γ) (1 : ℂ)) = Matrix.single (a, γ) (b, β) 1 := by
  ext p q
  simp only [pt, Matrix.single_apply, Prod.ext_iff]
  by_cases h1 : a = p.1 <;> by_cases h2 : γ = p.2 <;> by_cases h3 : b = q.1 <;>
    by_cases h4 : β = q.2 <;> simp [h1, h2, h3, h4]

lemma S191P11b_contract {U X : Type*} [Fintype U] [Fintype X] {P : Matrix X X ℂ}
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

lemma S191P11b_contract' {U X : Type*} [Fintype U] [Fintype X] {P : Matrix X X ℂ}
    {Q : Matrix (U × X) (U × X) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (M : Matrix U U ℂ) (hM : ∀ u v, M u v = ∑ x, ∑ y, P x y * Q (u, x) (v, y)) :
    M.PosSemidef := by
  rw [show M = Matrix.of fun u v => ∑ x, ∑ y, P x y * Q (u, x) (v, y) from Matrix.ext hM]
  exact S191P11b_contract hP hQ

lemma S191P11b_offdiag {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) (x y : n) :
    (M x y).re + (M y x).re ≤ (M x x).re + (M y y).re := by
  have h2 := (hM.submatrix ![x, y]).re_dotProduct_nonneg ![1, -1]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two] at h2
  linarith

lemma S191P11b_fid (K : ℕ) (hK : 0 < K) (L : Superop (Fin K) (Fin K))
    (hL : ∀ (c : ℂ) X, L (c • X) = c • L X) :
    channelFidelity K L = ((K:ℝ)^2)⁻¹ * (∑ a, ∑ b, L (Matrix.single a b 1) a b).re := by
  unfold channelFidelity
  rw [dif_pos hK]
  unfold QuditFidelity.entanglementFidelity effectProb
  simp only [pureDensity, finiteMaxEntangled, idTensorSuperop, Matrix.trace, Matrix.mul_apply,
    Matrix.diag, Fintype.card_fin, Matrix.of_apply]
  have hs : (starRingEnd ℂ) ((↑(√(K:ℝ)) : ℂ)⁻¹) = (↑(√(K:ℝ)) : ℂ)⁻¹ := by
    simp [Complex.conj_ofReal]
  have hss : ((↑(√(K:ℝ)) : ℂ)⁻¹) * (↑(√(K:ℝ)) : ℂ)⁻¹ = (K:ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hM : ∀ a b : Fin K, (Matrix.of fun i_1 i' =>
      (if a = i_1 then (↑(√(K:ℝ)) : ℂ)⁻¹ else 0) *
        (starRingEnd ℂ) (if b = i' then (↑(√(K:ℝ)) : ℂ)⁻¹ else 0)) =
      (K:ℂ)⁻¹ • Matrix.single a b 1 := by
    intro a b; ext x y
    simp only [apply_ite (starRingEnd ℂ), hs, map_zero, Matrix.of_apply, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all
  simp_rw [hM, hL]
  simp only [apply_ite (starRingEnd ℂ), hs, map_zero, Fintype.sum_prod_type, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.smul_apply, smul_eq_mul, Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_eq_single_of_mem x (Finset.mem_univ _)
    (fun b _ hb => by simp [Ne.symm hb]))]
  simp only [if_true, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
  simp_rw [← mul_assoc, hss, ← Finset.mul_sum]
  rw [Finset.sum_comm, show ((K:ℂ)⁻¹ * (K:ℂ)⁻¹ * ∑ y, ∑ x, L (Matrix.single y x 1) y x) =
    ((((K:ℝ)^2)⁻¹ : ℝ) : ℂ) * ∑ y, ∑ x, L (Matrix.single y x 1) y x by push_cast; ring,
    Complex.re_ofReal_mul]

lemma S191P11b_link_smul {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) (c : ℂ) (X : Matrix (Fin K) (Fin K) ℂ) :
    link K N Z (c • X) = c • link K N Z X := by
  ext b d
  simp [link, Finset.mul_sum, mul_assoc]

lemma S191P11b_link_entry {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) (a b : Fin K) :
    link K N Z (Matrix.single a b 1) a b = ∑ i, ∑ j, ∑ β, ∑ γ,
      N (Matrix.single i j 1) β γ * Z (Matrix.single (a, β) (b, γ) 1) (i, a) (j, b) := by
  simp [link, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]


lemma S191P11b_tr_psd {n : Type*} [Fintype n] {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have h := (hA.hadamard hB.transpose).dotProduct_mulVec_nonneg (fun _ => 1)
  have e : star (fun _ : n => (1:ℂ)) ⬝ᵥ ((A ⊙ Bᵀ) *ᵥ fun _ => 1) = (A * B).trace := by
    simp [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.mul_apply, Matrix.hadamard_apply]
  rw [e] at h
  simpa using (Complex.le_def.mp h).1

lemma S191P11b_tr_vec {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    (M * Matrix.vecMulVec v (star v)).trace = star v ⬝ᵥ (M *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.star_apply]; ring

lemma S191P11b_pt_herm {A B : Type*} {M : Matrix (A × B) (A × B) ℂ} (hM : M.IsHermitian) :
    (pt M).IsHermitian :=
  Matrix.IsHermitian.ext fun p q => by simp only [pt]; exact hM.apply _ _

lemma S191P11b_trR_herm {A B : Type*} [Fintype B] {M : Matrix (A × B) (A × B) ℂ}
    (hM : M.IsHermitian) : (traceRight M).IsHermitian :=
  Matrix.IsHermitian.ext fun p q => by
    simp only [traceRight, Matrix.of_apply, star_sum]
    exact Finset.sum_congr rfl fun k _ => hM.apply _ _

lemma S191P11b_kron_herm {A B : Type*} [DecidableEq A] {W : Matrix B B ℂ} (hW : W.IsHermitian) :
    (Matrix.kronecker (1 : Matrix A A ℂ) W).IsHermitian :=
  Matrix.IsHermitian.ext fun p q => by
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, star_mul']
    rw [hW.apply]
    by_cases h : p.1 = q.1
    · simp [h]
    · simp [h, Ne.symm h]

lemma S191P11b_comm3 {A B C : Type*} [Fintype A] [Fintype B] (f : A → B → A → ℂ) :
    ∑ b, ∑ c, ∑ d, f b c d = ∑ b, ∑ c, ∑ d, f d c b := by
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma S191P11b_tr_pt {A B : Type*} [Fintype A] [Fintype B] (Y L : Matrix (A × B) (A × B) ℂ) :
    (Y * pt L).trace = (pt Y * L).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pt, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ =>
    S191P11b_comm3 (C := A) (fun b c d => Y (a,b) (c,d) * L (c,b) (a,d))

lemma S191P11b_tr_trL {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] (W : Matrix B B ℂ)
    (L : Matrix (A × B) (A × B) ℂ) :
    (W * traceLeft L).trace = (Matrix.kronecker (1 : Matrix A A ℂ) W * L).trace := by
  have hR : (Matrix.kronecker (1 : Matrix A A ℂ) W * L).trace =
      ∑ a, ∑ β, ∑ γ, W β γ * L (a, γ) (a, β) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_eq_single a (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
    simp
  rw [hR]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceLeft, Matrix.of_apply,
    Finset.mul_sum]
  rw [eq_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun β _ => Finset.sum_comm

lemma S191P11b_tr_kron {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (X : Matrix (A × B) (A × B) ℂ) (rho : Matrix A A ℂ) :
    (X * Matrix.kronecker rho (1 : Matrix B B ℂ)).trace = (traceRight X * rho).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceRight, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma S191P11b_pt_sub {A B : Type*} (Y V : Matrix (A × B) (A × B) ℂ) :
    pt (Y - V) = pt Y - pt V := by ext p q; simp [pt]

lemma S191P11b_trR_lin {A B : Type*} [Fintype B] (X Y V : Matrix (A × B) (A × B) ℂ) (c : ℂ) :
    traceRight (X + c • (Y + V)) = traceRight X + c • traceRight Y + c • traceRight V := by
  ext i j
  simp [traceRight, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  ring

lemma S191P11b_ident {I O : Type} [Fintype I] [Fintype O] (N : Superop I O) (K : ℕ) (mu : ℝ)
    (W : Matrix O O ℂ) (X Y V L : Matrix (I × O) (I × O) ℂ) (rho : Matrix I I ℂ) :
    lagrangian N K mu W X Y V L rho = mu + W.trace.re / (K : ℝ)^2
      - (((X + Matrix.kronecker (1 : Matrix I I ℂ) W) - ((choi N).transpose + pt (Y - V))) * L).trace.re
      - (((mu : ℂ) • 1 - traceRight (X + (K : ℂ)⁻¹ • (Y + V))) * rho).trace.re := by
  have hc : ((K : ℂ)^2)⁻¹ = ((((K:ℝ)^2)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  unfold lagrangian primalObjective
  have e1 := S191P11b_tr_pt Y L
  have e2 := S191P11b_tr_pt V L
  have e3 := S191P11b_tr_trL (A := I) W L
  have e4 := S191P11b_tr_kron (B := O) X rho
  have e5 := S191P11b_tr_kron (B := O) Y rho
  have e6 := S191P11b_tr_kron (B := O) V rho
  rw [S191P11b_pt_sub, S191P11b_trR_lin, hc]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.mul_one,
    Matrix.one_mul, smul_eq_mul, e1, e2, e3, e4, e5, e6, Complex.add_re, Complex.sub_re,
    Complex.re_ofReal_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring


lemma S191P11b_herm_smul {n : Type*} {M : Matrix n n ℂ} (c : ℂ) (hc : star c = c)
    (hM : M.IsHermitian) : (c • M).IsHermitian :=
  Matrix.IsHermitian.ext fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', hc, hM.apply]

lemma S191P11b_le_of {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (h : ∀ v : n → ℂ, 0 ≤ (M * Matrix.vecMulVec v (star v)).trace.re) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM fun v => ?_
  have h1 := h v
  rw [S191P11b_tr_vec] at h1
  have h2 := hM.im_star_dotProduct_mulVec_self v
  refine Complex.le_def.mpr ⟨by simpa using h1, ?_⟩
  simpa using h2.symm

lemma S191P11b_iff_mp {I O : Type} [Fintype I] [Fintype O] {N : Superop I O} {K : ℕ}
    {s p : Bool} {mu : ℝ} {W : Matrix O O ℂ} {X Y V : Matrix (I × O) (I × O) ℂ}
    (hF : ExpandedDualFeasible N K s p mu W X Y V) (rho : Matrix I I ℂ)
    (L : Matrix (I × O) (I × O) ℂ) (hrho : rho.PosSemidef) (hL : L.PosSemidef) :
    lagrangian N K mu W X Y V L rho ≤ mu + W.trace.re / (K : ℝ)^2 := by
  rw [S191P11b_ident]
  have h1 := S191P11b_tr_psd hF.2.2.2.2.2.2.1 hL
  have h2 := S191P11b_tr_psd hF.2.2.2.2.2.2.2 hrho
  linarith

lemma S191P11b_iff_mpr {I O : Type} [Fintype I] [Fintype O] (N : Superop I O)
    (hN : IsChannel N) (K : ℕ) (s p : Bool) (mu : ℝ) (W : Matrix O O ℂ)
    (X Y V : Matrix (I × O) (I × O) ℂ)
    (hW : W.IsHermitian) (hX : X.PosSemidef) (hY : Y.PosSemidef) (hV : V.PosSemidef)
    (hzeroW : s = false → W = 0) (hzeroYV : p = false → Y = 0 ∧ V = 0)
    (H : ∀ (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ), rho.PosSemidef → L.PosSemidef →
        lagrangian N K mu W X Y V L rho ≤ mu + W.trace.re / (K : ℝ)^2) :
    ExpandedDualFeasible N K s p mu W X Y V := by
  refine ⟨hW, hX, hY, hV, hzeroW, hzeroYV, ?_, ?_⟩
  · have hH : ((X + Matrix.kronecker (1 : Matrix I I ℂ) W) -
        ((choi N).transpose + pt (Y - V))).IsHermitian :=
      (hX.1.add (S191P11b_kron_herm hW)).sub
        ((S191P11b_choi_psd hN).1.transpose.add (S191P11b_pt_herm (hY.1.sub hV.1)))
    refine S191P11b_le_of hH fun v => ?_
    have h := H 0 (Matrix.vecMulVec v (star v)) Matrix.PosSemidef.zero
      (Matrix.posSemidef_vecMulVec_self_star v)
    rw [S191P11b_ident] at h
    simp only [Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re] at h
    show 0 ≤ (((X + Matrix.kronecker (1 : Matrix I I ℂ) W) -
        ((choi N).transpose + pt (Y - V))) * Matrix.vecMulVec v (star v)).trace.re
    linarith
  · have hs1 : star (K : ℂ)⁻¹ = (K : ℂ)⁻¹ := by simp
    have hs2 : star (mu : ℂ) = (mu : ℂ) := by simp
    have hH : ((mu : ℂ) • 1 - traceRight (X + (K : ℂ)⁻¹ • (Y + V))).IsHermitian :=
      (S191P11b_herm_smul _ hs2 Matrix.isHermitian_one).sub
        (S191P11b_trR_herm (hX.1.add (S191P11b_herm_smul _ hs1 (hY.1.add hV.1))))
    refine S191P11b_le_of hH fun v => ?_
    have h := H (Matrix.vecMulVec v (star v)) 0 (Matrix.posSemidef_vecMulVec_self_star v)
      Matrix.PosSemidef.zero
    rw [S191P11b_ident] at h
    simp only [Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re] at h
    show 0 ≤ (((mu : ℂ) • 1 - traceRight (X + (K : ℂ)⁻¹ • (Y + V))) *
      Matrix.vecMulVec v (star v)).trace.re
    linarith

lemma S191P11b_primal_le {I O : Type} [Fintype I] [Fintype O] {N : Superop I O} {K : ℕ}
    {s p : Bool} {mu : ℝ} {W : Matrix O O ℂ} {X Y V : Matrix (I × O) (I × O) ℂ}
    (hF : ExpandedDualFeasible N K s p mu W X Y V) (rho : Matrix I I ℂ)
    (L : Matrix (I × O) (I × O) ℂ) (hP : Primal K s p rho L) :
    primalObjective N L ≤ mu + W.trace.re / (K : ℝ)^2 := by
  have h1 := S191P11b_iff_mp hF rho L hP.1.1 hP.2.1
  refine le_trans ?_ h1
  obtain ⟨hW, hX, hY, hV, hzW, hzYV, -, -⟩ := hF
  have tX := S191P11b_tr_psd hX hP.2.2.1
  have tYV : 0 ≤ (Y * ((K : ℂ)⁻¹ • Matrix.kronecker rho 1 + pt L)).trace.re ∧
      0 ≤ (V * ((K : ℂ)⁻¹ • Matrix.kronecker rho 1 - pt L)).trace.re := by
    cases p with
    | false => obtain ⟨rfl, rfl⟩ := hzYV rfl; simp
    | true =>
      obtain ⟨h1, h2⟩ := hP.2.2.2.2 rfl
      refine ⟨S191P11b_tr_psd hY ?_, S191P11b_tr_psd hV h2⟩
      have : pt L - -((K : ℂ)⁻¹ • Matrix.kronecker rho 1) =
          (K : ℂ)⁻¹ • Matrix.kronecker rho 1 + pt L := by rw [sub_neg_eq_add, add_comm]
      unfold Loewner at h1; rwa [this] at h1
  have tW : (W * (((K : ℂ)^2)⁻¹ • 1 - traceLeft L)).trace.re = 0 := by
    cases s with
    | false => rw [hzW rfl]; simp
    | true => rw [hP.2.2.2.1 rfl]; simp
  have tmu : mu * (1 - rho.trace.re) = 0 := by rw [hP.1.2]; simp
  unfold lagrangian
  linarith [tYV.1, tYV.2]

lemma S191P11b_psd_scal {n : Type*} [Fintype n] [DecidableEq n] (c : ℝ) (hc : 0 ≤ c) :
    ((c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
  Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hc)

lemma S191P11b_pt_one {A B : Type*} [DecidableEq A] [DecidableEq B] (c : ℂ) :
    pt (c • (1 : Matrix (A × B) (A × B) ℂ)) = c • 1 := by
  ext p q
  simp only [pt, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff, eq_comm]

lemma S191P11b_bound_nonneg {I O : Type} [Fintype I] [Nonempty I] [Fintype O] {N : Superop I O}
    (hN : IsChannel N) {K : ℕ} (hK : 0 < K)
    {s p : Bool} {mu : ℝ} {W : Matrix O O ℂ} {X Y V : Matrix (I × O) (I × O) ℂ}
    (hF : ExpandedDualFeasible N K s p mu W X Y V) : 0 ≤ mu + W.trace.re / (K : ℝ)^2 := by
  set r : ℝ := ((Fintype.card I : ℝ))⁻¹ with hr
  set t : ℝ := ((K : ℝ)^2)⁻¹ with ht
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hr0 : 0 ≤ r := by positivity
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht]; apply inv_le_one_of_one_le₀; nlinarith
  have htK : t ≤ (K : ℝ)⁻¹ := by
    rw [ht]; apply inv_anti₀ (by positivity); nlinarith
  let rho0 : Matrix I I ℂ := (r : ℂ) • 1
  let L0 : Matrix (I × O) (I × O) ℂ := ((r * t : ℝ) : ℂ) • 1
  have hkr : Matrix.kronecker rho0 (1 : Matrix O O ℂ) = (r : ℂ) • 1 := by
    ext p q
    simp only [rho0, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, Prod.ext_iff]
    by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2]
  have hP : Primal K s p rho0 L0 := by
    refine ⟨⟨S191P11b_psd_scal r hr0, ?_⟩, S191P11b_psd_scal _ (by positivity), ?_, fun _ => ?_,
      fun _ => ⟨?_, ?_⟩⟩
    · simp only [rho0, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, hr]
      push_cast
      field_simp
    · unfold Loewner
      rw [hkr, show (r : ℂ) • (1 : Matrix (I × O) (I × O) ℂ) - L0 = ((r - r * t : ℝ) : ℂ) • 1 by
        simp only [L0]; rw [← sub_smul]; push_cast; rfl]
      exact S191P11b_psd_scal _ (by nlinarith)
    · ext β γ
      simp only [traceLeft, L0, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
        Prod.mk.injEq, true_and, smul_eq_mul, Finset.sum_const, Finset.card_univ]
      split_ifs <;> simp [hr, ht]
    · unfold Loewner
      rw [hkr, S191P11b_pt_one, show ((r * t : ℝ) : ℂ) • (1 : Matrix (I × O) (I × O) ℂ) -
          -((K : ℂ)⁻¹ • (r : ℂ) • 1) = ((r * t + (K : ℝ)⁻¹ * r : ℝ) : ℂ) • 1 by
        rw [smul_smul, sub_neg_eq_add, ← add_smul]; push_cast; rfl]
      exact S191P11b_psd_scal _ (by positivity)
    · unfold Loewner
      rw [hkr, S191P11b_pt_one, show (K : ℂ)⁻¹ • (r : ℂ) • (1 : Matrix (I × O) (I × O) ℂ) -
          ((r * t : ℝ) : ℂ) • 1 = (((K : ℝ)⁻¹ * r - r * t : ℝ) : ℂ) • 1 by
        rw [smul_smul, ← sub_smul]; push_cast; rfl]
      exact S191P11b_psd_scal _ (by nlinarith)
  have h0 : 0 ≤ primalObjective N L0 :=
    S191P11b_tr_psd (S191P11b_choi_psd hN).transpose (S191P11b_psd_scal _ (by positivity))
  linarith [S191P11b_primal_le hF rho0 L0 hP]


lemma S191P11b_primal0 {I O : Type} [Fintype I] [Nonempty I] [Fintype O] {N : Superop I O}
    (hN : IsChannel N) {K : ℕ} (hK : 0 < K)
    (s p : Bool) : ∃ rho L, Primal K s p rho L ∧ 0 ≤ primalObjective N L := by
  set r : ℝ := ((Fintype.card I : ℝ))⁻¹ with hr
  set t : ℝ := ((K : ℝ)^2)⁻¹ with ht
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hr0 : 0 ≤ r := by positivity
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht]; apply inv_le_one_of_one_le₀; nlinarith
  have htK : t ≤ (K : ℝ)⁻¹ := by
    rw [ht]; apply inv_anti₀ (by positivity); nlinarith
  let rho0 : Matrix I I ℂ := (r : ℂ) • 1
  let L0 : Matrix (I × O) (I × O) ℂ := ((r * t : ℝ) : ℂ) • 1
  have hkr : Matrix.kronecker rho0 (1 : Matrix O O ℂ) = (r : ℂ) • 1 := by
    ext p q
    simp only [rho0, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, Prod.ext_iff]
    by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2]
  have hP : Primal K s p rho0 L0 := by
    refine ⟨⟨S191P11b_psd_scal r hr0, ?_⟩, S191P11b_psd_scal _ (by positivity), ?_, fun _ => ?_,
      fun _ => ⟨?_, ?_⟩⟩
    · simp only [rho0, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, hr]
      push_cast
      field_simp
    · unfold Loewner
      rw [hkr, show (r : ℂ) • (1 : Matrix (I × O) (I × O) ℂ) - L0 = ((r - r * t : ℝ) : ℂ) • 1 by
        simp only [L0]; rw [← sub_smul]; push_cast; rfl]
      exact S191P11b_psd_scal _ (by nlinarith)
    · ext β γ
      simp only [traceLeft, L0, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
        Prod.mk.injEq, true_and, smul_eq_mul, Finset.sum_const, Finset.card_univ]
      split_ifs <;> simp [hr, ht]
    · unfold Loewner
      rw [hkr, S191P11b_pt_one, show ((r * t : ℝ) : ℂ) • (1 : Matrix (I × O) (I × O) ℂ) -
          -((K : ℂ)⁻¹ • (r : ℂ) • 1) = ((r * t + (K : ℝ)⁻¹ * r : ℝ) : ℂ) • 1 by
        rw [smul_smul, sub_neg_eq_add, ← add_smul]; push_cast; rfl]
      exact S191P11b_psd_scal _ (by positivity)
    · unfold Loewner
      rw [hkr, S191P11b_pt_one, show (K : ℂ)⁻¹ • (r : ℂ) • (1 : Matrix (I × O) (I × O) ℂ) -
          ((r * t : ℝ) : ℂ) • 1 = (((K : ℝ)⁻¹ * r - r * t : ℝ) : ℂ) • 1 by
        rw [smul_smul, ← sub_smul]; push_cast; rfl]
      exact S191P11b_psd_scal _ (by nlinarith)
  have h0 : 0 ≤ primalObjective N L0 :=
    S191P11b_tr_psd (S191P11b_choi_psd hN).transpose (S191P11b_psd_scal _ (by positivity))
  exact ⟨rho0, L0, hP, h0⟩


lemma S191P11b_ch_psd {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) {M : Matrix ι ι ℂ} (hM : M.PosSemidef) : (Φ M).PosSemidef := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ]
  exact Matrix.posSemidef_sum _ fun j _ => hM.mul_mul_conjTranspose_same (E j)

lemma S191P11b_single_psd {n : Type*} [Fintype n] [DecidableEq n] (a : n) :
    (Matrix.single a a (1 : ℂ)).PosSemidef := by
  have : Matrix.single a a (1 : ℂ) = Matrix.vecMulVec (Pi.single a 1) (star (Pi.single a 1)) := by
    ext x y
    simp only [Matrix.single_apply, Matrix.vecMulVec_apply, Pi.star_apply, Pi.single_apply]
    by_cases h1 : x = a <;> by_cases h2 : y = a <;> simp [h1, h2, @eq_comm _ a]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

lemma S191P11b_trR_single {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    (a a' : A) (β γ : B) :
    traceRight (Matrix.single (a, β) (a', γ) (1 : ℂ)) =
      (if β = γ then (1 : ℂ) else 0) • Matrix.single a a' 1 := by
  ext x y
  simp only [traceRight, Matrix.of_apply, Matrix.smul_apply, Matrix.single_apply,
    Prod.mk.injEq, smul_eq_mul]
  by_cases hxy : a = x ∧ a' = y
  · obtain ⟨rfl, rfl⟩ := hxy
    rcases eq_or_ne β γ with rfl | h3
    · simp
    · rw [if_neg h3, zero_mul]
      exact Finset.sum_eq_zero fun k _ => if_neg (fun h => h3 (h.1.2.trans h.2.2.symm))
  · rw [if_neg hxy, mul_zero]
    exact Finset.sum_eq_zero fun k _ => if_neg (fun h => hxy ⟨h.1.1, h.2.1⟩)

lemma S191P11b_trL_single {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (a a' : A) (β γ : B) :
    traceLeft (Matrix.single (a, β) (a', γ) (1 : ℂ)) =
      (if a = a' then (1 : ℂ) else 0) • Matrix.single β γ 1 := by
  ext x y
  simp only [traceLeft, Matrix.of_apply, Matrix.smul_apply, Matrix.single_apply,
    Prod.mk.injEq, smul_eq_mul]
  by_cases hxy : β = x ∧ γ = y
  · obtain ⟨rfl, rfl⟩ := hxy
    rcases eq_or_ne a a' with rfl | h3
    · simp
    · rw [if_neg h3, zero_mul]
      exact Finset.sum_eq_zero fun k _ => if_neg (fun h => h3 (h.1.1.trans h.2.1.symm))
  · rw [if_neg hxy, mul_zero]
    exact Finset.sum_eq_zero fun k _ => if_neg (fun h => hxy ⟨h.1.2, h.2.2⟩)

/-- the code-induced primal operator -/
def S191P11b_Lz {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) : Matrix (I × O) (I × O) ℂ :=
  ((K : ℂ)^2)⁻¹ • ∑ a, ∑ b, Matrix.of (fun u v : I × O =>
    Z (Matrix.single (a, u.2) (b, v.2) 1) (u.1, a) (v.1, b))

lemma S191P11b_Lz_apply {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (u v : I × O) :
    S191P11b_Lz K Z u v = ((K : ℂ)^2)⁻¹ *
      ∑ a, ∑ b, Z (Matrix.single (a, u.2) (b, v.2) 1) (u.1, a) (v.1, b) := by
  simp [S191P11b_Lz, Matrix.sum_apply]

lemma S191P11b_obj {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) :
    primalObjective N (S191P11b_Lz K Z) = channelFidelity K (link K N Z) := by
  rw [S191P11b_fid K hK _ (S191P11b_link_smul K N Z)]
  simp only [S191P11b_link_entry]
  unfold primalObjective S191P11b_Lz
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum,
    show ((K : ℂ)^2)⁻¹ = ((((K:ℝ)^2)⁻¹ : ℝ) : ℂ) by push_cast; rfl, smul_eq_mul,
    Complex.re_ofReal_mul]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, choi,
    Matrix.of_apply]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_comm


lemma S191P11b_psd_of_sq {n : Type*} [Fintype n] (A : Matrix n n ℂ) (c : ℝ) (hc : 0 < c)
    (h : Aᴴ * A = (c : ℂ) • A) : A.PosSemidef := by
  have e : A = ((c⁻¹ : ℝ) : ℂ) • (Aᴴ * A) := by
    rw [h, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_smul]
  rw [e]
  exact (Matrix.posSemidef_conjTranspose_mul_self A).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))

lemma S191P11b_Lz_psd {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsChannel Z) : (S191P11b_Lz K Z).PosSemidef := by
  have hC := S191P11b_choi_psd hZ
  let f : (I × O) × Fin K → (Fin K × O) × (I × Fin K) := fun w => ((w.2, w.1.2), (w.1.1, w.2))
  refine S191P11b_contract' (Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin K => (K : ℂ)⁻¹))
    (hC.submatrix f) _ fun u v => ?_
  rw [S191P11b_Lz_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, Matrix.submatrix_apply, choi, f]
  rw [show star (K:ℂ)⁻¹ = (K:ℂ)⁻¹ by simp]
  ring

def S191P11b_rho {I : Type} [Fintype I] (K : ℕ) (E : Superop (Fin K) I) : Matrix I I ℂ :=
  (K : ℂ)⁻¹ • ∑ a, E (Matrix.single a a 1)

lemma S191P11b_Kinv_nonneg (K : ℕ) : (0 : ℂ) ≤ (K : ℂ)⁻¹ := by
  rw [show (K : ℂ)⁻¹ = (((K : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  exact Complex.zero_le_real.mpr (by positivity)

lemma S191P11b_rho_dens {I : Type} [Fintype I] (K : ℕ) (hK : 0 < K) (E : Superop (Fin K) I)
    (hE : IsChannel E) : IsDensityMatrix (S191P11b_rho K E) := by
  refine ⟨(Matrix.posSemidef_sum _ fun a _ => S191P11b_ch_psd hE (S191P11b_single_psd a)).smul
    (S191P11b_Kinv_nonneg K), ?_⟩
  simp only [S191P11b_rho, Matrix.trace_smul, Matrix.trace_sum, S191P11b_ch_trace hE,
    Matrix.trace_single_eq_same, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, nsmul_eq_mul, mul_one]
  have : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp

lemma S191P11b_nsba {I O : Type} [Fintype I] [Fintype O] {K : ℕ}
    {Z : Superop (Fin K × O) (I × Fin K)} {E : Superop (Fin K) I} (hE : IsChannel E)
    (hEZ : ∀ X, traceRight (Z X) = E (traceRight X)) (a : Fin K) (β γ : O) (i j : I) :
    ∑ c, Z (Matrix.single (a, β) (a, γ) 1) (i, c) (j, c) =
      (if β = γ then 1 else 0) * E (Matrix.single a a 1) i j := by
  rw [show ∑ c, Z (Matrix.single (a, β) (a, γ) 1) (i, c) (j, c) =
    traceRight (Z (Matrix.single (a, β) (a, γ) 1)) i j from rfl, hEZ, S191P11b_trR_single,
    S191P11b_ch_smul hE]
  rfl

lemma S191P11b_phi_sum (K : ℕ) (G : (Fin K × Fin K) → (Fin K × Fin K) → ℂ) :
    ∑ x : Fin K × Fin K, ∑ y : Fin K × Fin K,
      ((if x.1 = x.2 then (1 : ℂ) else 0) * (if y.1 = y.2 then 1 else 0)) * G x y =
      ∑ a, ∑ b, G (a, a) (b, b) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun c _ hc => Finset.sum_eq_zero fun y _ => by
    simp [Ne.symm hc]) (by simp)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single b (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
  simp

lemma S191P11b_P2_sum (K : ℕ) (c : ℂ) (G : (Fin K × Fin K) → (Fin K × Fin K) → ℂ) :
    ∑ x : Fin K × Fin K, ∑ y : Fin K × Fin K,
      c * ((if x = y then (1 : ℂ) else 0) -
        c * ((if x.1 = x.2 then (1 : ℂ) else 0) * (if y.1 = y.2 then 1 else 0))) * G x y =
      c * ∑ x, G x x - c * c * ∑ a, ∑ b, G (a, a) (b, b) := by
  rw [← S191P11b_phi_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp [mul_ite, ite_mul]
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring

lemma S191P11b_loew {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsChannel Z) (E : Superop (Fin K) I)
    (hE : IsChannel E) (hEZ : ∀ X, traceRight (Z X) = E (traceRight X)) :
    Loewner (S191P11b_Lz K Z) (Matrix.kronecker (S191P11b_rho K E) 1) := by
  unfold Loewner
  have hC := S191P11b_choi_psd hZ
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  set c : ℂ := (K : ℂ)⁻¹ with hc
  have hsc : star c = c := by simp [hc]
  let φ : Fin K × Fin K → ℂ := fun x => if x.1 = x.2 then (1 : ℂ) else 0
  let J : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ := Matrix.of fun x y => φ x * φ y
  have hJh : Jᴴ = J := by
    ext x y
    simp only [J, φ, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', apply_ite star,
      star_one, star_zero]
    ring
  have hφ : ∑ z, φ z * φ z = (K : ℂ) := by
    simp [φ, Fintype.sum_prod_type]
  have hJJ : J * J = (K : ℂ) • J := by
    ext x y
    simp only [J, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← hφ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hcc : c * (c * (K : ℂ)) = c := by rw [hc]; field_simp
  have hPi : (1 - c • J)ᴴ * (1 - c • J) = ((1 : ℝ) : ℂ) • (1 - c • J) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hsc, hJh]
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hJJ,
      smul_smul, hcc, Complex.ofReal_one, one_smul]
    abel
  have hP2 : (c • (1 - c • J)).PosSemidef :=
    (S191P11b_psd_of_sq _ 1 one_pos hPi).smul (S191P11b_Kinv_nonneg K)
  let g : (I × O) × (Fin K × Fin K) → (Fin K × O) × (I × Fin K) :=
    fun w => ((w.2.1, w.1.2), (w.1.1, w.2.2))
  refine S191P11b_contract' hP2 (hC.submatrix g) _ fun u v => ?_
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, J, Matrix.of_apply,
    smul_eq_mul, φ]
  rw [S191P11b_P2_sum]
  simp only [Matrix.submatrix_apply, choi, g, Fintype.sum_prod_type, S191P11b_nsba hE hEZ]
  rw [S191P11b_Lz_apply]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, S191P11b_rho, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, Matrix.one_apply]
  rw [← Finset.mul_sum]
  rw [hc]
  ring


lemma S191P11b_trL_Lz {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (D : Superop O (Fin K)) (hD : IsChannel D)
    (hDZ : ∀ X, traceLeft (Z X) = D (traceLeft X)) :
    traceLeft (S191P11b_Lz K Z) = ((K : ℂ)^2)⁻¹ • 1 := by
  ext β γ
  simp only [traceLeft, Matrix.of_apply, S191P11b_Lz_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  calc ∑ i, ∑ a, ∑ b, Z (Matrix.single (a, β) (b, γ) 1) (i, a) (i, b)
      = ∑ a, ∑ b, ∑ i, Z (Matrix.single (a, β) (b, γ) 1) (i, a) (i, b) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, (if a = b then (1 : ℂ) else 0) * D (Matrix.single β γ 1) a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [show ∑ i, Z (Matrix.single (a, β) (b, γ) 1) (i, a) (i, b) =
          traceLeft (Z (Matrix.single (a, β) (b, γ) 1)) a b from rfl, hDZ, S191P11b_trL_single,
          S191P11b_ch_smul hD]
        rfl
    _ = (D (Matrix.single β γ 1)).trace := by
        simp [ite_mul, Matrix.trace]
    _ = _ := by
        rw [S191P11b_ch_trace hD]
        simp [Matrix.trace, Matrix.single_apply, ite_and]
        by_cases h : β = γ
        · simp [h]
        · simp [h, Ne.symm h]

lemma S191P11b_P3_sum (K : ℕ) (d s : ℂ) (G : (Fin K × Fin K) → (Fin K × Fin K) → ℂ) :
    ∑ x : Fin K × Fin K, ∑ y : Fin K × Fin K,
      d * ((if x = y then (1 : ℂ) else 0) + s * (if y = x.swap then 1 else 0)) * G x y =
      d * ∑ x, G x x + d * s * ∑ x, G x x.swap := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp [mul_ite, ite_mul]
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp [mul_ite, ite_mul, mul_assoc]

lemma S191P11b_ppt {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ' : IsChannel (fun X => pt (Z (pt X))))
    (E : Superop (Fin K) I)
    (hE : IsChannel E) (hEZ : ∀ X, traceRight (Z X) = E (traceRight X)) :
    Loewner (-((K : ℂ)⁻¹ • Matrix.kronecker (S191P11b_rho K E) 1)) (pt (S191P11b_Lz K Z)) ∧
      Loewner (pt (S191P11b_Lz K Z)) ((K : ℂ)⁻¹ • Matrix.kronecker (S191P11b_rho K E) 1) := by
  have hC := S191P11b_choi_psd hZ'
  let F : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ := Matrix.of fun x y =>
    if y = x.swap then 1 else 0
  have hFh : Fᴴ = F := by
    ext x y
    simp only [F, Matrix.conjTranspose_apply, Matrix.of_apply, apply_ite star, star_one,
      star_zero]
    by_cases h : y = x.swap
    · subst h; simp
    · rw [if_neg h, if_neg]; rintro rfl; exact h (Prod.swap_swap y).symm
  have hFF : F * F = 1 := by
    ext x y
    simp only [F, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Prod.swap_swap]
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  have h1 : (1 + F)ᴴ * (1 + F) = ((2 : ℝ) : ℂ) • (1 + F) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hFh]
    simp only [add_mul, mul_add, one_mul, mul_one, hFF]
    push_cast
    module
  have h2 : (1 - F)ᴴ * (1 - F) = ((2 : ℝ) : ℂ) • (1 - F) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hFh]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hFF]
    push_cast
    module
  have hd : (0 : ℂ) ≤ ((K : ℂ)^2)⁻¹ := by
    rw [show ((K : ℂ)^2)⁻¹ = ((((K:ℝ)^2)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.zero_le_real.mpr (by positivity)
  have hP1 := (S191P11b_psd_of_sq _ 2 two_pos h1).smul hd
  have hP2 := (S191P11b_psd_of_sq _ 2 two_pos h2).smul hd
  let g : (I × O) × (Fin K × Fin K) → (Fin K × O) × (I × Fin K) :=
    fun w => ((w.2.1, w.1.2), (w.1.1, w.2.2))
  have hQ : ∀ (u v : I × O) (x y : Fin K × Fin K), (choi (fun X => pt (Z (pt X)))).submatrix g g
      (u, x) (v, y) = Z (Matrix.single (x.1, v.2) (y.1, u.2) 1) (u.1, y.2) (v.1, x.2) := by
    intro u v x y
    simp only [Matrix.submatrix_apply, choi, g, S191P11b_pt_single]
    rfl
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  constructor
  · unfold Loewner
    refine S191P11b_contract' hP1 (hC.submatrix g) _ fun u v => ?_
    have := S191P11b_P3_sum K ((K : ℂ)^2)⁻¹ 1 (fun x y =>
      (choi (fun X => pt (Z (pt X)))).submatrix g g (u, x) (v, y))
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, F, Matrix.of_apply,
      smul_eq_mul, one_mul] at this ⊢
    rw [this]
    simp only [hQ, Prod.fst_swap, Prod.snd_swap, Fintype.sum_prod_type, S191P11b_nsba hE hEZ]
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, pt, S191P11b_Lz_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, S191P11b_rho, Matrix.sum_apply, smul_eq_mul,
      Matrix.one_apply]
    rw [← Finset.mul_sum]
    by_cases h : u.2 = v.2
    · simp only [h, if_true]; field_simp; ring
    · simp only [h, Ne.symm h, if_false]; ring
  · unfold Loewner
    refine S191P11b_contract' hP2 (hC.submatrix g) _ fun u v => ?_
    have := S191P11b_P3_sum K ((K : ℂ)^2)⁻¹ (-1) (fun x y =>
      (choi (fun X => pt (Z (pt X)))).submatrix g g (u, x) (v, y))
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, F, Matrix.of_apply,
      smul_eq_mul, neg_one_mul, ← sub_eq_add_neg] at this ⊢
    rw [this]
    simp only [hQ, Prod.fst_swap, Prod.snd_swap, Fintype.sum_prod_type, S191P11b_nsba hE hEZ]
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, pt, S191P11b_Lz_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, S191P11b_rho, Matrix.sum_apply, smul_eq_mul,
      Matrix.one_apply]
    rw [← Finset.mul_sum]
    by_cases h : u.2 = v.2
    · simp only [h, if_true]; field_simp; ring
    · simp only [h, Ne.symm h, if_false]; ring


lemma S191P11b_code_primal {I O : Type} [Fintype I] [Fintype O] (N : Superop I O) (K : ℕ)
    (hK : 0 < K) (s p : Bool) (Z : Superop (Fin K × O) (I × Fin K))
    (hZ : IsForwardCode K (flagsClass s p) Z) :
    ∃ rho L, Primal K s p rho L ∧ primalObjective N L = channelFidelity K (link K N Z) := by
  obtain ⟨hZc, ⟨E, hE, hEZ⟩, hc⟩ := hZ
  have hS : s = true → NSAB Z := by
    rintro rfl
    cases p
    · exact hc
    · exact hc.1
  have hPp : p = true → PPTMap Z := by
    rintro rfl
    cases s
    · exact hc
    · exact hc.2
  have hE' : IsChannel E := by convert hE
  refine ⟨S191P11b_rho K E, S191P11b_Lz K Z, ⟨S191P11b_rho_dens K hK E hE', S191P11b_Lz_psd K Z hZc,
    S191P11b_loew K hK Z hZc E hE' hEZ, fun h => ?_,
    fun h => S191P11b_ppt K hK Z (by convert (hPp h).2) E hE' hEZ⟩, S191P11b_obj K hK N Z⟩
  obtain ⟨D, hD, hDZ⟩ := hS h
  exact S191P11b_trL_Lz K Z D hD hDZ


lemma S191P11b_trR_choiT {I O : Type} [Fintype I] [Fintype O] (N : Superop I O)
    (hN : IsChannel N) : traceRight ((choi N)ᵀ) = 1 := by
  ext i j
  calc traceRight ((choi N)ᵀ) i j = (N (Matrix.single j i 1)).trace := rfl
    _ = _ := by
      rw [S191P11b_ch_trace hN]
      by_cases h : i = j
      · subst h; simp [Matrix.trace, Matrix.single_apply]
      · simp [Matrix.trace, Matrix.single_apply, h, Ne.symm h]

lemma S191P11b_obj_le_one {I O : Type} [Fintype I] [Fintype O] (N : Superop I O)
    (hN : IsChannel N) (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (L : Matrix (I × O) (I × O) ℂ) (hL : Loewner L (Matrix.kronecker rho 1)) :
    primalObjective N L ≤ 1 := by
  have h := S191P11b_tr_psd (S191P11b_choi_psd hN).transpose hL
  have e : ((choi N)ᵀ * Matrix.kronecker rho 1).trace = 1 := by
    rw [S191P11b_tr_kron, S191P11b_trR_choiT N hN, Matrix.one_mul, hrho.2]
  unfold primalObjective
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, e] at h
  simp only [Complex.one_re] at h
  linarith

lemma S191P11b_code_fid {I O : Type} [Fintype I] [Fintype O] (N : Superop I O)
    (hN : IsChannel N) (K : ℕ) (hK : 0 < K) (Z : Superop (Fin K × O) (I × Fin K))
    (hZc : IsChannel Z) (hNS : NSBA Z) :
    0 ≤ channelFidelity K (link K N Z) ∧ channelFidelity K (link K N Z) ≤ 1 := by
  obtain ⟨E, hE, hEZ⟩ := hNS
  have hE' : IsChannel E := by convert hE
  rw [← S191P11b_obj K hK N Z]
  exact ⟨S191P11b_tr_psd (S191P11b_choi_psd hN).transpose (S191P11b_Lz_psd K Z hZc),
    S191P11b_obj_le_one N hN _ (S191P11b_rho_dens K hK E hE') _ (S191P11b_loew K hK Z hZc E hE' hEZ)⟩


lemma S191P11b_isChannel_of {ι κ ι' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    {_ : DecidableEq ι} {Φ : Superop ι κ} (A : ι' → Matrix κ ι ℂ)
    (hA : ∑ k, (A k)ᴴ * A k = 1) (hΦ : ∀ ρ, Φ ρ = ∑ k, A k * ρ * (A k)ᴴ) : IsChannel Φ := by
  refine ⟨Fintype.card ι', fun j => A ((Fintype.equivFin ι').symm j), ?_, fun ρ => ?_⟩
  · show ∑ j, _ = 1
    rw [Equiv.sum_comp ((Fintype.equivFin ι').symm) (fun k => (A k)ᴴ * A k)]
    exact hA
  · rw [hΦ]
    show _ = ∑ j, _
    exact (Equiv.sum_comp _ (fun k => A k * ρ * (A k)ᴴ)).symm

lemma S191P11b_comp_ch {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    [DecidableEq ι] [DecidableEq κ] {Φ : Superop κ μ} {Ψ : Superop ι κ}
    (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) : IsChannel (fun X => Φ (Ψ X)) := by
  obtain ⟨m, d, hd, hΦe⟩ := hΦ
  obtain ⟨m', v, hv, hΨe⟩ := hΨ
  refine S191P11b_isChannel_of (fun jk : Fin m × Fin m' => d jk.1 * v jk.2) ?_ ?_
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hd' : ∑ j, (d j)ᴴ * d j = 1 := hd
    have hv' : ∑ k, (v k)ᴴ * v k = 1 := hv
    calc ∑ y, ∑ x, (d x * v y)ᴴ * (d x * v y) = ∑ y, (v y)ᴴ * (∑ x, (d x)ᴴ * d x) * v y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Matrix.mul_sum, Matrix.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by simp only [hd', Matrix.mul_one]; exact hv'
  · intro X
    rw [hΦe, hΨe]
    unfold krausApply
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

lemma S191P11b_ch_expand {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι}
    {Φ : Superop ι κ} (h : IsChannel Φ) (M : Matrix ι ι ℂ) :
    Φ M = ∑ x, ∑ y, M x y • Φ (Matrix.single x y 1) := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  simp only [hΦ, krausApply]
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Finset.sum_congr rfl fun j _ => by ring

lemma S191P11b_decomp {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : ∃ w : n → n → ℂ, ∀ r r', A r r' = ∑ k, w k r * star (w k r') := by
  have hs := hA.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  refine ⟨fun k r => (hA.1.eigenvectorUnitary : Matrix n n ℂ) r k *
    (Real.sqrt (hA.1.eigenvalues k) : ℂ), fun r r' => ?_⟩
  conv_lhs => rw [hs]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.star_apply, star_mul']
  refine Finset.sum_congr rfl fun k _ => ?_
  have h0 := hA.eigenvalues_nonneg k
  set U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ)
  generalize hA.1.eigenvalues k = x at h0 ⊢
  have e : ((√x : ℝ) : ℂ) * ((√x : ℝ) : ℂ) = (x : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  simp only [Complex.star_def, Complex.conj_ofReal]
  linear_combination (-(U r k * (starRingEnd ℂ) (U r' k))) * e

lemma S191P11b_append_ch {B R : Type} [Fintype B] [Fintype R] [DecidableEq B] [DecidableEq R]
    (τ : Matrix R R ℂ) (hτ : τ.PosSemidef) (htr : τ.trace = 1) :
    IsChannel (fun M : Matrix B B ℂ => Matrix.kronecker M τ) := by
  obtain ⟨w, hw⟩ := S191P11b_decomp hτ
  have hsum : ∑ k, ∑ ρ, star (w k ρ) * w k ρ = 1 := by
    rw [← htr, Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag, hw]
    exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => by ring
  refine S191P11b_isChannel_of (fun k : R => (Matrix.of fun (p : B × R) (b : B) =>
    if p.1 = b then w k p.2 else 0)) ?_ ?_
  · ext b b'
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply, apply_ite star, star_zero, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases h : b = b'
    · subst h; simpa using hsum
    · simp [h, Ne.symm h]
  · intro M
    ext ⟨b, ρ⟩ ⟨b', ρ'⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, apply_ite star, star_zero, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, hw,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

lemma S191P11b_trL_psd {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {σ : Matrix (L × R) (L × R) ℂ} (hσ : σ.PosSemidef) : (traceLeft σ).PosSemidef := by
  have : traceLeft σ = ∑ l, (Matrix.of fun (p : L × R) (r : R) =>
      if p = (l, r) then (1 : ℂ) else 0)ᴴ * σ * (Matrix.of fun (p : L × R) (r : R) =>
      if p = (l, r) then (1 : ℂ) else 0) := by
    ext r r'
    simp only [traceLeft, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, apply_ite star, star_one, star_zero, ite_mul, mul_ite,
      zero_mul, mul_zero, one_mul, mul_one, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [this]
  exact Matrix.posSemidef_sum _ fun l _ => hσ.conjTranspose_mul_mul_same _

lemma S191P11b_trL_trace {L R : Type} [Fintype L] [Fintype R] (σ : Matrix (L × R) (L × R) ℂ) :
    (traceLeft σ).trace = σ.trace := by
  simp only [Matrix.trace, Matrix.diag, traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma S191P11b_trL_ea {A B I K L R : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype K]
    [Fintype L] [Fintype R] [DecidableEq A] [DecidableEq B] [DecidableEq L] [DecidableEq R]
    (σ : Matrix (L × R) (L × R) ℂ) (E : Superop (A × L) I) (D : Superop (B × R) K)
    (hE : IsChannel E) (hD : IsChannel D) (X : Matrix (A × B) (A × B) ℂ) :
    traceLeft (eaOp σ E D X) = D (Matrix.kronecker (traceLeft X) (traceLeft σ)) := by
  rw [S191P11b_ch_expand hD]
  ext c c'
  simp only [traceLeft, eaOp, tensorAction, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.kronecker, Matrix.kroneckerMap_apply]
  have htr : ∀ a aa : A × L, ∑ i, E (Matrix.single a aa 1) i i = if a = aa then 1 else 0 := by
    intro a aa
    rw [show ∑ i, E (Matrix.single a aa 1) i i = (E (Matrix.single a aa 1)).trace from rfl,
      S191P11b_ch_trace hE]
    by_cases h : a = aa
    · subst h; simp [Matrix.trace, Matrix.single_apply]
    · simp [Matrix.trace, Matrix.single_apply, h]
  calc _ = ∑ a : A × L, ∑ aa : A × L, ∑ b : B × R, ∑ bb : B × R,
        X (a.1, b.1) (aa.1, bb.1) * σ (a.2, b.2) (aa.2, bb.2) *
          (∑ i, E (Matrix.single a aa 1) i i) * D (Matrix.single b bb 1) c c' := by
        refine Finset.sum_comm.trans ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_comm.trans ?_
        refine Finset.sum_congr rfl fun aa _ => ?_
        refine Finset.sum_comm.trans ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_comm.trans ?_
        refine Finset.sum_congr rfl fun bb _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        convert rfl
    _ = ∑ a : A × L, ∑ b : B × R, ∑ bb : B × R,
        X (a.1, b.1) (a.1, bb.1) * σ (a.2, b.2) (a.2, bb.2) * D (Matrix.single b bb 1) c c' := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single a (fun aa _ h => by simp [htr, Ne.symm h]) (by simp)]
        simp [htr]
    _ = _ := by
        refine Finset.sum_comm.trans ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_comm.trans ?_
        refine Finset.sum_congr rfl fun bb _ => ?_
        rw [Finset.sum_mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]


lemma S191P11b_ea_ns {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsForwardCode K .EA Z) :
    IsForwardCode K .NS Z := by
  obtain ⟨hZc, hNS, l, r, hl, hr, σ, E, D, hσ, hE, hD, rfl⟩ := hZ
  refine ⟨hZc, hNS, ?_⟩
  show NSAB (eaOp σ E D)
  refine ⟨fun M => D (Matrix.kronecker M (traceLeft σ)), ?_, fun X => ?_⟩
  · have h1 := S191P11b_append_ch (B := O) (traceLeft σ) (S191P11b_trL_psd hσ.1)
      (by rw [S191P11b_trL_trace, hσ.2])
    have := S191P11b_comp_ch hD h1
    convert this
  · convert S191P11b_trL_ea σ E D (by convert hE) (by convert hD) X

lemma S191P11b_mem_relaxed {I O : Type} [Fintype I] [Fintype O] (N : Superop I O) (K : ℕ)
    (p : Bool) (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (hP : Primal K true p rho L) :
    primalObjective N L ∈ {v | ∃ rho : Matrix I I ℂ, ∃ L : Matrix (I × O) (I × O) ℂ,
      IsDensityMatrix rho ∧ L.PosSemidef ∧ Loewner L (Matrix.kronecker rho 1) ∧
      Loewner (traceLeft L) (((K * K : ℕ) : ℂ)⁻¹ • 1) ∧ v = primalObjective N L} := by
  refine ⟨rho, L, hP.1, hP.2.1, hP.2.2.1, ?_, rfl⟩
  unfold Loewner
  rw [hP.2.2.2.1 rfl, show ((K * K : ℕ) : ℂ)⁻¹ = ((K : ℂ)^2)⁻¹ by push_cast; ring, sub_self]
  exact Matrix.PosSemidef.zero

end S191P11b
end QAlgorithms.Papers.Independent.Support50.P11

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P11 in
theorem solution {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]
    (N : Superop I O) (hN : IsChannel N) (K : ℕ) (hK : 0 < K) :
    optimalCodeFidelity .EA N K ≤ optimalCodeFidelity .NS N K ∧ optimalCodeFidelity .NS N K ≤ relaxedBound N (K * K) := by
  have hbdd : BddAbove {f | ∃ Z, IsForwardCode K .NS Z ∧ f = channelFidelity K (link K N Z)} := by
    refine ⟨1, ?_⟩
    rintro f ⟨Z, hZ, rfl⟩
    exact (S191P11b_code_fid N hN K hK Z hZ.1 hZ.2.1).2
  have hbddR : BddAbove {v | ∃ rho : Matrix I I ℂ, ∃ L : Matrix (I × O) (I × O) ℂ,
      IsDensityMatrix rho ∧ L.PosSemidef ∧ Loewner L (Matrix.kronecker rho 1) ∧
      Loewner (traceLeft L) (((K * K : ℕ) : ℂ)⁻¹ • 1) ∧ v = primalObjective N L} := by
    refine ⟨1, ?_⟩
    rintro v ⟨rho, L, hrho, hL, hLo, -, rfl⟩
    exact S191P11b_obj_le_one N hN rho hrho L hLo
  constructor
  · unfold optimalCodeFidelity
    rcases Set.eq_empty_or_nonempty
        {f | ∃ Z, IsForwardCode K .EA Z ∧ f = channelFidelity K (link K N Z)} with h | h
    · rw [h, Real.sSup_empty]
      rcases Set.eq_empty_or_nonempty
          {f | ∃ Z, IsForwardCode K .NS Z ∧ f = channelFidelity K (link K N Z)} with h' | ⟨f, hf⟩
      · rw [h', Real.sSup_empty]
      · obtain ⟨Z, hZ, rfl⟩ := hf
        exact (S191P11b_code_fid N hN K hK Z hZ.1 hZ.2.1).1.trans (le_csSup hbdd ⟨Z, hZ, rfl⟩)
    · refine csSup_le h ?_
      rintro f ⟨Z, hZ, rfl⟩
      exact le_csSup hbdd ⟨Z, S191P11b_ea_ns K Z hZ, rfl⟩
  · unfold optimalCodeFidelity relaxedBound
    rcases Set.eq_empty_or_nonempty
        {f | ∃ Z, IsForwardCode K .NS Z ∧ f = channelFidelity K (link K N Z)} with h | h
    · rw [h, Real.sSup_empty]
      obtain ⟨rho, L, hP, h0⟩ := S191P11b_primal0 (N := N) hN hK true false
      exact h0.trans (le_csSup hbddR (S191P11b_mem_relaxed N K false rho L hP))
    · refine csSup_le h ?_
      rintro f ⟨Z, hZ, rfl⟩
      obtain ⟨rho, L, hP, hobj⟩ := S191P11b_code_primal N K hK true false Z hZ
      rw [← hobj]
      exact le_csSup hbddR (S191P11b_mem_relaxed N K false rho L hP)
