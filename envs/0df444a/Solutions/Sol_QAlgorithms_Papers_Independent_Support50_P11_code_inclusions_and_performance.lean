-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P11.code_inclusions_and_performance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:31:25.193652+00:00
-- url     : https://prove2.me/submissions/3042f760-0539-4b67-9b6f-a7e430a62903

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

section S192CIP
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma S192CIP_ch_trace {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) (X : Matrix ι ι ℂ) : (Φ X).trace = X.trace := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ]
  unfold krausApply
  calc (∑ j, E j * X * (E j)ᴴ).trace = ∑ j, ((E j)ᴴ * E j * X).trace := by
        rw [Matrix.trace_sum]; congr 1; ext j; rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = ((∑ j, (E j)ᴴ * E j) * X).trace := by rw [Finset.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [show (∑ j, (E j)ᴴ * E j) = 1 from hE, Matrix.one_mul]

lemma S192CIP_ch_smul {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) (c : ℂ) (X : Matrix ι ι ℂ) : Φ (c • X) = c • Φ X := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ, hΦ]
  unfold krausApply
  simp [Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

lemma S192CIP_choi_psd {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) : (choi Φ).PosSemidef := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  have : choi Φ = ∑ j, Matrix.vecMulVec (fun p : ι × κ => E j p.2 p.1)
      (star (fun p : ι × κ => E j p.2 p.1)) := by
    ext ⟨p, r⟩ ⟨q, s⟩
    simp [choi, hΦ, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.vecMulVec_apply, ite_and, Finset.sum_ite_eq, ite_mul]
  rw [this]
  exact Matrix.posSemidef_sum _ fun j _ => Matrix.posSemidef_vecMulVec_self_star _

lemma S192CIP_contract {U X : Type*} [Fintype U] [Fintype X] {P : Matrix X X ℂ}
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

lemma S192CIP_contract' {U X : Type*} [Fintype U] [Fintype X] {P : Matrix X X ℂ}
    {Q : Matrix (U × X) (U × X) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (M : Matrix U U ℂ) (hM : ∀ u v, M u v = ∑ x, ∑ y, P x y * Q (u, x) (v, y)) :
    M.PosSemidef := by
  rw [show M = Matrix.of fun u v => ∑ x, ∑ y, P x y * Q (u, x) (v, y) from Matrix.ext hM]
  exact S192CIP_contract hP hQ

lemma S192CIP_fid (K : ℕ) (hK : 0 < K) (L : Superop (Fin K) (Fin K))
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

lemma S192CIP_link_smul {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) (c : ℂ) (X : Matrix (Fin K) (Fin K) ℂ) :
    link K N Z (c • X) = c • link K N Z X := by
  ext b d
  simp [link, Finset.mul_sum, mul_assoc]

lemma S192CIP_link_entry {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) (a b : Fin K) :
    link K N Z (Matrix.single a b 1) a b = ∑ i, ∑ j, ∑ β, ∑ γ,
      N (Matrix.single i j 1) β γ * Z (Matrix.single (a, β) (b, γ) 1) (i, a) (j, b) := by
  simp [link, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

lemma S192CIP_tr_psd {n : Type*} [Fintype n] {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have h := (hA.hadamard hB.transpose).dotProduct_mulVec_nonneg (fun _ => 1)
  have e : star (fun _ : n => (1:ℂ)) ⬝ᵥ ((A ⊙ Bᵀ) *ᵥ fun _ => 1) = (A * B).trace := by
    simp [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.mul_apply, Matrix.hadamard_apply]
  rw [e] at h
  simpa using (Complex.le_def.mp h).1

lemma S192CIP_tr_kron {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (X : Matrix (A × B) (A × B) ℂ) (rho : Matrix A A ℂ) :
    (X * Matrix.kronecker rho (1 : Matrix B B ℂ)).trace = (traceRight X * rho).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceRight, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma S192CIP_ch_psd {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) {M : Matrix ι ι ℂ} (hM : M.PosSemidef) : (Φ M).PosSemidef := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ]
  exact Matrix.posSemidef_sum _ fun j _ => hM.mul_mul_conjTranspose_same (E j)

lemma S192CIP_single_psd {n : Type*} [Fintype n] [DecidableEq n] (a : n) :
    (Matrix.single a a (1 : ℂ)).PosSemidef := by
  have : Matrix.single a a (1 : ℂ) = Matrix.vecMulVec (Pi.single a 1) (star (Pi.single a 1)) := by
    ext x y
    simp only [Matrix.single_apply, Matrix.vecMulVec_apply, Pi.star_apply, Pi.single_apply]
    by_cases h1 : x = a <;> by_cases h2 : y = a <;> simp [h1, h2, @eq_comm _ a]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

lemma S192CIP_trR_single {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
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

def S192CIP_Lz {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) : Matrix (I × O) (I × O) ℂ :=
  ((K : ℂ)^2)⁻¹ • ∑ a, ∑ b, Matrix.of (fun u v : I × O =>
    Z (Matrix.single (a, u.2) (b, v.2) 1) (u.1, a) (v.1, b))

lemma S192CIP_Lz_apply {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (u v : I × O) :
    S192CIP_Lz K Z u v = ((K : ℂ)^2)⁻¹ *
      ∑ a, ∑ b, Z (Matrix.single (a, u.2) (b, v.2) 1) (u.1, a) (v.1, b) := by
  simp [S192CIP_Lz, Matrix.sum_apply]

lemma S192CIP_obj {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) :
    primalObjective N (S192CIP_Lz K Z) = channelFidelity K (link K N Z) := by
  rw [S192CIP_fid K hK _ (S192CIP_link_smul K N Z)]
  simp only [S192CIP_link_entry]
  unfold primalObjective S192CIP_Lz
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

lemma S192CIP_psd_of_sq {n : Type*} [Fintype n] (A : Matrix n n ℂ) (c : ℝ) (hc : 0 < c)
    (h : Aᴴ * A = (c : ℂ) • A) : A.PosSemidef := by
  have e : A = ((c⁻¹ : ℝ) : ℂ) • (Aᴴ * A) := by
    rw [h, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_smul]
  rw [e]
  exact (Matrix.posSemidef_conjTranspose_mul_self A).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))

lemma S192CIP_Lz_psd {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsChannel Z) : (S192CIP_Lz K Z).PosSemidef := by
  have hC := S192CIP_choi_psd hZ
  let f : (I × O) × Fin K → (Fin K × O) × (I × Fin K) := fun w => ((w.2, w.1.2), (w.1.1, w.2))
  refine S192CIP_contract' (Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin K => (K : ℂ)⁻¹))
    (hC.submatrix f) _ fun u v => ?_
  rw [S192CIP_Lz_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, Matrix.submatrix_apply, choi, f]
  rw [show star (K:ℂ)⁻¹ = (K:ℂ)⁻¹ by simp]
  ring

def S192CIP_rho {I : Type} [Fintype I] (K : ℕ) (E : Superop (Fin K) I) : Matrix I I ℂ :=
  (K : ℂ)⁻¹ • ∑ a, E (Matrix.single a a 1)

lemma S192CIP_Kinv_nonneg (K : ℕ) : (0 : ℂ) ≤ (K : ℂ)⁻¹ := by
  rw [show (K : ℂ)⁻¹ = (((K : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  exact Complex.zero_le_real.mpr (by positivity)

lemma S192CIP_rho_dens {I : Type} [Fintype I] (K : ℕ) (hK : 0 < K) (E : Superop (Fin K) I)
    (hE : IsChannel E) : IsDensityMatrix (S192CIP_rho K E) := by
  refine ⟨(Matrix.posSemidef_sum _ fun a _ => S192CIP_ch_psd hE (S192CIP_single_psd a)).smul
    (S192CIP_Kinv_nonneg K), ?_⟩
  simp only [S192CIP_rho, Matrix.trace_smul, Matrix.trace_sum, S192CIP_ch_trace hE,
    Matrix.trace_single_eq_same, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, nsmul_eq_mul, mul_one]
  have : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp

lemma S192CIP_nsba {I O : Type} [Fintype I] [Fintype O] {K : ℕ}
    {Z : Superop (Fin K × O) (I × Fin K)} {E : Superop (Fin K) I} (hE : IsChannel E)
    (hEZ : ∀ X, traceRight (Z X) = E (traceRight X)) (a : Fin K) (β γ : O) (i j : I) :
    ∑ c, Z (Matrix.single (a, β) (a, γ) 1) (i, c) (j, c) =
      (if β = γ then 1 else 0) * E (Matrix.single a a 1) i j := by
  rw [show ∑ c, Z (Matrix.single (a, β) (a, γ) 1) (i, c) (j, c) =
    traceRight (Z (Matrix.single (a, β) (a, γ) 1)) i j from rfl, hEZ, S192CIP_trR_single,
    S192CIP_ch_smul hE]
  rfl

lemma S192CIP_phi_sum (K : ℕ) (G : (Fin K × Fin K) → (Fin K × Fin K) → ℂ) :
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

lemma S192CIP_P2_sum (K : ℕ) (c : ℂ) (G : (Fin K × Fin K) → (Fin K × Fin K) → ℂ) :
    ∑ x : Fin K × Fin K, ∑ y : Fin K × Fin K,
      c * ((if x = y then (1 : ℂ) else 0) -
        c * ((if x.1 = x.2 then (1 : ℂ) else 0) * (if y.1 = y.2 then 1 else 0))) * G x y =
      c * ∑ x, G x x - c * c * ∑ a, ∑ b, G (a, a) (b, b) := by
  rw [← S192CIP_phi_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp [mul_ite, ite_mul]
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring

lemma S192CIP_loew {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsChannel Z) (E : Superop (Fin K) I)
    (hE : IsChannel E) (hEZ : ∀ X, traceRight (Z X) = E (traceRight X)) :
    Loewner (S192CIP_Lz K Z) (Matrix.kronecker (S192CIP_rho K E) 1) := by
  unfold Loewner
  have hC := S192CIP_choi_psd hZ
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
    (S192CIP_psd_of_sq _ 1 one_pos hPi).smul (S192CIP_Kinv_nonneg K)
  let g : (I × O) × (Fin K × Fin K) → (Fin K × O) × (I × Fin K) :=
    fun w => ((w.2.1, w.1.2), (w.1.1, w.2.2))
  refine S192CIP_contract' hP2 (hC.submatrix g) _ fun u v => ?_
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, J, Matrix.of_apply,
    smul_eq_mul, φ]
  rw [S192CIP_P2_sum]
  simp only [Matrix.submatrix_apply, choi, g, Fintype.sum_prod_type, S192CIP_nsba hE hEZ]
  rw [S192CIP_Lz_apply]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, S192CIP_rho, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, Matrix.one_apply]
  rw [← Finset.mul_sum]
  rw [hc]
  ring

lemma S192CIP_trR_choiT {I O : Type} [Fintype I] [Fintype O] (N : Superop I O)
    (hN : IsChannel N) : traceRight ((choi N)ᵀ) = 1 := by
  ext i j
  calc traceRight ((choi N)ᵀ) i j = (N (Matrix.single j i 1)).trace := rfl
    _ = _ := by
      rw [S192CIP_ch_trace hN]
      by_cases h : i = j
      · subst h; simp [Matrix.trace, Matrix.single_apply]
      · simp [Matrix.trace, Matrix.single_apply, h, Ne.symm h]

lemma S192CIP_obj_le_one {I O : Type} [Fintype I] [Fintype O] (N : Superop I O)
    (hN : IsChannel N) (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (L : Matrix (I × O) (I × O) ℂ) (hL : Loewner L (Matrix.kronecker rho 1)) :
    primalObjective N L ≤ 1 := by
  have h := S192CIP_tr_psd (S192CIP_choi_psd hN).transpose hL
  have e : ((choi N)ᵀ * Matrix.kronecker rho 1).trace = 1 := by
    rw [S192CIP_tr_kron, S192CIP_trR_choiT N hN, Matrix.one_mul, hrho.2]
  unfold primalObjective
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, e] at h
  simp only [Complex.one_re] at h
  linarith

lemma S192CIP_code_fid {I O : Type} [Fintype I] [Fintype O] (N : Superop I O)
    (hN : IsChannel N) (K : ℕ) (hK : 0 < K) (Z : Superop (Fin K × O) (I × Fin K))
    (hZc : IsChannel Z) (hNS : NSBA Z) :
    0 ≤ channelFidelity K (link K N Z) ∧ channelFidelity K (link K N Z) ≤ 1 := by
  obtain ⟨E, hE, hEZ⟩ := hNS
  have hE' : IsChannel E := by convert hE
  rw [← S192CIP_obj K hK N Z]
  exact ⟨S192CIP_tr_psd (S192CIP_choi_psd hN).transpose (S192CIP_Lz_psd K Z hZc),
    S192CIP_obj_le_one N hN _ (S192CIP_rho_dens K hK E hE') _ (S192CIP_loew K hK Z hZc E hE' hEZ)⟩

lemma S192CIP_isChannel_of {ι κ ι' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    {_ : DecidableEq ι} {Φ : Superop ι κ} (A : ι' → Matrix κ ι ℂ)
    (hA : ∑ k, (A k)ᴴ * A k = 1) (hΦ : ∀ ρ, Φ ρ = ∑ k, A k * ρ * (A k)ᴴ) : IsChannel Φ := by
  refine ⟨Fintype.card ι', fun j => A ((Fintype.equivFin ι').symm j), ?_, fun ρ => ?_⟩
  · show ∑ j, _ = 1
    rw [Equiv.sum_comp ((Fintype.equivFin ι').symm) (fun k => (A k)ᴴ * A k)]
    exact hA
  · rw [hΦ]
    show _ = ∑ j, _
    exact (Equiv.sum_comp _ (fun k => A k * ρ * (A k)ᴴ)).symm

lemma S192CIP_comp_ch {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    {dι : DecidableEq ι} {dκ : DecidableEq κ} {Φ : Superop κ μ} {Ψ : Superop ι κ}
    (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) : IsChannel (fun X => Φ (Ψ X)) := by
  obtain ⟨m, d, hd, hΦe⟩ := hΦ
  obtain ⟨m', v, hv, hΨe⟩ := hΨ
  refine S192CIP_isChannel_of (fun jk : Fin m × Fin m' => d jk.1 * v jk.2) ?_ ?_
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

lemma S192CIP_ch_expand {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι}
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

lemma S192CIP_decomp {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
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

lemma S192CIP_append_ch {B R : Type} [Fintype B] [Fintype R] [DecidableEq B] [DecidableEq R]
    (τ : Matrix R R ℂ) (hτ : τ.PosSemidef) (htr : τ.trace = 1) :
    IsChannel (fun M : Matrix B B ℂ => Matrix.kronecker M τ) := by
  obtain ⟨w, hw⟩ := S192CIP_decomp hτ
  have hsum : ∑ k, ∑ ρ, star (w k ρ) * w k ρ = 1 := by
    rw [← htr, Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag, hw]
    exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => by ring
  refine S192CIP_isChannel_of (fun k : R => (Matrix.of fun (p : B × R) (b : B) =>
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

lemma S192CIP_trL_psd {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
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

lemma S192CIP_trL_trace {L R : Type} [Fintype L] [Fintype R] (σ : Matrix (L × R) (L × R) ℂ) :
    (traceLeft σ).trace = σ.trace := by
  simp only [Matrix.trace, Matrix.diag, traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma S192CIP_trL_ea {A B I K L R : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype K]
    [Fintype L] [Fintype R] [DecidableEq A] [DecidableEq B] [DecidableEq L] [DecidableEq R]
    (σ : Matrix (L × R) (L × R) ℂ) (E : Superop (A × L) I) (D : Superop (B × R) K)
    (hE : IsChannel E) (hD : IsChannel D) (X : Matrix (A × B) (A × B) ℂ) :
    traceLeft (eaOp σ E D X) = D (Matrix.kronecker (traceLeft X) (traceLeft σ)) := by
  rw [S192CIP_ch_expand hD]
  ext c c'
  simp only [traceLeft, eaOp, tensorAction, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.kronecker, Matrix.kroneckerMap_apply]
  have htr : ∀ a aa : A × L, ∑ i, E (Matrix.single a aa 1) i i = if a = aa then 1 else 0 := by
    intro a aa
    rw [show ∑ i, E (Matrix.single a aa 1) i i = (E (Matrix.single a aa 1)).trace from rfl,
      S192CIP_ch_trace hE]
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

lemma S192CIP_ea_ns {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsForwardCode K .EA Z) :
    IsForwardCode K .NS Z := by
  obtain ⟨hZc, hNS, l, r, hl, hr, σ, E, D, hσ, hE, hD, rfl⟩ := hZ
  refine ⟨hZc, hNS, ?_⟩
  show NSAB (eaOp σ E D)
  refine ⟨fun M => D (Matrix.kronecker M (traceLeft σ)), ?_, fun X => ?_⟩
  · have h1 := S192CIP_append_ch (B := O) (traceLeft σ) (S192CIP_trL_psd hσ.1)
      (by rw [S192CIP_trL_trace, hσ.2])
    have := S192CIP_comp_ch hD h1
    convert this
  · convert S192CIP_trL_ea σ E D (by convert hE) (by convert hD) X

lemma S192CIP_swap3 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] (f : A → B → C → ℂ) :
    ∑ x, ∑ y, ∑ l, f x y l = ∑ l, ∑ y, ∑ x, f x y l := by
  calc ∑ x, ∑ y, ∑ l, f x y l = ∑ x, ∑ l, ∑ y, f x y l :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ l, ∑ x, ∑ y, f x y l := Finset.sum_comm
    _ = ∑ l, ∑ y, ∑ x, f x y l := Finset.sum_congr rfl fun l _ => Finset.sum_comm

lemma S192CIP_ch_of_C {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} (Φ : Superop ι κ)
    (C : ι → ι → κ → κ → ℂ) (hΦ : ∀ X u v, Φ X u v = ∑ p, ∑ q, X p q * C p q u v)
    (hC : (Matrix.of fun (a b : ι × κ) => C a.1 b.1 a.2 b.2).PosSemidef)
    (hT : ∀ p q, ∑ u, C p q u u = if p = q then 1 else 0) : IsChannel Φ := by
  obtain ⟨m, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hE : ∀ x y o o', C x y o o' = ∑ l, g l (x, o) * star (g l (y, o')) := by
    intro x y o o'
    have := congrFun (congrFun hg (x, o)) (y, o')
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
  refine S192CIP_isChannel_of (fun l : Fin m => (Matrix.of fun (o : κ) (x : ι) => g l (x, o))) ?_ ?_
  · ext x y
    have h := hT y x
    simp only [hE] at h
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun l _ => mul_comm _ _).trans ?_
    rw [h]
    rcases eq_or_ne x y with rfl | hxy
    · simp
    · simp [hxy, Ne.symm hxy]
  · intro X
    ext o o'
    rw [hΦ]
    simp only [hE, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [S192CIP_swap3]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun x _ => ?_
    ring

lemma S192CIP_tr_single {ι : Type*} [Fintype ι] {dι : DecidableEq ι} (p q : ι) :
    (Matrix.single p q (1 : ℂ)).trace = if p = q then 1 else 0 := by
  by_cases h : p = q
  · subst h; simp
  · simp [h, Matrix.trace, Matrix.single_apply]

lemma S192CIP_trace_C {ι κ : Type*} [Fintype ι] [Fintype κ] {dι : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) (p q : ι) : ∑ u, Φ (Matrix.single p q 1) u u = if p = q then 1 else 0 := by
  rw [show ∑ u, Φ (Matrix.single p q 1) u u = (Φ (Matrix.single p q 1)).trace from rfl,
    S192CIP_ch_trace h, S192CIP_tr_single]

lemma S192CIP_id_ch {ι : Type*} [Fintype ι] {dι : DecidableEq ι} :
    IsChannel (fun X : Matrix ι ι ℂ => X) :=
  S192CIP_isChannel_of (fun _ : Unit => (1 : Matrix ι ι ℂ)) (by simp) (fun ρ => by simp)

lemma S192CIP_tensor_ch {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {dA : DecidableEq A} {dB : DecidableEq B} {dAB : DecidableEq (A × B)}
    {E : Superop A C} {F : Superop B D}
    (hE : IsChannel E) (hF : IsChannel F) : IsChannel (tensorAction E F) := by
  obtain rfl : dA = Classical.decEq A := Subsingleton.elim _ _
  obtain rfl : dB = Classical.decEq B := Subsingleton.elim _ _
  refine S192CIP_ch_of_C _ (fun p q u v => E (Matrix.single p.1 q.1 1) u.1 v.1 *
    F (Matrix.single p.2 q.2 1) u.2 v.2) ?_ ?_ ?_
  · intro X u v
    simp only [tensorAction, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun aa _ =>
      Finset.sum_congr rfl fun bb _ => by ring
  · have := ((S192CIP_choi_psd hE).submatrix
      (fun w : (A × B) × (C × D) => (w.1.1, w.2.1))).hadamard ((S192CIP_choi_psd hF).submatrix
      (fun w : (A × B) × (C × D) => (w.1.2, w.2.2)))
    have e : (Matrix.of fun (a b : (A × B) × (C × D)) => E (Matrix.single a.1.1 b.1.1 1) a.2.1 b.2.1 *
        F (Matrix.single a.1.2 b.1.2 1) a.2.2 b.2.2) = ((choi E).submatrix
      (fun w : (A × B) × (C × D) => (w.1.1, w.2.1)) (fun w : (A × B) × (C × D) => (w.1.1, w.2.1)))
        ⊙ ((choi F).submatrix (fun w : (A × B) × (C × D) => (w.1.2, w.2.2))
          (fun w : (A × B) × (C × D) => (w.1.2, w.2.2))) := by
      ext a b; simp [choi, Matrix.hadamard_apply]
    rw [e]; exact this
  · intro p q
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, S192CIP_trace_C hE, S192CIP_trace_C hF]
    rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
    by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;> simp [h1, h2]

lemma S192CIP_idT_eq {R ι κ : Type} [Fintype R] [Fintype ι] [Fintype κ] {dι : DecidableEq ι}
    {Φ : Superop ι κ} (hΦ : IsChannel Φ) :
    idTensorSuperop (R := R) Φ = tensorAction (fun Y : Matrix R R ℂ => Y) Φ := by
  obtain rfl : dι = Classical.decEq ι := Subsingleton.elim _ _
  funext X; ext u v
  simp only [idTensorSuperop, Matrix.of_apply]
  rw [S192CIP_ch_expand hΦ]
  simp only [tensorAction, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    Matrix.single_apply, ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

lemma S192CIP_idT_ch {R ι κ : Type} [Fintype R] [Fintype ι] [Fintype κ]
    {dι : DecidableEq ι} {dRι : DecidableEq (R × ι)} {Φ : Superop ι κ} (hΦ : IsChannel Φ) :
    IsChannel (idTensorSuperop (R := R) Φ) := by
  rw [S192CIP_idT_eq hΦ]
  exact S192CIP_tensor_ch (dA := Classical.decEq R) S192CIP_id_ch hΦ

lemma S192CIP_reidx_ch {α β : Type*} [Fintype α] [Fintype β] {dβ : DecidableEq β} (e : α ≃ β) :
    IsChannel (fun X : Matrix β β ℂ => (Matrix.of fun u v : α => X (e u) (e v))) := by
  refine S192CIP_ch_of_C _ (fun p q u v => (if p = e u then 1 else 0) * (if q = e v then 1 else 0))
    ?_ ?_ ?_
  · intro X u v
    simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  · have := Matrix.posSemidef_vecMulVec_self_star
      (fun w : β × α => if w.1 = e w.2 then (1 : ℂ) else 0)
    convert this using 1
    ext a b
    simp [Matrix.vecMulVec_apply, apply_ite star]
  · intro p q
    rw [Finset.sum_eq_single (e.symm p) (fun b _ hb => by
      have : p ≠ e b := fun h => hb (by rw [h]; simp)
      simp [this]) (by simp)]
    by_cases h : p = q
    · subst h; simp
    · simp [h, Ne.symm h]

lemma S192CIP_fwd_ch {A B I K Q R : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype K]
    [Fintype Q] [Fintype R] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
    {dAB : DecidableEq (A × B)} {dRB : DecidableEq (R × B)}
    {E : Superop A (I × Q)} {F : Superop Q R} {D : Superop (R × B) K}
    (hE : IsChannel E) (hF : IsChannel F) (hD : IsChannel D) : IsChannel (forwardOp E F D) := by
  obtain rfl : dAB = Classical.decEq _ := Subsingleton.elim _ _
  obtain rfl : dRB = Classical.decEq _ := Subsingleton.elim _ _
  have h1 := S192CIP_tensor_ch (B := B) (dB := Classical.decEq B) (dAB := Classical.decEq _)
    hE S192CIP_id_ch
  have h2 := S192CIP_reidx_ch (β := (I × Q) × B) (dβ := Classical.decEq _)
    (Equiv.prodAssoc I Q B).symm
  have h3 := S192CIP_idT_ch (R := I) (dRι := Classical.decEq _)
    (S192CIP_tensor_ch (B := B) (dB := Classical.decEq B) (dAB := Classical.decEq _)
      hF S192CIP_id_ch)
  have h4 := S192CIP_idT_ch (R := I) (dRι := Classical.decEq _) hD
  have := S192CIP_comp_ch h4 (S192CIP_comp_ch h3 (S192CIP_comp_ch h2 h1))
  convert this using 1
  funext X; rfl

lemma S192CIP_tAid_apply {A B C : Type} [Fintype A] [Fintype B] (E : Superop A C)
    (X : Matrix (A × B) (A × B) ℂ) (c c' : C) (b b' : B) :
    tensorAction E (fun Y : Matrix B B ℂ => Y) X (c, b) (c', b') =
      ∑ a, ∑ aa, X (a, b) (aa, b') * E (Matrix.single a aa 1) c c' := by
  simp only [tensorAction, Matrix.single_apply, ite_and, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun aa _ => ?_
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

lemma S192CIP_idT_apply {R ι κ : Type} [Fintype ι] {dι : DecidableEq ι} {Φ : Superop ι κ}
    [Fintype κ] (hΦ : IsChannel Φ) (X : Matrix (R × ι) (R × ι) ℂ) (u v : R × κ) :
    idTensorSuperop Φ X u v = ∑ i, ∑ i', X (u.1, i) (v.1, i') *
      Φ (@Matrix.single _ _ _ (Classical.decEq ι) (Classical.decEq ι) _ i i' 1) u.2 v.2 := by
  obtain rfl : dι = Classical.decEq ι := Subsingleton.elim _ _
  simp only [idTensorSuperop, Matrix.of_apply]
  rw [S192CIP_ch_expand hΦ]
  simp [Matrix.sum_apply]

lemma S192CIP_fwd_apply {A B I K Q R : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype K]
    [Fintype Q] [Fintype R] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
    {dRB : DecidableEq (R × B)}
    (E : Superop A (I × Q)) (F : Superop Q R) {D : Superop (R × B) K}
    (hD : IsChannel D) (X : Matrix (A × B) (A × B) ℂ) (u v : I × K) :
    forwardOp E F D X u v = ∑ i : R × B, ∑ i' : R × B,
      (∑ q, ∑ q', (∑ a, ∑ aa, X (a, i.2) (aa, i'.2) *
        E (@Matrix.single _ _ _ (Classical.decEq A) (Classical.decEq A) _ a aa 1) (u.1, q) (v.1, q'))
        * F (@Matrix.single _ _ _ (Classical.decEq Q) (Classical.decEq Q) _ q q' 1) i.1 i'.1) *
        D (@Matrix.single _ _ _ (Classical.decEq _) (Classical.decEq _) _ i i' 1) u.2 v.2 := by
  unfold forwardOp
  rw [S192CIP_idT_apply hD]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  congr 1
  rcases i with ⟨r, b⟩; rcases i' with ⟨r', b'⟩
  simp only [idTensorSuperop, Matrix.of_apply, S192CIP_tAid_apply]

lemma S192CIP_trF_ch {Q R : Type} [Fintype Q] [Fintype R] {dQ : DecidableEq Q} {F : Superop Q R}
    (hF : Horodecki F) : IsChannel (fun Y => (F Y)ᵀ) := by
  obtain rfl : dQ = Classical.decEq Q := Subsingleton.elim _ _
  refine S192CIP_ch_of_C _ (fun p q u v => F (Matrix.single p q 1) v u) (fun X u v => ?_) ?_
    (fun p q => S192CIP_trace_C hF.1 p q)
  · rw [Matrix.transpose_apply, S192CIP_ch_expand hF.1 X]
    simp [Matrix.sum_apply]
  · have := hF.2
    convert this using 1
    ext ⟨p, u⟩ ⟨q, v⟩
    simp [pt, choi]

lemma S192CIP_trD_ch {A K : Type} [Fintype A] [Fintype K] {dA : DecidableEq A} {D : Superop A K}
    (hD : IsChannel D) : IsChannel (fun Y => (D Yᵀ)ᵀ) := by
  obtain rfl : dA = Classical.decEq A := Subsingleton.elim _ _
  refine S192CIP_ch_of_C _ (fun p q u v => D (Matrix.single q p 1) v u) (fun X u v => ?_) ?_
    (fun p q => ?_)
  · rw [Matrix.transpose_apply, S192CIP_ch_expand hD]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply]
    rw [Finset.sum_comm]
  · have e : (Matrix.of fun (a b : A × K) => D (Matrix.single b.1 a.1 1) b.2 a.2) = (choi D)ᵀ := by
      ext a b; simp [choi]
    show (Matrix.of fun (a b : A × K) => D (Matrix.single b.1 a.1 1) b.2 a.2).PosSemidef
    rw [e]; exact (S192CIP_choi_psd hD).transpose
  · rw [S192CIP_trace_C hD]
    by_cases h : p = q
    · simp [h]
    · simp [h, Ne.symm h]

lemma S192CIP_pt_fwd {A B I K Q R : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype K]
    [Fintype Q] [Fintype R] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
    {dRB : DecidableEq (R × B)}
    (E : Superop A (I × Q)) (F : Superop Q R) {D : Superop (R × B) K} (hD : IsChannel D)
    (hD' : IsChannel (fun Y : Matrix (R × B) (R × B) ℂ => (D Yᵀ)ᵀ)) :
    (fun X => pt (forwardOp E F D (pt X))) =
      forwardOp E (fun Y => (F Y)ᵀ) (fun Y => (D Yᵀ)ᵀ) := by
  funext X; ext u v
  rw [show pt (forwardOp E F D (pt X)) u v = forwardOp E F D (pt X) (u.1, v.2) (v.1, u.2) from rfl,
    S192CIP_fwd_apply E F hD, S192CIP_fwd_apply E _ hD']
  simp only [Matrix.transpose_apply, Matrix.transpose_single, pt]
  rw [Finset.sum_comm]

lemma S192CIP_cls_horo {Q R : Type} [Fintype Q] [Fintype R] {F : Superop Q R}
    (hF : IsClassicalSideChannel F) : Horodecki F := by
  refine ⟨hF.1, ?_⟩
  have e : pt (choi F) = choi F := by
    ext ⟨p, u⟩ ⟨q, v⟩
    simp only [pt, choi]
    by_cases h : u = v
    · subst h; rfl
    · rw [← hF.2.2 (Matrix.single p q 1)]
      simp [dephasing, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [e]; exact S192CIP_choi_psd hF.1

def S192CIP_dropR {A C : Type} (G : Superop A C) : Superop (A × Fin 1) C :=
  fun X => G (Matrix.of fun a a' => X (a, 0) (a', 0))

def S192CIP_dropL {A C : Type} (G : Superop A C) : Superop (Fin 1 × A) C :=
  fun X => G (Matrix.of fun a a' => X (0, a) (0, a'))

def S192CIP_app {A C : Type} (G : Superop A C) : Superop A (C × Fin 1) :=
  fun X => Matrix.of fun p q => G X p.1 q.1

lemma S192CIP_dropR_single {A C : Type} {d : DecidableEq (A × Fin 1)} (G : Superop A C) (p q : A × Fin 1) :
    S192CIP_dropR G (Matrix.single p q 1) = G (Matrix.single p.1 q.1 1) := by
  unfold S192CIP_dropR; congr 1
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  obtain rfl : p2 = 0 := Subsingleton.elim _ _
  obtain rfl : q2 = 0 := Subsingleton.elim _ _
  ext a b; simp [Matrix.single_apply]

lemma S192CIP_dropL_single {A C : Type} {d : DecidableEq (Fin 1 × A)} (G : Superop A C) (p q : Fin 1 × A) :
    S192CIP_dropL G (Matrix.single p q 1) = G (Matrix.single p.2 q.2 1) := by
  unfold S192CIP_dropL; congr 1
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  obtain rfl : p1 = 0 := Subsingleton.elim _ _
  obtain rfl : q1 = 0 := Subsingleton.elim _ _
  ext a b; simp [Matrix.single_apply]

lemma S192CIP_dropR_ch {A C : Type} [Fintype A] [Fintype C] {dA : DecidableEq A} {G : Superop A C}
    (hG : IsChannel G) {d1 : DecidableEq (A × Fin 1)} : IsChannel (S192CIP_dropR G) := by
  obtain rfl : dA = Classical.decEq A := Subsingleton.elim _ _
  refine S192CIP_ch_of_C _ (fun p q u v => G (Matrix.single p.1 q.1 1) u v) (fun X u v => ?_) ?_
    (fun p q => ?_)
  · simp only [S192CIP_dropR]
    rw [S192CIP_ch_expand hG]
    simp [Matrix.sum_apply, Fintype.sum_prod_type]
  · have := (S192CIP_choi_psd hG).submatrix (fun w : (A × Fin 1) × C => (w.1.1, w.2))
    convert this using 1
    ext a b; simp [choi]
  · rw [S192CIP_trace_C hG]
    have : p = q ↔ p.1 = q.1 := ⟨fun h => h ▸ rfl, fun h => Prod.ext h (Subsingleton.elim _ _)⟩
    by_cases h : p.1 = q.1
    · simp [h, this.mpr h]
    · rw [if_neg h, if_neg (fun e => h (this.mp e))]

lemma S192CIP_dropL_ch {A C : Type} [Fintype A] [Fintype C] {dA : DecidableEq A} {G : Superop A C}
    (hG : IsChannel G) {d1 : DecidableEq (Fin 1 × A)} : IsChannel (S192CIP_dropL G) := by
  obtain rfl : dA = Classical.decEq A := Subsingleton.elim _ _
  refine S192CIP_ch_of_C _ (fun p q u v => G (Matrix.single p.2 q.2 1) u v) (fun X u v => ?_) ?_
    (fun p q => ?_)
  · simp only [S192CIP_dropL]
    rw [S192CIP_ch_expand hG]
    simp [Matrix.sum_apply, Fintype.sum_prod_type]
  · have := (S192CIP_choi_psd hG).submatrix (fun w : (Fin 1 × A) × C => (w.1.2, w.2))
    convert this using 1
    ext a b; simp [choi]
  · rw [S192CIP_trace_C hG]
    have : p = q ↔ p.2 = q.2 := ⟨fun h => h ▸ rfl, fun h => Prod.ext (Subsingleton.elim _ _) h⟩
    by_cases h : p.2 = q.2
    · simp [h, this.mpr h]
    · rw [if_neg h, if_neg (fun e => h (this.mp e))]

lemma S192CIP_app_ch {A C : Type} [Fintype A] [Fintype C] {dA : DecidableEq A} {G : Superop A C}
    (hG : IsChannel G) : IsChannel (S192CIP_app G) := by
  refine S192CIP_ch_of_C _ (fun p q u v => G (Matrix.single p q 1) u.1 v.1) (fun X u v => ?_) ?_
    (fun p q => ?_)
  · simp only [S192CIP_app, Matrix.of_apply]
    rw [S192CIP_ch_expand hG]
    simp [Matrix.sum_apply]
  · have := (S192CIP_choi_psd hG).submatrix (fun w : A × (C × Fin 1) => (w.1, w.2.1))
    convert this using 1
    ext a b; simp [choi]
  · rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_one]
    exact S192CIP_trace_C hG p q

lemma S192CIP_sum4 {α α' β β' : Type*} [Fintype α] [Fintype α'] [Fintype β] [Fintype β']
    (f : α → α' → β → β' → ℂ) :
    ∑ a, ∑ aa, ∑ b, ∑ bb, f a aa b bb = ∑ b, ∑ bb, ∑ a, ∑ aa, f a aa b bb := by
  calc ∑ a, ∑ aa, ∑ b, ∑ bb, f a aa b bb = ∑ a, ∑ b, ∑ aa, ∑ bb, f a aa b bb :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ aa, ∑ bb, f a aa b bb := Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ bb, ∑ aa, f a aa b bb :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ b, ∑ bb, ∑ a, ∑ aa, f a aa b bb := Finset.sum_congr rfl fun b _ => Finset.sum_comm

lemma S192CIP_ua_ea {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsForwardCode K .UA Z) :
    IsForwardCode K .EA Z := by
  obtain ⟨hZc, hNS, E, D, hE, hD, rfl⟩ := hZ
  refine ⟨hZc, hNS, 1, 1, one_pos, one_pos, 1, S192CIP_dropR E, S192CIP_dropR D,
    ⟨Matrix.PosSemidef.one, by simp⟩, S192CIP_dropR_ch hE, S192CIP_dropR_ch hD, ?_⟩
  funext X; ext u v
  simp only [eaOp, tensorAction, S192CIP_dropR_single, Fintype.sum_prod_type, Fin.sum_univ_one,
    Matrix.one_apply_eq, mul_one]

lemma S192CIP_ua_fca {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsForwardCode K .UA Z) :
    IsForwardCode K .FCA Z := by
  obtain ⟨hZc, hNS, E, D, hE, hD, rfl⟩ := hZ
  refine ⟨hZc, hNS, 1, 1, one_pos, one_pos, S192CIP_app E, fun Y => Y, S192CIP_dropL D,
    S192CIP_app_ch hE, ⟨S192CIP_id_ch, fun X => ?_, fun X => ?_⟩, S192CIP_dropL_ch hD, ?_⟩
  · ext i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [dephasing]
  · ext i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [dephasing]
  · funext X; ext u v
    rw [S192CIP_fwd_apply _ _ (S192CIP_dropL_ch (d1 := Classical.decEq _) hD)]
    simp only [tensorAction, Fintype.sum_prod_type, Fin.sum_univ_one, S192CIP_dropL_single,
      S192CIP_app, Matrix.of_apply, Matrix.single_apply_same, mul_one, Finset.sum_mul]
    rw [S192CIP_sum4]

lemma S192CIP_fca_fha {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsForwardCode K .FCA Z) :
    IsForwardCode K .FHA Z := by
  obtain ⟨hZc, hNS, q, r, hq, hr, E, F, D, hE, hF, hD, rfl⟩ := hZ
  exact ⟨hZc, hNS, q, r, hq, hr, E, F, D, hE, S192CIP_cls_horo hF, hD, rfl⟩

lemma S192CIP_fha_ppt {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsForwardCode K .FHA Z) :
    IsForwardCode K .PPTp Z := by
  obtain ⟨hZc, hNS, q, r, hq, hr, E, F, D, hE, hF, hD, rfl⟩ := hZ
  refine ⟨hZc, hNS, by convert hZc, ?_⟩
  have e := S192CIP_pt_fwd E F hD (S192CIP_trD_ch hD)
  have h := S192CIP_fwd_ch (dAB := Classical.decEq _) hE (S192CIP_trF_ch hF) (S192CIP_trD_ch hD)
  convert h using 1

lemma S192CIP_prod_psd {m ι : Type*} [Fintype m] (s : Finset ι) (M : ι → Matrix m m ℂ)
    (h : ∀ i, (M i).PosSemidef) : (Matrix.of fun a b => ∏ i ∈ s, M i a b).PosSemidef := by
  induction s using Finset.induction_on with
  | empty =>
    have e : (Matrix.of fun a b => ∏ i ∈ (∅ : Finset ι), M i a b) =
        Matrix.vecMulVec (fun _ : m => (1 : ℂ)) (star fun _ : m => (1 : ℂ)) := by
      ext a b; simp [Matrix.vecMulVec_apply]
    rw [e]; exact Matrix.posSemidef_vecMulVec_self_star _
  | insert j s hj ih =>
    have e : (Matrix.of fun a b => ∏ i ∈ insert j s, M i a b) =
        M j ⊙ Matrix.of fun a b => ∏ i ∈ s, M i a b := by
      ext a b; simp [Finset.prod_insert hj, Matrix.hadamard_apply]
    rw [e]; exact (h j).hadamard ih

lemma S192CIP_pi_ch {ι κ : Type} [Fintype ι] [Fintype κ] {dι : DecidableEq ι} {N : Superop ι κ}
    (hN : IsChannel N) (n : ℕ) {dι2 : DecidableEq ι} {dpi : DecidableEq (Fin n → ι)} :
    IsChannel (piSuperop (fun _ : Fin n => N)) := by
  obtain rfl : dι = Classical.decEq ι := Subsingleton.elim _ _
  obtain rfl : dι2 = Classical.decEq ι := Subsingleton.elim _ _
  refine S192CIP_ch_of_C _ (fun x x' y y' => ∏ i, N (Matrix.single (x i) (x' i) 1) (y i) (y' i))
    (fun X u v => rfl) ?_ (fun x x' => ?_)
  · have := S192CIP_prod_psd Finset.univ (fun i : Fin n => (choi N).submatrix
      (fun w : (Fin n → ι) × (Fin n → κ) => (w.1 i, w.2 i))
      (fun w : (Fin n → ι) × (Fin n → κ) => (w.1 i, w.2 i)))
      (fun i => (S192CIP_choi_psd hN).submatrix _)
    convert this using 1
    ext a b; simp [choi]
  · rw [← Fintype.prod_sum (fun i o => N (Matrix.single (x i) (x' i) 1) o o)]
    simp only [S192CIP_trace_C hN]
    by_cases h : x = x'
    · subst h; simp
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      rw [if_neg h]; exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma S192CIP_fid01 {I O : Type} [Fintype I] [Fintype O] (N : Superop I O) (hN : IsChannel N)
    (K : ℕ) (c : CodeAssistance) (Z : Superop (Fin K × O) (I × Fin K))
    (hZ : IsForwardCode K c Z) :
    0 ≤ channelFidelity K (link K N Z) ∧ channelFidelity K (link K N Z) ≤ 1 := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [channelFidelity]
  · exact S192CIP_code_fid N hN K hK Z hZ.1 hZ.2.1

lemma S192CIP_mono {I O : Type} [Fintype I] [Fintype O] (N : Superop I O) (hN : IsChannel N)
    (K : ℕ) (c1 c2 : CodeAssistance)
    (h : ∀ Z : Superop (Fin K × O) (I × Fin K), IsForwardCode K c1 Z → IsForwardCode K c2 Z) :
    optimalCodeFidelity c1 N K ≤ optimalCodeFidelity c2 N K := by
  unfold optimalCodeFidelity
  have hbdd : BddAbove {f | ∃ Z, IsForwardCode K c2 Z ∧ f = channelFidelity K (link K N Z)} :=
    ⟨1, by rintro f ⟨Z, hZ, rfl⟩; exact (S192CIP_fid01 N hN K c2 Z hZ).2⟩
  rcases Set.eq_empty_or_nonempty
      {f | ∃ Z, IsForwardCode K c1 Z ∧ f = channelFidelity K (link K N Z)} with h1 | h1
  · rw [h1, Real.sSup_empty]
    rcases Set.eq_empty_or_nonempty
        {f | ∃ Z, IsForwardCode K c2 Z ∧ f = channelFidelity K (link K N Z)} with h2 | ⟨f, Z, hZ, rfl⟩
    · rw [h2, Real.sSup_empty]
    · exact (S192CIP_fid01 N hN K c2 Z hZ).1.trans (le_csSup hbdd ⟨Z, hZ, rfl⟩)
  · exact csSup_le h1 (by rintro f ⟨Z, hZ, rfl⟩; exact le_csSup hbdd ⟨Z, h Z hZ, rfl⟩)

lemma S192CIP_le1 {I O : Type} [Fintype I] [Fintype O] (N : Superop I O) (hN : IsChannel N)
    (K : ℕ) (c : CodeAssistance) : optimalCodeFidelity c N K ≤ 1 := by
  unfold optimalCodeFidelity
  rcases Set.eq_empty_or_nonempty
      {f | ∃ Z, IsForwardCode K c Z ∧ f = channelFidelity K (link K N Z)} with h | h
  · rw [h, Real.sSup_empty]; norm_num
  · exact csSup_le h (by rintro f ⟨Z, hZ, rfl⟩; exact (S192CIP_fid01 N hN K c Z hZ).2)

lemma S192CIP_cap_mono {I O : Type} [Fintype I] [Fintype O] (N : Superop I O) (hN : IsChannel N)
    (c1 c2 : CodeAssistance)
    (h : ∀ {I' O' : Type} [Fintype I'] [Fintype O'] (K : ℕ) (Z : Superop (Fin K × O') (I' × Fin K)),
      IsForwardCode K c1 Z → IsForwardCode K c2 Z) :
    quantumCodeCapacity c1 N ≤ quantumCodeCapacity c2 N := by
  unfold quantumCodeCapacity
  refine iSup_mono fun r => ?_
  have hpi : ∀ n : ℕ, @IsChannel _ _ _ _ (Classical.decEq _) (piSuperop (fun _ : Fin n => N)) :=
    fun n => S192CIP_pi_ch (dpi := Classical.decEq _) hN n
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso; apply h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
      (fun n => S192CIP_mono _ (hpi n) _ c1 c2 (h _)) (fun n => S192CIP_le1 _ (hpi n) _ _)
  · simp
  · exact le_rfl

end S192CIP
end QAlgorithms.Papers.Independent.Support50.P11

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P11 in
theorem solution {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]
    (N : Superop I O) (hN : IsChannel N) (K : ℕ) (hK : 0 < K) :
    (∀ Z : Superop (Fin K × O) (I × Fin K),
      (IsForwardCode K .UA Z → IsForwardCode K .EA Z) ∧
      (IsForwardCode K .EA Z → IsForwardCode K .NS Z) ∧
      (IsForwardCode K .UA Z → IsForwardCode K .FCA Z) ∧
      (IsForwardCode K .FCA Z → IsForwardCode K .FHA Z) ∧
      (IsForwardCode K .FHA Z → IsForwardCode K .PPTp Z)) ∧
    optimalCodeFidelity .UA N K ≤ optimalCodeFidelity .EA N K ∧ optimalCodeFidelity .EA N K ≤ optimalCodeFidelity .NS N K ∧
    optimalCodeFidelity .UA N K ≤ optimalCodeFidelity .FCA N K ∧ optimalCodeFidelity .FCA N K ≤ optimalCodeFidelity .FHA N K ∧
    optimalCodeFidelity .FHA N K ≤ optimalCodeFidelity .PPTp N K ∧
    quantumCodeCapacity .UA N ≤ quantumCodeCapacity .EA N ∧ quantumCodeCapacity .EA N ≤ quantumCodeCapacity .NS N ∧
    quantumCodeCapacity .UA N ≤ quantumCodeCapacity .FCA N ∧ quantumCodeCapacity .FCA N ≤ quantumCodeCapacity .FHA N ∧
    quantumCodeCapacity .FHA N ≤ quantumCodeCapacity .PPTp N := by
  refine ⟨fun Z => ⟨S192CIP_ua_ea K Z, S192CIP_ea_ns K Z, S192CIP_ua_fca K Z, S192CIP_fca_fha K Z,
      S192CIP_fha_ppt K Z⟩,
    S192CIP_mono N hN K _ _ (S192CIP_ua_ea K), S192CIP_mono N hN K _ _ (S192CIP_ea_ns K),
    S192CIP_mono N hN K _ _ (S192CIP_ua_fca K), S192CIP_mono N hN K _ _ (S192CIP_fca_fha K),
    S192CIP_mono N hN K _ _ (S192CIP_fha_ppt K),
    S192CIP_cap_mono N hN _ _ (fun K Z => S192CIP_ua_ea K Z),
    S192CIP_cap_mono N hN _ _ (fun K Z => S192CIP_ea_ns K Z),
    S192CIP_cap_mono N hN _ _ (fun K Z => S192CIP_ua_fca K Z),
    S192CIP_cap_mono N hN _ _ (fun K Z => S192CIP_fca_fha K Z),
    S192CIP_cap_mono N hN _ _ (fun K Z => S192CIP_fha_ppt K Z)⟩
