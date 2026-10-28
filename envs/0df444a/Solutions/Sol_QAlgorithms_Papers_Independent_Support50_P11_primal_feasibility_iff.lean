-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P11.primal_feasibility_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:07:56.968987+00:00
-- url     : https://prove2.me/submissions/5329ac36-c8ca-460a-803d-4febb703bcc8

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

section S192P11
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma S192P11_ch_trace {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) (X : Matrix ι ι ℂ) : (Φ X).trace = X.trace := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ]
  unfold krausApply
  calc (∑ j, E j * X * (E j)ᴴ).trace = ∑ j, ((E j)ᴴ * E j * X).trace := by
        rw [Matrix.trace_sum]; congr 1; ext j; rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = ((∑ j, (E j)ᴴ * E j) * X).trace := by rw [Finset.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [show (∑ j, (E j)ᴴ * E j) = 1 from hE, Matrix.one_mul]

lemma S192P11_ch_smul {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) (c : ℂ) (X : Matrix ι ι ℂ) : Φ (c • X) = c • Φ X := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ, hΦ]
  unfold krausApply
  simp [Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

lemma S192P11_choi_psd {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) : (choi Φ).PosSemidef := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  have : choi Φ = ∑ j, Matrix.vecMulVec (fun p : ι × κ => E j p.2 p.1)
      (star (fun p : ι × κ => E j p.2 p.1)) := by
    ext ⟨p, r⟩ ⟨q, s⟩
    simp [choi, hΦ, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.vecMulVec_apply, ite_and, Finset.sum_ite_eq, ite_mul]
  rw [this]
  exact Matrix.posSemidef_sum _ fun j _ => Matrix.posSemidef_vecMulVec_self_star _

lemma S192P11_pt_single {A B : Type*} [DecidableEq A] [DecidableEq B] (a b : A) (β γ : B) :
    pt (Matrix.single (a, β) (b, γ) (1 : ℂ)) = Matrix.single (a, γ) (b, β) 1 := by
  ext p q
  simp only [pt, Matrix.single_apply, Prod.ext_iff]
  by_cases h1 : a = p.1 <;> by_cases h2 : γ = p.2 <;> by_cases h3 : b = q.1 <;>
    by_cases h4 : β = q.2 <;> simp [h1, h2, h3, h4]

lemma S192P11_contract {U X : Type*} [Fintype U] [Fintype X] {P : Matrix X X ℂ}
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

lemma S192P11_contract' {U X : Type*} [Fintype U] [Fintype X] {P : Matrix X X ℂ}
    {Q : Matrix (U × X) (U × X) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (M : Matrix U U ℂ) (hM : ∀ u v, M u v = ∑ x, ∑ y, P x y * Q (u, x) (v, y)) :
    M.PosSemidef := by
  rw [show M = Matrix.of fun u v => ∑ x, ∑ y, P x y * Q (u, x) (v, y) from Matrix.ext hM]
  exact S192P11_contract hP hQ

lemma S192P11_fid (K : ℕ) (hK : 0 < K) (L : Superop (Fin K) (Fin K))
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

lemma S192P11_link_smul {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) (c : ℂ) (X : Matrix (Fin K) (Fin K) ℂ) :
    link K N Z (c • X) = c • link K N Z X := by
  ext b d
  simp [link, Finset.mul_sum, mul_assoc]

lemma S192P11_link_entry {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) (a b : Fin K) :
    link K N Z (Matrix.single a b 1) a b = ∑ i, ∑ j, ∑ β, ∑ γ,
      N (Matrix.single i j 1) β γ * Z (Matrix.single (a, β) (b, γ) 1) (i, a) (j, b) := by
  simp [link, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

lemma S192P11_ch_psd {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) {M : Matrix ι ι ℂ} (hM : M.PosSemidef) : (Φ M).PosSemidef := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ]
  exact Matrix.posSemidef_sum _ fun j _ => hM.mul_mul_conjTranspose_same (E j)

lemma S192P11_single_psd {n : Type*} [Fintype n] [DecidableEq n] (a : n) :
    (Matrix.single a a (1 : ℂ)).PosSemidef := by
  have : Matrix.single a a (1 : ℂ) = Matrix.vecMulVec (Pi.single a 1) (star (Pi.single a 1)) := by
    ext x y
    simp only [Matrix.single_apply, Matrix.vecMulVec_apply, Pi.star_apply, Pi.single_apply]
    by_cases h1 : x = a <;> by_cases h2 : y = a <;> simp [h1, h2, @eq_comm _ a]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

lemma S192P11_trR_single {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
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

lemma S192P11_trL_single {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
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
def S192P11_Lz {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) : Matrix (I × O) (I × O) ℂ :=
  ((K : ℂ)^2)⁻¹ • ∑ a, ∑ b, Matrix.of (fun u v : I × O =>
    Z (Matrix.single (a, u.2) (b, v.2) 1) (u.1, a) (v.1, b))

lemma S192P11_Lz_apply {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (u v : I × O) :
    S192P11_Lz K Z u v = ((K : ℂ)^2)⁻¹ *
      ∑ a, ∑ b, Z (Matrix.single (a, u.2) (b, v.2) 1) (u.1, a) (v.1, b) := by
  simp [S192P11_Lz, Matrix.sum_apply]

lemma S192P11_obj {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) :
    primalObjective N (S192P11_Lz K Z) = channelFidelity K (link K N Z) := by
  rw [S192P11_fid K hK _ (S192P11_link_smul K N Z)]
  simp only [S192P11_link_entry]
  unfold primalObjective S192P11_Lz
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


lemma S192P11_psd_of_sq {n : Type*} [Fintype n] (A : Matrix n n ℂ) (c : ℝ) (hc : 0 < c)
    (h : Aᴴ * A = (c : ℂ) • A) : A.PosSemidef := by
  have e : A = ((c⁻¹ : ℝ) : ℂ) • (Aᴴ * A) := by
    rw [h, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_smul]
  rw [e]
  exact (Matrix.posSemidef_conjTranspose_mul_self A).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))

lemma S192P11_Lz_psd {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsChannel Z) : (S192P11_Lz K Z).PosSemidef := by
  have hC := S192P11_choi_psd hZ
  let f : (I × O) × Fin K → (Fin K × O) × (I × Fin K) := fun w => ((w.2, w.1.2), (w.1.1, w.2))
  refine S192P11_contract' (Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin K => (K : ℂ)⁻¹))
    (hC.submatrix f) _ fun u v => ?_
  rw [S192P11_Lz_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, Matrix.submatrix_apply, choi, f]
  rw [show star (K:ℂ)⁻¹ = (K:ℂ)⁻¹ by simp]
  ring

def S192P11_rho {I : Type} [Fintype I] (K : ℕ) (E : Superop (Fin K) I) : Matrix I I ℂ :=
  (K : ℂ)⁻¹ • ∑ a, E (Matrix.single a a 1)

lemma S192P11_Kinv_nonneg (K : ℕ) : (0 : ℂ) ≤ (K : ℂ)⁻¹ := by
  rw [show (K : ℂ)⁻¹ = (((K : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  exact Complex.zero_le_real.mpr (by positivity)

lemma S192P11_rho_dens {I : Type} [Fintype I] (K : ℕ) (hK : 0 < K) (E : Superop (Fin K) I)
    (hE : IsChannel E) : IsDensityMatrix (S192P11_rho K E) := by
  refine ⟨(Matrix.posSemidef_sum _ fun a _ => S192P11_ch_psd hE (S192P11_single_psd a)).smul
    (S192P11_Kinv_nonneg K), ?_⟩
  simp only [S192P11_rho, Matrix.trace_smul, Matrix.trace_sum, S192P11_ch_trace hE,
    Matrix.trace_single_eq_same, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, nsmul_eq_mul, mul_one]
  have : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp

lemma S192P11_nsba {I O : Type} [Fintype I] [Fintype O] {K : ℕ}
    {Z : Superop (Fin K × O) (I × Fin K)} {E : Superop (Fin K) I} (hE : IsChannel E)
    (hEZ : ∀ X, traceRight (Z X) = E (traceRight X)) (a : Fin K) (β γ : O) (i j : I) :
    ∑ c, Z (Matrix.single (a, β) (a, γ) 1) (i, c) (j, c) =
      (if β = γ then 1 else 0) * E (Matrix.single a a 1) i j := by
  rw [show ∑ c, Z (Matrix.single (a, β) (a, γ) 1) (i, c) (j, c) =
    traceRight (Z (Matrix.single (a, β) (a, γ) 1)) i j from rfl, hEZ, S192P11_trR_single,
    S192P11_ch_smul hE]
  rfl

lemma S192P11_phi_sum (K : ℕ) (G : (Fin K × Fin K) → (Fin K × Fin K) → ℂ) :
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

lemma S192P11_P2_sum (K : ℕ) (c : ℂ) (G : (Fin K × Fin K) → (Fin K × Fin K) → ℂ) :
    ∑ x : Fin K × Fin K, ∑ y : Fin K × Fin K,
      c * ((if x = y then (1 : ℂ) else 0) -
        c * ((if x.1 = x.2 then (1 : ℂ) else 0) * (if y.1 = y.2 then 1 else 0))) * G x y =
      c * ∑ x, G x x - c * c * ∑ a, ∑ b, G (a, a) (b, b) := by
  rw [← S192P11_phi_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp [mul_ite, ite_mul]
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring

lemma S192P11_loew {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsChannel Z) (E : Superop (Fin K) I)
    (hE : IsChannel E) (hEZ : ∀ X, traceRight (Z X) = E (traceRight X)) :
    Loewner (S192P11_Lz K Z) (Matrix.kronecker (S192P11_rho K E) 1) := by
  unfold Loewner
  have hC := S192P11_choi_psd hZ
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
    (S192P11_psd_of_sq _ 1 one_pos hPi).smul (S192P11_Kinv_nonneg K)
  let g : (I × O) × (Fin K × Fin K) → (Fin K × O) × (I × Fin K) :=
    fun w => ((w.2.1, w.1.2), (w.1.1, w.2.2))
  refine S192P11_contract' hP2 (hC.submatrix g) _ fun u v => ?_
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, J, Matrix.of_apply,
    smul_eq_mul, φ]
  rw [S192P11_P2_sum]
  simp only [Matrix.submatrix_apply, choi, g, Fintype.sum_prod_type, S192P11_nsba hE hEZ]
  rw [S192P11_Lz_apply]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, S192P11_rho, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, Matrix.one_apply]
  rw [← Finset.mul_sum]
  rw [hc]
  ring


lemma S192P11_trL_Lz {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (D : Superop O (Fin K)) (hD : IsChannel D)
    (hDZ : ∀ X, traceLeft (Z X) = D (traceLeft X)) :
    traceLeft (S192P11_Lz K Z) = ((K : ℂ)^2)⁻¹ • 1 := by
  ext β γ
  simp only [traceLeft, Matrix.of_apply, S192P11_Lz_apply, Matrix.smul_apply, Matrix.one_apply,
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
          traceLeft (Z (Matrix.single (a, β) (b, γ) 1)) a b from rfl, hDZ, S192P11_trL_single,
          S192P11_ch_smul hD]
        rfl
    _ = (D (Matrix.single β γ 1)).trace := by
        simp [ite_mul, Matrix.trace]
    _ = _ := by
        rw [S192P11_ch_trace hD]
        simp [Matrix.trace, Matrix.single_apply, ite_and]
        by_cases h : β = γ
        · simp [h]
        · simp [h, Ne.symm h]

lemma S192P11_P3_sum (K : ℕ) (d s : ℂ) (G : (Fin K × Fin K) → (Fin K × Fin K) → ℂ) :
    ∑ x : Fin K × Fin K, ∑ y : Fin K × Fin K,
      d * ((if x = y then (1 : ℂ) else 0) + s * (if y = x.swap then 1 else 0)) * G x y =
      d * ∑ x, G x x + d * s * ∑ x, G x x.swap := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp [mul_ite, ite_mul]
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp [mul_ite, ite_mul, mul_assoc]

lemma S192P11_ppt {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ' : IsChannel (fun X => pt (Z (pt X))))
    (E : Superop (Fin K) I)
    (hE : IsChannel E) (hEZ : ∀ X, traceRight (Z X) = E (traceRight X)) :
    Loewner (-((K : ℂ)⁻¹ • Matrix.kronecker (S192P11_rho K E) 1)) (pt (S192P11_Lz K Z)) ∧
      Loewner (pt (S192P11_Lz K Z)) ((K : ℂ)⁻¹ • Matrix.kronecker (S192P11_rho K E) 1) := by
  have hC := S192P11_choi_psd hZ'
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
  have hP1 := (S192P11_psd_of_sq _ 2 two_pos h1).smul hd
  have hP2 := (S192P11_psd_of_sq _ 2 two_pos h2).smul hd
  let g : (I × O) × (Fin K × Fin K) → (Fin K × O) × (I × Fin K) :=
    fun w => ((w.2.1, w.1.2), (w.1.1, w.2.2))
  have hQ : ∀ (u v : I × O) (x y : Fin K × Fin K), (choi (fun X => pt (Z (pt X)))).submatrix g g
      (u, x) (v, y) = Z (Matrix.single (x.1, v.2) (y.1, u.2) 1) (u.1, y.2) (v.1, x.2) := by
    intro u v x y
    simp only [Matrix.submatrix_apply, choi, g, S192P11_pt_single]
    rfl
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  constructor
  · unfold Loewner
    refine S192P11_contract' hP1 (hC.submatrix g) _ fun u v => ?_
    have := S192P11_P3_sum K ((K : ℂ)^2)⁻¹ 1 (fun x y =>
      (choi (fun X => pt (Z (pt X)))).submatrix g g (u, x) (v, y))
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, F, Matrix.of_apply,
      smul_eq_mul, one_mul] at this ⊢
    rw [this]
    simp only [hQ, Prod.fst_swap, Prod.snd_swap, Fintype.sum_prod_type, S192P11_nsba hE hEZ]
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, pt, S192P11_Lz_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, S192P11_rho, Matrix.sum_apply, smul_eq_mul,
      Matrix.one_apply]
    rw [← Finset.mul_sum]
    by_cases h : u.2 = v.2
    · simp only [h, if_true]; field_simp; ring
    · simp only [h, Ne.symm h, if_false]; ring
  · unfold Loewner
    refine S192P11_contract' hP2 (hC.submatrix g) _ fun u v => ?_
    have := S192P11_P3_sum K ((K : ℂ)^2)⁻¹ (-1) (fun x y =>
      (choi (fun X => pt (Z (pt X)))).submatrix g g (u, x) (v, y))
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, F, Matrix.of_apply,
      smul_eq_mul, neg_one_mul, ← sub_eq_add_neg] at this ⊢
    rw [this]
    simp only [hQ, Prod.fst_swap, Prod.snd_swap, Fintype.sum_prod_type, S192P11_nsba hE hEZ]
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, pt, S192P11_Lz_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, S192P11_rho, Matrix.sum_apply, smul_eq_mul,
      Matrix.one_apply]
    rw [← Finset.mul_sum]
    by_cases h : u.2 = v.2
    · simp only [h, if_true]; field_simp; ring
    · simp only [h, Ne.symm h, if_false]; ring


lemma S192P11_isChannel_of {ι κ ι' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    {_ : DecidableEq ι} {Φ : Superop ι κ} (A : ι' → Matrix κ ι ℂ)
    (hA : ∑ k, (A k)ᴴ * A k = 1) (hΦ : ∀ ρ, Φ ρ = ∑ k, A k * ρ * (A k)ᴴ) : IsChannel Φ := by
  refine ⟨Fintype.card ι', fun j => A ((Fintype.equivFin ι').symm j), ?_, fun ρ => ?_⟩
  · show ∑ j, _ = 1
    rw [Equiv.sum_comp ((Fintype.equivFin ι').symm) (fun k => (A k)ᴴ * A k)]
    exact hA
  · rw [hΦ]
    show _ = ∑ j, _
    exact (Equiv.sum_comp _ (fun k => A k * ρ * (A k)ᴴ)).symm

lemma S192P11_ch_expand {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι}
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

lemma S192P11_decomp {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
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


lemma S192P11_swap3 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] (f : A → B → C → ℂ) :
    ∑ x, ∑ y, ∑ l, f x y l = ∑ l, ∑ y, ∑ x, f x y l := by
  calc ∑ x, ∑ y, ∑ l, f x y l = ∑ x, ∑ l, ∑ y, f x y l :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ l, ∑ x, ∑ y, f x y l := Finset.sum_comm
    _ = ∑ l, ∑ y, ∑ x, f x y l := Finset.sum_congr rfl fun l _ => Finset.sum_comm

lemma S192P11_ch_of_C {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} (Φ : Superop ι κ)
    (C : ι → ι → κ → κ → ℂ) (hΦ : ∀ X u v, Φ X u v = ∑ p, ∑ q, X p q * C p q u v)
    (hC : (Matrix.of fun (a b : ι × κ) => C a.1 b.1 a.2 b.2).PosSemidef)
    (hT : ∀ p q, ∑ u, C p q u u = if p = q then 1 else 0) : IsChannel Φ := by
  obtain ⟨m, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hE : ∀ x y o o', C x y o o' = ∑ l, g l (x, o) * star (g l (y, o')) := by
    intro x y o o'
    have := congrFun (congrFun hg (x, o)) (y, o')
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
  refine S192P11_isChannel_of (fun l : Fin m => (Matrix.of fun (o : κ) (x : ι) => g l (x, o))) ?_ ?_
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
    rw [S192P11_swap3]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun x _ => ?_
    ring

lemma S192P11_repl_ch {A B : Type*} [Fintype A] [Fintype B] {_ : DecidableEq A}
    (σ : Matrix B B ℂ) (hσ : IsDensityMatrix σ) :
    IsChannel (fun Y : Matrix A A ℂ => Y.trace • σ) := by
  refine S192P11_ch_of_C _ (fun p q u v => (if p = q then 1 else 0) * σ u v) (fun X u v => ?_) ?_
    (fun p q => ?_)
  · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [mul_ite, Finset.sum_ite_eq]
  · have : (Matrix.of fun (a b : A × B) => (if a.1 = b.1 then (1:ℂ) else 0) * σ a.2 b.2) =
        (1 : Matrix A A ℂ).submatrix Prod.fst Prod.fst ⊙ σ.submatrix Prod.snd Prod.snd := by
      ext a b; simp [Matrix.hadamard_apply, Matrix.one_apply]
    rw [this]; exact (Matrix.PosSemidef.one.submatrix _).hadamard (hσ.1.submatrix _)
  · rw [← Finset.mul_sum, show ∑ u, σ u u = 1 from hσ.2, mul_one]

lemma S192P11_phi {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] (x y : ι × ι) :
    pureDensity (finiteMaxEntangled ι) x y =
      (Fintype.card ι : ℂ)⁻¹ * ((if x.1 = x.2 then 1 else 0) * (if y.1 = y.2 then 1 else 0)) := by
  have hss : ((↑(√(Fintype.card ι : ℝ)) : ℂ)⁻¹) * (↑(√(Fintype.card ι : ℝ)) : ℂ)⁻¹ =
      (Fintype.card ι : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  simp only [pureDensity, finiteMaxEntangled, Matrix.of_apply, PiLp.toLp_apply]
  split_ifs <;> simp [Complex.conj_ofReal, hss]

/-- entry kernel of reconstructedCode -/
def S192P11_C {I O : Type} (K : ℕ) (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ)
    (p q : Fin K × O) (u v : I × Fin K) : ℂ :=
  (K : ℂ) * ((K : ℂ)⁻¹ * ((if u.2 = p.1 then 1 else 0) * (if v.2 = q.1 then 1 else 0)) *
      L (u.1, p.2) (v.1, q.2) +
    ((if u.2 = v.2 ∧ p.1 = q.1 then 1 else 0) -
      (K : ℂ)⁻¹ * ((if u.2 = p.1 then 1 else 0) * (if v.2 = q.1 then 1 else 0))) *
      (((K : ℂ)^2 - 1)⁻¹ * (rho u.1 v.1 * (if p.2 = q.2 then 1 else 0) - L (u.1, p.2) (v.1, q.2))))

lemma S192P11_Z_apply {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (X : Matrix (Fin K × O) (Fin K × O) ℂ)
    (u v : I × Fin K) :
    reconstructedCode K hK rho L X u v = ∑ p, ∑ q, X p q * S192P11_C K rho L p q u v := by
  simp only [reconstructedCode, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    S192P11_phi, Fintype.card_fin, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Prod.mk.injEq]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a2 _ =>
    Finset.sum_congr rfl fun b2 _ => ?_)
  simp only [S192P11_C]
  ring

lemma S192P11_Z_single {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (p q : Fin K × O) (u v : I × Fin K) :
    reconstructedCode K hK rho L (Matrix.single p q 1) u v = S192P11_C K rho L p q u v := by
  rw [S192P11_Z_apply]
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma S192P11_K1 (K : ℕ) (hK : 2 ≤ K) : (K : ℂ)^2 - 1 ≠ 0 := by
  have h : (1 : ℝ) < (K : ℝ)^2 := by
    have : (2:ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  intro h0
  have := congrArg Complex.re h0
  simp [pow_two] at this
  nlinarith

lemma S192P11_C_trR {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (p q : Fin K × O) (i j : I) :
    ∑ c, S192P11_C K rho L p q (i, c) (j, c) = (if p = q then 1 else 0) * rho i j := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a2, b2⟩ := q
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hK1 := S192P11_K1 K hK
  by_cases ha : a = a2
  · subst ha
    simp [S192P11_C, mul_add, mul_sub, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]
    by_cases hb : b = b2
    · subst hb; simp; field_simp; ring
    · simp [hb]; field_simp; ring
  · rw [Finset.sum_eq_zero]
    · simp [ha]
    intro c _
    simp only [S192P11_C]
    by_cases hc : c = a
    · subst hc; simp [ha]
    · simp [hc, ha]

lemma S192P11_C_trL {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K)
    (rho : Matrix I I ℂ) (hr : rho.trace = 1) (L : Matrix (I × O) (I × O) ℂ)
    (hL : traceLeft L = ((K : ℂ)^2)⁻¹ • 1) (p q : Fin K × O) (c c' : Fin K) :
    ∑ i, S192P11_C K rho L p q (i, c) (i, c') =
      (if p = q then 1 else 0) * ((if c = c' then 1 else 0) * (K : ℂ)⁻¹) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a2, b2⟩ := q
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hK1 := S192P11_K1 K hK
  have hLs : ∀ b b2, ∑ i, L (i, b) (i, b2) = ((K : ℂ)^2)⁻¹ * (if b = b2 then 1 else 0) := by
    intro b b2
    have := congrFun (congrFun hL b) b2
    simpa [traceLeft, Matrix.one_apply] using this
  have hrs : ∑ i, rho i i = 1 := hr
  set d : ℂ := (if c = a then 1 else 0) * (if c' = a2 then 1 else 0) with hd
  set e : ℂ := if c = c' ∧ a = a2 then 1 else 0 with he
  set g : ℂ := ((K : ℂ)^2 - 1)⁻¹ with hg
  set db : ℂ := if b = b2 then 1 else 0 with hdb
  have hpt : ∀ i, S192P11_C K rho L (a, b) (a2, b2) (i, c) (i, c') =
      ((K : ℂ) * ((K : ℂ)⁻¹ * d - (e - (K : ℂ)⁻¹ * d) * g)) * L (i, b) (i, b2) +
      ((K : ℂ) * (e - (K : ℂ)⁻¹ * d) * g * db) * rho i i := by
    intro i
    simp only [S192P11_C, hd, he, hg, hdb]
    ring
  rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hLs, hrs]
  have key : (K : ℂ) * ((K : ℂ)⁻¹ * d - (e - (K : ℂ)⁻¹ * d) * g) * ((K : ℂ)^2)⁻¹ +
      (K : ℂ) * (e - (K : ℂ)⁻¹ * d) * g = e * (K : ℂ)⁻¹ := by
    rw [hg]; field_simp; ring
  by_cases hb : b = b2
  · subst hb
    have hdb1 : db = 1 := by simp [hdb]
    rw [hdb1, if_pos rfl]; simp only [mul_one]; rw [key, he]
    by_cases h1 : c = c' <;> by_cases h2 : a = a2 <;> simp [h1, h2]
  · have hdb0 : db = 0 := by simp [hdb, hb]
    rw [hdb0]
    simp [hb]

lemma S192P11_C_psd {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (hL : L.PosSemidef)
    (hLr : Loewner L (Matrix.kronecker rho 1)) :
    (Matrix.of fun (w w' : (Fin K × O) × (I × Fin K)) =>
      S192P11_C K rho L w.1 w'.1 w.2 w'.2).PosSemidef := by
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
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
  have hP2 : (1 - c • J).PosSemidef := S192P11_psd_of_sq _ 1 one_pos hPi
  have hP1 : (c • J).PosSemidef := by
    have : J = Matrix.vecMulVec φ (star φ) := by
      ext x y
      simp only [J, φ, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, apply_ite star,
        star_one, star_zero]
    rw [this]
    exact (Matrix.posSemidef_vecMulVec_self_star φ).smul (S192P11_Kinv_nonneg K)
  have hgn : (0 : ℂ) ≤ ((K : ℂ)^2 - 1)⁻¹ := by
    rw [show ((K : ℂ)^2 - 1)⁻¹ = ((((K:ℝ)^2 - 1)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    have : (2:ℝ) ≤ K := by exact_mod_cast hK
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr (by nlinarith))
  have hG : (((K : ℂ)^2 - 1)⁻¹ • (Matrix.kronecker rho 1 - L)).PosSemidef := hLr.smul hgn
  have hKn : (0 : ℂ) ≤ (K : ℂ) := by
    rw [show (K : ℂ) = (((K : ℝ)) : ℂ) by push_cast; rfl]
    exact Complex.zero_le_real.mpr (Nat.cast_nonneg _)
  let g1 : (Fin K × O) × (I × Fin K) → Fin K × Fin K := fun w => (w.2.2, w.1.1)
  let g2 : (Fin K × O) × (I × Fin K) → I × O := fun w => (w.2.1, w.1.2)
  have e : (Matrix.of fun (w w' : (Fin K × O) × (I × Fin K)) =>
      S192P11_C K rho L w.1 w'.1 w.2 w'.2) = (K : ℂ) • ((c • J).submatrix g1 g1 ⊙ L.submatrix g2 g2 +
        (1 - c • J).submatrix g1 g1 ⊙ (((K : ℂ)^2 - 1)⁻¹ • (Matrix.kronecker rho 1 - L)).submatrix g2 g2) := by
    ext w w'
    simp only [S192P11_C, J, φ, g1, g2, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.hadamard_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul, Prod.mk.injEq, hc]
  rw [e]
  exact (((hP1.submatrix g1).hadamard (hL.submatrix g2)).add
    ((hP2.submatrix g1).hadamard (hG.submatrix g2))).smul hKn

lemma S192P11_Lz_eq {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K) (hK0 : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) :
    S192P11_Lz K (reconstructedCode K hK0 rho L) = L := by
  have hK0' : (K : ℂ) ≠ 0 := by exact_mod_cast hK0.ne'
  ext u v
  rw [S192P11_Lz_apply]
  simp only [S192P11_Z_single, S192P11_C]
  have hK1 := S192P11_K1 K hK
  simp [mul_add, mul_sub, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  split_ifs <;> field_simp <;> ring

lemma S192P11_comm3' {A B : Type*} [Fintype A] [Fintype B] (f : A → B → A → ℂ) :
    ∑ b, ∑ c, ∑ d, f b c d = ∑ b, ∑ c, ∑ d, f d c b := by
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma S192P11_pt_sum {A B : Type*} [Fintype A] [Fintype B] (F : A × B → A × B → ℂ) :
    ∑ p : A × B, ∑ q : A × B, F (p.1, q.2) (q.1, p.2) = ∑ p, ∑ q, F p q := by
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact S192P11_comm3' (fun b a2 b2 => F (a, b2) (a2, b))

def S192P11_Cp {I O : Type} (K : ℕ) (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ)
    (p q : Fin K × O) (u v : I × Fin K) : ℂ :=
  S192P11_C K rho L (p.1, q.2) (q.1, p.2) (u.1, v.2) (v.1, u.2)

lemma S192P11_Zpt_apply {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (X : Matrix (Fin K × O) (Fin K × O) ℂ)
    (u v : I × Fin K) :
    pt (reconstructedCode K hK rho L (pt X)) u v = ∑ p, ∑ q, X p q * S192P11_Cp K rho L p q u v := by
  show reconstructedCode K hK rho L (pt X) (u.1, v.2) (v.1, u.2) = _
  rw [S192P11_Z_apply]
  exact S192P11_pt_sum (fun p q => X p q * S192P11_Cp K rho L p q u v)

lemma S192P11_Cp_psd {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ)
    (h1 : Loewner (-((K : ℂ)⁻¹ • Matrix.kronecker rho 1)) (pt L))
    (h2 : Loewner (pt L) ((K : ℂ)⁻¹ • Matrix.kronecker rho 1)) :
    (Matrix.of fun (w w' : (Fin K × O) × (I × Fin K)) =>
      S192P11_Cp K rho L w.1 w'.1 w.2 w'.2).PosSemidef := by
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hK1 := S192P11_K1 K hK
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hKp : (K : ℂ) + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hKm : (K : ℂ) - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
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
  have hs1 : (1 + F)ᴴ * (1 + F) = ((2 : ℝ) : ℂ) • (1 + F) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hFh]
    simp only [add_mul, mul_add, one_mul, mul_one, hFF]
    push_cast
    module
  have hs2 : (1 - F)ᴴ * (1 - F) = ((2 : ℝ) : ℂ) • (1 - F) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hFh]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hFF]
    push_cast
    module
  have hh : (0 : ℂ) ≤ (2 : ℂ)⁻¹ := by
    rw [show (2 : ℂ)⁻¹ = (((2 : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.zero_le_real.mpr (by norm_num)
  have hP1 := (S192P11_psd_of_sq _ 2 two_pos hs1).smul hh
  have hP2 := (S192P11_psd_of_sq _ 2 two_pos hs2).smul hh
  have hA0 : (0 : ℂ) ≤ (K : ℂ) / ((K : ℂ) + 1) := by
    rw [show (K : ℂ) / ((K : ℂ) + 1) = ((((K : ℝ) / ((K : ℝ) + 1)) : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.zero_le_real.mpr (by positivity)
  have hB0 : (0 : ℂ) ≤ (K : ℂ) / ((K : ℂ) - 1) := by
    rw [show (K : ℂ) / ((K : ℂ) - 1) = ((((K : ℝ) / ((K : ℝ) - 1)) : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.zero_le_real.mpr (div_nonneg (by linarith) (by linarith))
  have hA := h1.smul hA0
  have hB := h2.smul hB0
  let g1 : (Fin K × O) × (I × Fin K) → Fin K × Fin K := fun w => (w.1.1, w.2.2)
  let g2 : (Fin K × O) × (I × Fin K) → I × O := fun w => (w.2.1, w.1.2)
  have e : (Matrix.of fun (w w' : (Fin K × O) × (I × Fin K)) =>
      S192P11_Cp K rho L w.1 w'.1 w.2 w'.2) =
      ((2 : ℂ)⁻¹ • (1 + F)).submatrix g1 g1 ⊙
        (((K : ℂ) / ((K : ℂ) + 1)) • (pt L - -((K : ℂ)⁻¹ • Matrix.kronecker rho 1))).submatrix g2 g2 +
      ((2 : ℂ)⁻¹ • (1 - F)).submatrix g1 g1 ⊙
        (((K : ℂ) / ((K : ℂ) - 1)) • ((K : ℂ)⁻¹ • Matrix.kronecker rho 1 - pt L)).submatrix g2 g2 := by
    ext ⟨⟨a, b⟩, ⟨i, c⟩⟩ ⟨⟨a2, b2⟩, ⟨j, c'⟩⟩
    simp only [S192P11_Cp, S192P11_C, F, g1, g2, Matrix.of_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.hadamard_apply, Matrix.submatrix_apply,
      Matrix.one_apply, Matrix.neg_apply, pt, Matrix.kronecker, Matrix.kroneckerMap_apply,
      smul_eq_mul, Prod.mk.injEq, Prod.swap_prod_mk]
    have hd1 : (if c' = c ∧ a = a2 then (1 : ℂ) else 0) = if a = a2 ∧ c = c' then 1 else 0 := by
      by_cases h1 : a = a2 <;> by_cases h2 : c = c' <;> simp [h1, h2, eq_comm]
    have hd2 : (if c' = a then (1 : ℂ) else 0) * (if c = a2 then 1 else 0) =
        if a2 = c ∧ c' = a then 1 else 0 := by
      by_cases h1 : c' = a <;> by_cases h2 : c = a2 <;> simp [h1, h2, eq_comm]
    have hd3 : (if b2 = b then (1 : ℂ) else 0) = if b = b2 then 1 else 0 := by
      by_cases h1 : b = b2 <;> simp [h1, eq_comm]
    rw [hd1, hd2, hd3]
    generalize (if a = a2 ∧ c = c' then (1 : ℂ) else 0) = d
    generalize (if a2 = c ∧ c' = a then (1 : ℂ) else 0) = f
    generalize (if b = b2 then (1 : ℂ) else 0) = db
    field_simp
    ring
  rw [e]
  exact ((hP1.submatrix g1).hadamard (hA.submatrix g2)).add
    ((hP2.submatrix g1).hadamard (hB.submatrix g2))

lemma S192P11_trR_trace {A B : Type*} [Fintype A] [Fintype B] (X : Matrix (A × B) (A × B) ℂ) :
    (traceRight X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, traceRight, Matrix.of_apply, Fintype.sum_prod_type]

lemma S192P11_trL_trace {A B : Type*} [Fintype A] [Fintype B] (X : Matrix (A × B) (A × B) ℂ) :
    (traceLeft X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma S192P11_Z_ch {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K) (hK0 : 0 < K)
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (L : Matrix (I × O) (I × O) ℂ)
    (hL : L.PosSemidef) (hLr : Loewner L (Matrix.kronecker rho 1)) :
    IsChannel (reconstructedCode K hK0 rho L) := by
  refine S192P11_ch_of_C _ (S192P11_C K rho L) (S192P11_Z_apply K hK0 rho L)
    (S192P11_C_psd K hK rho L hL hLr) (fun p q => ?_)
  simp only [Fintype.sum_prod_type, S192P11_C_trR K hK]
  rw [← Finset.mul_sum, show ∑ i, rho i i = 1 from hrho.2, mul_one]

lemma S192P11_Zpt_ch {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K) (hK0 : 0 < K)
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (L : Matrix (I × O) (I × O) ℂ)
    (h1 : Loewner (-((K : ℂ)⁻¹ • Matrix.kronecker rho 1)) (pt L))
    (h2 : Loewner (pt L) ((K : ℂ)⁻¹ • Matrix.kronecker rho 1)) :
    IsChannel (fun X => pt (reconstructedCode K hK0 rho L (pt X))) := by
  refine S192P11_ch_of_C _ (S192P11_Cp K rho L) (S192P11_Zpt_apply K hK0 rho L)
    (S192P11_Cp_psd K hK rho L h1 h2) (fun p q => ?_)
  obtain ⟨a, b⟩ := p
  obtain ⟨a2, b2⟩ := q
  simp only [S192P11_Cp, Fintype.sum_prod_type, S192P11_C_trR K hK]
  rw [← Finset.mul_sum, show ∑ i, rho i i = 1 from hrho.2, mul_one]
  by_cases h1 : a = a2 <;> by_cases h2 : b = b2 <;> simp [h1, h2, eq_comm]

lemma S192P11_Z_trR {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K) (hK0 : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (X : Matrix (Fin K × O) (Fin K × O) ℂ) :
    traceRight (reconstructedCode K hK0 rho L X) = X.trace • rho := by
  ext i j
  simp only [traceRight, Matrix.of_apply, S192P11_Z_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ c, ∑ p, ∑ q, X p q * S192P11_C K rho L p q (i, c) (j, c)
      = ∑ p, ∑ q, X p q * ∑ c, S192P11_C K rho L p q (i, c) (j, c) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = ∑ p, X p p * rho i j := by
        simp only [S192P11_C_trR K hK]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [mul_ite, ite_mul, Finset.sum_ite_eq]
    _ = X.trace * rho i j := by rw [← Finset.sum_mul]; rfl

lemma S192P11_Z_trL {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K) (hK0 : 0 < K)
    (rho : Matrix I I ℂ) (hr : rho.trace = 1) (L : Matrix (I × O) (I × O) ℂ)
    (hL : traceLeft L = ((K : ℂ)^2)⁻¹ • 1) (X : Matrix (Fin K × O) (Fin K × O) ℂ) :
    traceLeft (reconstructedCode K hK0 rho L X) = X.trace • ((K : ℂ)⁻¹ • 1) := by
  ext c c'
  simp only [traceLeft, Matrix.of_apply, S192P11_Z_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ i, ∑ p, ∑ q, X p q * S192P11_C K rho L p q (i, c) (i, c')
      = ∑ p, ∑ q, X p q * ∑ i, S192P11_C K rho L p q (i, c) (i, c') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = ∑ p, X p p * ((if c = c' then 1 else 0) * (K : ℂ)⁻¹) := by
        simp only [S192P11_C_trL K hK rho hr L hL]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [mul_ite, ite_mul, Finset.sum_ite_eq]
    _ = X.trace * ((K : ℂ)⁻¹ * (1 : Matrix (Fin K) (Fin K) ℂ) c c') := by
        rw [← Finset.sum_mul, Matrix.one_apply, mul_comm ((K : ℂ)⁻¹)]; rfl

lemma S192P11_dens_scal (K : ℕ) (hK : 0 < K) :
    IsDensityMatrix ((K : ℂ)⁻¹ • (1 : Matrix (Fin K) (Fin K) ℂ)) := by
  refine ⟨Matrix.PosSemidef.one.smul (S192P11_Kinv_nonneg K), ?_⟩
  have : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, inv_mul_cancel₀ this]

lemma S192P11_avg_c {O : Type} [Fintype O] [Nonempty O] (K : ℕ) (hK : 0 < K) :
    (((K * Fintype.card O : ℕ) : ℂ)⁻¹ • (1 : Matrix (Fin K × O) (Fin K × O) ℂ)).trace = 1 := by
  have h : ((K * Fintype.card O : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hK.ne' Fintype.card_ne_zero)
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
    inv_mul_cancel₀ h]

lemma S192P11_cls {I O : Type} [Fintype I] [Fintype O] {K : ℕ}
    {Z : Superop (Fin K × O) (I × Fin K)} (s p : Bool) (hflags : s = true ∨ p = true)
    (hNS : s = true → NSAB Z) (hPP : p = true → PPTMap Z) : InCodeClass K (flagsClass s p) Z := by
  cases s <;> cases p
  · simp at hflags
  · exact hPP rfl
  · exact hNS rfl
  · exact ⟨hNS rfl, hPP rfl⟩

lemma S192P11_back2 {I O : Type} [Fintype I] [Fintype O] [Nonempty O] (N : Superop I O)
    (K : ℕ) (hK0 : 0 < K) (hK : 2 ≤ K)
    (s p : Bool) (hflags : s = true ∨ p = true) (rho : Matrix I I ℂ)
    (L : Matrix (I × O) (I × O) ℂ) (hP : Primal K s p rho L) :
    ∃ Z : Superop (Fin K × O) (I × Fin K),
      IsForwardCode K (flagsClass s p) Z ∧ codeAverageInput K Z = rho ∧
      channelFidelity K (link K N Z) = primalObjective N L := by
  obtain ⟨hrho, hL, hLr, hS, hPt⟩ := hP
  have hZc := S192P11_Z_ch K hK hK0 rho hrho L hL hLr
  refine ⟨reconstructedCode K hK0 rho L, ⟨hZc, ⟨fun Y => Y.trace • rho,
    S192P11_repl_ch rho hrho, fun X => ?_⟩, S192P11_cls s p hflags (fun hs => ?_) (fun hp => ?_)⟩,
    ?_, ?_⟩
  · beta_reduce
    rw [S192P11_Z_trR K hK hK0, S192P11_trR_trace]
  · refine ⟨fun Y => Y.trace • ((K : ℂ)⁻¹ • 1), S192P11_repl_ch _ (S192P11_dens_scal K hK0),
      fun X => ?_⟩
    beta_reduce
    rw [S192P11_Z_trL K hK hK0 rho hrho.2 L (hS hs), S192P11_trL_trace]
  · obtain ⟨h1, h2⟩ := hPt hp
    exact ⟨by convert hZc, by convert S192P11_Zpt_ch K hK hK0 rho hrho L h1 h2⟩
  · unfold codeAverageInput
    rw [S192P11_Z_trR K hK hK0, S192P11_avg_c K hK0, one_smul]
  · rw [← S192P11_obj K hK0 N, S192P11_Lz_eq K hK hK0]

lemma S192P11_fid_one {I O : Type} [Fintype I] [Fintype O] (N : Superop I O) (hN : IsChannel N)
    (Z : Superop (Fin 1 × O) (I × Fin 1)) (E : Superop (Fin 1) I) (hE : IsChannel E)
    (hEZ : ∀ X, traceRight (Z X) = E (traceRight X)) : channelFidelity 1 (link 1 N Z) = 1 := by
  rw [S192P11_fid 1 one_pos _ (S192P11_link_smul 1 N Z)]
  simp only [S192P11_link_entry, Fin.sum_univ_one]
  set σ := E (Matrix.single 0 0 1) with hσ
  have hz : ∀ β γ i j, Z (Matrix.single (0, β) (0, γ) 1) (i, 0) (j, 0) =
      (if β = γ then 1 else 0) * σ i j := by
    intro β γ i j
    have := S192P11_nsba hE hEZ 0 β γ i j
    rw [Fin.sum_univ_one] at this
    exact this
  simp only [hz]
  have hN' : ∀ i j, ∑ β, ∑ γ, N (Matrix.single i j 1) β γ * ((if β = γ then 1 else 0) * σ i j) =
      (if i = j then 1 else 0) * σ i j := by
    intro i j
    have h := S192P11_ch_trace hN (Matrix.single i j 1)
    calc ∑ β, ∑ γ, N (Matrix.single i j 1) β γ * ((if β = γ then 1 else 0) * σ i j)
        = (N (Matrix.single i j 1)).trace * σ i j := by
          simp [Matrix.trace, mul_ite, Finset.sum_mul]
      _ = _ := by
          rw [h]
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij, Matrix.trace, Matrix.single_apply]
  simp only [hN']
  have hs : ∑ i, ∑ j, (if i = j then (1:ℂ) else 0) * σ i j = 1 := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have := S192P11_ch_trace hE (Matrix.single 0 0 1)
    rw [Matrix.trace_single_eq_same] at this
    exact this
  rw [hs]
  simp

lemma S192P11_avg {I O : Type} [Fintype I] [Fintype O] [Nonempty O] (K : ℕ) (hK : 0 < K)
    (Z : Superop (Fin K × O) (I × Fin K)) (E : Superop (Fin K) I) (hE : IsChannel E)
    (hEZ : ∀ X, traceRight (Z X) = E (traceRight X)) :
    codeAverageInput K Z = S192P11_rho K E := by
  unfold codeAverageInput S192P11_rho
  rw [hEZ]
  have hO : (Fintype.card O : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have htr : traceRight (((K * Fintype.card O : ℕ) : ℂ)⁻¹ •
      (1 : Matrix (Fin K × O) (Fin K × O) ℂ)) = (K : ℂ)⁻¹ • (1 : Matrix (Fin K) (Fin K) ℂ) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [traceRight]
    · simp [traceRight, h]
  rw [htr, S192P11_ch_smul hE, S192P11_ch_expand hE 1]
  congr 1
  simp [Matrix.one_apply, ite_smul, Finset.sum_ite_eq]

lemma S192P11_code_primal2 {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (hK : 0 < K) (s p : Bool) (Z : Superop (Fin K × O) (I × Fin K))
    (hZ : IsForwardCode K (flagsClass s p) Z) :
    ∃ E : Superop (Fin K) I, IsChannel E ∧ (∀ X, traceRight (Z X) = E (traceRight X)) ∧
      Primal K s p (S192P11_rho K E) (S192P11_Lz K Z) := by
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
  refine ⟨E, hE', hEZ, S192P11_rho_dens K hK E hE', S192P11_Lz_psd K Z hZc,
    S192P11_loew K hK Z hZc E hE' hEZ, fun h => ?_,
    fun h => S192P11_ppt K hK Z (by convert (hPp h).2) E hE' hEZ⟩
  obtain ⟨D, hD, hDZ⟩ := hS h
  exact S192P11_trL_Lz K Z D hD hDZ

lemma S192P11_back1 {I O : Type} [Fintype I] [Fintype O] [Nonempty O] (N : Superop I O)
    (hN : IsChannel N) (s p : Bool) (hflags : s = true ∨ p = true) (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) :
    ∃ Z : Superop (Fin 1 × O) (I × Fin 1),
      IsForwardCode 1 (flagsClass s p) Z ∧ codeAverageInput 1 Z = rho ∧
      channelFidelity 1 (link 1 N Z) = 1 := by
  let σ : Matrix (I × Fin 1) (I × Fin 1) ℂ := Matrix.of fun u v => rho u.1 v.1
  have hσd : IsDensityMatrix σ := by
    refine ⟨hrho.1.submatrix (Prod.fst : I × Fin 1 → I), ?_⟩
    rw [← hrho.2]
    simp [σ, Matrix.trace, Fintype.sum_prod_type]
  have hZc : IsChannel (fun X : Matrix (Fin 1 × O) (Fin 1 × O) ℂ => X.trace • σ) :=
    S192P11_repl_ch σ hσd
  have hE : IsChannel (fun Y : Matrix (Fin 1) (Fin 1) ℂ => Y.trace • rho) :=
    S192P11_repl_ch rho hrho
  have hEZ : ∀ X : Matrix (Fin 1 × O) (Fin 1 × O) ℂ,
      traceRight ((fun X : Matrix (Fin 1 × O) (Fin 1 × O) ℂ => X.trace • σ) X) =
        (fun Y : Matrix (Fin 1) (Fin 1) ℂ => Y.trace • rho) (traceRight X) := by
    intro X
    beta_reduce
    rw [S192P11_trR_trace]
    ext i j
    simp [traceRight, σ]
  have hpt : (fun X => pt ((fun X : Matrix (Fin 1 × O) (Fin 1 × O) ℂ => X.trace • σ) (pt X))) =
      fun X : Matrix (Fin 1 × O) (Fin 1 × O) ℂ => X.trace • σ := by
    funext X
    ext u v
    rfl
  refine ⟨fun X => X.trace • σ, ⟨hZc, ⟨fun Y : Matrix (Fin 1) (Fin 1) ℂ => Y.trace • rho, by convert hE, hEZ⟩,
    S192P11_cls s p hflags (fun _ => ?_) (fun _ => ?_)⟩, ?_, ?_⟩
  · refine ⟨fun Y => Y.trace • (1 : Matrix (Fin 1) (Fin 1) ℂ),
      S192P11_repl_ch _ ⟨Matrix.PosSemidef.one, by simp⟩, fun X => ?_⟩
    beta_reduce
    rw [S192P11_trL_trace]
    ext c c'
    have : c = c' := Subsingleton.elim _ _
    subst this
    simp only [traceLeft, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, σ,
      Matrix.one_apply_eq, mul_one]
    rw [← Finset.mul_sum, show ∑ i, rho i i = 1 from hrho.2, mul_one]
  · exact ⟨by convert hZc, by rw [hpt]; convert hZc⟩
  · unfold codeAverageInput
    rw [hEZ]
    beta_reduce
    rw [S192P11_trR_trace, S192P11_avg_c 1 one_pos, one_smul]
  · exact S192P11_fid_one N hN _ _ (by convert hE) hEZ

end S192P11
end QAlgorithms.Papers.Independent.Support50.P11

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P11 in
theorem solution {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]
    (N : Superop I O) (hN : IsChannel N) (K : ℕ) (hK : 0 < K)
    (s p : Bool) (hflags : s = true ∨ p = true)
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (f : ℝ) :
    (∃ Z : Superop (Fin K × O) (I × Fin K),
      IsForwardCode K (flagsClass s p) Z ∧ codeAverageInput K Z = rho ∧
      channelFidelity K (link K N Z) = f) ↔
    (if K = 1 then f = 1 else
      ∃ L : Matrix (I × O) (I × O) ℂ, Primal K s p rho L ∧ f = primalObjective N L) := by
  by_cases hK1 : K = 1
  · subst hK1
    rw [if_pos rfl]
    constructor
    · rintro ⟨Z, ⟨hZc, ⟨E, hE, hEZ⟩, -⟩, -, rfl⟩
      exact S192P11_fid_one N hN Z E (by convert hE) hEZ
    · rintro rfl
      exact S192P11_back1 N hN s p hflags rho hrho
  · rw [if_neg hK1]
    have hK2 : 2 ≤ K := by omega
    constructor
    · rintro ⟨Z, hZ, havg, hfid⟩
      obtain ⟨E, hE, hEZ, hP⟩ := S192P11_code_primal2 K hK s p Z hZ
      refine ⟨S192P11_Lz K Z, ?_, ?_⟩
      · rw [← havg, S192P11_avg K hK Z E hE hEZ]; exact hP
      · rw [← hfid, S192P11_obj K hK N Z]
    · rintro ⟨L, hP, rfl⟩
      exact S192P11_back2 N K hK hK2 s p hflags rho L hP

