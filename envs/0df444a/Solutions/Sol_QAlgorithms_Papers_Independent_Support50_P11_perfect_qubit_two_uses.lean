-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P11.perfect_qubit_two_uses
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:59:42.105123+00:00
-- url     : https://prove2.me/submissions/a60e3149-a426-4091-a818-f158b74182a3

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

section S192PQ
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma S192PQ_fid (K : ℕ) (hK : 0 < K) (L : Superop (Fin K) (Fin K))
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
lemma S192PQ_link_smul {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) (c : ℂ) (X : Matrix (Fin K) (Fin K) ℂ) :
    link K N Z (c • X) = c • link K N Z X := by
  ext b d
  simp [link, Finset.mul_sum, mul_assoc]
lemma S192PQ_link_entry {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) (a b : Fin K) :
    link K N Z (Matrix.single a b 1) a b = ∑ i, ∑ j, ∑ β, ∑ γ,
      N (Matrix.single i j 1) β γ * Z (Matrix.single (a, β) (b, γ) 1) (i, a) (j, b) := by
  simp [link, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]
/-- the code-induced primal operator -/def S192PQ_Lz {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) : Matrix (I × O) (I × O) ℂ :=
  ((K : ℂ)^2)⁻¹ • ∑ a, ∑ b, Matrix.of (fun u v : I × O =>
    Z (Matrix.single (a, u.2) (b, v.2) 1) (u.1, a) (v.1, b))
lemma S192PQ_Lz_apply {I O : Type} [Fintype I] [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) (u v : I × O) :
    S192PQ_Lz K Z u v = ((K : ℂ)^2)⁻¹ *
      ∑ a, ∑ b, Z (Matrix.single (a, u.2) (b, v.2) 1) (u.1, a) (v.1, b) := by
  simp [S192PQ_Lz, Matrix.sum_apply]
lemma S192PQ_obj {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) :
    primalObjective N (S192PQ_Lz K Z) = channelFidelity K (link K N Z) := by
  rw [S192PQ_fid K hK _ (S192PQ_link_smul K N Z)]
  simp only [S192PQ_link_entry]
  unfold primalObjective S192PQ_Lz
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

lemma S192PQ_psd_of_sq {n : Type*} [Fintype n] (A : Matrix n n ℂ) (c : ℝ) (hc : 0 < c)
    (h : Aᴴ * A = (c : ℂ) • A) : A.PosSemidef := by
  have e : A = ((c⁻¹ : ℝ) : ℂ) • (Aᴴ * A) := by
    rw [h, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_smul]
  rw [e]
  exact (Matrix.posSemidef_conjTranspose_mul_self A).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))
lemma S192PQ_Kinv_nonneg (K : ℕ) : (0 : ℂ) ≤ (K : ℂ)⁻¹ := by
  rw [show (K : ℂ)⁻¹ = (((K : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  exact Complex.zero_le_real.mpr (by positivity)
lemma S192PQ_isChannel_of {ι κ ι' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    {_ : DecidableEq ι} {Φ : Superop ι κ} (A : ι' → Matrix κ ι ℂ)
    (hA : ∑ k, (A k)ᴴ * A k = 1) (hΦ : ∀ ρ, Φ ρ = ∑ k, A k * ρ * (A k)ᴴ) : IsChannel Φ := by
  refine ⟨Fintype.card ι', fun j => A ((Fintype.equivFin ι').symm j), ?_, fun ρ => ?_⟩
  · show ∑ j, _ = 1
    rw [Equiv.sum_comp ((Fintype.equivFin ι').symm) (fun k => (A k)ᴴ * A k)]
    exact hA
  · rw [hΦ]
    show _ = ∑ j, _
    exact (Equiv.sum_comp _ (fun k => A k * ρ * (A k)ᴴ)).symm
lemma S192PQ_swap3 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] (f : A → B → C → ℂ) :
    ∑ x, ∑ y, ∑ l, f x y l = ∑ l, ∑ y, ∑ x, f x y l := by
  calc ∑ x, ∑ y, ∑ l, f x y l = ∑ x, ∑ l, ∑ y, f x y l :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ l, ∑ x, ∑ y, f x y l := Finset.sum_comm
    _ = ∑ l, ∑ y, ∑ x, f x y l := Finset.sum_congr rfl fun l _ => Finset.sum_comm
lemma S192PQ_ch_of_C {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} (Φ : Superop ι κ)
    (C : ι → ι → κ → κ → ℂ) (hΦ : ∀ X u v, Φ X u v = ∑ p, ∑ q, X p q * C p q u v)
    (hC : (Matrix.of fun (a b : ι × κ) => C a.1 b.1 a.2 b.2).PosSemidef)
    (hT : ∀ p q, ∑ u, C p q u u = if p = q then 1 else 0) : IsChannel Φ := by
  obtain ⟨m, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hE : ∀ x y o o', C x y o o' = ∑ l, g l (x, o) * star (g l (y, o')) := by
    intro x y o o'
    have := congrFun (congrFun hg (x, o)) (y, o')
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
  refine S192PQ_isChannel_of (fun l : Fin m => (Matrix.of fun (o : κ) (x : ι) => g l (x, o))) ?_ ?_
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
    rw [S192PQ_swap3]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun x _ => ?_
    ring
lemma S192PQ_repl_ch {A B : Type*} [Fintype A] [Fintype B] {_ : DecidableEq A}
    (σ : Matrix B B ℂ) (hσ : IsDensityMatrix σ) :
    IsChannel (fun Y : Matrix A A ℂ => Y.trace • σ) := by
  refine S192PQ_ch_of_C _ (fun p q u v => (if p = q then 1 else 0) * σ u v) (fun X u v => ?_) ?_
    (fun p q => ?_)
  · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [mul_ite, Finset.sum_ite_eq]
  · have : (Matrix.of fun (a b : A × B) => (if a.1 = b.1 then (1:ℂ) else 0) * σ a.2 b.2) =
        (1 : Matrix A A ℂ).submatrix Prod.fst Prod.fst ⊙ σ.submatrix Prod.snd Prod.snd := by
      ext a b; simp [Matrix.hadamard_apply, Matrix.one_apply]
    rw [this]; exact (Matrix.PosSemidef.one.submatrix _).hadamard (hσ.1.submatrix _)
  · rw [← Finset.mul_sum, show ∑ u, σ u u = 1 from hσ.2, mul_one]
lemma S192PQ_phi {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] (x y : ι × ι) :
    pureDensity (finiteMaxEntangled ι) x y =
      (Fintype.card ι : ℂ)⁻¹ * ((if x.1 = x.2 then 1 else 0) * (if y.1 = y.2 then 1 else 0)) := by
  have hss : ((↑(√(Fintype.card ι : ℝ)) : ℂ)⁻¹) * (↑(√(Fintype.card ι : ℝ)) : ℂ)⁻¹ =
      (Fintype.card ι : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  simp only [pureDensity, finiteMaxEntangled, Matrix.of_apply, PiLp.toLp_apply]
  split_ifs <;> simp [Complex.conj_ofReal, hss]
/-- entry kernel of reconstructedCode -/def S192PQ_C {I O : Type} (K : ℕ) (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ)
    (p q : Fin K × O) (u v : I × Fin K) : ℂ :=
  (K : ℂ) * ((K : ℂ)⁻¹ * ((if u.2 = p.1 then 1 else 0) * (if v.2 = q.1 then 1 else 0)) *
      L (u.1, p.2) (v.1, q.2) +
    ((if u.2 = v.2 ∧ p.1 = q.1 then 1 else 0) -
      (K : ℂ)⁻¹ * ((if u.2 = p.1 then 1 else 0) * (if v.2 = q.1 then 1 else 0))) *
      (((K : ℂ)^2 - 1)⁻¹ * (rho u.1 v.1 * (if p.2 = q.2 then 1 else 0) - L (u.1, p.2) (v.1, q.2))))
lemma S192PQ_Z_apply {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (X : Matrix (Fin K × O) (Fin K × O) ℂ)
    (u v : I × Fin K) :
    reconstructedCode K hK rho L X u v = ∑ p, ∑ q, X p q * S192PQ_C K rho L p q u v := by
  simp only [reconstructedCode, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    S192PQ_phi, Fintype.card_fin, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Prod.mk.injEq]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a2 _ =>
    Finset.sum_congr rfl fun b2 _ => ?_)
  simp only [S192PQ_C]
  ring
lemma S192PQ_Z_single {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (p q : Fin K × O) (u v : I × Fin K) :
    reconstructedCode K hK rho L (Matrix.single p q 1) u v = S192PQ_C K rho L p q u v := by
  rw [S192PQ_Z_apply]
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
lemma S192PQ_K1 (K : ℕ) (hK : 2 ≤ K) : (K : ℂ)^2 - 1 ≠ 0 := by
  have h : (1 : ℝ) < (K : ℝ)^2 := by
    have : (2:ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  intro h0
  have := congrArg Complex.re h0
  simp [pow_two] at this
  nlinarith
lemma S192PQ_C_trR {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (p q : Fin K × O) (i j : I) :
    ∑ c, S192PQ_C K rho L p q (i, c) (j, c) = (if p = q then 1 else 0) * rho i j := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a2, b2⟩ := q
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hK1 := S192PQ_K1 K hK
  by_cases ha : a = a2
  · subst ha
    simp [S192PQ_C, mul_add, mul_sub, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]
    by_cases hb : b = b2
    · subst hb; simp; field_simp; ring
    · simp [hb]; field_simp; ring
  · rw [Finset.sum_eq_zero]
    · simp [ha]
    intro c _
    simp only [S192PQ_C]
    by_cases hc : c = a
    · subst hc; simp [ha]
    · simp [hc, ha]
lemma S192PQ_C_trL {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K)
    (rho : Matrix I I ℂ) (hr : rho.trace = 1) (L : Matrix (I × O) (I × O) ℂ)
    (hL : traceLeft L = ((K : ℂ)^2)⁻¹ • 1) (p q : Fin K × O) (c c' : Fin K) :
    ∑ i, S192PQ_C K rho L p q (i, c) (i, c') =
      (if p = q then 1 else 0) * ((if c = c' then 1 else 0) * (K : ℂ)⁻¹) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a2, b2⟩ := q
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hK1 := S192PQ_K1 K hK
  have hLs : ∀ b b2, ∑ i, L (i, b) (i, b2) = ((K : ℂ)^2)⁻¹ * (if b = b2 then 1 else 0) := by
    intro b b2
    have := congrFun (congrFun hL b) b2
    simpa [traceLeft, Matrix.one_apply] using this
  have hrs : ∑ i, rho i i = 1 := hr
  set d : ℂ := (if c = a then 1 else 0) * (if c' = a2 then 1 else 0) with hd
  set e : ℂ := if c = c' ∧ a = a2 then 1 else 0 with he
  set g : ℂ := ((K : ℂ)^2 - 1)⁻¹ with hg
  set db : ℂ := if b = b2 then 1 else 0 with hdb
  have hpt : ∀ i, S192PQ_C K rho L (a, b) (a2, b2) (i, c) (i, c') =
      ((K : ℂ) * ((K : ℂ)⁻¹ * d - (e - (K : ℂ)⁻¹ * d) * g)) * L (i, b) (i, b2) +
      ((K : ℂ) * (e - (K : ℂ)⁻¹ * d) * g * db) * rho i i := by
    intro i
    simp only [S192PQ_C, hd, he, hg, hdb]
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
lemma S192PQ_C_psd {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (hL : L.PosSemidef)
    (hLr : Loewner L (Matrix.kronecker rho 1)) :
    (Matrix.of fun (w w' : (Fin K × O) × (I × Fin K)) =>
      S192PQ_C K rho L w.1 w'.1 w.2 w'.2).PosSemidef := by
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
  have hP2 : (1 - c • J).PosSemidef := S192PQ_psd_of_sq _ 1 one_pos hPi
  have hP1 : (c • J).PosSemidef := by
    have : J = Matrix.vecMulVec φ (star φ) := by
      ext x y
      simp only [J, φ, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, apply_ite star,
        star_one, star_zero]
    rw [this]
    exact (Matrix.posSemidef_vecMulVec_self_star φ).smul (S192PQ_Kinv_nonneg K)
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
      S192PQ_C K rho L w.1 w'.1 w.2 w'.2) = (K : ℂ) • ((c • J).submatrix g1 g1 ⊙ L.submatrix g2 g2 +
        (1 - c • J).submatrix g1 g1 ⊙ (((K : ℂ)^2 - 1)⁻¹ • (Matrix.kronecker rho 1 - L)).submatrix g2 g2) := by
    ext w w'
    simp only [S192PQ_C, J, φ, g1, g2, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.hadamard_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul, Prod.mk.injEq, hc]
  rw [e]
  exact (((hP1.submatrix g1).hadamard (hL.submatrix g2)).add
    ((hP2.submatrix g1).hadamard (hG.submatrix g2))).smul hKn
lemma S192PQ_Lz_eq {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K) (hK0 : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) :
    S192PQ_Lz K (reconstructedCode K hK0 rho L) = L := by
  have hK0' : (K : ℂ) ≠ 0 := by exact_mod_cast hK0.ne'
  ext u v
  rw [S192PQ_Lz_apply]
  simp only [S192PQ_Z_single, S192PQ_C]
  have hK1 := S192PQ_K1 K hK
  simp [mul_add, mul_sub, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  split_ifs <;> field_simp <;> ring
lemma S192PQ_comm3' {A B : Type*} [Fintype A] [Fintype B] (f : A → B → A → ℂ) :
    ∑ b, ∑ c, ∑ d, f b c d = ∑ b, ∑ c, ∑ d, f d c b := by
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
lemma S192PQ_pt_sum {A B : Type*} [Fintype A] [Fintype B] (F : A × B → A × B → ℂ) :
    ∑ p : A × B, ∑ q : A × B, F (p.1, q.2) (q.1, p.2) = ∑ p, ∑ q, F p q := by
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact S192PQ_comm3' (fun b a2 b2 => F (a, b2) (a2, b))
def S192PQ_Cp {I O : Type} (K : ℕ) (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ)
    (p q : Fin K × O) (u v : I × Fin K) : ℂ :=
  S192PQ_C K rho L (p.1, q.2) (q.1, p.2) (u.1, v.2) (v.1, u.2)
lemma S192PQ_Zpt_apply {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (X : Matrix (Fin K × O) (Fin K × O) ℂ)
    (u v : I × Fin K) :
    pt (reconstructedCode K hK rho L (pt X)) u v = ∑ p, ∑ q, X p q * S192PQ_Cp K rho L p q u v := by
  show reconstructedCode K hK rho L (pt X) (u.1, v.2) (v.1, u.2) = _
  rw [S192PQ_Z_apply]
  exact S192PQ_pt_sum (fun p q => X p q * S192PQ_Cp K rho L p q u v)
lemma S192PQ_Cp_psd {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ)
    (h1 : Loewner (-((K : ℂ)⁻¹ • Matrix.kronecker rho 1)) (pt L))
    (h2 : Loewner (pt L) ((K : ℂ)⁻¹ • Matrix.kronecker rho 1)) :
    (Matrix.of fun (w w' : (Fin K × O) × (I × Fin K)) =>
      S192PQ_Cp K rho L w.1 w'.1 w.2 w'.2).PosSemidef := by
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hK1 := S192PQ_K1 K hK
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
  have hP1 := (S192PQ_psd_of_sq _ 2 two_pos hs1).smul hh
  have hP2 := (S192PQ_psd_of_sq _ 2 two_pos hs2).smul hh
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
      S192PQ_Cp K rho L w.1 w'.1 w.2 w'.2) =
      ((2 : ℂ)⁻¹ • (1 + F)).submatrix g1 g1 ⊙
        (((K : ℂ) / ((K : ℂ) + 1)) • (pt L - -((K : ℂ)⁻¹ • Matrix.kronecker rho 1))).submatrix g2 g2 +
      ((2 : ℂ)⁻¹ • (1 - F)).submatrix g1 g1 ⊙
        (((K : ℂ) / ((K : ℂ) - 1)) • ((K : ℂ)⁻¹ • Matrix.kronecker rho 1 - pt L)).submatrix g2 g2 := by
    ext ⟨⟨a, b⟩, ⟨i, c⟩⟩ ⟨⟨a2, b2⟩, ⟨j, c'⟩⟩
    simp only [S192PQ_Cp, S192PQ_C, F, g1, g2, Matrix.of_apply, Matrix.add_apply,
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
lemma S192PQ_trR_trace {A B : Type*} [Fintype A] [Fintype B] (X : Matrix (A × B) (A × B) ℂ) :
    (traceRight X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, traceRight, Matrix.of_apply, Fintype.sum_prod_type]
lemma S192PQ_trL_trace {A B : Type*} [Fintype A] [Fintype B] (X : Matrix (A × B) (A × B) ℂ) :
    (traceLeft X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm
lemma S192PQ_Z_ch {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K) (hK0 : 0 < K)
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (L : Matrix (I × O) (I × O) ℂ)
    (hL : L.PosSemidef) (hLr : Loewner L (Matrix.kronecker rho 1)) :
    IsChannel (reconstructedCode K hK0 rho L) := by
  refine S192PQ_ch_of_C _ (S192PQ_C K rho L) (S192PQ_Z_apply K hK0 rho L)
    (S192PQ_C_psd K hK rho L hL hLr) (fun p q => ?_)
  simp only [Fintype.sum_prod_type, S192PQ_C_trR K hK]
  rw [← Finset.mul_sum, show ∑ i, rho i i = 1 from hrho.2, mul_one]
lemma S192PQ_Zpt_ch {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K) (hK0 : 0 < K)
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (L : Matrix (I × O) (I × O) ℂ)
    (h1 : Loewner (-((K : ℂ)⁻¹ • Matrix.kronecker rho 1)) (pt L))
    (h2 : Loewner (pt L) ((K : ℂ)⁻¹ • Matrix.kronecker rho 1)) :
    IsChannel (fun X => pt (reconstructedCode K hK0 rho L (pt X))) := by
  refine S192PQ_ch_of_C _ (S192PQ_Cp K rho L) (S192PQ_Zpt_apply K hK0 rho L)
    (S192PQ_Cp_psd K hK rho L h1 h2) (fun p q => ?_)
  obtain ⟨a, b⟩ := p
  obtain ⟨a2, b2⟩ := q
  simp only [S192PQ_Cp, Fintype.sum_prod_type, S192PQ_C_trR K hK]
  rw [← Finset.mul_sum, show ∑ i, rho i i = 1 from hrho.2, mul_one]
  by_cases h1 : a = a2 <;> by_cases h2 : b = b2 <;> simp [h1, h2, eq_comm]
lemma S192PQ_Z_trR {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K) (hK0 : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) (X : Matrix (Fin K × O) (Fin K × O) ℂ) :
    traceRight (reconstructedCode K hK0 rho L X) = X.trace • rho := by
  ext i j
  simp only [traceRight, Matrix.of_apply, S192PQ_Z_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ c, ∑ p, ∑ q, X p q * S192PQ_C K rho L p q (i, c) (j, c)
      = ∑ p, ∑ q, X p q * ∑ c, S192PQ_C K rho L p q (i, c) (j, c) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = ∑ p, X p p * rho i j := by
        simp only [S192PQ_C_trR K hK]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [mul_ite, ite_mul, Finset.sum_ite_eq]
    _ = X.trace * rho i j := by rw [← Finset.sum_mul]; rfl
lemma S192PQ_Z_trL {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 2 ≤ K) (hK0 : 0 < K)
    (rho : Matrix I I ℂ) (hr : rho.trace = 1) (L : Matrix (I × O) (I × O) ℂ)
    (hL : traceLeft L = ((K : ℂ)^2)⁻¹ • 1) (X : Matrix (Fin K × O) (Fin K × O) ℂ) :
    traceLeft (reconstructedCode K hK0 rho L X) = X.trace • ((K : ℂ)⁻¹ • 1) := by
  ext c c'
  simp only [traceLeft, Matrix.of_apply, S192PQ_Z_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ i, ∑ p, ∑ q, X p q * S192PQ_C K rho L p q (i, c) (i, c')
      = ∑ p, ∑ q, X p q * ∑ i, S192PQ_C K rho L p q (i, c) (i, c') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = ∑ p, X p p * ((if c = c' then 1 else 0) * (K : ℂ)⁻¹) := by
        simp only [S192PQ_C_trL K hK rho hr L hL]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [mul_ite, ite_mul, Finset.sum_ite_eq]
    _ = X.trace * ((K : ℂ)⁻¹ * (1 : Matrix (Fin K) (Fin K) ℂ) c c') := by
        rw [← Finset.sum_mul, Matrix.one_apply, mul_comm ((K : ℂ)⁻¹)]; rfl
lemma S192PQ_dens_scal (K : ℕ) (hK : 0 < K) :
    IsDensityMatrix ((K : ℂ)⁻¹ • (1 : Matrix (Fin K) (Fin K) ℂ)) := by
  refine ⟨Matrix.PosSemidef.one.smul (S192PQ_Kinv_nonneg K), ?_⟩
  have : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, inv_mul_cancel₀ this]
lemma S192PQ_avg_c {O : Type} [Fintype O] [Nonempty O] (K : ℕ) (hK : 0 < K) :
    (((K * Fintype.card O : ℕ) : ℂ)⁻¹ • (1 : Matrix (Fin K × O) (Fin K × O) ℂ)).trace = 1 := by
  have h : ((K * Fintype.card O : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hK.ne' Fintype.card_ne_zero)
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
    inv_mul_cancel₀ h]
lemma S192PQ_cls {I O : Type} [Fintype I] [Fintype O] {K : ℕ}
    {Z : Superop (Fin K × O) (I × Fin K)} (s p : Bool) (hflags : s = true ∨ p = true)
    (hNS : s = true → NSAB Z) (hPP : p = true → PPTMap Z) : InCodeClass K (flagsClass s p) Z := by
  cases s <;> cases p
  · simp at hflags
  · exact hPP rfl
  · exact hNS rfl
  · exact ⟨hNS rfl, hPP rfl⟩

lemma S192PQ_fwd {I O : Type} [Fintype I] [Fintype O] [Nonempty O] (N : Superop I O)
    (K : ℕ) (hK0 : 0 < K) (hK : 2 ≤ K)
    (s p : Bool) (hflags : s = true ∨ p = true) (rho : Matrix I I ℂ)
    (L : Matrix (I × O) (I × O) ℂ) (hP : Primal K s p rho L) :
      IsForwardCode K (flagsClass s p) (reconstructedCode K hK0 rho L) ∧
      codeAverageInput K (reconstructedCode K hK0 rho L) = rho ∧
      channelFidelity K (link K N (reconstructedCode K hK0 rho L)) = primalObjective N L := by
  obtain ⟨hrho, hL, hLr, hS, hPt⟩ := hP
  have hZc := S192PQ_Z_ch K hK hK0 rho hrho L hL hLr
  refine ⟨⟨hZc, ⟨fun Y => Y.trace • rho,
    S192PQ_repl_ch rho hrho, fun X => ?_⟩, S192PQ_cls s p hflags (fun hs => ?_) (fun hp => ?_)⟩,
    ?_, ?_⟩
  · beta_reduce
    rw [S192PQ_Z_trR K hK hK0, S192PQ_trR_trace]
  · refine ⟨fun Y => Y.trace • ((K : ℂ)⁻¹ • 1), S192PQ_repl_ch _ (S192PQ_dens_scal K hK0),
      fun X => ?_⟩
    beta_reduce
    rw [S192PQ_Z_trL K hK hK0 rho hrho.2 L (hS hs), S192PQ_trL_trace]
  · obtain ⟨h1, h2⟩ := hPt hp
    exact ⟨by convert hZc, by convert S192PQ_Zpt_ch K hK hK0 rho hrho L h1 h2⟩
  · unfold codeAverageInput
    rw [S192PQ_Z_trR K hK hK0, S192PQ_avg_c K hK0, one_smul]
  · rw [← S192PQ_obj K hK0 N, S192PQ_Lz_eq K hK hK0]

lemma S192PQ_proj_psd {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (hH : Mᴴ = M) (hI : M * M = M) : M.PosSemidef := by
  have e : M = Mᴴ * M := by rw [hH, hI]
  rw [e]; exact Matrix.posSemidef_conjTranspose_mul_self M

abbrev S192PQ_site := Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ
abbrev S192PQ_big := Matrix ((Fin 2 → Fin 3) × (Fin 2 → Fin 3)) ((Fin 2 → Fin 3) × (Fin 2 → Fin 3)) ℂ

def S192PQ_F : S192PQ_site := swapMatrix (I := Fin 3)
def S192PQ_G : S192PQ_site := Matrix.of fun u v => if u.1 = u.2 ∧ v.1 = v.2 then 1 else 0
def S192PQ_Ph : S192PQ_site := (3 : ℂ)⁻¹ • S192PQ_G
def S192PQ_Q : S192PQ_site := 1 - S192PQ_Ph

lemma S192PQ_S_eq : wernerSector 3 false = (2 : ℂ)⁻¹ • (1 + S192PQ_F) := rfl
lemma S192PQ_A_eq : wernerSector 3 true = (2 : ℂ)⁻¹ • (1 - S192PQ_F) := rfl

lemma S192PQ_FF : S192PQ_F * S192PQ_F = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [S192PQ_F, swapMatrix, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Prod.mk.injEq]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2, ite_and, eq_comm]

lemma S192PQ_FH : S192PQ_Fᴴ = S192PQ_F := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [S192PQ_F, swapMatrix, Matrix.conjTranspose_apply]
  by_cases h1 : a = d <;> by_cases h2 : b = c <;> simp [h1, h2, eq_comm]

lemma S192PQ_GG : S192PQ_G * S192PQ_G = (3 : ℂ) • S192PQ_G := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [S192PQ_G, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Matrix.smul_apply,
    smul_eq_mul]
  by_cases h1 : a = b <;> by_cases h2 : c = d <;> simp [h1, h2, Fin.sum_univ_three]

lemma S192PQ_GH : S192PQ_Gᴴ = S192PQ_G := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [S192PQ_G, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h1 : a = b <;> by_cases h2 : c = d <;> simp [h1, h2]

lemma S192PQ_pt1 : pt (1 : S192PQ_site) = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [pt, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2, eq_comm]

lemma S192PQ_ptF : pt S192PQ_F = S192PQ_G := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [pt, S192PQ_F, S192PQ_G, swapMatrix, Matrix.of_apply]
  by_cases h1 : a = b <;> by_cases h2 : c = d <;> simp [h1, h2, eq_comm]

lemma S192PQ_pt_add (X Y : S192PQ_site) : pt (X + Y) = pt X + pt Y := rfl
lemma S192PQ_pt_sub (X Y : S192PQ_site) : pt (X - Y) = pt X - pt Y := rfl
lemma S192PQ_pt_smul (c : ℂ) (X : S192PQ_site) : pt (c • X) = c • pt X := rfl

lemma S192PQ_ptS : pt (wernerSector 3 false) = (2 : ℂ) • S192PQ_Ph + (2 : ℂ)⁻¹ • S192PQ_Q := by
  rw [S192PQ_S_eq, S192PQ_pt_smul, S192PQ_pt_add, S192PQ_pt1, S192PQ_ptF, S192PQ_Q, S192PQ_Ph]
  module

lemma S192PQ_ptA : pt (wernerSector 3 true) = (-1 : ℂ) • S192PQ_Ph + (2 : ℂ)⁻¹ • S192PQ_Q := by
  rw [S192PQ_A_eq, S192PQ_pt_smul, S192PQ_pt_sub, S192PQ_pt1, S192PQ_ptF, S192PQ_Q, S192PQ_Ph]
  module

lemma S192PQ_PhQ : (1 : S192PQ_site) = S192PQ_Ph + S192PQ_Q := by
  rw [S192PQ_Q]; abel

lemma S192PQ_SA1 : (1 : S192PQ_site) = wernerSector 3 false + wernerSector 3 true := by
  rw [S192PQ_S_eq, S192PQ_A_eq]; module

lemma S192PQ_Ph_psd : S192PQ_Ph.PosSemidef := by
  refine S192PQ_proj_psd _ ?_ ?_
  · rw [S192PQ_Ph, Matrix.conjTranspose_smul, S192PQ_GH]; simp
  · rw [S192PQ_Ph, Matrix.smul_mul, Matrix.mul_smul, S192PQ_GG, smul_smul, smul_smul]
    congr 1; norm_num

lemma S192PQ_Q_psd : S192PQ_Q.PosSemidef := by
  have hH : S192PQ_Phᴴ = S192PQ_Ph := by
    rw [S192PQ_Ph, Matrix.conjTranspose_smul, S192PQ_GH]; simp
  have hI : S192PQ_Ph * S192PQ_Ph = S192PQ_Ph := by
    rw [S192PQ_Ph, Matrix.smul_mul, Matrix.mul_smul, S192PQ_GG, smul_smul, smul_smul]
    congr 1; norm_num
  refine S192PQ_proj_psd _ ?_ ?_
  · rw [S192PQ_Q, Matrix.conjTranspose_sub, hH, Matrix.conjTranspose_one]
  · rw [S192PQ_Q, sub_mul, mul_sub, mul_sub, hI]; simp only [one_mul, mul_one]; abel

lemma S192PQ_SS : wernerSector 3 false * wernerSector 3 false = wernerSector 3 false := by
  rw [S192PQ_S_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_mul, mul_add, mul_add,
    S192PQ_FF, one_mul, mul_one, one_mul]
  module

lemma S192PQ_AA : wernerSector 3 true * wernerSector 3 true = wernerSector 3 true := by
  rw [S192PQ_A_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sub_mul, mul_sub, mul_sub,
    S192PQ_FF, one_mul, mul_one, one_mul]
  module

lemma S192PQ_AS : wernerSector 3 true * wernerSector 3 false = 0 := by
  rw [S192PQ_A_eq, S192PQ_S_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sub_mul, mul_add,
    mul_add, S192PQ_FF, one_mul, mul_one, one_mul]
  module

lemma S192PQ_SH : (wernerSector 3 false)ᴴ = wernerSector 3 false := by
  rw [S192PQ_S_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, S192PQ_FH,
    Matrix.conjTranspose_one]; simp

lemma S192PQ_AH : (wernerSector 3 true)ᴴ = wernerSector 3 true := by
  rw [S192PQ_A_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, S192PQ_FH,
    Matrix.conjTranspose_one]; simp

lemma S192PQ_S_psd : (wernerSector 3 false).PosSemidef :=
  S192PQ_proj_psd _ S192PQ_SH S192PQ_SS
lemma S192PQ_A_psd : (wernerSector 3 true).PosSemidef :=
  S192PQ_proj_psd _ S192PQ_AH S192PQ_AA

lemma S192PQ_trL_S : traceLeft (wernerSector 3 false) = (2 : ℂ) • 1 := by
  ext b d
  simp only [traceLeft, S192PQ_S_eq, S192PQ_F, swapMatrix, Matrix.of_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  by_cases h : b = d <;> simp [h, Fin.sum_univ_three] <;> fin_cases b <;> fin_cases d <;>
    simp_all <;> norm_num

lemma S192PQ_trL_A : traceLeft (wernerSector 3 true) = (1 : ℂ) • 1 := by
  ext b d
  simp only [traceLeft, S192PQ_A_eq, S192PQ_F, swapMatrix, Matrix.of_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  by_cases h : b = d <;> simp [h, Fin.sum_univ_three] <;> fin_cases b <;> fin_cases d <;>
    simp_all <;> norm_num

lemma S192PQ_trA : (wernerSector 3 true).trace = 3 := by
  simp only [Matrix.trace, Matrix.diag, S192PQ_A_eq, S192PQ_F, swapMatrix, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_three, smul_eq_mul]
  simp; norm_num

lemma S192PQ_AT : (wernerSector 3 true)ᵀ = wernerSector 3 true := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.transpose_apply, S192PQ_A_eq, S192PQ_F, swapMatrix, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> by_cases h3 : a = d <;> by_cases h4 : b = c <;>
    simp [h1, h2, h3, h4, eq_comm]

def S192PQ_P2 (X Y : S192PQ_site) : S192PQ_big :=
  Matrix.of fun p q => X (p.1 0, p.2 0) (q.1 0, q.2 0) * Y (p.1 1, p.2 1) (q.1 1, q.2 1)

lemma S192PQ_sum2 {α : Type*} [Fintype α] (f : (Fin 2 → α) → ℂ) :
    ∑ x, f x = ∑ a, ∑ b, f ![a, b] := by
  rw [← (finTwoArrowEquiv α).symm.sum_comp, Fintype.sum_prod_type]
  rfl

lemma S192PQ_sumP (f : (Fin 2 → Fin 3) × (Fin 2 → Fin 3) → ℂ) :
    ∑ p, f p = ∑ u : Fin 3 × Fin 3, ∑ v : Fin 3 × Fin 3, f (![u.1, v.1], ![u.2, v.2]) := by
  rw [Fintype.sum_prod_type, S192PQ_sum2]
  simp only [S192PQ_sum2 (α := Fin 3), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

lemma S192PQ_P2_psd {X Y : S192PQ_site} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (S192PQ_P2 X Y).PosSemidef := by
  have : S192PQ_P2 X Y =
      X.submatrix (fun p : (Fin 2 → Fin 3) × (Fin 2 → Fin 3) => (p.1 0, p.2 0))
        (fun p => (p.1 0, p.2 0)) ⊙
      Y.submatrix (fun p : (Fin 2 → Fin 3) × (Fin 2 → Fin 3) => (p.1 1, p.2 1))
        (fun p => (p.1 1, p.2 1)) := by
    ext p q; rfl
  rw [this]; exact (hX.submatrix _).hadamard (hY.submatrix _)

lemma S192PQ_P2_addl (X X' Y : S192PQ_site) :
    S192PQ_P2 (X + X') Y = S192PQ_P2 X Y + S192PQ_P2 X' Y := by
  ext p q; simp [S192PQ_P2, add_mul]
lemma S192PQ_P2_addr (X Y Y' : S192PQ_site) :
    S192PQ_P2 X (Y + Y') = S192PQ_P2 X Y + S192PQ_P2 X Y' := by
  ext p q; simp [S192PQ_P2, mul_add]
lemma S192PQ_P2_smull (c : ℂ) (X Y : S192PQ_site) :
    S192PQ_P2 (c • X) Y = c • S192PQ_P2 X Y := by
  ext p q; simp [S192PQ_P2, mul_assoc]
lemma S192PQ_P2_smulr (c : ℂ) (X Y : S192PQ_site) :
    S192PQ_P2 X (c • Y) = c • S192PQ_P2 X Y := by
  ext p q; simp [S192PQ_P2]; ring

lemma S192PQ_P2_one : S192PQ_P2 1 1 = 1 := by
  ext p q
  simp only [S192PQ_P2, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff, funext_iff,
    Fin.forall_fin_two]
  by_cases h1 : p.1 0 = q.1 0 <;> by_cases h2 : p.2 0 = q.2 0 <;> by_cases h3 : p.1 1 = q.1 1 <;>
    by_cases h4 : p.2 1 = q.2 1 <;> simp [h1, h2, h3, h4]

lemma S192PQ_P2_pt (X Y : S192PQ_site) : pt (S192PQ_P2 X Y) = S192PQ_P2 (pt X) (pt Y) := rfl

lemma S192PQ_P2_mul (X Y X' Y' : S192PQ_site) :
    S192PQ_P2 X Y * S192PQ_P2 X' Y' = S192PQ_P2 (X * X') (Y * Y') := by
  ext p q
  simp only [Matrix.mul_apply, S192PQ_P2, Matrix.of_apply]
  rw [S192PQ_sumP, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.eta]
  ring

lemma S192PQ_P2_trace (X Y : S192PQ_site) : (S192PQ_P2 X Y).trace = X.trace * Y.trace := by
  simp only [Matrix.trace, Matrix.diag, S192PQ_P2, Matrix.of_apply]
  rw [S192PQ_sumP, Finset.sum_mul_sum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.eta]

lemma S192PQ_P2_T (X Y : S192PQ_site) : (S192PQ_P2 X Y)ᵀ = S192PQ_P2 Xᵀ Yᵀ := rfl

def S192PQ_Q2 (x y : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 2 → Fin 3) (Fin 2 → Fin 3) ℂ :=
  Matrix.of fun o o' => x (o 0) (o' 0) * y (o 1) (o' 1)

lemma S192PQ_P2_trL (X Y : S192PQ_site) :
    traceLeft (S192PQ_P2 X Y) = S192PQ_Q2 (traceLeft X) (traceLeft Y) := by
  ext o o'
  simp only [traceLeft, S192PQ_P2, S192PQ_Q2, Matrix.of_apply]
  rw [S192PQ_sum2, Finset.sum_mul_sum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

lemma S192PQ_Q2_one (a b : ℂ) : S192PQ_Q2 (a • 1) (b • 1) = (a * b) • 1 := by
  ext o o'
  simp only [S192PQ_Q2, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, funext_iff,
    Fin.forall_fin_two, smul_eq_mul]
  by_cases h1 : o 0 = o' 0 <;> by_cases h2 : o 1 = o' 1 <;> simp [h1, h2]

lemma S192PQ_trL_add {A B : Type} [Fintype A] (X Y : Matrix (A × B) (A × B) ℂ) :
    traceLeft (X + Y) = traceLeft X + traceLeft Y := by
  ext; simp [traceLeft, Finset.sum_add_distrib]
lemma S192PQ_trL_smul {A B : Type} [Fintype A] (c : ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    traceLeft (c • X) = c • traceLeft X := by
  ext; simp [traceLeft, Finset.mul_sum]

local notation "S192PQ_S" => wernerSector 3 false
local notation "S192PQ_A" => wernerSector 3 true

lemma S192PQ_lam : exampleLambda =
    ((3 : ℂ) / 288) • S192PQ_P2 S192PQ_S S192PQ_S +
    ((7 : ℂ) / 288) • (S192PQ_P2 S192PQ_S S192PQ_A + S192PQ_P2 S192PQ_A S192PQ_S) +
    ((32 : ℂ) / 288) • S192PQ_P2 S192PQ_A S192PQ_A := by
  ext p q
  have hsec : ∀ j : ℕ, sectorSum 3 2 j p q = ∑ a : Bool, ∑ b : Bool,
      if ((if a then 1 else 0) + (if b then 1 else 0) : ℕ) = j then
        wernerSector 3 a (p.1 0, p.2 0) (q.1 0, q.2 0) * wernerSector 3 b (p.1 1, p.2 1) (q.1 1, q.2 1)
      else 0 := by
    intro j
    refine (S192PQ_sum2 _).trans ?_
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.card_filter, Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    congr 1
  simp only [exampleLambda, ansatz, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply,
    S192PQ_P2, Matrix.of_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, hsec, Fintype.sum_bool]
  simp
  ring

lemma S192PQ_pt_add' {I J : Type*} (X Y : Matrix (I × J) (I × J) ℂ) : pt (X + Y) = pt X + pt Y := rfl
lemma S192PQ_pt_smul' {I J : Type*} (c : ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    pt (c • X) = c • pt X := rfl

lemma S192PQ_loewL (M : S192PQ_big)
    (hM : M = (9 : ℂ)⁻¹ • S192PQ_P2 (S192PQ_S + S192PQ_A) (S192PQ_S + S192PQ_A)) :
    Loewner exampleLambda M := by
  have hSS := S192PQ_P2_psd S192PQ_S_psd S192PQ_S_psd
  have hSA := S192PQ_P2_psd S192PQ_S_psd S192PQ_A_psd
  have hAS := S192PQ_P2_psd S192PQ_A_psd S192PQ_S_psd
  unfold Loewner
  rw [hM, S192PQ_lam]
  have e : (9 : ℂ)⁻¹ • S192PQ_P2 (S192PQ_S + S192PQ_A) (S192PQ_S + S192PQ_A) -
      (((3 : ℂ) / 288) • S192PQ_P2 S192PQ_S S192PQ_S +
        ((7 : ℂ) / 288) • (S192PQ_P2 S192PQ_S S192PQ_A + S192PQ_P2 S192PQ_A S192PQ_S) +
        ((32 : ℂ) / 288) • S192PQ_P2 S192PQ_A S192PQ_A) =
      ((29 : ℂ) / 288) • S192PQ_P2 S192PQ_S S192PQ_S +
        ((25 : ℂ) / 288) • (S192PQ_P2 S192PQ_S S192PQ_A + S192PQ_P2 S192PQ_A S192PQ_S) := by
    simp only [S192PQ_P2_addl, S192PQ_P2_addr]
    module
  rw [e]
  refine (hSS.smul ?_).add ((hSA.add hAS).smul ?_) <;> positivity

lemma S192PQ_ptL : pt exampleLambda =
    ((1 : ℂ) / 18) • S192PQ_P2 S192PQ_Ph S192PQ_Ph +
    ((-19 : ℂ) / 576) • (S192PQ_P2 S192PQ_Ph S192PQ_Q + S192PQ_P2 S192PQ_Q S192PQ_Ph) +
    ((49 : ℂ) / 1152) • S192PQ_P2 S192PQ_Q S192PQ_Q := by
  rw [S192PQ_lam]
  simp only [S192PQ_pt_add', S192PQ_pt_smul', S192PQ_P2_pt, S192PQ_ptS, S192PQ_ptA,
    S192PQ_P2_addl, S192PQ_P2_addr, S192PQ_P2_smull, S192PQ_P2_smulr]
  module

lemma S192PQ_ptb (M : S192PQ_big)
    (hM : M = (9 : ℂ)⁻¹ • S192PQ_P2 (S192PQ_Ph + S192PQ_Q) (S192PQ_Ph + S192PQ_Q)) :
    Loewner (-(((2 : ℕ) : ℂ)⁻¹ • M)) (pt exampleLambda) ∧
      Loewner (pt exampleLambda) (((2 : ℕ) : ℂ)⁻¹ • M) := by
  have hPP := S192PQ_P2_psd S192PQ_Ph_psd S192PQ_Ph_psd
  have hPQ := S192PQ_P2_psd S192PQ_Ph_psd S192PQ_Q_psd
  have hQP := S192PQ_P2_psd S192PQ_Q_psd S192PQ_Ph_psd
  have hQQ := S192PQ_P2_psd S192PQ_Q_psd S192PQ_Q_psd
  unfold Loewner
  rw [hM, S192PQ_ptL]
  constructor
  · have e : ((1 : ℂ) / 18) • S192PQ_P2 S192PQ_Ph S192PQ_Ph +
        ((-19 : ℂ) / 576) • (S192PQ_P2 S192PQ_Ph S192PQ_Q + S192PQ_P2 S192PQ_Q S192PQ_Ph) +
        ((49 : ℂ) / 1152) • S192PQ_P2 S192PQ_Q S192PQ_Q -
        -(((2 : ℕ) : ℂ)⁻¹ • (9 : ℂ)⁻¹ • S192PQ_P2 (S192PQ_Ph + S192PQ_Q) (S192PQ_Ph + S192PQ_Q)) =
        ((1 : ℂ) / 9) • S192PQ_P2 S192PQ_Ph S192PQ_Ph +
        ((13 : ℂ) / 576) • (S192PQ_P2 S192PQ_Ph S192PQ_Q + S192PQ_P2 S192PQ_Q S192PQ_Ph) +
        ((113 : ℂ) / 1152) • S192PQ_P2 S192PQ_Q S192PQ_Q := by
      simp only [S192PQ_P2_addl, S192PQ_P2_addr]; push_cast; module
    rw [e]
    refine ((hPP.smul ?_).add ((hPQ.add hQP).smul ?_)).add (hQQ.smul ?_) <;> positivity
  · have e : ((2 : ℕ) : ℂ)⁻¹ • (9 : ℂ)⁻¹ • S192PQ_P2 (S192PQ_Ph + S192PQ_Q) (S192PQ_Ph + S192PQ_Q) -
        (((1 : ℂ) / 18) • S192PQ_P2 S192PQ_Ph S192PQ_Ph +
        ((-19 : ℂ) / 576) • (S192PQ_P2 S192PQ_Ph S192PQ_Q + S192PQ_P2 S192PQ_Q S192PQ_Ph) +
        ((49 : ℂ) / 1152) • S192PQ_P2 S192PQ_Q S192PQ_Q) =
        ((51 : ℂ) / 576) • (S192PQ_P2 S192PQ_Ph S192PQ_Q + S192PQ_P2 S192PQ_Q S192PQ_Ph) +
        ((15 : ℂ) / 1152) • S192PQ_P2 S192PQ_Q S192PQ_Q := by
      simp only [S192PQ_P2_addl, S192PQ_P2_addr]; push_cast; module
    rw [e]
    refine ((hPQ.add hQP).smul ?_).add (hQQ.smul ?_) <;> positivity

lemma S192PQ_primal :
    Primal 2 true true ((9 : ℂ)⁻¹ • (1 : Matrix (Fin 2 → Fin 3) (Fin 2 → Fin 3) ℂ)) exampleLambda := by
  have hSS := S192PQ_P2_psd S192PQ_S_psd S192PQ_S_psd
  have hSA := S192PQ_P2_psd S192PQ_S_psd S192PQ_A_psd
  have hAS := S192PQ_P2_psd S192PQ_A_psd S192PQ_S_psd
  have hAA := S192PQ_P2_psd S192PQ_A_psd S192PQ_A_psd
  refine ⟨⟨Matrix.PosSemidef.one.smul (by positivity), ?_⟩, ?_, S192PQ_loewL _ ?_, fun _ => ?_,
    fun _ => S192PQ_ptb _ ?_⟩
  · rw [Matrix.trace_smul, Matrix.trace_one]; simp
  · rw [S192PQ_lam]
    refine ((hSS.smul ?_).add ((hSA.add hAS).smul ?_)).add (hAA.smul ?_) <;> positivity
  · rw [← S192PQ_SA1]
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
      Prod.mk.injEq, smul_eq_mul, S192PQ_P2, Matrix.of_apply, funext_iff, Fin.forall_fin_two]
    by_cases h1 : a 0 = c 0 <;> by_cases h2 : b 0 = d 0 <;> by_cases h3 : a 1 = c 1 <;>
      by_cases h4 : b 1 = d 1 <;> simp [h1, h2, h3, h4]
  · rw [S192PQ_lam, S192PQ_trL_add, S192PQ_trL_add, S192PQ_trL_smul, S192PQ_trL_smul,
      S192PQ_trL_smul, S192PQ_trL_add]
    simp only [S192PQ_P2_trL, S192PQ_trL_S, S192PQ_trL_A, S192PQ_Q2_one, smul_smul, ← add_smul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> norm_num
  · rw [← S192PQ_PhQ]
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
      Prod.mk.injEq, smul_eq_mul, S192PQ_P2, Matrix.of_apply, funext_iff, Fin.forall_fin_two]
    by_cases h1 : a 0 = c 0 <;> by_cases h2 : b 0 = d 0 <;> by_cases h3 : a 1 = c 1 <;>
      by_cases h4 : b 1 = d 1 <;> simp [h1, h2, h3, h4]

lemma S192PQ_wh (a b c d : Fin 3) :
    wernerHolevoChannel 3 1 (Matrix.single a c 1) b d = S192PQ_A (a, b) (c, d) := by
  have ht : (Matrix.single a c (1 : ℂ)).trace = if a = c then 1 else 0 := by
    by_cases h : a = c
    · subst h; simp
    · simp [Matrix.trace_single_eq_of_ne _ _ _ h, h]
  simp only [wernerHolevoChannel, S192PQ_A_eq, S192PQ_F, swapMatrix, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.transpose_apply, ht,
    Matrix.single_apply, Prod.mk.injEq, smul_eq_mul]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> norm_num

lemma S192PQ_obj_of (M : S192PQ_big) (hM : M = S192PQ_P2 S192PQ_A S192PQ_A) :
    (Mᵀ * exampleLambda).trace.re = 1 := by
  rw [hM, S192PQ_P2_T, S192PQ_AT, S192PQ_lam]
  simp only [Matrix.mul_add, Matrix.mul_smul, S192PQ_P2_mul, S192PQ_AA, S192PQ_AS,
    Matrix.trace_add, Matrix.trace_smul, S192PQ_P2_trace, S192PQ_trA]
  simp
  norm_num

lemma S192PQ_objective :
    primalObjective (piSuperop (fun _ : Fin 2 => wernerHolevoChannel 3 1)) exampleLambda = 1 := by
  refine S192PQ_obj_of _ ?_
  ext p q
  simp only [choi, piSuperop, S192PQ_P2, Matrix.of_apply, Matrix.single_apply, ite_and, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Fin.prod_univ_two, S192PQ_wh]
  rw [Fintype.sum_eq_single p.1 (fun x hx => by simp [Ne.symm hx])]
  rw [Fintype.sum_eq_single q.1 (fun x hx => by simp [Ne.symm hx])]
  simp

end S192PQ
end QAlgorithms.Papers.Independent.Support50.P11

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P11 in
theorem solution :
    let N := piSuperop (fun _ : Fin 2 => wernerHolevoChannel 3 1)
    let rho : Matrix (Fin 2 → Fin 3) (Fin 2 → Fin 3) ℂ := (9 : ℂ)⁻¹ • 1
    let Z := reconstructedCode 2 (by decide) rho exampleLambda
    Primal 2 true true rho exampleLambda ∧ primalObjective N exampleLambda = 1 ∧
    IsForwardCode 2 .both Z ∧ codeAverageInput 2 Z = rho ∧ channelFidelity 2 (link 2 N Z) = 1 := by
  intro N rho Z
  have hP : Primal 2 true true rho exampleLambda := S192PQ_primal
  have hO : primalObjective N exampleLambda = 1 := S192PQ_objective
  obtain ⟨h1, h2, h3⟩ := S192PQ_fwd N 2 (by decide) le_rfl true true (Or.inl rfl) rho
    exampleLambda hP
  exact ⟨hP, hO, h1, h2, h3.trans hO⟩
