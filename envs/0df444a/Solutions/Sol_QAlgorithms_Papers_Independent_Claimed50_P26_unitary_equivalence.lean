-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P26.unitary_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:36:09.186468+00:00
-- url     : https://prove2.me/submissions/ec360faf-2852-42af-a186-8b218977fdd7

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26

noncomputable section

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

namespace X6P26

def tpow {n : ℕ} {I J : Type} (A : Matrix I J ℂ) : Matrix (Fin n → I) (Fin n → J) ℂ :=
  Matrix.of fun x y => ∏ i, A (x i) (y i)

lemma prod_sum_sum {n : ℕ} {I J : Type} [Fintype I] [Fintype J] (g : Fin n → I → J → ℂ) :
    ∏ i, ∑ c, ∑ c', g i c c' = ∑ z : Fin n → I, ∑ z' : Fin n → J, ∏ i, g i (z i) (z' i) := by
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]

lemma tpow_mul {n : ℕ} {I J K : Type} [Fintype J] (A : Matrix I J ℂ) (B : Matrix J K ℂ) :
    (tpow (n := n) A) * tpow B = tpow (A * B) := by
  ext x y
  change ∑ z, tpow A x z * tpow B z y = _
  simp only [tpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

lemma tpow_conjTranspose {n : ℕ} {I J : Type} (A : Matrix I J ℂ) :
    (tpow (n := n) A)ᴴ = tpow Aᴴ := by
  ext x y
  simp [tpow, Matrix.conjTranspose_apply]

lemma tpow_one {n : ℕ} {I : Type} [DecidableEq I] :
    tpow (n := n) (1 : Matrix I I ℂ) = 1 := by
  ext x y
  simp only [tpow, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma tpow_unitary {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ unitary (Matrix I I ℂ)) :
    tpow (n := n) U ∈ unitary (Matrix (Fin n → I) (Fin n → I) ℂ) := by
  rw [Unitary.mem_iff] at hU ⊢
  simp only [Matrix.star_eq_conjTranspose] at hU ⊢
  rw [tpow_conjTranspose]
  have h1 := tpow_mul (n := n) Uᴴ U
  have h2 := tpow_mul (n := n) U Uᴴ
  rw [hU.1] at h1; rw [hU.2] at h2
  rw [tpow_one] at h1 h2
  exact ⟨h1, h2⟩


lemma mapp {I J K : Type} [Fintype J] (M : Matrix I J ℂ) (N : Matrix J K ℂ) (i : I) (k : K) :
    (M * N) i k = ∑ j, M i j * N j k := rfl

lemma sum4 {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h1 : ∀ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ b, f a b c d := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma pi_post {n : ℕ} {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K]
    (Φ : Matrix I I ℂ → Matrix J J ℂ) (A : Matrix K J ℂ) (X : Matrix (Fin n → I) (Fin n → I) ℂ) :
    QAlgorithms.piSuperop (fun _ : Fin n => fun Y => A * Φ Y * Aᴴ) X =
      tpow (n := n) A * QAlgorithms.piSuperop (fun _ : Fin n => Φ) X * (tpow (n := n) A)ᴴ := by
  ext y y'
  simp only [QAlgorithms.piSuperop, Matrix.of_apply, mapp, tpow, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  simp only [prod_sum_sum, Finset.prod_mul_distrib, Finset.mul_sum, Finset.sum_mul, star_prod]
  rw [sum4]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring


lemma conj_single {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (B : Matrix J I ℂ) (a a' : I) :
    B * Matrix.single a a' (1 : ℂ) * Bᴴ =
      ∑ b, ∑ b', (B b a * star (B b' a')) • Matrix.single b b' (1 : ℂ) := by
  ext p q
  rw [mapp, Matrix.sum_apply]
  simp only [mapp, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, smul_eq_mul]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]

lemma pi_pre {n : ℕ} {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K]
    (Φ : Matrix J J ℂ → Matrix K K ℂ) (L : Matrix J J ℂ →ₗ[ℂ] Matrix K K ℂ) (hL : ∀ Y, Φ Y = L Y)
    (B : Matrix J I ℂ) (X : Matrix (Fin n → I) (Fin n → I) ℂ) :
    QAlgorithms.piSuperop (fun _ : Fin n => fun Y => Φ (B * Y * Bᴴ)) X =
      QAlgorithms.piSuperop (fun _ : Fin n => Φ) (tpow (n := n) B * X * (tpow (n := n) B)ᴴ) := by
  ext y y'
  simp only [QAlgorithms.piSuperop, Matrix.of_apply, conj_single, hL, map_sum, map_smul]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [mapp, tpow, Matrix.conjTranspose_apply, Matrix.of_apply,
    Finset.sum_mul, prod_sum_sum, Finset.prod_mul_distrib, Finset.mul_sum, star_prod]
  rw [sum4]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

lemma supportPower_conj {I : Type} [Fintype I] [DecidableEq I]
    (U : unitary (Matrix I I ℂ)) (X : Matrix I I ℂ) (t : ℝ) :
    supportPower ((U : Matrix I I ℂ) * X * star (U : Matrix I I ℂ)) t =
      (U : Matrix I I ℂ) * supportPower X t * star (U : Matrix I I ℂ) := by
  unfold supportPower
  by_cases hX : IsSelfAdjoint X
  · have := StarAlgHomClass.map_cfc (S := ℂ) (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U)
      (fun x : ℝ => if x = 0 then 0 else Real.rpow x t) X
      (hf := (Matrix.finite_real_spectrum (A := X)).continuousOn _)
      (hφ := by
        show Continuous fun a : Matrix I I ℂ => (U : Matrix I I ℂ) * a * star (U : Matrix I I ℂ)
        exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    simpa [Unitary.conjStarAlgAut_apply] using this.symm
  · rw [cfc_apply_of_not_predicate _ hX, cfc_apply_of_not_predicate]
    · simp
    · intro h
      apply hX
      have : X = star (U : Matrix I I ℂ) * ((U : Matrix I I ℂ) * X * star (U : Matrix I I ℂ)) * U := by
        simp only [← mul_assoc, Unitary.coe_star_mul_self, one_mul]
        rw [mul_assoc, Unitary.coe_star_mul_self, mul_one]
      rw [this]
      exact h.conjugate' _

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Claimed50.P26 (channelChi)

lemma density_conj {K : Type} [Fintype K] [DecidableEq K] (P : unitary (Matrix K K ℂ))
    (ρ : Matrix K K ℂ) (h : QAlgorithms.IsDensityMatrix ρ) :
    QAlgorithms.IsDensityMatrix ((P : Matrix K K ℂ) * ρ * (P : Matrix K K ℂ)ᴴ) := by
  refine ⟨h.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self,
    one_mul, h.2]

def conjEns {K : Type} [Fintype K] [DecidableEq K] (P : unitary (Matrix K K ℂ))
    (e : Ensemble K) : Ensemble K where
  size := e.size
  prob := e.prob
  state := fun x => (P : Matrix K K ℂ) * e.state x * (P : Matrix K K ℂ)ᴴ
  nonneg := e.nonneg
  total := e.total
  density := fun x => density_conj P _ (e.density x)

lemma trace_conj {K : Type} [Fintype K] [DecidableEq K] (Q : unitary (Matrix K K ℂ))
    (Z : Matrix K K ℂ) : ((Q : Matrix K K ℂ) * Z * star (Q : Matrix K K ℂ)).trace = Z.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

lemma chi_conj {K L : Type} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (α : ℝ) (hα : α ≠ 1) (Γ : Matrix K K ℂ → Matrix L L ℂ)
    (P : unitary (Matrix K K ℂ)) (Q : unitary (Matrix L L ℂ)) :
    channelChi α (fun X => (Q : Matrix L L ℂ) * Γ ((P : Matrix K K ℂ) * X * (P : Matrix K K ℂ)ᴴ) *
      (Q : Matrix L L ℂ)ᴴ) = channelChi α Γ := by
  have key : ∀ e : Ensemble K,
      (supportPower (∑ x, (e.prob x : ℂ) • supportPower ((Q : Matrix L L ℂ) *
        Γ ((P : Matrix K K ℂ) * e.state x * (P : Matrix K K ℂ)ᴴ) * (Q : Matrix L L ℂ)ᴴ) α)
        (1 / α)).trace.re =
      (supportPower (∑ x, (e.prob x : ℂ) • supportPower (Γ ((conjEns P e).state x)) α)
        (1 / α)).trace.re := by
    intro e
    simp only [← Matrix.star_eq_conjTranspose, supportPower_conj]
    have : ∀ (S : Fin e.size → Matrix L L ℂ),
        ∑ x, (e.prob x : ℂ) • ((Q : Matrix L L ℂ) * S x * star (Q : Matrix L L ℂ)) =
          (Q : Matrix L L ℂ) * (∑ x, (e.prob x : ℂ) • S x) * star (Q : Matrix L L ℂ) := by
      intro S
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro x _
      rw [mul_smul_comm, smul_mul_assoc]
    rw [this, supportPower_conj, trace_conj]
    rfl
  unfold channelChi
  congr 1
  ext v
  simp only [if_neg hα, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨conjEns P e, ?_⟩
    rw [key]
    rfl
  · rintro ⟨e, rfl⟩
    refine ⟨conjEns (star P) e, ?_⟩
    rw [key]
    congr 6
    funext x
    simp only [conjEns, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    congr 1
    rw [← Matrix.star_eq_conjTranspose]
    have hP : (P : Matrix K K ℂ) * star (P : Matrix K K ℂ) = 1 := Unitary.mul_star_self_of_mem P.2
    simp only [← mul_assoc, hP, one_mul]
    rw [mul_assoc, hP, mul_one]


lemma kraus_linear {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (Φ : Matrix I I ℂ → Matrix J J ℂ) (hΦ : QAlgorithms.IsChannel Φ) :
    ∃ L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ, ∀ Y, Φ Y = L Y := by
  obtain ⟨m, E, _, hE⟩ := hΦ
  let L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ :=
    { toFun := fun ρ => ∑ j, E j * ρ * (E j)ᴴ
      map_add' := by
        intro a b
        simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul] }
  exact ⟨L, fun Y => by rw [hE]; rfl⟩

end X6P26

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower channelPower) in
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P26 X6P26 in
theorem solution
    (Phi : Superop (Fin 2) (Fin 2)) (hPhi : IsChannel Phi)
    (hunit : Phi ((2 : ℂ)⁻¹ • 1) = (2 : ℂ)⁻¹ • 1)
    (alpha : ℝ) (ha : 1 < alpha)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    regularizedChi alpha (fun X =>
      (V : Matrix (Fin 2) (Fin 2) ℂ)*Phi ((U : Matrix (Fin 2) (Fin 2) ℂ)*X*
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)*(V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) =
      regularizedChi alpha Phi := by
  obtain ⟨L, hL⟩ := kraus_linear Phi hPhi
  have hk : ∀ k : ℕ, channelChi alpha (channelPower (fun X =>
      (V : Matrix (Fin 2) (Fin 2) ℂ)*Phi ((U : Matrix (Fin 2) (Fin 2) ℂ)*X*
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)*(V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) (k + 1)) =
      channelChi alpha (channelPower Phi (k + 1)) := by
    intro k
    have hpow : channelPower (fun X =>
        (V : Matrix (Fin 2) (Fin 2) ℂ)*Phi ((U : Matrix (Fin 2) (Fin 2) ℂ)*X*
          (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)*(V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) (k + 1) =
        fun X => (tpow (n := k + 1) (V : Matrix (Fin 2) (Fin 2) ℂ)) *
          channelPower Phi (k + 1) ((tpow (n := k + 1) (U : Matrix (Fin 2) (Fin 2) ℂ)) * X *
            (tpow (n := k + 1) (U : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) *
          (tpow (n := k + 1) (V : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
      funext X
      unfold channelPower
      rw [pi_post (fun Y => Phi ((U : Matrix (Fin 2) (Fin 2) ℂ) * Y *
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)), pi_pre Phi L hL]
    rw [hpow]
    exact chi_conj alpha (ne_of_gt ha)
      (channelPower Phi (k + 1))
      ⟨tpow (n := k + 1) (U : Matrix (Fin 2) (Fin 2) ℂ), tpow_unitary _ U.2⟩
      ⟨tpow (n := k + 1) (V : Matrix (Fin 2) (Fin 2) ℂ), tpow_unitary _ V.2⟩
  simp only [regularizedChi, hk]
