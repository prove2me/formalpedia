-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.pureOutputDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:06:13.275692+00:00
-- url     : https://prove2.me/submissions/79f1608b-17dc-42ec-8ab1-ab626ba1d8c4

import Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_oneDimensionalEnvironment
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_kraus_complement
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Gap20 QAlgorithms.Papers.Independent.Gap20.P19
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker
open Filter Topology
open QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Claimed50.P48
open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)
open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)
open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)
open QAlgorithms.Papers.Independent.Information100.P69 (choi)
open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B C E F R K A2 B2 E2 : Type}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [Fintype E] [DecidableEq E] [Nonempty E]
variable [Fintype F] [DecidableEq F] [Nonempty F]
variable [Fintype R] [DecidableEq R] [Nonempty R]
variable [Fintype K] [DecidableEq K]
variable [Fintype A2] [DecidableEq A2] [Nonempty A2]
variable [Fintype B2] [DecidableEq B2] [Nonempty B2]
variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

theorem S174D_lag {K : Type} [Fintype K] (α β : K → ℂ) :
    ∑ j, ∑ k, (α j * β k - α k * β j) * star (α j * β k - α k * β j) =
      2 * ((∑ j, α j * star (α j)) * (∑ k, β k * star (β k)) -
        (∑ j, α j * star (β j)) * (∑ k, β k * star (α k))) := by
  set g : K → K → ℂ := fun j k => α j * star (α j) * (β k * star (β k)) -
    α j * star (β j) * (β k * star (α k)) with hg
  calc _ = ∑ j, ∑ k, (g j k + g k j) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        simp only [hg, star_sub, star_mul']; ring
    _ = ∑ j, ∑ k, g j k + ∑ j, ∑ k, g k j := by simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ j, ∑ k, g j k := by rw [Finset.sum_comm (f := fun j k => g k j)]; ring
    _ = _ := by
        simp only [hg, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]

theorem S174D_zero {K K' : Type} [Fintype K] [Fintype K'] (f : K → K' → ℂ)
    (h : ∑ j, ∑ k, f j k * star (f j k) = 0) : ∀ j k, f j k = 0 := by
  have nn : ∀ z : ℂ, 0 ≤ z * star z := fun z => by
    rw [show star z = conj z from rfl, Complex.mul_conj]; exact_mod_cast Complex.normSq_nonneg _
  intro j k
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg fun k _ => nn (f j k))).1 h j
    (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => nn (f j k))).1 h1 k (Finset.mem_univ _)
  rw [show star (f j k) = conj (f j k) from rfl, Complex.mul_conj] at h2
  exact Complex.normSq_eq_zero.1 (by exact_mod_cast h2)

theorem S174D_prod {A : Type} (g k : A → ℂ) (h : ∀ a a', g a * k a' + g a' * k a = 0) :
    (∀ a, g a = 0) ∨ (∀ a, k a = 0) := by
  by_contra hc
  push_neg at hc
  obtain ⟨⟨a1, h1⟩, ⟨a2, h2⟩⟩ := hc
  have e1 : k a1 = 0 := by
    have := h a1 a1
    have : g a1 * k a1 = 0 := by linear_combination this / 2
    exact (mul_eq_zero.1 this).resolve_left h1
  have := h a1 a2
  rw [e1, mul_zero, add_zero] at this
  exact h2 ((mul_eq_zero.1 this).resolve_left h1)

theorem S174D_dich {J B A : Type} (T : J → B → A → ℂ) (j0 : J) (b0 : B) (a0 : A)
    (ht : T j0 b0 a0 ≠ 0)
    (hM : ∀ j k b b' a a', T j b a * T k b' a' + T j b a' * T k b' a =
      T k b a * T j b' a' + T k b a' * T j b' a) :
    (∀ j b a, T j b0 a0 * T j0 b a = T j0 b0 a0 * T j b a) ∨
    (∀ j b a, T j0 b a0 * T j b0 a = T j0 b0 a0 * T j b a) := by
  set t := T j0 b0 a0 with htdef
  have hw : ∀ j b, T j b a0 * t = T j0 b a0 * T j b0 a0 := by
    intro j b
    have := hM j j0 b b0 a0 a0
    linear_combination this / 2
  have h1 : ∀ j b a, t * T j b a + T j b a0 * T j0 b0 a = T j0 b a * T j b0 a0 + T j0 b a0 * T j b0 a := by
    intro j b a
    have := hM j j0 b b0 a a0
    linear_combination this
  have hGK : ∀ j b, (∀ a, t * T j0 b a - T j0 b a0 * T j0 b0 a = 0) ∨
      (∀ a, T j b0 a0 * T j0 b0 a - t * T j b0 a = 0) := by
    intro j b
    apply S174D_prod
    intro a a'
    have h := hM j j0 b b0 a a'
    linear_combination t ^ 2 * h - t * T j0 b0 a' * h1 j b a - t * T j0 b0 a * h1 j b a'
      + 2 * T j0 b0 a * T j0 b0 a' * hw j b
  by_cases hK : ∀ j a, T j b0 a0 * T j0 b0 a - t * T j b0 a = 0
  · left
    intro j b a
    apply mul_left_cancel₀ ht
    linear_combination (-1) * t * h1 j b a + T j0 b a0 * hK j a + T j0 b0 a * hw j b
  · right
    push_neg at hK
    obtain ⟨j1, a1, hj1⟩ := hK
    have hG : ∀ b a, t * T j0 b a - T j0 b a0 * T j0 b0 a = 0 := by
      intro b
      rcases hGK j1 b with h | h
      · exact h
      · exact absurd (h a1) hj1
    intro j b a
    apply mul_left_cancel₀ ht
    linear_combination (-1) * t * h1 j b a - T j b0 a0 * hG b a + T j0 b0 a * hw j b
theorem S174D_kapp {K' ι κ : Type} [Fintype K'] [Fintype ι] (E : K' → Matrix κ ι ℂ)
    (X : Matrix ι ι ℂ) (y y' : κ) :
    krausApply E X y y' = ∑ k, ∑ x, ∑ x', E k y x * X x x' * star (E k y' x') := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]

theorem S174D_unit {m : ℕ} (Phi : Superop A B) (E : Fin m → Matrix B A ℂ)
    (hE : ∀ ρ, Phi ρ = krausApply E ρ)
    (hpure : ∀ psi : EuclideanSpace ℂ A, IsState psi → IsPure (Phi (pureDensity psi)))
    (psi : EuclideanSpace ℂ A) (hpsi : IsState psi) (j k : Fin m) (b b' : B) :
    (∑ a, E j b a * psi a) * (∑ a, E k b' a * psi a) =
      (∑ a, E k b a * psi a) * (∑ a, E j b' a * psi a) := by
  obtain ⟨v, -, hv⟩ := hpure psi hpsi
  have key : ∀ b b', ∑ j, (∑ a, E j b a * psi a) * star (∑ a, E j b' a * psi a) =
      v b * star (v b') := by
    intro b b'
    have := congrFun (congrFun hv b) b'
    rw [hE, S174D_kapp] at this
    simp only [pureDensity, Matrix.of_apply] at this
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    simp only [star_mul']; rw [show star (psi a') = conj (psi a') from rfl]; ring
  have L := S174D_lag (fun j => ∑ a, E j b a * psi a) (fun j => ∑ a, E j b' a * psi a)
  simp only [key] at L
  have L2 : ∑ j, ∑ k, ((∑ a, E j b a * psi a) * (∑ a, E k b' a * psi a) -
      (∑ a, E k b a * psi a) * (∑ a, E j b' a * psi a)) *
      star ((∑ a, E j b a * psi a) * (∑ a, E k b' a * psi a) -
      (∑ a, E k b a * psi a) * (∑ a, E j b' a * psi a)) = 0 := by
    rw [L]; ring
  have := S174D_zero _ L2 j k
  exact sub_eq_zero.1 this

theorem S174D_all {m : ℕ} (Phi : Superop A B) (E : Fin m → Matrix B A ℂ)
    (hE : ∀ ρ, Phi ρ = krausApply E ρ)
    (hpure : ∀ psi : EuclideanSpace ℂ A, IsState psi → IsPure (Phi (pureDensity psi)))
    (v : A → ℂ) (j k : Fin m) (b b' : B) :
    (∑ a, E j b a * v a) * (∑ a, E k b' a * v a) =
      (∑ a, E k b a * v a) * (∑ a, E j b' a * v a) := by
  by_cases hv : v = 0
  · subst hv; simp
  set s : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ A)‖ with hs
  have hs0 : s ≠ 0 := by
    rw [hs, norm_ne_zero_iff]
    intro h; apply hv
    have := congrArg WithLp.ofLp h
    simpa using this
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hunit : IsState (WithLp.toLp 2 (((s : ℂ)⁻¹) • v) : EuclideanSpace ℂ A) := by
    unfold IsState
    rw [WithLp.toLp_smul, norm_smul, ← hs, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ hs0
  have := S174D_unit Phi E hE hpure _ hunit j k b b'
  simp only [Pi.smul_apply, smul_eq_mul] at this
  have e : ∀ (F : Matrix B A ℂ) (b : B), ∑ a, F b a * ((s : ℂ)⁻¹ * v a) = (s : ℂ)⁻¹ * ∑ a, F b a * v a := by
    intro F b; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring
  simp only [e] at this
  have h2 : ((s : ℂ)⁻¹) ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero hsC)
  apply mul_left_cancel₀ h2
  linear_combination this

theorem S174D_minor {m : ℕ} (Phi : Superop A B) (E : Fin m → Matrix B A ℂ)
    (hE : ∀ ρ, Phi ρ = krausApply E ρ)
    (hpure : ∀ psi : EuclideanSpace ℂ A, IsState psi → IsPure (Phi (pureDensity psi))) :
    ∀ j k b b' a a', E j b a * E k b' a' + E j b a' * E k b' a =
      E k b a * E j b' a' + E k b a' * E j b' a := by
  intro j k b b' a a'
  have ev : ∀ (F : Matrix B A ℂ) (b : B) (x : A), ∑ y, F b y * (Pi.single x (1:ℂ) : A → ℂ) y = F b x := by
    intro F b x; simp [Pi.single_apply]
  have ev2 : ∀ (F : Matrix B A ℂ) (b : B), ∑ y, F b y * ((Pi.single a (1:ℂ) + Pi.single a' (1:ℂ) : A → ℂ)) y
      = F b a + F b a' := by
    intro F b; simp [Pi.single_apply, mul_add, Finset.sum_add_distrib]
  have h1 := S174D_all Phi E hE hpure (Pi.single a 1) j k b b'
  have h2 := S174D_all Phi E hE hpure (Pi.single a' 1) j k b b'
  have h3 := S174D_all Phi E hE hpure (Pi.single a 1 + Pi.single a' 1) j k b b'
  simp only [ev, ev2] at h1 h2 h3
  linear_combination h3 - h1 - h2
theorem S174DB_chan {K' ι κ : Type} [Fintype K'] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K' → Matrix κ ι ℂ) (h : ∑ j, (E j)ᴴ * E j = 1) : IsChannel (krausApply E) := by
  refine ⟨Fintype.card K', fun j => E ((Fintype.equivFin K').symm j), ?_, fun rho => ?_⟩
  · unfold IsKrausFamily
    rw [← h]; exact Equiv.sum_comp (Fintype.equivFin K').symm (fun j => (E j)ᴴ * E j)
  · unfold krausApply
    exact (Equiv.sum_comp (Fintype.equivFin K').symm (fun j => E j * rho * (E j)ᴴ)).symm

theorem S174DB_kapp {K' ι κ : Type} [Fintype K'] [Fintype ι] (E : K' → Matrix κ ι ℂ)
    (X : Matrix ι ι ℂ) (y y' : κ) :
    krausApply E X y y' = ∑ k, ∑ x, ∑ x', E k y x * X x x' * star (E k y' x') := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]

theorem S174DB_single {K' ι κ : Type} [Fintype K'] [Fintype ι] [DecidableEq ι]
    (E : K' → Matrix κ ι ℂ) (x x' : ι) (y y' : κ) :
    krausApply E (Matrix.single x x' 1) y y' = ∑ k, E k y x * star (E k y' x') := by
  rw [S174DB_kapp]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem S174DB_lin {K' ι κ : Type} [Fintype K'] [Fintype ι] [DecidableEq ι]
    (E : K' → Matrix κ ι ℂ) (X : Matrix ι ι ℂ) (y y' : κ) :
    krausApply E X y y' = ∑ x, ∑ x', X x x' * krausApply E (Matrix.single x x' 1) y y' := by
  simp only [S174DB_single]
  simp only [S174DB_kapp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem S174DB_ext {K1 K2 ι κ : Type} [Fintype K1] [Fintype K2] [Fintype ι] [DecidableEq ι]
    (E : K1 → Matrix κ ι ℂ) (E' : K2 → Matrix κ ι ℂ)
    (h : ∀ x x' y y', ∑ k, E k y x * star (E k y' x') = ∑ k, E' k y x * star (E' k y' x')) :
    krausApply E = krausApply E' := by
  funext X; ext y y'
  rw [S174DB_lin, S174DB_lin E']
  simp only [S174DB_single, h]

theorem S174DB_smul {K' ι κ : Type} [Fintype K'] [Fintype ι]
    (E : K' → Matrix κ ι ℂ) (c : ℂ) (X : Matrix ι ι ℂ) :
    krausApply E (c • X) = c • krausApply E X := by
  simp [krausApply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

theorem S174DB_TP {K1 K2 ι κ : Type} [Fintype K1] [Fintype K2] [Fintype ι] [DecidableEq ι]
    [Fintype κ] (E0 : K1 → Matrix κ ι ℂ) (h0 : IsKrausFamily E0) (E : K2 → Matrix κ ι ℂ)
    (h : ∀ ρ, krausApply E0 ρ = krausApply E ρ) : IsKrausFamily E := by
  have tr : ∀ {K3 : Type} [Fintype K3] (F : K3 → Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ),
      (krausApply F ρ).trace = ((∑ j, (F j)ᴴ * F j) * ρ).trace := by
    intro K3 _ F ρ
    simp only [krausApply, Matrix.trace_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  unfold IsKrausFamily at *
  ext x x'
  have := tr E (Matrix.single x' x 1)
  rw [← h, tr E0, h0, Matrix.trace_mul_single, Matrix.trace_mul_single] at this
  simp at this
  exact this.symm

theorem S174DB_iso {K' : Type} [Fintype K'] (E : K' → Matrix B A ℂ) (h : IsKrausFamily E) :
    IsIsometry (indexedKrausDilation E) := by
  unfold IsIsometry
  unfold IsKrausFamily at h
  rw [← h]
  ext a a'
  simp only [Matrix.mul_apply, indexedKrausDilation, Matrix.sum_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

theorem S174DB_norm {Y : Type} [Fintype Y] [Nonempty Y] (x : Y → ℂ) :
    ∃ u : Y → ℂ, ∑ y, star (u y) * u y = 1 ∧
      Matrix.vecMulVec x (star x) = (∑ y, star (x y) * x y) • Matrix.vecMulVec u (star u) := by
  have hS : (∑ y, star (x y) * x y) = (((∑ y, Complex.normSq (x y) : ℝ)) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  by_cases hx : x = 0
  · refine ⟨Pi.single (Classical.arbitrary Y) 1, ?_, ?_⟩
    · simp [Pi.single_apply]
    · subst hx; simp
  · set s : ℝ := ∑ y, Complex.normSq (x y) with hs
    have hpos : 0 < s := by
      obtain ⟨y0, hy0⟩ : ∃ y, x y ≠ 0 := by
        by_contra hc; push_neg at hc; exact hx (funext hc)
      have : 0 < Complex.normSq (x y0) := Complex.normSq_pos.mpr hy0
      calc 0 < Complex.normSq (x y0) := this
        _ ≤ s := Finset.single_le_sum (f := fun y => Complex.normSq (x y))
              (fun y _ => Complex.normSq_nonneg _) (Finset.mem_univ y0)
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hpos.le
    have hsq0 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    refine ⟨fun y => ((Real.sqrt s : ℂ))⁻¹ * x y, ?_, ?_⟩
    · have : ∀ y, star (((Real.sqrt s : ℂ))⁻¹ * x y) * (((Real.sqrt s : ℂ))⁻¹ * x y)
          = ((s : ℂ))⁻¹ * (star (x y) * x y) := by
        intro y
        have h1 : star (((Real.sqrt s : ℂ))⁻¹) = ((Real.sqrt s : ℂ))⁻¹ := by
          simp [Complex.conj_ofReal]
        rw [star_mul', h1]
        have h2 : ((s : ℂ)) = ((Real.sqrt s : ℂ)) ^ 2 := by exact_mod_cast hsq.symm
        rw [h2]
        have : ((Real.sqrt s : ℂ)) ≠ 0 := by exact_mod_cast hsq0
        field_simp
      simp only [this, ← Finset.mul_sum, hS]
      have : ((s : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
      field_simp
    · rw [hS]
      ext i j
      simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.star_apply, smul_eq_mul, star_mul']
      have h1 : star (((Real.sqrt s : ℂ))⁻¹) = ((Real.sqrt s : ℂ))⁻¹ := by
        simp [Complex.conj_ofReal]
      rw [h1]
      have h2 : ((s : ℂ)) = ((Real.sqrt s : ℂ)) ^ 2 := by exact_mod_cast hsq.symm
      rw [h2]
      have : ((Real.sqrt s : ℂ)) ≠ 0 := by exact_mod_cast hsq0
      field_simp

theorem S174DB_Dchan {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] (U : Matrix X X ℂ)
    (hU : U * Uᴴ = 1) (u : X → Y → ℂ) (hu : ∀ k, ∑ y, star (u k y) * u k y = 1) :
    IsChannel (fun σ : Matrix X X ℂ =>
      ∑ k, (Uᴴ * σ * U) k k • Matrix.vecMulVec (u k) (star (u k))) := by
  let F : X → Matrix Y X ℂ := fun k => Matrix.of fun y x => u k y * star (U x k)
  have hF : (fun σ : Matrix X X ℂ =>
      ∑ k, (Uᴴ * σ * U) k k • Matrix.vecMulVec (u k) (star (u k))) = krausApply F := by
    funext σ; ext y y'
    rw [S174DB_kapp]
    simp only [F, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul, Pi.star_apply, Finset.sum_mul,
      star_mul', star_star]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    ring
  rw [hF]
  apply S174DB_chan
  rw [← hU]
  ext x x'
  simp only [F, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_mul', star_star]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have := hu k
  calc ∑ y, star (u k y) * U x k * (u k y * star (U x' k))
      = (∑ y, star (u k y) * u k y) * (U x k * star (U x' k)) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun y _ => ?_); ring
    _ = U x k * star (U x' k) := by rw [this, one_mul]

theorem S174DB_G0 {n : ℕ} (f : Fin n → B → ℂ) (g : Fin n → A → ℂ)
    (hK : IsKrausFamily (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ))) :
    ∃ W : Matrix (B × Fin n) A ℂ,
      receiverChannel W = krausApply (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ))
        ∧ IsAntidegradable W := by
  set E : Fin n → Matrix B A ℂ := fun k => Matrix.of fun y x => f k y * g k x with hEdef
  have hKC := kraus_complement E
  choose u hu1 hu2 using fun k => S174DB_norm (f k)
  refine ⟨indexedKrausDilation E, hKC.1, S174DB_iso E hK, ?_⟩
  have hD := S174DB_Dchan (1 : Matrix (Fin n) (Fin n) ℂ) (by simp) u hu1
  simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hD
  refine ⟨fun σ : Matrix (Fin n) (Fin n) ℂ => ∑ k, σ k k •
      Matrix.vecMulVec (u k) (star (u k)), hD, fun ρ => ?_⟩
  rw [hKC.1]
  have hk : ∀ k, E k * ρ * (E k)ᴴ = (∑ x, ∑ x', g k x * ρ x x' * star (g k x')) •
      Matrix.vecMulVec (f k) (star (f k)) := by
    intro k; ext y y'
    simp only [E, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, Pi.star_apply, star_mul', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    ring
  have hc : ∀ k, complementaryChannel (indexedKrausDilation E) ρ k k =
      (∑ x, ∑ x', g k x * ρ x x' * star (g k x')) * ∑ y, star (f k y) * f k y := by
    intro k
    rw [(hKC.2.1 ρ k k).1, hk, Matrix.trace_smul, Matrix.trace_vecMulVec]
    simp [dotProduct, mul_comm]
  simp only [hc]
  unfold krausApply
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hk, hu2 k, smul_smul]

theorem S174DB_G {K' : Type} [Fintype K'] (f : K' → B → ℂ) (g : K' → A → ℂ)
    (hK : IsKrausFamily (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ))) :
    ∃ n : ℕ, ∃ W : Matrix (B × Fin n) A ℂ,
      receiverChannel W = krausApply (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ))
        ∧ IsAntidegradable W := by
  let e := (Fintype.equivFin K').symm
  have hK' : IsKrausFamily (fun k => (Matrix.of fun y x => f (e k) y * g (e k) x : Matrix B A ℂ)) := by
    unfold IsKrausFamily at *
    rw [← hK]
    exact Equiv.sum_comp e (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ)ᴴ *
      (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ))
  obtain ⟨W, hW1, hW2⟩ := S174DB_G0 (fun k => f (e k)) (fun k => g (e k)) hK'
  refine ⟨Fintype.card K', W, ?_, hW2⟩
  rw [hW1]
  funext ρ
  unfold krausApply
  exact Equiv.sum_comp e (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ) * ρ *
      (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ)ᴴ)

theorem S174D_rank0 {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y] (M : Matrix X Y ℂ)
    (h : M.rank = 0) : ∀ x y, M x y = 0 := by
  intro x y
  unfold Matrix.rank at h
  have h2 := Submodule.finrank_eq_zero.1 h
  have : M.mulVecLin (Pi.single y 1) ∈ LinearMap.range M.mulVecLin := LinearMap.mem_range_self _ _
  rw [h2, Submodule.mem_bot] at this
  have := congrFun this x
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this

theorem S174D_main [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi)
    (hpure : ∀ psi : EuclideanSpace ℂ A, IsState psi → IsPure (Phi (pureDensity psi))) :
    (Fintype.card A ≤ Fintype.card B ∧
      (∃ U : Matrix B A ℂ, IsIsometry U ∧ Phi = conjSuperop U) ∧
      (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsDegradable witness) ∧ (choi Phi).rank = 1) ∨
    (∃ phi : EuclideanSpace ℂ B, IsState phi ∧
      (∀ rho, Phi rho = rho.trace • pureDensity phi) ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness)) := by
  obtain ⟨m, E, hK, hE⟩ := hPhi
  have hM := S174D_minor Phi E hE hpure
  have hnz : ∃ j b a, E j b a ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : (∑ j, (E j)ᴴ * E j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have : E j = 0 := by ext b a; exact hc j b a
      rw [this]; simp
    unfold IsKrausFamily at hK
    rw [hK] at h0
    have := congrFun (congrFun h0 (Classical.arbitrary A)) (Classical.arbitrary A)
    simp at this
  obtain ⟨j0, b0, a0, ht⟩ := hnz
  rcases S174D_dich (fun j b a => E j b a) j0 b0 a0 ht hM with hR | hC
  · left
    have hEk : ∀ k b a, E k b a = (E k b0 a0 / E j0 b0 a0) * E j0 b a := by
      intro k b a
      rw [div_mul_eq_mul_div, eq_div_iff ht]
      linear_combination -(hR k b a)
    have hchoi : choi Phi = Matrix.vecMulVec (fun x : A × B => E j0 x.2 x.1)
        (fun y => ∑ k, (E k b0 a0 / E j0 b0 a0) * star (E k b0 a0 / E j0 b0 a0) *
          star (E j0 y.2 y.1)) := by
      ext x y
      simp only [choi, hE, S174DB_single, Matrix.vecMulVec_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hEk k x.2 x.1, hEk k y.2 y.1, star_mul']
      ring
    have hle : (choi Phi).rank ≤ 1 := hchoi ▸ Matrix.rank_vecMulVec_le _ _
    have hne : (choi Phi).rank ≠ 0 := by
      intro h0
      have hdiag := S174D_rank0 _ h0 (a0, b0) (a0, b0)
      simp only [choi, hE, S174DB_single] at hdiag
      have := S174D_zero (fun k (_ : Unit) => E k b0 a0) (by simpa using hdiag) j0 ()
      exact ht this
    have hrank : (choi Phi).rank = 1 := by omega
    obtain ⟨hcard, hdeg, V, hV, hPV, -⟩ :=
      oneDimensionalEnvironment Phi ⟨m, E, hK, hE⟩ hrank
    exact ⟨hcard, ⟨V, hV, hPV⟩, hdeg, hrank⟩
  · right
    obtain ⟨u, hu⟩ : ∃ u : B → ℂ, u = fun b => E j0 b a0 := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : Fin m → A → ℂ, w = fun j a => E j b0 a / E j0 b0 a0 := ⟨_, rfl⟩
    have hEuw : ∀ j, E j = Matrix.of fun y x => u y * w j x := by
      intro j; ext b a
      simp only [Matrix.of_apply, hu, hw]
      rw [mul_div_assoc', eq_div_iff ht]
      linear_combination -(hC j b a)
    have hEeq : E = fun j => Matrix.of fun y x => u y * w j x := funext hEuw
    have hK' : IsKrausFamily (fun k => (Matrix.of fun y x => u y * w k x : Matrix B A ℂ)) := by
      rw [← hEeq]; exact hK
    obtain ⟨n, W, hW1, hW2⟩ := S174DB_G (fun _ => u) w hK'
    obtain ⟨φ0, hφ1, hφ2⟩ := S174DB_norm u
    have hTP : ∀ a a', (∑ b, star (u b) * u b) * ∑ j, w j a * star (w j a') =
        if a' = a then 1 else 0 := by
      intro a a'
      have := congrFun (congrFun hK a') a
      rw [Matrix.sum_apply, Matrix.one_apply] at this
      rw [← this]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hEuw, Matrix.of_apply, star_mul',
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hPhiC : ∀ ρ, Phi ρ = ρ.trace • pureDensity (WithLp.toLp 2 φ0 : EuclideanSpace ℂ B) := by
      intro ρ; ext y y'
      rw [hE, S174DB_lin]
      have h2 := congrFun (congrFun hφ2 y) y'
      simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Pi.star_apply] at h2
      have hs : ∀ x x', krausApply E (Matrix.single x x' 1) y y' =
          if x' = x then φ0 y * star (φ0 y') else 0 := by
        intro x x'
        rw [S174DB_single]
        calc ∑ k, E k y x * star (E k y' x')
            = (u y * star (u y')) * ∑ k, w k x * star (w k x') := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hEuw k]; simp only [Matrix.of_apply, star_mul']; ring
          _ = φ0 y * star (φ0 y') * ((∑ b, star (u b) * u b) * ∑ k, w k x * star (w k x')) := by
              rw [h2]; ring
          _ = _ := by rw [hTP]; simp
      simp only [hs, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [Matrix.smul_apply, pureDensity, Matrix.of_apply, smul_eq_mul, Matrix.trace,
        Matrix.diag, Finset.sum_mul, PiLp.toLp_apply]
      rfl
    refine ⟨WithLp.toLp 2 φ0, ?_, hPhiC, n, W, ?_, hW2⟩
    · unfold IsState
      rw [EuclideanSpace.norm_eq]
      have e : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
        rw [show star z = conj z from rfl, Complex.conj_mul']; push_cast; rfl
      have h : ∑ i, ‖φ0 i‖ ^ 2 = (1:ℝ) := by
        have := hφ1
        simp only [e] at this
        exact_mod_cast this
      simp [h]
    · rw [hW1]; funext ρ; rw [hE ρ, hEeq]

theorem solution [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi)
    (hpure : ∀ psi : EuclideanSpace ℂ A, IsState psi → IsPure (Phi (pureDensity psi))) :
    (Fintype.card A ≤ Fintype.card B ∧
      (∃ U : Matrix B A ℂ, IsIsometry U ∧ Phi = conjSuperop U) ∧
      (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsDegradable witness) ∧ (choi Phi).rank = 1) ∨
    (∃ phi : EuclideanSpace ℂ B, IsState phi ∧
      (∀ rho, Phi rho = rho.trace • pureDensity phi) ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness)) := by
  exact S174D_main Phi hPhi hpure

end
