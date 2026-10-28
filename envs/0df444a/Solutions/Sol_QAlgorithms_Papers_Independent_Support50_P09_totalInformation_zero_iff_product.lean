-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.totalInformation_zero_iff_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:12:16.287864+00:00
-- url     : https://prove2.me/submissions/e7dee0a4-9700-4262-8150-d66ef2cb733a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

-- ===== ZKD =====

/-! Strict Klein inequality for (possibly singular) density matrices with support inclusion. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

namespace X4ZK

/-- scalar Klein gap. -/
def kg (r s : ℝ) : ℝ := r * Real.log r - r * Real.log s - (r - s)

lemma kg_nonneg {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (h0 : s = 0 → r = 0) :
    0 ≤ kg r s ∧ (kg r s = 0 → r = s) := by
  unfold kg
  rcases hs.lt_or_eq with hs' | hs'
  · rcases hr.lt_or_eq with hr' | hr'
    · have key : Real.log (s / r) ≤ s / r - 1 := Real.log_le_sub_one_of_pos (div_pos hs' hr')
      rw [Real.log_div hs'.ne' hr'.ne'] at key
      have e : r * (s / r - 1) = s - r := by field_simp
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left key hr]
      · intro h
        by_contra hne
        have hne' : s / r ≠ 1 := by
          intro h'; apply hne; field_simp at h'; linarith
        have key' := Real.log_lt_sub_one_of_pos (div_pos hs' hr') hne'
        rw [Real.log_div hs'.ne' hr'.ne'] at key'
        nlinarith [mul_lt_mul_of_pos_left key' hr']
    · subst hr'
      simp only [Real.log_zero, mul_zero, zero_mul, sub_zero, zero_sub, neg_neg, sub_self]
      exact ⟨hs'.le, fun h => by linarith⟩
  · subst hs'
    have := h0 rfl
    subst this
    simp [kg]

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma normSq_rows {W : Matrix n n ℂ} (hW : W * Wᴴ = 1) (i : n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have := congrFun (congrFun hW i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
  have h2 : ∑ j, W i j * star (W i j) = ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.star_def, Complex.mul_conj]
  rw [h2] at this
  exact_mod_cast this

lemma normSq_cols {W : Matrix n n ℂ} (hW : Wᴴ * W = 1) (j : n) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have := congrFun (congrFun hW j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
  have h2 : ∑ i, star (W i j) * W i j = ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, RCLike.star_def, Complex.mul_conj]
  rw [h2] at this
  exact_mod_cast this

/-- the abstract strict Klein inequality in eigen-coordinates. -/
lemma klein_coord (W : Matrix n n ℂ) (hW1 : W * Wᴴ = 1) (hW2 : Wᴴ * W = 1) (r s : n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j) (hrs : ∑ i, r i = ∑ j, s j)
    (hsupp : ∀ i j, W i j ≠ 0 → s j = 0 → r i = 0) :
    0 ≤ ∑ i, r i * Real.log (r i) - ∑ i, ∑ j, Complex.normSq (W i j) * (r i * Real.log (s j)) ∧
    (∑ i, r i * Real.log (r i) - ∑ i, ∑ j, Complex.normSq (W i j) * (r i * Real.log (s j)) ≤ 0 →
      ∀ i j, W i j ≠ 0 → r i = s j) := by
  have hk : ∀ i j, 0 ≤ kg (r i) (s j) ∨ W i j = 0 := by
    intro i j
    by_cases h : W i j = 0
    · exact Or.inr h
    · exact Or.inl (kg_nonneg (hr i) (hs j) (hsupp i j h)).1
  have ht : ∀ i j, 0 ≤ Complex.normSq (W i j) * kg (r i) (s j) := by
    intro i j
    rcases hk i j with h | h
    · exact mul_nonneg (Complex.normSq_nonneg _) h
    · simp [h]
  have hD : ∑ i, r i * Real.log (r i) - ∑ i, ∑ j, Complex.normSq (W i j) * (r i * Real.log (s j)) =
      ∑ i, ∑ j, Complex.normSq (W i j) * kg (r i) (s j) := by
    have e1 : ∀ i, r i * Real.log (r i) = ∑ j, Complex.normSq (W i j) * (r i * Real.log (r i)) := by
      intro i; rw [← Finset.sum_mul, normSq_rows hW1, one_mul]
    have e2 : ∑ i, ∑ j, Complex.normSq (W i j) * (r i - s j) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [Finset.sum_comm (f := fun i j => Complex.normSq (W i j) * s j)]
      simp only [← Finset.sum_mul, normSq_rows hW1, normSq_cols hW2, one_mul, hrs, sub_self]
    have e3 : ∑ i, ∑ j, Complex.normSq (W i j) * kg (r i) (s j) =
        ∑ i, ∑ j, Complex.normSq (W i j) * (r i * Real.log (r i) - r i * Real.log (s j)) -
          ∑ i, ∑ j, Complex.normSq (W i j) * (r i - s j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold kg; ring
    rw [e3, e2, sub_zero, Finset.sum_congr rfl fun i _ => e1 i, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hD]
  refine ⟨Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ht i j, fun hle i j hij => ?_⟩
  have h0 : ∑ i, ∑ j, Complex.normSq (W i j) * kg (r i) (s j) = 0 :=
    le_antisymm hle (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ht i j)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => ht i j).1 h0 i (Finset.mem_univ _)
  have hij0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => ht i j).1 hi j (Finset.mem_univ _)
  have hn : Complex.normSq (W i j) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have hkg : kg (r i) (s j) = 0 := (mul_eq_zero.1 hij0).resolve_left hn
  exact (kg_nonneg (hr i) (hs j) (hsupp i j hij)).2 hkg

end X4ZK

end

-- ===== ZKE =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

namespace X4ZK

open QAlgorithms

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma cfc_eq_spec {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    cfc f Y = (hY.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((f (hY.eigenvalues i) : ℝ) : ℂ)) *
        star (hY.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma spec_eq {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    Y = (hY.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((hY.eigenvalues i : ℝ) : ℂ)) *
        star (hY.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hY.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

lemma tr_cfc {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    (cfc f Y).trace.re = ∑ i, f (hY.eigenvalues i) := by
  rw [cfc_eq_spec hY, Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2,
    one_mul, Matrix.trace_diagonal, Complex.re_sum]
  simp

theorem klein_strict (ρ σ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) (hne : ρ ≠ σ) :
    0 < (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log σ).trace.re := by
  have hA := hρ.1.isHermitian
  have hB := hσ.1.isHermitian
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set V : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ) with hV
  set r := hA.eigenvalues with hr
  set s := hB.eigenvalues with hs
  have hU1 : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hU2 : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hV1 : V * star V = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  have hV2 : star V * V = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  set R := Matrix.diagonal (fun i => ((r i : ℝ) : ℂ)) with hR
  set S := Matrix.diagonal (fun i => ((s i : ℝ) : ℂ)) with hS
  set Λ := Matrix.diagonal (fun i => ((Real.log (s i) : ℝ) : ℂ)) with hΛ
  have eρ : ρ = U * R * star U := spec_eq hA
  have eσ : σ = V * S * star V := spec_eq hB
  have eL : cfc Real.log σ = V * Λ * star V := cfc_eq_spec hB Real.log
  set W := star U * V with hW
  have hW1 : W * Wᴴ = 1 := by
    rw [hW, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      star_star]
    calc star U * V * (star V * U) = star U * (V * star V) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV1, Matrix.mul_one, hU2]
  have hW2 : Wᴴ * W = 1 := by
    rw [hW, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      star_star]
    calc star V * U * (star U * V) = star V * (U * star U) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU1, Matrix.mul_one, hV2]
  have hr0 : ∀ i, 0 ≤ r i := hρ.1.eigenvalues_nonneg
  have hs0 : ∀ j, 0 ≤ s j := hσ.1.eigenvalues_nonneg
  have hrs : ∑ i, r i = ∑ j, s j := by
    have h1 := hA.trace_eq_sum_eigenvalues
    have h2 := hB.trace_eq_sum_eigenvalues
    rw [hρ.2] at h1; rw [hσ.2] at h2
    have h1' : (1 : ℝ) = ∑ i, r i := by
      have := congrArg Complex.re h1; simpa [hr] using this
    have h2' : (1 : ℝ) = ∑ i, s i := by
      have := congrArg Complex.re h2; simpa [hs] using this
    rw [← h1', ← h2']
  -- trace of the cross term
  have htr : (ρ * cfc Real.log σ).trace.re =
      ∑ i, ∑ j, Complex.normSq (W i j) * (r i * Real.log (s j)) := by
    have e : ρ * cfc Real.log σ = U * (R * W * Λ * Wᴴ) * star U := by
      rw [eρ, eL, hW, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
        ← Matrix.star_eq_conjTranspose, star_star]
      calc U * R * star U * (V * Λ * star V) = U * R * star U * (V * Λ * star V) * (U * star U) := by
            rw [hU1, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.trace,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΛ, Matrix.mul_diagonal, hR, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
    rw [show (r i : ℂ) * W i j * (Real.log (s j) : ℂ) * star (W i j) =
      ((r i * Real.log (s j) : ℝ) : ℂ) * (W i j * conj (W i j)) by
        rw [Complex.star_def]; push_cast; ring, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, mul_comm]
  -- support condition
  have hsupp : ∀ i j, W i j ≠ 0 → s j = 0 → r i = 0 := by
    intro i j hij hsj
    set v : n → ℂ := fun k => V k j with hv
    have hσV : σ * V = V * S := by
      rw [eσ]
      calc V * S * star V * V = V * S * (star V * V) := by simp only [Matrix.mul_assoc]
        _ = V * S := by rw [hV2, Matrix.mul_one]
    have hσv : σ *ᵥ v = 0 := by
      ext k
      have := congrFun (congrFun hσV k) j
      rw [hS, Matrix.mul_diagonal, hsj, Complex.ofReal_zero, mul_zero] at this
      change (σ * V) k j = 0
      exact this
    have hρv : ρ *ᵥ v = 0 := by
      have : v ∈ LinearMap.ker σ.mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hσv]
      have h2 := hker this
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    -- (V* ρ V)_jj = Σ_i r_i |W_ij|²
    have hq : (star V * ρ * V) j j = ((∑ i, r i * Complex.normSq (W i j) : ℝ) : ℂ) := by
      have e : star V * ρ * V = Wᴴ * R * W := by
        rw [eρ, hW, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
          ← Matrix.star_eq_conjTranspose, star_star]
        simp only [Matrix.mul_assoc]
      rw [e, Matrix.mul_apply]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hR, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
      rw [show star (W i j) * (r i : ℂ) * W i j = (r i : ℂ) * (W i j * conj (W i j)) by
        rw [Complex.star_def]; ring, Complex.mul_conj]
    have hq0 : (star V * ρ * V) j j = 0 := by
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : (ρ * V) k j = 0 := congrFun hρv k
      rw [this, mul_zero]
    rw [hq0] at hq
    have hsum : ∑ i, r i * Complex.normSq (W i j) = 0 := by exact_mod_cast hq.symm
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hr0 i) (Complex.normSq_nonneg _)).1 hsum i (Finset.mem_univ _)
    have hn : Complex.normSq (W i j) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
    exact (mul_eq_zero.1 this).resolve_right hn
  obtain ⟨h0, heq⟩ := klein_coord W hW1 hW2 r s hr0 hs0 hrs hsupp
  rw [Matrix.trace_sub, Complex.sub_re, tr_cfc hA, htr]
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hne
    have hRW : R * W = W * S := by
      ext i j
      simp only [hR, hS, Matrix.diagonal_mul, Matrix.mul_diagonal]
      by_cases hij : W i j = 0
      · rw [hij]; ring
      · rw [heq h.symm.le i j hij, mul_comm]
    have hVUW : V = U * W := by
      rw [hW, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
    rw [eρ, eσ, hVUW, star_mul, Matrix.star_eq_conjTranspose W]
    calc U * R * star U = U * R * (W * Wᴴ) * star U := by rw [hW1, Matrix.mul_one]
      _ = U * (R * W) * Wᴴ * star U := by simp only [Matrix.mul_assoc]
      _ = U * W * S * Wᴴ * star U := by rw [hRW]; simp only [Matrix.mul_assoc]
      _ = U * W * S * (Wᴴ * star U) := by simp only [Matrix.mul_assoc]

end X4ZK

end

-- ===== C1A =====

/-! Strong subadditivity for disjoint register sets (Claimed50.P33 conventions). -/

noncomputable section

namespace X4C1
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def selM {X K F : Type*} (k : X → K) (f : X → F) (φ : F) : Matrix K X ℂ :=
  Matrix.of fun a x => if k x = a ∧ f x = φ then (1:ℂ) else 0

lemma rmA {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] (ρ : Matrix X X ℂ)
    (k : X → K) (f : X → F) :
    redistributionMarginal ρ k f = ∑ φ : F, selM k f φ * ρ * (selM k f φ)ᴴ := by
  ext a b
  simp only [redistributionMarginal, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, selM, of_apply,
    Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset F)) (t := (Finset.univ : Finset X))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (f x)]
  · by_cases hx : k x = a <;> by_cases hy : k y = b <;> by_cases hxy : f x = f y <;>
      simp [hx, hy, hxy, eq_comm]
  · intro φ _ hφ
    have : ¬ f x = φ := fun h => hφ h.symm
    simp [this]
  · simp

lemma rm_density {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] (ρ : Matrix X X ℂ)
    (k : X → K) (f : X → F) (hinj : ∀ x y, k x = k y → f x = f y → x = y)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (redistributionMarginal ρ k f) := by
  have hA := rmA ρ k f
  refine ⟨?_, ?_⟩
  · rw [hA]
    exact Matrix.posSemidef_sum _ fun φ _ => hρ.1.mul_mul_conjTranspose_same (selM k f φ)
  · rw [← hρ.2]
    simp only [Matrix.trace, Matrix.diag, redistributionMarginal]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single (k x)]
      · simp
      · intro b _ hb; rw [if_neg]; rintro ⟨h1, _⟩; exact hb h1.symm
      · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [if_neg]; rintro ⟨h1, h2, h3⟩; exact hy (hinj _ _ (h1.trans h2.symm) h3).symm
    · simp

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

/-- Restriction to a register set. -/
def restr (s : Finset (Fin n)) (x : RegisterBasis D) : SubBasis D s := fun i => x i.1

/-- Restriction to the complement of a register set. -/
def restrC (s : Finset (Fin n)) (x : RegisterBasis D) : (i : {i : Fin n // i ∉ s}) → D i.1 :=
  fun i => x i.1

lemma restr_eq {s : Finset (Fin n)} {x y : RegisterBasis D} :
    restr s x = restr s y ↔ ∀ i ∈ s, x i = y i := by
  simp [restr, funext_iff]

lemma restr_eq' {s : Finset (Fin n)} {x : RegisterBasis D} {c : SubBasis D s} :
    restr s x = c ↔ ∀ i (hi : i ∈ s), x i = c ⟨i, hi⟩ := by
  simp [restr, funext_iff]

lemma restrC_eq {s : Finset (Fin n)} {x y : RegisterBasis D} :
    restrC s x = restrC s y ↔ ∀ i, i ∉ s → x i = y i := by
  simp [restrC, funext_iff]

lemma reg_rm {E : Type} [Fintype E] (ρ : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Finset (Fin n)) :
    registerMarginal ρ s = redistributionMarginal ρ (fun x => (restr s x.1, x.2))
      (fun x => restrC s x.1) := by
  ext a b
  simp only [registerMarginal, redistributionMarginal, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single a.2]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single b.2]
    · congr 1
      apply propext
      simp only [Prod.ext_iff, restr_eq', restrC_eq, and_true]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun i hi => (h1 i hi).1, fun i hi => (h1 i hi).2, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨fun i hi => ⟨h1 i hi, h2 i hi⟩, h3⟩
    · intro e _ he; rw [if_neg]; intro h; exact he (Prod.ext_iff.1 h.2.1).2
    · simp
  · intro e _ he; refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun e' _ => ?_
    rw [if_neg]; intro h; exact he (Prod.ext_iff.1 h.1).2
  · simp

end X4C1

end

-- ===== C1B =====

/-! Conditional mutual information of disjoint register sets is nonnegative. -/

noncomputable section

namespace X4C1
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

variable [∀ i, Nonempty (D i)]

end X4C1

end

-- ===== KFA =====

/-! Generic: two families with equal Gram data are related by a unitary matrix. -/

noncomputable section

namespace X4KF
open scoped Matrix ComplexConjugate InnerProductSpace

variable {P : Type*} [Fintype P]

end X4KF

end

-- ===== KFD =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFD (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix

variable {d e : ℕ}

end X4KF

end

-- ===== KFF =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFF (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix Polynomial

-- entropy swap S(VVᴴ) = S((VᴴV)ᵀ), copied from Solutions/X4/TRC.lean
theorem x4_tr_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem x4_tr_cfc_eq {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M1 : Matrix ι ι ℂ) (M2 : Matrix κ κ ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (h : ∀ k : ℕ, 1 ≤ k → (M1 ^ k).trace = (M2 ^ k).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f M1).trace = (cfc f M2).trace := by
  classical
  let S : Finset ℝ := Finset.univ.image h1.eigenvalues ∪ Finset.univ.image h2.eigenvalues ∪ {0}
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have e1 : cfc f M1 = cfc (fun x => p.eval x) M1 := by
    apply cfc_congr
    intro x hx
    rw [h1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have e2 : cfc f M2 = cfc (fun x => p.eval x) M2 := by
    apply cfc_congr
    intro x hx
    rw [h2.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [S]), hf]
  rw [e1, e2, cfc_polynomial p M1, cfc_polynomial p M2, x4_tr_aeval, x4_tr_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · rw [h i hi]

theorem x4_pow_mul {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem x4_tr_pow_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [x4_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- tr f(V Vᴴ) = tr f((Vᴴ V)ᵀ) when f 0 = 0. -/
theorem x4_ent_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) :
    QAlgorithms.vnEntropy (V * Vᴴ) = QAlgorithms.vnEntropy ((Vᴴ * V)ᵀ) := by
  unfold QAlgorithms.vnEntropy
  rw [x4_tr_cfc_eq (V * Vᴴ) ((Vᴴ * V)ᵀ) (isHermitian_mul_conjTranspose_self V)
    (isHermitian_conjTranspose_mul_self V).transpose _ _ (by simp)]
  intro k hk
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, x4_tr_pow_swap _ _ k hk]

variable {d m : ℕ}

end X4KF

end

-- ===== KFG =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] instKFF

namespace X4KF
open Matrix

variable {d m : ℕ}

variable {e : ℕ}

end X4KF

end

-- ===== DP =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) instDP (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _


namespace X4DP
open Matrix X4KF
open scoped InnerProductSpace

variable {d e : ℕ}

end X4DP

end QAlgorithms.Papers.Independent.Support50.P41

end


-- ===== FanoLib =====

/-! Generic: Schur concavity of von Neumann entropy and the (quantum) Fano bound. -/

noncomputable section

namespace X4FN
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

end X4FN

end

-- ===== SFB =====

/-! Generic: `Σ_k |tr(ρ E_k)|² ≤ F(ρ, Σ_k E_k ρ E_kᴴ)²` for PSD `ρ`. -/

noncomputable section

namespace X4SF
open Matrix QAlgorithms
open scoped Matrix ComplexOrder ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

end X4SF

end

-- ===== SUB =====

/-! Generic: subadditivity of von Neumann entropy, `S(AB) ≤ S(A) + S(B)`. -/

noncomputable section

namespace X4SU
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

end X4SU

end

-- ===== ZEA =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open scoped Matrix ComplexConjugate ComplexOrder

/-- spectral decomposition as a sum of eigenprojectors. -/
lemma spec_sum {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (h : ρ.IsHermitian) :
    ρ = ∑ k, ((h.eigenvalues k : ℝ) : ℂ) • pureDensity (h.eigenvectorBasis k) := by
  conv_lhs => rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [Matrix.mul_apply, diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    pureDensity, smul_eq_mul, Function.comp_apply, Matrix.star_apply, RCLike.star_def,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
    Finset.sum_ite_eq, Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.ofReal_eq_complex_ofReal]
  ring

end X4ZE

end

-- ===== LEA =====

/-! Generic von Neumann entropy facts: scaling, orthogonal rank-one sums, `S(Σσ) ≤ ΣS(σ)`
for unnormalized PSD terms, and concavity `Σ (S(σ_m) + p_m log p_m) ≤ S(Σσ)`. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

/-- square-root eigen-amplitudes of a PSD matrix. -/
def amp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (k a : ι) : ℂ :=
  ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * hσ.1.eigenvectorBasis k a

lemma amp_decomp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) :
    σ = ∑ k, Matrix.of fun a b => amp hσ k a * conj (amp hσ k b) := by
  conv_lhs => rw [X4ZE.spec_sum hσ.1]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext a b
  have hs : ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) =
      ((hσ.1.eigenvalues k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hσ.eigenvalues_nonneg k)]
  simp only [Matrix.smul_apply, pureDensity, Matrix.of_apply, smul_eq_mul, amp, map_mul,
    Complex.conj_ofReal]
  rw [← hs]; ring

end X4LE

end

-- ===== LEB =====

/-! Kraus branches of a bipartite pure vector: Bob marginals, the unnormalized entanglement
functional `Gv` and its monotonicity under Alice-side Kraus families. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)
open scoped Matrix ComplexConjugate ComplexOrder

variable {a b : ℕ}

end X4LE

end

-- ===== ERA =====

/-! Generic entropy facts: scaling with `c ≥ 0`, additivity on orthogonal PSD summands,
invariance under isometric conjugation, pure states, and the qubit bound `S ≤ 1`. -/

noncomputable section

namespace X4ER
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

end X4ER

end

-- ===== DPI =====

/-! Data processing for conditional entropy: a local channel on `A` (in Kraus form) does not
decrease `H(C | A Y)`, i.e. `S(AY) - S(AYC)` can only decrease. Proof: Stinespring isometry
from the Kraus family, isometric invariance of entropy, and strong subadditivity. -/

noncomputable section

namespace X4DPI
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

lemma sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

variable {A A' Y C R : Type} [Fintype A] [Fintype A'] [Fintype Y] [Fintype C] [Fintype R]
  {N : ℕ} (E : Fin N → Matrix A' A ℂ)

end X4DPI

end

-- ===== RMC =====

/-! Entropy of a redistribution marginal depends only on the two partitions
(`keep` and `forget` level sets), not on the labels; conjugation by a partial isometry
that is isometric on the support preserves entropy. -/

noncomputable section

namespace X4RM
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

lemma vn_conj_piso {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef) (J : Matrix κ ι ℂ) (hJ : Jᴴ * J * X = X) :
    vnEntropy (J * X * Jᴴ) = vnEntropy X := by
  set V : Matrix ι ι ℂ := Matrix.of fun a k => X4LE.amp hX k a
  have hV : X = V * Vᴴ := by
    conv_lhs => rw [X4LE.amp_decomp hX]
    ext a b; simp [V, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
  set P := Jᴴ * J with hPdef
  have hP : Pᴴ = P := by simp [hPdef, conjTranspose_mul]
  have hXP : X * P = X := by
    have := congrArg conjTranspose hJ
    rwa [conjTranspose_mul, hX.1.eq, hP] at this
  have hPV : P * V = V := by
    have hW : (P * V - V) * (P * V - V)ᴴ = 0 := by
      have e1 : P * V * (P * V)ᴴ = X := by
        rw [conjTranspose_mul, hP, Matrix.mul_assoc, ← Matrix.mul_assoc V, ← hV,
          ← Matrix.mul_assoc, hJ, hXP]
      have e2 : P * V * Vᴴ = X := by rw [Matrix.mul_assoc, ← hV, hJ]
      have e3 : V * (P * V)ᴴ = X := by
        rw [conjTranspose_mul, hP, ← Matrix.mul_assoc, ← hV, hXP]
      rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, e1, e2, e3, ← hV]
      abel
    exact sub_eq_zero.1 (self_mul_conjTranspose_eq_zero.1 hW)
  have h1 : J * X * Jᴴ = (J * V) * (J * V)ᴴ := by
    rw [hV, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have h2 : (J * V)ᴴ * (J * V) = Vᴴ * V := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, ← hPdef, hPV]
  rw [h1, X4KF.x4_ent_swap, h2, ← X4KF.x4_ent_swap, ← hV]

lemma rm_psd {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] {Z : Matrix X X ℂ}
    (hZ : Z.PosSemidef) (k : X → K) (f : X → F) : (redistributionMarginal Z k f).PosSemidef := by
  rw [X4C1.rmA]
  exact Matrix.posSemidef_sum _ fun φ _ => hZ.mul_mul_conjTranspose_same _

/-- Entropy of a redistribution marginal only depends on the level-set partitions. -/
theorem rm_ent_congr {X K1 F1 K2 F2 : Type} [Fintype X] [Fintype K1] [Fintype F1] [Fintype K2]
    {Z : Matrix X X ℂ} (hZ : Z.PosSemidef) (k1 : X → K1) (f1 : X → F1) (k2 : X → K2) (f2 : X → F2)
    (hk : ∀ x y, k1 x = k1 y ↔ k2 x = k2 y) (hf : ∀ x y, f1 x = f1 y ↔ f2 x = f2 y) :
    vnEntropy (redistributionMarginal Z k2 f2) = vnEntropy (redistributionMarginal Z k1 f1) := by
  set M := redistributionMarginal Z k1 f1
  let J : Matrix K2 K1 ℂ := Matrix.of fun b a => if ∃ x, k1 x = a ∧ k2 x = b then 1 else 0
  have hJk : ∀ b x, J b (k1 x) = if k2 x = b then 1 else 0 := by
    intro b x
    simp only [J, of_apply]
    congr 1
    apply propext
    constructor
    · rintro ⟨x', h1, h2⟩; rw [← h2]; exact ((hk x' x).1 h1).symm
    · intro h; exact ⟨x, rfl, h⟩
  have hM : ∀ a a', M a a' = ∑ x, ∑ y, if k1 x = a ∧ k1 y = a' ∧ f1 x = f1 y then Z x y else 0 := by
    intro a a'; rfl
  have c1 : redistributionMarginal Z k2 f2 = J * M * Jᴴ := by
    funext b b'
    simp only [Matrix.mul_apply, conjTranspose_apply, hM, Finset.mul_sum, Finset.sum_mul]
    rw [X4DPI.sum4]
    simp only [redistributionMarginal]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (k1 y), Finset.sum_eq_single (k1 x)]
    rotate_left
    · intro a _ h; simp [Ne.symm h]
    · simp
    · intro a' _ h; refine Finset.sum_eq_zero fun a _ => ?_; simp [Ne.symm h]
    · simp
    simp only [true_and, hJk]
    by_cases h3 : f1 x = f1 y
    · have h4 := (hf x y).1 h3
      by_cases h1 : k2 x = b <;> by_cases h2 : k2 y = b' <;> simp [h1, h2, h3, h4]
    · have h4 : ¬ f2 x = f2 y := mt (hf x y).2 h3
      simp [h3, h4]
  have c2 : Jᴴ * J * M = M := by
    funext a a'
    simp only [Matrix.mul_apply, conjTranspose_apply, hM, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (k1 x)]
    · by_cases h : k1 y = a' ∧ f1 x = f1 y
      · simp only [h, and_true, true_and]
        have : ∑ b, star (J b a) * J b (k1 x) = if k1 x = a then 1 else 0 := by
          simp_rw [hJk]
          rw [Finset.sum_eq_single (k2 x)]
          · simp only [if_true, mul_one, J, of_apply]
            by_cases hxa : k1 x = a
            · rw [if_pos ⟨x, hxa, rfl⟩, if_pos hxa]; simp
            · rw [if_neg, if_neg hxa]; · simp
              rintro ⟨x', h1, h2⟩; exact hxa ((hk x' x).2 h2 ▸ h1)
          · intro b _ hb; simp [Ne.symm hb]
          · simp
        rw [this]
        by_cases hxa : k1 x = a <;> simp [hxa]
      · simp only [h, and_false, if_false, mul_zero]
    · intro a'' _ h; simp [Ne.symm h]
    · simp
  rw [c1, vn_conj_piso (rm_psd hZ k1 f1) J c2]

theorem rm_ent_congr' {X K1 F1 K2 F2 : Type} [Fintype X] [Fintype K1] [Fintype F1] [Fintype K2]
    {Z : Matrix X X ℂ} (hZ : Z.PosSemidef) (k1 : X → K1) (f1 : X → F1) (k2 : X → K2) (f2 : X → F2)
    (hk : ∀ x y, k1 x = k1 y ↔ k2 x = k2 y) (hf : ∀ x y, f1 x = f1 y ↔ f2 x = f2 y)
    (d1 : DecidableEq K1) (d2 : DecidableEq K2) :
    @vnEntropy K2 _ d2 (redistributionMarginal Z k2 f2) = @vnEntropy K1 _ d1 (redistributionMarginal Z k1 f1) := by
  have h := rm_ent_congr hZ k1 f1 k2 f2 hk hf
  convert h using 2

end X4RM

end

-- ===== SQA =====

/-! Strong subadditivity for register sets with an environment register (Claimed50.P33
`entropyAt` conventions), and nonnegativity of both conditional multipartite informations. -/

noncomputable section

namespace X4SQ
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {G : Fin n → Type} [∀ i, Fintype (G i)] {E : Type} [Fintype E]

lemma ent_rm (τ : Matrix (RegisterBasis G × E) (RegisterBasis G × E) ℂ) (hτ : τ.PosSemidef)
    (s : Finset (Fin n)) {K F : Type} [Fintype K] [Fintype F]
    (k : RegisterBasis G × E → K) (f : RegisterBasis G × E → F)
    (hk : ∀ x y, k x = k y ↔ (∀ i ∈ s, x.1 i = y.1 i) ∧ x.2 = y.2)
    (hf : ∀ x y, f x = f y ↔ ∀ i, i ∉ s → x.1 i = y.1 i) (d : DecidableEq K) :
    @vnEntropy K _ d (redistributionMarginal τ k f) = entropyAt τ s := by
  rw [entropyAt, X4C1.reg_rm]
  exact X4RM.rm_ent_congr' hτ (fun x => (X4C1.restr s x.1, x.2)) (fun x => X4C1.restrC s x.1) k f
    (fun x y => by rw [Prod.mk.injEq, X4C1.restr_eq, hk]) (fun x y => by rw [X4C1.restrC_eq, hf]) _ _

end X4SQ

end

-- ===== ZT1 =====

/-! Tensor products of local matrices on a product register basis. -/

noncomputable section

namespace X4ZT
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]

def tens (A : ∀ i, Matrix (D i) (D i) ℂ) : Matrix (RegisterBasis D) (RegisterBasis D) ℂ :=
  Matrix.of fun x y => ∏ i, A i (x i) (y i)

lemma tens_mul (A B : ∀ i, Matrix (D i) (D i) ℂ) : tens A * tens B = tens (fun i => A i * B i) := by
  ext x y
  simp only [tens, mul_apply, of_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma tens_conjT (A : ∀ i, Matrix (D i) (D i) ℂ) : (tens A)ᴴ = tens (fun i => (A i)ᴴ) := by
  ext x y
  simp only [tens, conjTranspose_apply, of_apply]
  exact map_prod (starRingEnd ℂ) _ _

lemma tens_diag (d : ∀ i, D i → ℂ) :
    tens (fun i => diagonal (d i)) = diagonal (fun x => ∏ i, d i (x i)) := by
  ext x y
  simp only [tens, of_apply, diagonal_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma tens_one : tens (fun i => (1 : Matrix (D i) (D i) ℂ)) = 1 := by
  have := tens_diag (D := D) (fun _ _ => 1)
  simp only [diagonal_one, Finset.prod_const_one] at this
  exact this

lemma marg {R : Type*} [CommSemiring R] (f : ∀ i, D i → R) (i : Fin m) (a : D i) :
    ∑ x : RegisterBasis D, (if x i = a then ∏ j, f j (x j) else 0) =
      f i a * ∏ j : {j // j ≠ i}, ∑ b, f j b := by
  rw [← (Equiv.piSplitAt i D).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.piSplitAt_symm_apply, dite_true]
  rw [Finset.sum_eq_single a]
  · simp only [if_true]
    rw [Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [dif_pos rfl]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [dif_neg j.2]
  · intro b _ hb; simp [hb]
  · simp

end X4ZT

end

-- ===== ZT2 =====

/-! Eigenbasis of the product of single-party marginals. -/

noncomputable section

namespace X4ZT
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

set_option linter.unusedSectionVars false

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]

lemma lm_rm (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (i : Fin m) :
    localMarginal ρ i = redistributionMarginal ρ (fun x : RegisterBasis D => x i)
      (fun x => fun j : {j // j ≠ i} => x j) := by
  ext a b
  simp only [localMarginal, redistributionMarginal]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [funext_iff, Subtype.forall]

lemma lm_density {ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ} (hρ : IsDensityMatrix ρ)
    (i : Fin m) : IsDensityMatrix (localMarginal ρ i) := by
  rw [lm_rm]
  refine X4C1.rm_density ρ _ _ (fun x y h1 h2 => funext fun j => ?_) hρ
  by_cases hj : j = i
  · subst hj; exact h1
  · exact congrFun h2 ⟨j, hj⟩

variable {ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ} (hρ : IsDensityMatrix ρ)

def V (i : Fin m) : Matrix (D i) (D i) ℂ :=
  ((lm_density hρ i).1.isHermitian.eigenvectorUnitary : Matrix (D i) (D i) ℂ)

def lam (i : Fin m) : D i → ℝ := (lm_density hρ i).1.isHermitian.eigenvalues

def U : Matrix (RegisterBasis D) (RegisterBasis D) ℂ := tens (V hρ)

def w (x : RegisterBasis D) : ℝ := ∏ i, lam hρ i (x i)

lemma V_mul (i : Fin m) : V hρ i * (V hρ i)ᴴ = 1 :=
  Unitary.mul_star_self_of_mem (lm_density hρ i).1.isHermitian.eigenvectorUnitary.2

lemma V_mul' (i : Fin m) : (V hρ i)ᴴ * V hρ i = 1 :=
  Unitary.star_mul_self_of_mem (lm_density hρ i).1.isHermitian.eigenvectorUnitary.2

lemma spec_i (i : Fin m) :
    localMarginal ρ i = V hρ i * diagonal (fun a => (lam hρ i a : ℂ)) * (V hρ i)ᴴ :=
  X4ZK.spec_eq _

lemma lam_eq (i : Fin m) :
    (V hρ i)ᴴ * localMarginal ρ i * V hρ i = diagonal (fun a => (lam hρ i a : ℂ)) := by
  rw [spec_i hρ i]
  calc (V hρ i)ᴴ * (V hρ i * diagonal (fun a => (lam hρ i a : ℂ)) * (V hρ i)ᴴ) * V hρ i
      = ((V hρ i)ᴴ * V hρ i) * diagonal (fun a => (lam hρ i a : ℂ)) * ((V hρ i)ᴴ * V hρ i) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [V_mul', Matrix.one_mul, Matrix.mul_one]

lemma lam_nonneg (i : Fin m) (a : D i) : 0 ≤ lam hρ i a := (lm_density hρ i).1.eigenvalues_nonneg a

lemma lam_sum (i : Fin m) : ∑ a, lam hρ i a = 1 := by
  have h := (lm_density hρ i).1.isHermitian.trace_eq_sum_eigenvalues
  have h2 := (lm_density hρ i).2
  have : ((∑ a, lam hρ i a : ℝ) : ℂ) = 1 := by rw [← h2, h]; push_cast; rfl
  exact_mod_cast this

lemma U_mul : U hρ * (U hρ)ᴴ = 1 := by
  rw [U, tens_conjT, tens_mul]
  simp only [V_mul]
  exact tens_one

lemma U_mul' : (U hρ)ᴴ * U hρ = 1 := by
  rw [U, tens_conjT, tens_mul]
  simp only [V_mul']
  exact tens_one

lemma pom_eq : productOfMarginals ρ = U hρ * diagonal (fun x => (w hρ x : ℂ)) * (U hρ)ᴴ := by
  have h0 : productOfMarginals ρ = tens (fun i => localMarginal ρ i) := rfl
  rw [h0, show (fun i => localMarginal ρ i) =
      fun i => V hρ i * diagonal (fun a => (lam hρ i a : ℂ)) * (V hρ i)ᴴ from funext (spec_i hρ),
    ← tens_mul, ← tens_mul, tens_diag, U, tens_conjT]
  congr 3
  funext x
  simp [w]

lemma w_nonneg (x : RegisterBasis D) : 0 ≤ w hρ x :=
  Finset.prod_nonneg fun i _ => lam_nonneg hρ i _

end X4ZT

end

-- ===== ZT3 =====

noncomputable section

namespace X4ZT
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

set_option linter.unusedSectionVars false

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
variable {ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ} (hρ : IsDensityMatrix ρ)

lemma lm_pair (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (i : Fin m) (g : D i → D i → ℂ) :
    ∑ c, ∑ d, g c d * localMarginal ρ i c d =
      ∑ y, ∑ z, if (∀ j, j ≠ i → y j = z j) then g (y i) (z i) * ρ y z else 0 := by
  simp only [localMarginal, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun d _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine (Finset.sum_congr rfl fun d _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single (z i), Finset.sum_eq_single (y i)]
  · split_ifs <;> simp_all
  · intro c _ hc; rw [if_neg]; · simp
    rintro ⟨h1, -⟩; exact hc h1.symm
  · simp
  · intro d _ hd; refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]; · simp
    rintro ⟨-, h2, -⟩; exact hd h2.symm
  · simp

lemma rot_apply (x : RegisterBasis D) :
    ((U hρ)ᴴ * ρ * U hρ) x x =
      ∑ y, ∑ z, ρ y z * ∏ j, (star (V hρ j (y j) (x j)) * V hρ j (z j) (x j)) := by
  simp only [mul_apply, conjTranspose_apply, U, tens, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib,
    show star (∏ i, V hρ i (y i) (x i)) = ∏ i, star (V hρ i (y i) (x i)) from
      map_prod (starRingEnd ℂ) _ _]
  ring

lemma col_sum (j : Fin m) (c d : D j) :
    ∑ b, star (V hρ j c b) * V hρ j d b = if d = c then 1 else 0 := by
  have h := congrFun (congrFun (V_mul hρ j) d) c
  simp only [mul_apply, conjTranspose_apply, one_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

lemma key (i : Fin m) (a : D i) :
    ∑ x, (if x i = a then ((U hρ)ᴴ * ρ * U hρ) x x else 0) = (lam hρ i a : ℂ) := by
  have hl : (lam hρ i a : ℂ) = ((V hρ i)ᴴ * localMarginal ρ i * V hρ i) a a := by
    rw [lam_eq]; simp
  rw [hl]
  have lhs : ∀ x, (if x i = a then ((U hρ)ᴴ * ρ * U hρ) x x else 0) =
      ∑ y, ∑ z, ρ y z * (if x i = a then
        ∏ j, (star (V hρ j (y j) (x j)) * V hρ j (z j) (x j)) else 0) := by
    intro x
    split_ifs
    · exact rot_apply hρ x
    · simp
  rw [Finset.sum_congr rfl fun x _ => lhs x, Finset.sum_comm]
  have rhs : ((V hρ i)ᴴ * localMarginal ρ i * V hρ i) a a =
      ∑ c, ∑ d, (star (V hρ i c a) * V hρ i d a) * localMarginal ρ i c d := by
    simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [rhs, lm_pair]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.mul_sum]
  have hm := marg (fun j b => star (V hρ j (y j) b) * V hρ j (z j) b) i a
  rw [hm]
  simp only [col_sum, Finset.prod_boole]
  have hiff : (∀ j ∈ (Finset.univ : Finset {j // j ≠ i}), z j = y j) ↔ ∀ j, j ≠ i → y j = z j :=
    ⟨fun h j hj => (h ⟨j, hj⟩ (Finset.mem_univ _)).symm, fun h j _ => (h j j.2).symm⟩
  by_cases h : ∀ j, j ≠ i → y j = z j
  · rw [if_pos h, if_pos (hiff.2 h)]; ring
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]; ring

end X4ZT

end

-- ===== ZT4 =====

noncomputable section

namespace X4ZT
open Matrix QAlgorithms Polynomial
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

lemma cfc_conjU {n : Type*} [Fintype n] [DecidableEq n] (U X : Matrix n n ℂ) (h1 : U * Uᴴ = 1) (h2 : Uᴴ * U = 1)
    (hX : X.IsHermitian) (f : ℝ → ℝ) : cfc f (U * X * Uᴴ) = U * cfc f X * Uᴴ := by
  have hu : U ∈ unitary (Matrix n n ℂ) := ⟨h2, h1⟩
  let φ := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) ⟨U, hu⟩).toStarAlgHom
  have hφ : ∀ M, φ M = U * M * Uᴴ := fun M => by
    simp [φ, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have hc : Continuous φ := by
    have : (φ : Matrix n n ℂ → Matrix n n ℂ) = fun M => U * M * Uᴴ := funext hφ
    rw [this]; fun_prop
  have hXs : IsSelfAdjoint X := hX
  have hφX : IsSelfAdjoint (φ X) := hXs.map φ
  rw [← hφ, ← hφ, StarAlgHom.map_cfc φ f X (hf := Matrix.finite_real_spectrum.continuousOn _) (hφ := hc) (ha := hXs) (hφa := hφX)]

lemma cfc_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  classical
  let S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have hD : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1; funext i; simp
  have hspec : ∀ x ∈ spectrum ℝ (diagonal (fun i => (d i : ℂ))), x ∈ S := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal] at hx
    obtain ⟨i, hi⟩ := hx
    have : d i = x := by simpa using hi
    simp [S, ← this]
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x (hspec x hx)).symm),
    cfc_polynomial p _ hD]
  have : aeval (diagonal (fun i => (d i : ℂ))) p = diagonal (aeval (fun i => (d i : ℂ)) p) :=
    (aeval_algHom_apply (diagonalAlgHom ℝ) (fun i => (d i : ℂ)) p)
  rw [this, aeval_pi_apply]
  congr 1; funext i
  have h := aeval_algebraMap_apply ℂ (d i) p
  simp only [Complex.coe_algebraMap] at h
  rw [h, coe_aeval_eq_eval, hp _ (by simp [S] : d i ∈ S)]


attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
variable {ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ} (hρ : IsDensityMatrix ρ)

def rr (x : RegisterBasis D) : ℝ := (((U hρ)ᴴ * ρ * U hρ) x x).re

lemma rot_psd : ((U hρ)ᴴ * ρ * U hρ).PosSemidef := hρ.1.conjTranspose_mul_mul_same _

lemma rot_diag (x : RegisterBasis D) : ((U hρ)ᴴ * ρ * U hρ) x x = (rr hρ x : ℂ) := by
  have h := (rot_psd hρ).diag_nonneg (i := x)
  apply Complex.ext
  · simp [rr]
  · simpa using (Complex.nonneg_iff.1 h).2.symm

lemma rr_nonneg (x : RegisterBasis D) : 0 ≤ rr hρ x := by
  have h := (rot_psd hρ).diag_nonneg (i := x)
  exact (Complex.nonneg_iff.1 h).1

lemma key_re (i : Fin m) (a : D i) : ∑ x, (if x i = a then rr hρ x else 0) = lam hρ i a := by
  have h := key hρ i a
  have : ((∑ x, (if x i = a then rr hρ x else 0) : ℝ) : ℂ) = (lam hρ i a : ℂ) := by
    rw [← h]; push_cast
    exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp [rot_diag]
  exact_mod_cast this

lemma rr_zero (x : RegisterBasis D) (hw : w hρ x = 0) : rr hρ x = 0 := by
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hw
  have h := key_re hρ i (x i)
  rw [hi] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by
    split_ifs
    · exact rr_nonneg hρ y
    · exact le_refl _)).1 h x (Finset.mem_univ _)
  simpa using this

end X4ZT

end

-- ===== ZT5 =====

noncomputable section

namespace X4ZT
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

set_option linter.unusedSectionVars false

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
variable {ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ} (hρ : IsDensityMatrix ρ)

lemma Dw_herm : (diagonal (fun x => (w hρ x : ℂ))).IsHermitian := by
  simp only [IsHermitian, diagonal_conjTranspose]
  congr 1; funext x; simp

include hρ in
lemma pom_density : IsDensityMatrix (productOfMarginals ρ) := by
  refine ⟨?_, ?_⟩
  · rw [pom_eq hρ]
    exact (PosSemidef.diagonal fun x => Complex.zero_le_real.2 (w_nonneg hρ x)).mul_mul_conjTranspose_same _
  · rw [pom_eq hρ, trace_mul_cycle, U_mul', Matrix.one_mul, trace_diagonal]
    simp only [w]
    have : ∑ x : RegisterBasis D, ∏ i, lam hρ i (x i) = 1 := by
      rw [← Fintype.prod_sum (κ := D) (fun i a => lam hρ i a)]
      simp [lam_sum]
    rw [← Complex.ofReal_sum, this, Complex.ofReal_one]

lemma col_zero {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (x : n) (h : A x x = 0) (y : n) : A y x = 0 := by
  have h1 := (hA.dotProduct_mulVec_zero_iff (Pi.single x 1)).1 (by simp [h])
  have := congrFun h1 y
  simpa using this

include hρ in
lemma pom_ker : LinearMap.ker (productOfMarginals ρ).mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  set u := (U hρ)ᴴ *ᵥ v with hu
  have h1 : diagonal (fun x => (w hρ x : ℂ)) *ᵥ u = 0 := by
    have : (U hρ)ᴴ *ᵥ (productOfMarginals ρ *ᵥ v) = 0 := by rw [hv, mulVec_zero]
    rw [pom_eq hρ, mulVec_mulVec] at this
    rw [hu, mulVec_mulVec, ← this]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, U_mul', Matrix.one_mul]
  have h2 : ∀ x, w hρ x * u x = 0 := fun x => by
    have := congrFun h1 x
    rw [mulVec_diagonal] at this
    exact_mod_cast this
  have hρeq : ρ = U hρ * ((U hρ)ᴴ * ρ * U hρ) * (U hρ)ᴴ := by
    simp only [← Matrix.mul_assoc, U_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, U_mul, Matrix.mul_one]
  have h3 : ((U hρ)ᴴ * ρ * U hρ) *ᵥ u = 0 := by
    funext y
    simp only [mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : u x = 0
    · rw [hx, mul_zero]
    · have hw : w hρ x = 0 := by
        have := h2 x
        rcases mul_eq_zero.1 this with h | h
        · exact_mod_cast h
        · exact absurd (by exact_mod_cast h) hx
      have hd : ((U hρ)ᴴ * ρ * U hρ) x x = 0 := by rw [rot_diag, rr_zero hρ x hw]; simp
      rw [col_zero (rot_psd hρ) x hd y, zero_mul]
  rw [hρeq, ← mulVec_mulVec, ← mulVec_mulVec, ← hu, h3, mulVec_zero]

lemma cfc_log_pom : cfc Real.log (productOfMarginals ρ) =
    U hρ * diagonal (fun x => ((Real.log (w hρ x) : ℝ) : ℂ)) * (U hρ)ᴴ := by
  rw [pom_eq hρ, cfc_conjU _ _ (U_mul hρ) (U_mul' hρ) (Dw_herm hρ), cfc_diag]

lemma sum_fib {R : Type*} [AddCommMonoid R] [Module ℝ R] (i : Fin m) (g : D i → ℝ) :
    ∑ x, rr hρ x * g (x i) = ∑ a, lam hρ i a * g a := by
  simp only [← key_re hρ i, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (x i)]
  · simp
  · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
  · simp

lemma tr_log : (ρ * cfc Real.log (productOfMarginals ρ)).trace.re =
    ∑ i, ∑ a, lam hρ i a * Real.log (lam hρ i a) := by
  rw [cfc_log_pom hρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_cycle,
    ← Matrix.mul_assoc]
  have : ((U hρ)ᴴ * ρ * U hρ * diagonal (fun x => ((Real.log (w hρ x) : ℝ) : ℂ))).trace.re =
      ∑ x, rr hρ x * Real.log (w hρ x) := by
    simp only [trace, diag, mul_diagonal, rot_diag, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [this]
  have hpt : ∀ x, rr hρ x * Real.log (w hρ x) = ∑ i, rr hρ x * Real.log (lam hρ i (x i)) := by
    intro x
    by_cases hw : w hρ x = 0
    · simp [rr_zero hρ x hw]
    · rw [← Finset.mul_sum, w, Real.log_prod]
      intro i _ hi
      exact hw (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_fib (R := ℝ) hρ i (fun a => Real.log (lam hρ i a))

end X4ZT

end

-- ===== ZT6 =====

noncomputable section

namespace X4ZT
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

set_option linter.unusedSectionVars false

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]

lemma re_xlogx {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (cfc (fun x : ℝ => x * Real.log x) X).trace.re = -(Real.log 2) * vnEntropy X := by
  unfold vnEntropy
  rw [X4ZK.tr_cfc hX, X4ZK.tr_cfc hX, neg_mul_neg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Real.log 2 ≠ 0 := by positivity
  rw [Real.logb]; field_simp

variable {ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ} (hρ : IsDensityMatrix ρ)

lemma vn_lm (i : Fin m) :
    ∑ a, lam hρ i a * Real.log (lam hρ i a) = -(Real.log 2) * vnEntropy (localMarginal ρ i) := by
  rw [← re_xlogx (lm_density hρ i).1.isHermitian, X4ZK.tr_cfc (lm_density hρ i).1.isHermitian]
  rfl

include hρ in
lemma triv_psd : (trivialExtension ρ).PosSemidef := hρ.1.submatrix Prod.fst

include hρ in
lemma ent_single (i : Fin m) :
    entropyAt (trivialExtension ρ) {i} = vnEntropy (localMarginal ρ i) := by
  rw [← X4SQ.ent_rm (trivialExtension ρ) (triv_psd hρ) {i} (fun x => x.1 i)
    (fun x => fun j : {j // j ≠ i} => x.1 j) (fun x y => by simp)
    (fun x y => by simp [funext_iff]) inferInstance]
  congr 1
  ext a b
  simp only [redistributionMarginal, localMarginal, trivialExtension, Fintype.sum_prod_type,
    Finset.univ_unique, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [funext_iff, Subtype.forall]

include hρ in
lemma ent_univ : entropyAt (trivialExtension ρ) Finset.univ = vnEntropy ρ := by
  rw [← X4SQ.ent_rm (trivialExtension ρ) (triv_psd hρ) Finset.univ (fun x => x.1)
    (fun _ => ()) (fun x y => by simp [funext_iff]) (fun x y => by simp) inferInstance]
  congr 1
  ext a b
  simp only [redistributionMarginal, trivialExtension, Fintype.sum_prod_type,
    Finset.univ_unique, Finset.sum_singleton, and_true]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy; simp [hy]
  · simp
  · intro x _ hx; refine Finset.sum_eq_zero fun y _ => ?_; simp [hx]
  · simp

include hρ in
lemma ent_empty : entropyAt (trivialExtension ρ) ∅ = 0 := by
  rw [← X4SQ.ent_rm (trivialExtension ρ) (triv_psd hρ) ∅ (fun _ => ())
    (fun x => x.1) (fun x y => by simp) (fun x y => by simp [funext_iff]) inferInstance]
  have hd := X4C1.rm_density (trivialExtension ρ) (fun _ => ()) (fun x => x.1)
    (fun x y _ h => Prod.ext h rfl) ⟨triv_psd hρ, by
      rw [← hρ.2]; simp [trace, trivialExtension, Fintype.sum_prod_type]⟩
  have hH := hd.1.isHermitian
  have ht := hH.trace_eq_sum_eigenvalues
  rw [hd.2, Fintype.sum_unique] at ht
  have he' : ((hH.eigenvalues default : ℝ) : ℂ) = 1 := ht.symm
  have he : hH.eigenvalues default = 1 := by exact_mod_cast he'
  unfold vnEntropy
  rw [X4ZK.tr_cfc hH, Fintype.sum_unique, he]
  simp

include hρ in
lemma info_eq : info .total ρ (singleParties m) ∅ =
    ∑ i, vnEntropy (localMarginal ρ i) - vnEntropy ρ := by
  simp only [info, conditionalMultipartiteInformation, singleParties, allParties,
    Finset.union_empty, ent_single hρ, ent_empty hρ, mul_zero, sub_zero]
  have hu : Finset.univ.biUnion (singleParties m) = Finset.univ := by ext; simp [singleParties]
  rw [hu, ent_univ hρ]

include hρ in
lemma T_eq : (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log (productOfMarginals ρ)).trace.re =
    Real.log 2 * info .total ρ (singleParties m) ∅ := by
  rw [trace_sub, Complex.sub_re, re_xlogx hρ.1.isHermitian, tr_log hρ, info_eq hρ]
  simp only [vn_lm hρ, ← Finset.mul_sum]
  ring

include hρ in
theorem main : info .total ρ (singleParties m) ∅ = 0 ↔ ρ = productOfMarginals ρ := by
  constructor
  · intro h
    by_contra hne
    have := X4ZK.klein_strict ρ (productOfMarginals ρ) hρ (pom_density hρ) (pom_ker hρ) hne
    rw [T_eq hρ, h, mul_zero] at this
    exact lt_irrefl _ this
  · intro h
    have e1 : cfc (fun x : ℝ => x * Real.log x) ρ = ρ * cfc Real.log ρ := by
      have hs : IsSelfAdjoint ρ := hρ.1.isHermitian
      rw [cfc_mul (fun x : ℝ => x) Real.log ρ (Matrix.finite_real_spectrum.continuousOn _)
        (Matrix.finite_real_spectrum.continuousOn _), cfc_id' ℝ ρ hs]
    have h0 : (cfc (fun x : ℝ => x * Real.log x) ρ -
        ρ * cfc Real.log (productOfMarginals ρ)).trace.re = 0 := by
      rw [e1, ← h, sub_self, trace_zero, Complex.zero_re]
    rw [T_eq hρ] at h0
    have : Real.log 2 ≠ 0 := by positivity
    exact (mul_eq_zero.1 h0).resolve_left this

end X4ZT

end

-- ===== ZTSol =====

open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexConjugate ComplexOrder

theorem solution {m : ℕ} (hm : 0 < m)
    {D : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    info .total rho (singleParties m) ∅ = 0 ↔ rho = productOfMarginals rho :=
  X4ZT.main hrho

