-- Prove2me | solution 2 for Schanuel.gelfond_schneider
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:10:57.329355+00:00
-- url     : https://prove2.me/submissions/129e4463-3aeb-460d-ae26-3dc6ffa25213

import Mathlib

/-!
The development below is M. Karatarakis's formalization of the Gelfond–Schneider theorem,
from `Mathlib/NumberTheory/Transcendental/GelfondSchneider/` (the files `MainAlg`, `MainAlgSetup`,
`MainOrder`, `MainAnalytic`, `AnalyticPart`, `MainPostAnalytic`, `MainAnalyticBounds`, `MainHol`,
`MainBounds` and `statement`, in that order) and the house
version of Siegel's lemma from `Mathlib/NumberTheory/NumberField/House.lean` (namespace
`NumberField.house`, here `GSHouse`, with its constants made public as in that fork), and the house
version of Siegel's lemma from `Mathlib/NumberTheory/NumberField/House.lean` (namespace
`NumberField.house`, here `GSHouse`, with its constants made public as in that fork), and the house
version of Siegel's lemma from `Mathlib/NumberTheory/NumberField/House.lean` (namespace
`NumberField.house`, here `GSHouse`, with its constants made public as in that fork), and the house
version of Siegel's lemma from `Mathlib/NumberTheory/NumberField/House.lean` (namespace
`NumberField.house`, here `GSHouse`, with its constants made public as in that fork), and the house
version of Siegel's lemma from `Mathlib/NumberTheory/NumberField/House.lean` (namespace
`NumberField.house`, here `GSHouse`, with its constants made public as in that fork), and the house
version of Siegel's lemma from `Mathlib/NumberTheory/NumberField/House.lean` (namespace
`NumberField.house`, here `GSHouse`, with its constants made public as in that fork), and the house
version of Siegel's lemma from `Mathlib/NumberTheory/NumberField/House.lean` (namespace
`NumberField.house`, here `GSHouse`, with its constants made public as in that fork), and the house
version of Siegel's lemma from `Mathlib/NumberTheory/NumberField/House.lean` (namespace
`NumberField.house`, here `GSHouse`, with its constants made public as in that fork), in
https://github.com/mkaratarakis/mathlib4 at commit cb781672b399c6badb5c70e3f73056bcb31012b0,
described in M. Karatarakis and F. Wiedijk, "A formalization of the Gelfond-Schneider theorem",
arXiv:2603.24823 (2026). Copyright (c) 2026 Michail Karatarakis, released under the Apache 2.0
license. Adapted here only as needed to build against this Mathlib revision.
-/

open Lean Meta Qq Mathlib.Meta.Positivity in
/-- `positivity` extension: the house of an algebraic number is non-negative. The fork declares
`house` as an `abbrev`, which `positivity` saw through; here it is a `def`, so this is added. -/
@[positivity NumberField.house _]
meta def evalGSHouse : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.house $K $f $nf $a) =>
    assertInstancesCommute
    pure (.nonnegative q(NumberField.house_nonneg $a))
  | _, _, _ => throwError "not NumberField.house"

section GSHouseSection
variable {K : Type*} [Field K] [NumberField K]
open NumberField
namespace GSHouse

noncomputable section

variable (K)

open Module.Free Module canonicalEmbedding Matrix Finset

attribute [local instance] Matrix.seminormedAddCommGroup

section DecidableEq

variable [DecidableEq (K →+* ℂ)]

/-- `c` is defined as the product of the maximum absolute
  value of the entries of the inverse of the matrix `basisMatrix` and  `finrank ℚ K`. -/
def c := (finrank ℚ K) * ‖((basisMatrix K).transpose)⁻¹‖

theorem c_nonneg : 0 ≤ c K := by
  rw [c]
  positivity

set_option backward.whnf.reducibleClassField false in
set_option backward.isDefEq.respectTransparency false in
theorem basis_repr_norm_le_const_mul_house (α : 𝓞 K) (i : K →+* ℂ) :
    ‖(((integralBasis K).reindex (equivReindex K).symm).repr α i : ℂ)‖ ≤
      (c K) * house (algebraMap (𝓞 K) K α) := by
  let σ := canonicalEmbedding K
  calc
    _ ≤ ∑ j, ‖(basisMatrix K)ᵀ⁻¹ i j‖ * ‖σ (algebraMap (𝓞 K) K α) j‖ := by
      rw [← inverse_basisMatrix_mulVec_eq_repr]
      exact norm_sum_le_of_le _ fun _ _ ↦ (norm_mul _ _).le
    _ ≤ ∑ j, ‖((basisMatrix K).transpose)⁻¹‖ * ‖σ (algebraMap (𝓞 K) K α) j‖ := by
      gcongr
      exact norm_entry_le_entrywise_sup_norm ((basisMatrix K).transpose)⁻¹
    _ ≤ ∑ _ : K →+* ℂ, ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖
        * house (algebraMap (𝓞 K) K α) := by
      gcongr with j
      exact norm_le_pi_norm (σ ((algebraMap (𝓞 K) K) α)) j
    _ = ↑(finrank ℚ K) * ‖((basisMatrix K).transpose)⁻¹‖ * house (algebraMap (𝓞 K) K α) := by
      simp [Embeddings.card, mul_assoc]

/-- `newBasis K` defines a reindexed basis of the ring of integers of `K`,
  adjusted by the inverse of the equivalence `equivReindex`. -/
def newBasis := (RingOfIntegers.basis K).reindex (equivReindex K).symm

/-- `supOfBasis K` calculates the supremum of the absolute values of
  the elements in `newBasis K`. -/
def supOfBasis : ℝ := univ.sup' univ_nonempty
  fun r ↦ house (algebraMap (𝓞 K) K (newBasis K r))

end DecidableEq

theorem supOfBasis_nonneg : 0 ≤ supOfBasis K := by
  simp only [supOfBasis, le_sup'_iff, mem_univ, and_self,
    exists_const, house_nonneg]

variable {α : Type*} {β : Type*} (a : Matrix α β (𝓞 K))

/-- `a' K a` returns the integer coefficients of the basis vector in the
  expansion of the product of an algebraic integer and a basis vectors. -/
def a' : α → β → (K →+* ℂ) → (K →+* ℂ) → ℤ := fun k l r =>
  (newBasis K).repr (a k l * (newBasis K) r)



/-- `asiegel K a` is the integer matrix of the coefficients of the
product of matrix elements and basis vectors. -/
def asiegel : Matrix (α × (K →+* ℂ)) (β × (K →+* ℂ)) ℤ := fun k l => a' K a k.1 l.1 l.2 k.2

variable (ha : a ≠ 0)

set_option backward.isDefEq.respectTransparency false in
include ha in
theorem asiegel_ne_0 : asiegel K a ≠ 0 := by
  simp +unfoldPartialApp only [asiegel, a']
  simp only [ne_eq]
  rw [funext_iff]; intro hs
  simp only [Prod.forall] at hs
  apply ha
  rw [← Matrix.ext_iff]; intro k' l
  specialize hs k'
  let ⟨b⟩ := Fintype.card_pos_iff.1 (Fintype.card_pos (α := (K →+* ℂ)))
  have := ((newBasis K).repr.map_eq_zero_iff (x := (a k' l * (newBasis K) b))).1 <| by
    ext b'
    specialize hs b'
    rw [funext_iff] at hs
    simp only [Prod.forall] at hs
    apply hs
  simp only [mul_eq_zero] at this
  exact this.resolve_right (Basis.ne_zero (newBasis K) b)

variable {p q : ℕ} (h0p : 0 < p) (hpq : p < q) (x : β × (K →+* ℂ) → ℤ) (hxl : x ≠ 0)

/-- `ξ` is the product of `x (l, r)` and the `r`-th basis element of the newBasis of `K`. -/
def ξ : β → 𝓞 K := fun l => ∑ r : K →+* ℂ, x (l, r) * (newBasis K r)

set_option backward.isDefEq.respectTransparency false in
include hxl in
theorem ξ_ne_0 : ξ K x ≠ 0 := by
  intro H
  apply hxl
  ext ⟨l, r⟩
  rw [funext_iff] at H
  have hblin := Basis.linearIndependent (newBasis K)
  simp only [zsmul_eq_mul, Fintype.linearIndependent_iff] at hblin
  exact hblin (fun r ↦ x (l, r)) (H _) r

set_option backward.isDefEq.respectTransparency false in
theorem lin_1 (l k r) : a k l * (newBasis K) r =
    ∑ u, (a' K a k l r u) * (newBasis K) u := by
  simp only [Basis.sum_repr (newBasis K) (a k l * (newBasis K) r), a', ← zsmul_eq_mul]

variable [Fintype β] (cardβ : Fintype.card β = q) (hmulvec0 : asiegel K a *ᵥ x = 0)

include hxl hmulvec0 in
theorem ξ_mulVec_eq_0 : a *ᵥ ξ K x = 0 := by
  funext k; simp only [Pi.zero_apply]; rw [eq_comm]
  have lin_0 : ∀ u, ∑ r, ∑ l, (a' K a k l r u * x (l, r) : 𝓞 K) = 0 := by
    intro u
    have hξ := ξ_ne_0 K x hxl
    rw [Ne, funext_iff, not_forall] at hξ
    rcases hξ with ⟨l, hξ⟩
    rw [funext_iff] at hmulvec0
    specialize hmulvec0 ⟨k, u⟩
    simp only [Fintype.sum_prod_type, mulVec, dotProduct, asiegel] at hmulvec0
    rw [sum_comm] at hmulvec0
    exact mod_cast hmulvec0
  have : 0 = ∑ u, (∑ r, ∑ l, a' K a k l r u * x (l, r) : 𝓞 K) * (newBasis K) u := by
    simp only [lin_0, zero_mul, sum_const_zero]
  have : 0 = ∑ r, ∑ l, x (l, r) * ∑ u, a' K a k l r u * (newBasis K) u := by
    conv at this => enter [2, 2, u]; rw [sum_mul]
    rw [sum_comm] at this
    rw [this]; congr 1; ext1 r
    conv => enter [1, 2, l]; rw [sum_mul]
    rw [sum_comm]; congr 1; ext1 r
    rw [mul_sum]; congr 1; ext1 r
    ring
  rw [sum_comm] at this
  rw [this]; congr 1; ext1 l
  rw [ξ, mul_sum]; congr 1; ext1 l
  rw [← lin_1]; ring

variable {A : ℝ} (habs : ∀ k l, (house ((algebraMap (𝓞 K) K) (a k l))) ≤ A)

variable [DecidableEq (K →+* ℂ)]

/-- `c₂` is the product of the maximum of `1` and `c`, and `supOfBasis`. -/
abbrev c₂ := max 1 (c K) * (max 1 (supOfBasis K))

theorem c₂_nonneg : 0 ≤ c₂ K := by
  apply mul_nonneg (le_trans zero_le_one (le_max_left ..))
  apply (le_trans zero_le_one (le_max_left ..))

variable [Fintype α] (cardα : Fintype.card α = p) (Apos : 0 ≤ A)
  (hxbound : ‖x‖ ≤ (q * finrank ℚ K * ‖asiegel K a‖) ^ ((p : ℝ) / (q - p)))

include habs Apos in
theorem asiegel_remark : ‖asiegel K a‖ ≤ c₂ K * A := by
  rw [Matrix.norm_le_iff]
  · intro kr lu
    calc
      ‖asiegel K a kr lu‖ = |asiegel K a kr lu| := ?_
      _ ≤ (c K) *
        house ((algebraMap (𝓞 K) K) (a kr.1 lu.1 * ((newBasis K) lu.2))) := ?_
      _ ≤ (c K) * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1)) *
        house ((algebraMap (𝓞 K) K) ((newBasis K) lu.2)) := ?_
      _ ≤ (c K) * A * house ((algebraMap (𝓞 K) K) ((newBasis K) lu.2)) := ?_
      _ ≤ (c K) * A * (supOfBasis K) := ?_
      _ ≤ (c₂ K) * A := ?_
    · simp only [Int.cast_abs, ← Real.norm_eq_abs (asiegel K a kr lu)]; rfl
    · have remark := basis_repr_norm_le_const_mul_house K
      simp only [Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
        NumberField.integralBasis_repr_apply, eq_intCast, Rat.cast_intCast,
          Complex.norm_intCast] at remark
      exact mod_cast remark ((a kr.1 lu.1 * ((newBasis K) lu.2))) kr.2
    · simp only [house, map_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (c_nonneg K)
    · rw [mul_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left ?_ (c_nonneg K)
      · apply mul_le_mul_of_nonneg_right (habs kr.1 lu.1) ?_
        · exact norm_nonneg ((canonicalEmbedding K) ((algebraMap (𝓞 K) K)
            ((newBasis K) lu.2)))
    ·  apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg (c_nonneg K) Apos)
       · simp only [supOfBasis, le_sup'_iff, mem_univ]; use lu.2
    · rw [mul_right_comm]
      apply mul_le_mul_of_nonneg_right ?_ Apos
      unfold c₂
      apply  mul_le_mul
      · apply le_max_right
      · apply le_max_right
      · exact supOfBasis_nonneg K
      · apply (le_trans zero_le_one (le_max_left ..))
  · rw [mul_nonneg_iff]; left; exact ⟨c₂_nonneg K, Apos⟩

/-- `c₁ K` is the product of `finrank ℚ K` and  `c₂ K` and depends on `K`. -/
def c₁ := finrank ℚ K * c₂ K

include habs Apos hxbound hpq in
theorem house_le_bound : ∀ l, house (ξ K x l).1 ≤ (c₁ K) *
    ((c₁ K * q * A)^((p : ℝ) / (q - p))) := by
  let h := finrank ℚ K
  intros l
  calc _ = house (algebraMap (𝓞 K) K (∑ r, (x (l, r)) * ((newBasis K) r))) := rfl
       _ ≤ ∑ r, house (((algebraMap (𝓞 K) K) (x (l, r))) *
        ((algebraMap (𝓞 K) K) ((newBasis K) r))) := ?_
       _ ≤ ∑ r, ‖x (l,r)‖ * house ((algebraMap (𝓞 K) K) ((newBasis K) r)) := ?_
       _ ≤ ∑ r, ‖x (l, r)‖ * (supOfBasis K) := ?_
       _ ≤ ∑ _r : K →+* ℂ, ((↑q * h * ‖asiegel K a‖) ^ ((p : ℝ) / (q - p))) * supOfBasis K := ?_
       _ ≤ h * (c₂ K) * ((q * c₁ K * A) ^ ((p : ℝ) / (q - p))) := ?_
       _ ≤ c₁ K * ((c₁ K * ↑q * A) ^ ((p : ℝ) / (q - p))) := ?_
  · simp_rw [← map_mul, map_sum]; apply house_sum_le_sum_house
  · apply sum_le_sum; intros r _; convert! house_mul_le ..
    simp only [map_intCast, house_intCast, Int.cast_abs, Int.norm_eq_abs]
  · apply sum_le_sum; intros r _; unfold supOfBasis
    apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg (x (l,r)))
    · simp only [le_sup'_iff, mem_univ, true_and]; use r
  · apply sum_le_sum; intros r _
    apply mul_le_mul_of_nonneg_right ?_ (supOfBasis_nonneg K)
    exact le_trans (norm_le_pi_norm x ⟨l, r⟩) hxbound
  · simp only [sum_const, card_univ, nsmul_eq_mul]
    rw [Embeddings.card, mul_comm _ (supOfBasis K), c₂, c₁, ← mul_assoc]
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg' _)
      · nth_rw 1 [← mul_one (a:=supOfBasis K)]
        rw [mul_comm]
        apply mul_le_mul
        · apply le_max_left ..
        · apply le_max_right ..
        · apply (supOfBasis_nonneg _)
        · exact (le_trans zero_le_one (le_max_left ..))
    · apply Real.rpow_le_rpow (mul_nonneg (mul_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg' _))
        (norm_nonneg _))
      · rw [← mul_assoc, mul_assoc (_*_)]
        apply mul_le_mul_of_nonneg_left (asiegel_remark K a habs Apos)
          (mul_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg _))
      · exact div_nonneg (Nat.cast_nonneg' _) (sub_nonneg.2 (mod_cast hpq.le))
    · apply Real.rpow_nonneg
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg' _))
        (norm_nonneg _)
    · apply mul_nonneg (Nat.cast_nonneg' _)
      apply mul_nonneg (le_trans zero_le_one (le_max_left ..))
      apply (le_trans zero_le_one (le_max_left ..))
  · rw [mul_comm (q : ℝ) (c₁ K)]; rfl

include hpq h0p cardα cardβ ha habs in
/-- There exists a "small" non-zero algebraic integral solution of an
non-trivial underdetermined system of linear equations with algebraic integer coefficients. -/
theorem exists_ne_zero_int_vec_house_le :
    ∃ (ξ : β → 𝓞 K), ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
    ∀ l, house (ξ l).1 ≤ c₁ K * ((c₁ K * q * A) ^ ((p : ℝ) / (q - p))) := by
  classical
  let h := finrank ℚ K
  have hphqh : p * h < q * h := mul_lt_mul_of_pos_right hpq finrank_pos
  have h0ph : 0 < p * h := by rw [mul_pos_iff]; constructor; exact ⟨h0p, finrank_pos⟩
  have hfinp : Fintype.card (α × (K →+* ℂ)) = p * h := by
    rw [Fintype.card_prod, cardα, Embeddings.card]
  have hfinq : Fintype.card (β × (K →+* ℂ)) = q * h := by
    rw [Fintype.card_prod, cardβ, Embeddings.card]
  have ⟨x, hxl, hmulvec0, hxbound⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le' (asiegel K a)
      (by rwa [hfinp, hfinq]) (by rwa [hfinp]) (asiegel_ne_0 K a ha)
  simp only [hfinp, hfinq, Nat.cast_mul] at hmulvec0 hxbound
  rw [← sub_mul, mul_div_mul_right _ _ (mod_cast finrank_pos.ne')] at hxbound
  have Apos : 0 ≤ A := by
    have ⟨k⟩ := Fintype.card_pos_iff.1 (cardα ▸ h0p)
    have ⟨l⟩ := Fintype.card_pos_iff.1 (cardβ ▸ h0p.trans hpq)
    exact le_trans (house_nonneg _) (habs k l)
  use ξ K x, ξ_ne_0 K x hxl, ξ_mulVec_eq_0 K a x hxl hmulvec0,
    house_le_bound K a hpq x habs Apos hxbound

end

end GSHouse
end GSHouseSection

/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/


/-!
Some auxiliary lemmata covering the analytic part of the proof of the Gelfond–Schneider theorem.
-/

section

open Set AnalyticAt AnalyticOnNhd

universe u₁ u₂ u₃

variable {𝕜 E F G : Type*}

variable {f g : 𝕜 → E} {s : Set 𝕜} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {x : E}

open AnalyticAt Filter

lemma gs_analyticOrderAt_deriv_of_pos {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E} {z₀ : 𝕜}
  (hf : AnalyticAt 𝕜 f z₀) {n : ℕ} (horder : analyticOrderAt f z₀ = n) (hn : n ≠ 0)
   [CharZero 𝕜] :
    analyticOrderAt (deriv f) z₀ = (n - 1 : ℕ) := by
  have ⟨g, hg, hgneq0, hexp⟩ := analyticOrderAt_eq_natCast hf |>.mp horder
  refine analyticOrderAt_eq_natCast hf.deriv |>.mpr ⟨fun z ↦ n • g z + (z - z₀) • deriv g z, ?_⟩
  refine ⟨fun_add (by
    have := fun_const_smul (c := (n : 𝕜)) (f := g) (x := z₀) hg
    norm_cast at this
    ) (by fun_prop), by
      simp only [sub_self, zero_smul, add_zero]
      have Hnx {x : E} (hn : (n : 𝕜) ≠ 0) (hx : x ≠ 0) : n • x ≠ 0 := by
        intro h
        apply hx
        have : x = (1 / (n : 𝕜)) • ((n : 𝕜) • x) := by rw [← smul_assoc]; aesop
        norm_cast at this
        rw [this, h]
        simp
      apply Hnx
      · intros H
        have := ringChar.dvd H
        simp only [ringChar.eq_zero, zero_dvd_iff] at this
        grind
      · exact hgneq0
    , ?_⟩
  apply eventually_iff_exists_mem.mpr
  have ⟨Ug, hU, hUf⟩ := eventually_iff_exists_mem.mp hexp
  have ⟨Ur, hgz, hgN⟩ := exists_mem_nhds_analyticOnNhd hg
  refine ⟨interior (Ug ∩ Ur), by simp_all, fun z Hz ↦ ?_⟩
  trans deriv (fun z ↦ (z - z₀) ^ n • g z) z
  · rw [EventuallyEq.deriv_eq <| eventually_iff_exists_mem.mpr ?_]
    exact ⟨_, isOpen_interior.mem_nhds Hz, (hUf · <| interior_subset · |>.left)⟩
  have := interior_subset Hz |>.right
  rw [ smul_add, deriv_fun_smul (by simp_all) (differentiableAt <| by aesop)]
  simp only [differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_sub,
    deriv_fun_pow, deriv_fun_sub, deriv_id'', deriv_const', ← mul_smul, ← pow_succ]
  have : n - 1 + 1 = n := by lia
  rw [this]
  have : (1 : 𝕜) - 0 = 1 := by aesop
  rw [this]
  rw [add_comm, mul_one]
  simp_all only [ne_eq, interior_inter, mem_inter_iff, sub_zero, add_left_inj]
  obtain ⟨left, right⟩ := Hz
  have : n • g z = (n : 𝕜) • g z := by norm_cast
  rw [this]
  rw [← mul_smul]
  rw [mul_comm]


lemma Complex.analyticOrderAt_iterated_deriv {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E} {z₀ : 𝕜}
  (hf : AnalyticAt 𝕜 f z₀) (k n : ℕ) [CharZero 𝕜] :
  n = analyticOrderAt f z₀ → n ≠ 0 → k ≤ n → analyticOrderAt (deriv^[k] f) z₀ = (n - k : ℕ) := by
  induction k generalizing n with
  | zero => exact fun Hn Hpos Hk ↦ Hn.symm
  | succ n' hk =>
    intro Hn Hpos Hk
    rw [Function.iterate_succ']
    apply gs_analyticOrderAt_deriv_of_pos (iterated_deriv hf _) (hk _ Hn Hpos <| by lia) (by lia)

lemma gs_analyticOrderAt_deriv_eq_top_iff_of_eq_zero (z₀ : ℂ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀)
    (hzero : f z₀ = 0) : analyticOrderAt (deriv f) z₀ = ⊤ ↔ analyticOrderAt f z₀ = ⊤ := by
  repeat rw [analyticOrderAt_eq_top, Metric.eventually_nhds_iff_ball]
  have ⟨r₁, hr₁, hB⟩ := exists_ball_analyticOnNhd hf
  refine ⟨fun ⟨r₂, hr₂, hball⟩ ↦ ?_, fun ⟨r₂, hr₂, hball⟩ ↦ ?_⟩
  · refine ⟨_, lt_min hr₁ hr₂, Metric.isOpen_ball.eqOn_of_deriv_eq ?_ ?_ ?_ ?_ ?_ hzero⟩
    · exact (Metric.isConnected_ball <| by grind).isPreconnected
    · intro x hx
      exact (hB x <| Metric.ball_subset_ball (min_le_left ..) hx).differentiableWithinAt
    · exact differentiableOn_const 0
    · intro x hx
      simpa using hball x <| Metric.ball_subset_ball (min_le_right r₁ r₂) hx
    · simpa using lt_min hr₁ hr₂
  · refine ⟨_, lt_min hr₁ hr₂, fun x hx ↦ ?_⟩
    rw [← derivWithin_of_mem_nhds <| Metric.isOpen_ball.mem_nhds hx]
    trans derivWithin 0 (Metric.ball z₀ (min r₁ r₂)) x
    · refine Filter.EventuallyEq.derivWithin_eq_of_nhds <| Filter.eventually_iff_exists_mem.mpr ?_
      refine ⟨_, Metric.isOpen_ball.mem_nhds hx, fun z hz ↦ hball z ?_⟩
      exact Metric.ball_subset_ball (min_le_right r₁ r₂) hz
    simp

lemma analyticOrderAt_eq_succ_iff_deriv_order_eq_pred {z₀ : ℂ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f z₀)
    {n : ℕ} (hzero : f z₀ = 0) (horder : analyticOrderAt (deriv f) z₀ = n) :
    analyticOrderAt f z₀ = n + 1 := by
  cases Hn' : analyticOrderAt f z₀ with
  | top => grind [ENat.coe_ne_top, gs_analyticOrderAt_deriv_eq_top_iff_of_eq_zero]
  | coe n' =>
    cases n' with
    | zero => exact hf.analyticOrderAt_eq_zero.mp Hn' hzero |>.elim
    | succ n'' =>
      have := horder ▸ gs_analyticOrderAt_deriv_of_pos hf Hn'
      norm_cast at this ⊢
      have hchar : ringChar ℂ = 0 := by aesop
      aesop

lemma iterated_deriv_mul_pow_sub_of_analytic (r : ℕ) (z₀ : ℂ) {R R₁ : ℂ → ℂ}
    (hf1 : ∀ z : ℂ, AnalyticAt ℂ R₁ z) (hR₁ : ∀ z, R z = (z - z₀)^r * R₁ z) :
    ∀ k ≤ r, ∃ R₂ : ℂ → ℂ, (∀ z : ℂ, AnalyticAt ℂ R₂ z) ∧ ∀ z, deriv^[k] R z =
    (z - z₀) ^ (r - k) * (r.factorial / (r - k).factorial * R₁ z + (z - z₀) * R₂ z) := by
  intros k hkr
  induction k generalizing r with
  | zero =>
    refine ⟨0, ?_⟩
    · simp only [Function.iterate_zero, id_eq, tsub_zero, Pi.zero_apply, mul_zero, add_zero]
      refine ⟨fun z ↦ Differentiable.analyticAt (differentiable_zero) z, fun z ↦ ?_⟩
      · rw [hR₁ z, mul_eq_mul_left_iff, pow_eq_zero_iff', div_self
        (h:= mod_cast Nat.factorial_ne_zero r)]; grind
  | succ k IH =>
    obtain ⟨R₂, hR₂, hR1⟩ := IH r hR₁ (by linarith)
    refine ⟨fun z ↦ (↑(r - k) * R₂ z +
         (↑r.factorial / ↑(r - k).factorial * deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z))), ?_⟩
    · refine ⟨fun z ↦ by fun_prop, fun z ↦ ?_⟩
      · calc _ = deriv (deriv^[k] R) z := ?_
             _ = ↑(r - k) * (z - z₀) ^ (r - k - 1) * (↑r.factorial / ↑(r - k).factorial *
                 R₁ z + (z - z₀) * R₂ z) + (z - z₀) ^ (r - k) * (↑r.factorial / ↑(r - k).factorial *
                 deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z)) := ?_
             _ = 1 * ((z - z₀) ^ (r - (k + 1)) *(↑r.factorial / ↑(r - k).factorial * R₁ z)) +
                 ↑(r - k - 1) * ((z - z₀) ^ (r - (k + 1)) *
                 (↑r.factorial / ↑(r - k).factorial * R₁ z)) +
                 ↑(r - k) * (z - z₀) ^ (r - (k + 1)) * ((z - z₀) * R₂ z) +
                 (z - z₀) ^ (r - k) * (↑r.factorial / ↑(r - k).factorial *
                 deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z)) := ?_
             _ = (z - z₀) ^ (r - (k + 1)) * (↑r.factorial / ↑(r - (k + 1)).factorial *
                 R₁ z + (z - z₀) *(fun z ↦ ↑(r - k) * R₂ z + (↑r.factorial / ↑(r - k).factorial *
                 deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z))) z) := ?_
        · symm
          have : deriv^[k] (deriv R) z = deriv^[k+1] R z := by
            rw [Function.iterate_succ, Function.comp_apply]
          induction k generalizing r with
            | zero => aesop
            | succ k IH =>
              rw [Function.iterate_succ, Function.comp_apply] at IH ⊢
              rw [← iteratedDeriv_eq_iterate] at this ⊢
              rw [← iteratedDeriv_succ, this]
        · conv => enter [1, 1]; ext z; rw [hR1 z];; simp (disch := fun_prop)
        · rw [mul_add, Nat.sub_sub r k 1, ← add_mul, mul_assoc]; congr; norm_cast; grind [mul_assoc]
        · simp only [one_mul, ← mul_assoc]; nth_rw 5 [mul_comm]; simp only [← add_assoc, mul_assoc]
          rw [← mul_add]; simp only [← mul_assoc]; nth_rw 6 [mul_comm]; nth_rw 7 [mul_comm];
          simp only [← mul_assoc]; nth_rw 7 [mul_comm]; simp only [mul_assoc, ← mul_add]
          have : (z - z₀) ^ (r - k) = (z - z₀) ^ (r - (k + 1)) * (z - z₀) ^ 1 := by
            rw [← pow_add]; congr; grind
          rw [this, mul_assoc, ← mul_add, pow_one, mul_eq_mul_left_iff]; left;
          nth_rw 1 [← mul_assoc, ← add_mul, ← one_mul (a := (r.factorial / (r - k).factorial : ℂ))]
          nth_rw 1 [← add_mul]; rw [add_assoc]; simp only [mul_assoc]; rw [← mul_add];
          nth_rw 2 [add_comm]; norm_cast; simp only [← mul_assoc, mul_div]
          have HR : ↑(r - (k + 1) + 1) = ↑(r - k) := by grind
          simp only [Nat.sub_sub r k 1, HR, add_assoc]; congr 1; simp only [mul_eq_mul_right_iff]
          left; nth_rw 2 [← Nat.mul_factorial_pred (hn := by grind)]; rw [Nat.sub_sub r k 1]
          ring_nf; nth_rw 2 [mul_comm]; nth_rw 3 [mul_comm]
          rw [Nat.cast_mul, mul_inv_rev, ← mul_assoc, mul_eq_mul_right_iff, inv_eq_zero,
            Nat.cast_eq_zero, mul_assoc, mul_inv_cancel₀ (h := by simp; grind)]
          grind

lemma gs_analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero {z₀ : ℂ} (n : ℕ) :
  ∀ (f : ℂ → ℂ) (_ : AnalyticAt ℂ f z₀),
    ((∀ k < n, deriv^[k] f z₀ = 0) ∧ deriv^[n] f z₀ ≠ 0) ↔ analyticOrderAt f z₀ = n := by
  induction n with
  | zero =>
    simp only [ne_eq, not_lt_zero', IsEmpty.forall_iff, implies_true, true_and, CharP.cast_eq_zero]
    exact fun f hf ↦ (AnalyticAt.analyticOrderAt_eq_zero hf).symm
  | succ n IH =>
    refine fun f hf ↦ ⟨fun ⟨hz, hnz⟩ ↦ ?_, ?_⟩
    · have IH' := IH (deriv f) (AnalyticAt.deriv hf)
      · exact analyticOrderAt_eq_succ_iff_deriv_order_eq_pred hf (hz 0 (by grind))
          (by simpa using ((IH').1 ⟨fun k hk => hz (k + 1) (Nat.succ_lt_succ hk), hnz⟩))
    · refine fun ho ↦ ⟨fun k hk ↦ (analyticOrderAt_ne_zero.mp ?_).2, ?_⟩
      · grind only [(Complex.analyticOrderAt_iterated_deriv (f:=f) hf k (n := (n + 1))
          ho.symm (by grind) hk.le), Nat.cast_ne_zero]
      · have := Complex.analyticOrderAt_iterated_deriv (f := f) hf (n + 1) (n := n + 1)
          ho.symm (by grind) (by grind)
        grind only [AnalyticAt.analyticOrderAt_eq_zero (hf := iterated_deriv hf (n + 1))]

lemma analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (n : ℕ) : analyticOrderAt f z₀ = n → (∀ k < n, deriv^[k] f z₀ = 0) ∧ (deriv^[n] f z₀ ≠ 0) :=
  fun h ↦ (gs_analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero n (f := f) hf).mpr h

lemma le_analyticOrderAt_iff_iteratedDeriv_eq_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (n : ℕ) (ho : analyticOrderAt f z₀ ≠ ⊤) :
    (∀ k < n, (deriv^[k] f) z₀ = 0) → n ≤ analyticOrderAt f z₀ := by
  intro hkn
  obtain ⟨m, Hm⟩ := ENat.ne_top_iff_exists (n := analyticOrderAt f z₀).mp ho
  rw [← Hm, ENat.coe_le_coe]
  by_contra! h
  exact ((gs_analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (n := m) f hf).mpr (Hm.symm)).2 (hkn m h)


/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/



/-!
# Hilbert's Seventh Problem (Gelfond–Schneider Theorem)
The goal of this file is to formalize a proof of the **Gelfond–Schneider Theorem**, which solves
Hilbert’s Seventh Problem: namely, that for algebraic numbers `α ≠ 0, 1` and irrational algebraic
`β`, the number `α ^ β` is transcendental.

## Main results
* `gelfondSchneider`: If `α` and `β` are algebraic, `α ≠ 0`, `α ≠ 1`, and `β` is irrational, then
  `α ^ β` is transcendental.

## Implementation details
We follow the proof in Keng’s *Introduction to Number Theory*, Chapter 17, Section 5, p.488 - 493.

The argument proceeds by contradiction. The core of the proof is an auxiliary function lemma, where
we construct a nonzero integer linear combination of exponential functions that vanishes to high
order at several algebraic points.

This specific file handles the foundational algebraic setup:
1. Constructing a common number field `K` of degree `h` containing `α, β, γ`.
2. Defining the structural parameters `m = 2h + 2` and `n = q^2 / (2m)`.
3. Establishing the common denominator scaling factor `c₁` such that `c₁α`, `c₁β`, and `c₁γ`
   are all algebraic integers in `K`.
4. Formulating the homogeneous linear system matrix `A` with scaled entries residing strictly
   in the ring of integers `𝓞 K`, ready for Siegel's Lemma.

## References
Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter XII (§13).
A. O. Gelfond (1934), *Sur le septième Problème de Hilbert
T. Schneider (1935), *Transzendenzuntersuchungen periodischer Funktionen*
-/

section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

/-!
Suppose that `α, β, γ` lie in an algebraic field `K` with degree `h`.
-/

lemma isNumberField_adjoin_of_isAlgebraic (α β γ : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
    (hγ : IsAlgebraic ℚ γ) : NumberField (adjoin ℚ {α, β, γ}) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := finiteDimensional_adjoin fun _ hx ↦ by
    rcases hx with rfl | rfl | rfl
    exacts [isAlgebraic_iff_isIntegral.1 hα, isAlgebraic_iff_isIntegral.1 hβ,
      isAlgebraic_iff_isIntegral.1 hγ]

lemma exists_common_field_of_isAlgebraic (α β γ : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
    (hγ : IsAlgebraic ℚ γ) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (σ : K →+* ℂ)
    (_ : DecidableEq (K →+* ℂ)), ∃ (α' β' γ' : K), α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  refine ⟨adjoin ℚ {α, β, γ}, ?_⟩
  let σ : ↥(adjoin ℚ {α, β, γ}) →+* ℂ :=
    { toFun := fun x ↦ x.1, map_one' := rfl, map_mul' := fun _ _ ↦ rfl,
      map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  refine ⟨inferInstance, isNumberField_adjoin_of_isAlgebraic α β γ hα hβ hγ, σ,
    Classical.typeDecidableEq _, ⟨⟨α, ?_⟩, ⟨β, ?_⟩, ⟨γ, ?_⟩, ?_⟩⟩
  · apply subset_adjoin
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
  · apply subset_adjoin
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · apply subset_adjoin
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  · dsimp [σ]
    exact ⟨rfl, ⟨rfl, rfl⟩⟩

variable {K} [Field K] [NumberField K]

lemma exists_int_smul_isIntegral {K : Type*} [Field K] [NumberField K] (α : K) :
    ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ (k • α) := by
  obtain ⟨y, hy, hf⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  refine ⟨y, hy, hf α (mem_singleton_self _)⟩

/-- A choice of a non-zero integer `c` such that `c • α` is an algebraic integer.
The existence of such an integer is guaranteed for any algebraic number. -/
def c₀ {K : Type*} [Field K] [NumberField K] (α : K) : {c : ℤ // c ≠ 0 ∧ IsIntegral ℤ (c • α)} :=
  ⟨(exists_int_smul_isIntegral α).choose, (exists_int_smul_isIntegral α).choose_spec⟩

/-- An abbreviation for the explicit integer value extracted from `c₀ α`. -/
abbrev c₀Coeff {K : Type*} [Field K] [NumberField K] (α : K) : ℤ := (c₀ α : ℤ)

lemma c₀Coeff_ne_zero (α : K) : c₀Coeff α ≠ 0 := (c₀ α).2.1

/-!
Let `α` and `β` be algebraic numbers with `α ≠ 0, 1` and `β` irrational. We prove that `αᵇ` is
transcendental by contradiction. Suppose `γ = αᵇ = e^(β log α)` is also algebraic.
-/

/-- This structure encapsulates all the foundational data and hypotheses for the proof
of the Gelfond-Schneider theorem. It binds the complex numbers to their algebraic
counterparts in a common number field. -/
structure Setup where
  /-- The base of the exponentiation, assumed to be an algebraic complex number. -/
  α : ℂ
  /-- The exponent, assumed to be an irrational algebraic complex number. -/
  β : ℂ
  /-- A common abstract type representing the number field containing the preimages
  of `α`, `β`, and `α ^ β`. -/
  K : Type
  [isField : Field K]
  [isNumberField : NumberField K]
  /-- A fixed ring homomorphism embedding the abstract number field `K` into `ℂ`. -/
  σ : K →+* ℂ
  /-- The algebraic preimage of `α` in the number field `K`. -/
  α' : K
  /-- The algebraic preimage of `β` in the number field `K`. -/
  β' : K
  /-- The algebraic preimage of the assumed-algebraic `α ^ β` in the number field `K`. -/
  γ' : K
  hirr : ∀ i j : ℤ, β ≠ i / j
  htriv : α ≠ 0 ∧ α ≠ 1
  hα : IsAlgebraic ℚ α
  hβ : IsAlgebraic ℚ β
  habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ'
  /-- A decidable equality instance for the complex embeddings of `K`. -/
  hd : DecidableEq (K →+* ℂ)

namespace Setup

attribute [instance] isField isNumberField

variable (h7 : Setup)

open Setup

lemma alpha_gamma_pow_beta_ne_zero : h7.α ^ h7.β ≠ 0 :=
  fun H ↦ h7.htriv.1 ((cpow_eq_zero_iff h7.α h7.β).mp H).1

lemma beta_ne_zero : h7.β ≠ 0 :=
  fun H ↦ h7.hirr 0 1 (by simpa [div_one] using H)

lemma alpha'_beta'_gamma'_ne_zero : h7.α' ≠ 0 ∧ h7.β' ≠ 0 ∧ h7.γ' ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro H
  · exact h7.htriv.1 (by simp [h7.habc.1, H, map_zero h7.σ])
  · exact h7.beta_ne_zero (by simp [h7.habc.2.1, H, map_zero h7.σ])
  · exact h7.alpha_gamma_pow_beta_ne_zero (by simp [h7.habc.2.2, H, map_zero h7.σ])

lemma alpha'_ne_one : h7.α' ≠ 1 := fun h ↦
  h7.htriv.2 <| by simpa [h7.habc.1, map_one] using congrArg h7.σ h

lemma beta'_ne_zero : h7.β' ≠ 0 := h7.alpha'_beta'_gamma'_ne_zero.2.1

open Complex

lemma log_α_ne_zero : log h7.α ≠ 0 :=
  mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2

/-- c₁ is a positive integer such that c₁ • α', c₁ • β', c₁ • γ' are algebraic integers -/
def c₁ : ℤ := abs (c₀ h7.α' * c₀ h7.β' * c₀ h7.γ')

lemma one_le_c₁ : 1 ≤ h7.c₁ := by
  simpa [c₁] using Int.one_le_abs <| mul_ne_zero (mul_ne_zero (c₀Coeff_ne_zero h7.α')
    (c₀Coeff_ne_zero h7.β')) (c₀Coeff_ne_zero h7.γ')

lemma one_le_abs_c₁ : 1 ≤ |↑h7.c₁| := Int.one_le_abs (Ne.symm (Int.ne_of_lt h7.one_le_c₁))

lemma IsIntegral_assoc (K : Type) [Field K] {x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
    IsIntegral ℤ ((x * y * z : ℤ) • α) := by
  simpa [Int.cast_mul, zsmul_eq_mul, mul_assoc] using IsIntegral.smul (x * y) ha

lemma isIntegral_c₁α : IsIntegral ℤ (h7.c₁ • h7.α') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.γ') (y := c₀Coeff h7.β') h7.K (c₀Coeff h7.α') h7.α'
    ((c₀ h7.α').2.2)
  conv => enter [2]; rw [c₁, mul_comm, mul_comm (c₀Coeff h7.α') (c₀Coeff h7.β'), ← mul_assoc]
  rcases abs_choice (c₀Coeff h7.γ' * c₀Coeff h7.β' * c₀Coeff h7.α') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁β : IsIntegral ℤ (h7.c₁ • h7.β') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.γ') (y := c₀Coeff h7.α') h7.K (c₀Coeff h7.β') h7.β'
    ((c₀ h7.β').2.2)
  rw [c₁, mul_comm, ← mul_assoc]
  rcases abs_choice (c₀Coeff h7.γ' * c₀Coeff h7.α' * c₀Coeff h7.β') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁γ : IsIntegral ℤ (h7.c₁ • h7.γ') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.α') (y := c₀Coeff h7.β') h7.K (c₀Coeff h7.γ') h7.γ'
    ((c₀ h7.γ').2.2)
  rw [c₁]
  rcases abs_choice (c₀Coeff h7.α' * c₀Coeff h7.β' * c₀Coeff h7.γ') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

/-!
Let `m = 2h + 2`, and `n = q^ 2 / (2 * h7.m)`, where $q^2 = t $ is a square of a natural number
and is a multiple of $2m.$  -/

/-- The finrank of the field extension `h7.K` -/
def h : ℕ := Module.finrank ℚ h7.K

/-- A parameter `m` dependent on the degree `h = [K : ℚ]`. -/
def m : ℕ := 2 * h7.h + 2

lemma one_le_m : 1 ≤ h7.m := Nat.succ_le_succ (Nat.zero_le (2 * h7.h + 1))

variable (q : ℕ) (hq0 : 0 < q)

/-- A target bound parameter `n` dependent on a free parameter `q`. -/
def n : ℕ := q ^ 2 / (2 * h7.m)

variable (u : Fin (h7.m * h7.n q)) (t : Fin (q * q))

-- `a, b, k, l` are values that depend on the context variables `t` and `u`.

/-- A variable `a` that satisfies `1 ≤ a ≤ q`. -/
def a : ℕ := (finProdFinEquiv.symm.toFun t).1 + 1

/-- A variable `b` that satisfies `1 ≤ b ≤ q`. -/
def b : ℕ := (finProdFinEquiv.symm.toFun t).2 + 1

/-- Also, let `ρ₁, ρ₂, …, ρₜ` represent the `t` numbers
  `(a + bβ) log α,  1 ≤ a ≤ q, 1 ≤ b ≤ q.` -/
def ρ : ℂ := (a q t + (b q t • h7.β)) * Complex.log h7.α

/-!
We introduce the integral function
  `R(x) = η₁ e^(ρ₁ x) + … + ηₜ e^(ρₜ x)`
where the coefficients `η₁, …, ηₜ` are determined by the following conditions.
The function `R` is defined in the next file.

We solve the system of `mn` homogeneous linear equations
  `(log α)⁻ᵏ R⁽ᵏ⁾(l) = 0,  0 ≤ k ≤ n - 1, 1 ≤ l ≤ m`
in the `t = 2mn` unknowns `η₁, …, ηₜ`. It follows from
`GSHouse.exists_ne_zero_int_vec_house_le` that there is a non-trivial set of integer
solutions `η₁, …, η₂` in `K`.
-/

/-!
The coefficients are in `K` and
  `(log α)⁻ᵏ ((a + bβ) log α)ᵏ e^(l(a + bβ) log α) = (a + bβ)ᵏ αᵃˡ γᵇˡ`
for `1 ≤ l ≤ m, 1 ≤ a, b ≤ q, 0 ≤ k ≤ n - 1`.-/

/-- A variable `k` that satisfies 0 ≤ k ≤ n - 1 -/
def k : ℕ := (finProdFinEquiv.symm.toFun u).2

/-- A variable `l` that satisfies 1 ≤ l ≤ m -/
def l : ℕ := (finProdFinEquiv.symm.toFun u).1 + 1

/-- The core algebraic coefficient appearing in the evaluation of the `k`-th derivative
of the auxiliary function at point `l`. Evaluates to `(a + bβ')^k * α'^(al) * γ'^(bl)`. -/
abbrev systemCoeffs : h7.K :=
  (a q t + b q t • h7.β') ^ (h7.k q u) * h7.α' ^ (a q t * h7.l q u) * h7.γ' ^ (b q t * h7.l q u)

variable (h2mq : 2 * h7.m ∣ q ^ 2)

include hq0 h2mq in
lemma one_le_n : 1 ≤ h7.n q := by
  simp [n, (Nat.one_le_div_iff (by positivity [h7.one_le_m])).2
  (Nat.le_of_dvd (Nat.pow_pos hq0) h2mq)]

/-!
Let `c₁, c₂, …` be natural numbers independent of `n`. There exists `c₁` such that
`c₁ α, c₁ β, c₁ γ` are integers in `K`.
-/

/-- A combined integer scaling factor `c₁^(n-1 + 2mq)` applied to the linear system to clear
all denominators and ensure the resulting matrix entries are algebraic integers. -/
abbrev c_coeffs (q : ℕ) := h7.c₁ ^ (h7.n q - 1) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)

/-- An unscaled sub-component of the matrix coefficients, used to establish intermediate
integrality bounds during the construction of the auxiliary function. -/
abbrev c_coeffs0 (q : ℕ) (u : Fin (h7.m * h7.n q)) (t : Fin (q * q)) :=
  h7.c₁ ^ (h7.k q u : ℕ) * h7.c₁ ^ (a q t * h7.l q u) * h7.c₁ ^ (b q t * h7.l q u)

lemma IsIntegral.Cast (K : Type) [Field K] (a : ℤ) : IsIntegral ℤ (a : K) :=
  map_isIntegral_int (algebraMap ℤ K) (Algebra.IsIntegral.isIntegral _)

lemma isIntegral_c₁_pow_smul_pow (u : h7.K) (n k a l : ℕ) (hnk : a * l ≤ n * k)
    (H : IsIntegral ℤ (↑h7.c₁ * u)) : IsIntegral ℤ (h7.c₁ ^ (n * k) • u ^ (a * l)) := by
  rw [zsmul_eq_mul, Int.cast_pow, ← Nat.sub_add_cancel hnk, pow_add, mul_assoc, ← mul_pow]
  exact IsIntegral.mul (IsIntegral.pow (IsIntegral.Cast h7.K h7.c₁) _) (IsIntegral.pow H _)

lemma IsIntegral.Nat (K : Type) [Field K] (a : ℕ) : IsIntegral ℤ (a : K) := by
  have : (a : K) = ((a : ℤ) : K) := by simp only [Int.cast_natCast]
  rw [this]; apply IsIntegral.Cast

lemma isIntegral_c₁_pow_smul_α'_pow : IsIntegral ℤ
    (h7.c₁ ^ (a q t * h7.l q u) • (h7.α' ^ (a q t * h7.l q u))) := by
  apply h7.isIntegral_c₁_pow_smul_pow h7.α' (a q t) (h7.l q u) (a q t) (h7.l q u) (by rfl)
    (by grind [h7.isIntegral_c₁α])

lemma isIntegral_c₁_pow_smul_γ'_pow : IsIntegral ℤ (h7.c₁ ^ (b q t * h7.l q u) •
    (h7.γ'^ (b q t * (h7.l q u)))) := by
  apply h7.isIntegral_c₁_pow_smul_pow h7.γ' (b q t) (h7.l q u) (b q t) (h7.l q u) (by rfl)
    (by grind [h7.isIntegral_c₁γ])

lemma isIntegral_c₁_pow_smul_α'_pow' :
    IsIntegral ℤ (h7.c₁^(h7.m * q) • (h7.α' ^ (a q t * h7.l q u))) :=
    h7.isIntegral_c₁_pow_smul_pow h7.α' h7.m q (a q t) (h7.l q u)
  (by simpa [mul_comm, a, b, l] using Nat.mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt)
       (((finProdFinEquiv.symm.toFun u).1).isLt)) <| by grind [h7.isIntegral_c₁α]

lemma isIntegral_c₁_pow_smul_γ'_pow' :
    IsIntegral ℤ (h7.c₁ ^ (h7.m * q) • (h7.γ'^ (b q t * h7.l q u))) :=
    h7.isIntegral_c₁_pow_smul_pow h7.γ' h7.m q (b q t) (h7.l q u)
  (by simpa [mul_comm, a, b, l] using Nat.mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt)
       (((finProdFinEquiv.symm.toFun u).1).isLt)) <| by grind [h7.isIntegral_c₁γ]

lemma c_coeffs_neq_zero : h7.c_coeffs q ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁)))
  (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁))))
  (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁)))

lemma isIntegral_c₁_pow_smul_add_smul_pow (n : ℕ) (k : ℕ) (hkn : k ≤ n - 1) (a : ℕ) (b : ℕ) :
    IsIntegral ℤ (h7.c₁ ^ (n - 1) • (↑a + ↑b • h7.β') ^ k) := by
  rw [zsmul_eq_mul, Int.cast_pow, ← Nat.sub_add_cancel hkn, pow_add, mul_assoc, ← mul_pow, mul_add]
  refine IsIntegral.mul (IsIntegral.pow (IsIntegral.Cast _ _) _)
    (IsIntegral.pow (IsIntegral.add ?_ ?_) _)
  · exact IsIntegral.mul (IsIntegral.Cast _ _) (IsIntegral.Nat _ _)
  · rw [nsmul_eq_mul, ← mul_assoc, mul_comm (h7.c₁ : h7.K), mul_assoc]
    exact IsIntegral.mul (IsIntegral.Nat _ _) (by grind [h7.isIntegral_c₁β])

/-!
Multiplying the system by
`c₁^(n-1) c₁^(mq) c₁^ (mq) = c₁^(n-1+2mq) ≤ (c₂^n)` ensures the coefficients are integers in `K`. -/

lemma zsmul_mul_mul_distrib {K : Type*} [Field K] (a b c : ℤ) (x y z : K) :
    ((a * b) * c) • ((x * y) * z) = a • x * b • y * c • z := by
  simp [zsmul_eq_mul]; ring

open Nat in
lemma c₁IsInt : IsIntegral ℤ (h7.c_coeffs q • h7.systemCoeffs q u t) := by
  rw [zsmul_mul_mul_distrib, mul_assoc]
  refine IsIntegral.mul ?_
    (IsIntegral.mul (h7.isIntegral_c₁_pow_smul_α'_pow' q u t)
    (h7.isIntegral_c₁_pow_smul_γ'_pow' q u t))
  · exact h7.isIntegral_c₁_pow_smul_add_smul_pow (h7.n q) (h7.k q u)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).2.isLt) (a q t) (b q t)

/-- The matrix representing the homogeneous linear system of `mn` equations in `q^2` unknowns.
Its entries are scaled to strictly reside in the ring of integers `𝓞 K`. -/
def A : Matrix (Fin (h7.m * h7.n q)) (Fin (q * q)) (𝓞 h7.K) :=
  fun i j ↦ RingOfIntegers.restrict _ (fun _ ↦ (h7.c₁IsInt q i j)) ℤ

lemma c₁_ne_zero : h7.c₁ ≠ 0 := Ne.symm (Int.ne_of_lt h7.one_le_c₁)

lemma c₁α_ne_zero : h7.c₁ • h7.α' ≠ 0 := by
  simpa using ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), (h7.alpha'_beta'_gamma'_ne_zero).1⟩

lemma c₁γ_ne_zero : h7.c₁ • h7.γ' ≠ 0 := by
  simpa using ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), (h7.alpha'_beta'_gamma'_ne_zero).2.2⟩

lemma house_bound_c₁α :
    house (h7.c₁ • h7.α') ^ (a q t * h7.l q u) ≤ house (h7.c₁ • h7.α') ^ (h7.m * q) := by
  refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨one_le_house_of_isIntegral
    (h7.isIntegral_c₁α) h7.c₁α_ne_zero, ?_⟩)
  simpa [mul_comm, a, b, l] using mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt)
    (((finProdFinEquiv.symm.toFun u).1).isLt) (Nat.zero_le _) (Nat.zero_le _)

lemma isInt_β_bound : IsIntegral ℤ (h7.c₁ • (↑q + q • h7.β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (IsIntegral.add ((IsIntegral.Cast h7.K h7.c₁).mul (IsIntegral.Nat h7.K q))
    ((IsIntegral.Nat h7.K q).mul h7.isIntegral_c₁β))

lemma isInt_β_bound_low (q : ℕ) (t : Fin (q * q)) :
    IsIntegral ℤ (h7.c₁ • (↑(a q t) + b q t • h7.β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_add,
  mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm] using
  (IsIntegral.add
    ((IsIntegral.Cast h7.K h7.c₁).mul (IsIntegral.Nat h7.K (a q t)))
    ((IsIntegral.Nat h7.K (b q t)).mul h7.isIntegral_c₁β))

lemma β'_ne_zero (y : ℕ) : (↑↑(a q t) + (↑(b q t)) • h7.β') ^ y ≠ 0 := fun H ↦
  h7.hirr (-(a q t : ℤ)) (b q t) <| by
    have hEq : (a q t : ℂ) + b q t * h7.β = 0 := by
      simpa [nsmul_eq_mul, map_add, map_mul, ← h7.habc.2.1] using
        congrArg h7.σ (eq_zero_of_pow_eq_zero H)
    push_cast
    exact eq_div_iff_mul_eq (by unfold b; norm_cast) |>.mpr (by grind)

include hq0 in
lemma b_sum_ne_zero : (↑q : h7.K) + q • h7.β' ≠ 0 := fun H ↦
  h7.hirr (-1) 1 <| by
    have hEq : (q : ℂ) + q * h7.β = 0 := by
      simpa [nsmul_eq_mul, ← h7.habc.2.1] using congrArg h7.σ H
    have hqC : (q : ℂ) ≠ 0 := mod_cast Nat.ne_zero_of_lt hq0
    norm_num
    exact mul_left_cancel₀ hqC (by linear_combination hEq)

lemma bound_c₁β (q : ℕ) (hq0 : 0 < q) : 1 ≤ house ((h7.c₁ • (q + q • h7.β'))) := by
  apply one_le_house_of_isIntegral (h7.isInt_β_bound q)
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), h7.b_sum_ne_zero q hq0⟩

lemma one_le_house_c₁γ : 1 ≤ house (h7.c₁ • h7.γ') := by
  apply one_le_house_of_isIntegral h7.isIntegral_c₁γ
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), (h7.alpha'_beta'_gamma'_ne_zero).2.2⟩

/-- A large integer constant independent of `n` and `q`, used as a foundational base
to bound the houses (maximum absolute values of conjugates) of the algebraic coefficients. -/
def c₂ : ℤ := (|h7.c₁| ^ (((1 + 2 * h7.m * (2 * h7.m))) + (1 + 2 * h7.m * (2 * h7.m))))

lemma one_le_c₂ : 1 ≤ h7.c₂ := by
  apply le_trans (Int.cast_one_le_of_pos (h7.one_le_abs_c₁))
  nth_rw 1 [← pow_one (a:= |h7.c₁|)]
  apply pow_le_pow_right₀ (h7.one_le_abs_c₁) (Nat.le_add_left 1
    ((1 + 2 * h7.m * (2 * h7.m)).add (Nat.add 1 (((2 * h7.m).mul
    (Nat.mul 2 (2 * h7.h + 1) + 1)).add (Nat.mul 2 (2 * h7.h + 1) + 1)))))

end Setup

end
end


/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/



/-!
# Gelfond-Schneider Theorem: Matrix Coefficient Bounds and Siegel's Lemma

This file is the second component in the formalization of the Gelfond–Schneider Theorem
  (Hilbert's Seventh Problem), establishing the transcendence of `α ^ β`.

## Main results
Following the construction of the algebraic setup and linear system matrix in `MainAlg.lean`,
this file establishes strict analytical bounds on the coefficients of the matrix `A` and
applies Siegel's Lemma to guarantee a small, non-trivial integer solution.

Specifically, we prove:
1. `house_matrixA_le`**: The maximum absolute value of the conjugates (the "house") of the
  entries of `A` is strictly bounded by `c₃^n * n^((n - 1) / 2)`.
2. `η`**: The existence of a non-trivial vector of algebraic integers `η₁ ... η_t` in the kernel
  of `A`.
3. `house_eta_le_c₄_pow`**: An explicit upper bound on the house of the solution vector `η`,
  showing `‖ηₖ‖ ≤ c₄ⁿ * n^((n + 1) / 2)`.

These bounded coefficients `η` will be used in subsequent files to explicitly construct the
auxiliary integer function `R(x)`.

## References
* Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter 17.9.
-/

section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q)) (t : Fin (q * q))
  (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup


/-!
In this file we bound the house of the coefficients of the auxiliary function `R`;
  `‖ηₖ‖ ≤ c₄ⁿ * n^((n - 1) / 2)`, for `1 ≤ k ≤ t`.
-/

open Real

/-- A real-valued bounding constant encompassing `c₂` and the houses of `α'`, `β'`, and `γ'`.
Used to establish a strict upper bound on the entries of the linear system matrix `A`. -/
def c₃ : ℝ := h7.c₂ * (1 + house h7.β') * Real.sqrt (2 * h7.m) *
  (max 1 (((house h7.α' ^ (2 * h7.m ^ 2)) * house h7.γ' ^(2 * h7.m ^ 2))))

lemma one_le_c₃ : 1 ≤ h7.c₃ := by
  simp only [c₃]
  refine one_le_mul_of_one_le_of_one_le ?_ (le_max_left 1 _)
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast h7.one_le_c₂)
      (le_add_of_nonneg_right (house_nonneg _))
  · rw [one_le_sqrt]
    have := h7.one_le_m
    exact_mod_cast (by omega : 1 ≤ 2 * h7.m)

lemma c₃_pow : h7.c₃ ^ ↑(h7.n q : ℝ) = h7.c₂ ^ ↑(h7.n q) * ((1 + house (h7.β')) ^ ↑(h7.n q)) *
    (Real.sqrt ((2 * h7.m)) ^ ↑(h7.n q)) * (max 1 ((house (h7.α') ^ (2 * h7.m ^ 2)) * house (h7.γ') ^
    (2*h7.m^ 2)))^ ↑(h7.n q) := by
  simp only [c₃, rpow_natCast]; rw [mul_pow, mul_pow, mul_pow]

include h2mq in
lemma q_sq_eq_two_mn : q ^ 2 = 2 * h7.m * h7.n q := Eq.symm (Nat.mul_div_cancel' h2mq)

include h2mq in
lemma q_sq_le_two_mn : q ^ 2 ≤ 2 * h7.m * h7.n q := by
  simpa using le_of_eq (h7.q_sq_eq_two_mn q h2mq)

include h2mq in
lemma q_eq_n_etc : q ^ (h7.n q - 1) ≤ (Real.sqrt (2 * h7.m) ^ (h7.n q - 1)) * (Real.sqrt (h7.n q)) ^
    (h7.n q - 1) := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ (h7.n q - 1)
  have hq : (q : ℝ) ≤ Real.sqrt (2 * h7.m * h7.n q) := by
    refine (le_sqrt (by positivity) (by positivity)).2 (mod_cast h7.q_sq_le_two_mn q h2mq)
  simpa [mul_assoc, sqrt_mul] using hq

include h2mq in
lemma q_le_two_mn : q ≤ 2 * h7.m * h7.n q :=
  le_trans (Nat.le_pow (Nat.zero_lt_two)) ((by simpa using le_of_eq (h7.q_sq_eq_two_mn q h2mq)))

include hq0 h2mq in
lemma m_mul_n_pos : 0 < h7.m * h7.n q :=
  Nat.mul_pos h7.one_le_m <| by simpa [n, Nat.div_pos_iff] using
    ⟨Nat.zero_lt_succ (2 * h7.h + 1), Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩

include h2mq hq0 in
lemma mul_div_sub_eq_one : ((h7.m : ℝ) * (h7.n q : ℝ) / (2 * (h7.m : ℝ) * (h7.n q : ℝ) -
    (h7.m * (h7.n q : ℝ))) : ℝ) = 1 := by
  have : 2 * (h7.m : ℝ) * (h7.n q : ℝ) - (h7.m : ℝ) * (h7.n q : ℝ) = (h7.m : ℝ) * (h7.n q : ℝ) :=
    by ring
  rw [this]
  exact div_self (by exact_mod_cast (h7.m_mul_n_pos q hq0 h2mq).ne')

include hq0 h2mq in
lemma mul_rpow_sub_one_div_two : (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2) =
    (h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) := by
  have h_exp : (((h7.n q : ℝ) + 1) / 2) = 1 + (((h7.n q : ℝ) - 1) / 2) := by ring
  rw [h_exp, Real.rpow_add (by
   norm_cast; refine Nat.ne_zero_iff_zero_lt.mp
     (Nat.ne_zero_of_lt (one_le_n h7 q hq0 h2mq))), Real.rpow_one]

include h2mq hq0 in
lemma abs_q_pow_mul_house_le_c₃_pow : |↑q| ^ (h7.n q - 1) * ((1 + house h7.β') ^ (h7.n q - 1) *
    (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) * house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))))) ≤
    (1 + house h7.β') ^ h7.n q * (√(2 * ↑h7.m) ^ h7.n q * (max 1 (house h7.α' ^ (2 * h7.m ^ 2) *
    house h7.γ' ^ (2 * h7.m ^ 2)) ^ h7.n q * √↑(h7.n q) ^ (↑(h7.n q : ℝ) - 1))) := by
  calc _ ≤ (Real.sqrt (2 * h7.m) ^ (h7.n q -1))* (Real.sqrt (h7.n q)) ^ ((h7.n q) -1) *
                 ((1 + house h7.β') ^ (h7.n q - 1) * (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
                 house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))))) := ?_
       _ ≤ (Real.sqrt (2 * h7.m) ^ (h7.n q -1)) * ((1 + house h7.β') ^ (h7.n q - 1) *
                 (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) * house h7.γ' ^
                 (h7.m * (2 * (h7.m * h7.n q))))) * Real.sqrt (h7.n q) ^ (((h7.n q) : ℝ) - 1) := ?_
       _ ≤ √(2 * ↑(h7.m)) ^ ((h7.n q)) * ((1 + house h7.β') ^ ((h7.n q)) * (house h7.α' ^
                 (h7.m * 2 * h7.m)) ^ (h7.n q) * (house h7.γ' ^ (h7.m * 2 * h7.m)) ^ (h7.n q)) *
                 (Real.sqrt (h7.n q )) ^ (((h7.n q) : ℝ)-1) := ?_
  · apply mul_le_mul (by simpa using (h7.q_eq_n_etc q h2mq)) (by rfl) (by positivity)
      (by positivity)
  · have hsqrt : (Real.sqrt (h7.n q) ^ (h7.n q - 1)) = (Real.sqrt (h7.n q) ^ ((h7.n q : ℝ) - 1)) := by
      simpa [(Nat.cast_sub (h7.one_le_n q hq0 h2mq))] using
        (rpow_natCast (x := Real.sqrt (h7.n q)) (n := h7.n q - 1)).symm
    refine le_of_eq ?_; simp [hsqrt]; ac_rfl
  · simp only [mul_assoc]
    apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨?_, by simp⟩)
      have hm1 : (1 : ℝ) ≤ (h7.m : ℝ) := by exact_mod_cast h7.one_le_m
      have : (1 : ℝ) ≤ (2 : ℝ) * (h7.m : ℝ) := by nlinarith
      simpa [Nat.cast_mul, Nat.cast_ofNat] using (one_le_sqrt).2 this
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl (by simp [NumberField.house_nonneg]))
      · apply mul_le_mul (by simp [pow_mul]) (by simp [pow_mul]) (by positivity)
                (pow_nonneg (pow_nonneg (house_nonneg _) _) _)
  · nth_rw 2 [← mul_assoc]
    rw [mul_comm  ((1 + house h7.β') ^ (h7.n q)) (((Real.sqrt ((2*h7.m)))) ^ (h7.n q))]
    simp only [mul_assoc]
    apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · refine pow_le_pow_left₀ (sqrt_nonneg _) (by rfl) (h7.n q)
    · apply mul_le_mul (by rfl) ?_ (by positivity) (by positivity)
      · simp only [← mul_assoc]
        apply mul_le_mul ?_ (by rfl) (by positivity) (by positivity)
        · rw [← mul_pow]
          refine pow_le_pow_left₀ (by positivity) ?_ (h7.n q)
          · have : ((h7.m * 2) * h7.m) = (2 * h7.m ^ 2) := by grind
            rw [this]; clear this
            calc _ ≤ house h7.α' ^ (2 * h7.m ^ 2) * house h7.γ' ^ (2 * h7.m ^ 2) := ?_
                 _ ≤ max 1 ((house h7.α' ^ (2 * h7.m ^ 2) * house h7.γ' ^ (2 * h7.m ^ 2))) := ?_
            · apply Preorder.le_refl
            · simp only [le_sup_right]

lemma c₁_pow_sub_one_mul_c₁_pow_mul_c₁_pow_eq :
    ((h7.c₁ : ℤ) ^ (h7.n q - 1) * (h7.c₁ : ℤ) ^ (h7.m * q) * (h7.c₁ : ℤ) ^ (h7.m * q)) =
    ((h7.c₁ : ℤ) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : ℤ) ^ (h7.m * q - a q t * h7.l q u) *
    (h7.c₁ : ℤ) ^ (h7.m * q - b q t * h7.l q u)) * ((h7.c₁ : ℤ) ^ h7.k q u *
    (h7.c₁ : ℤ) ^ (a q t * h7.l q u) * (h7.c₁ : ℤ) ^ (b q t * h7.l q u)) := by
  symm
  calc _ = ((h7.c₁ : ℤ) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : ℤ) ^ h7.k q u) *
          ((h7.c₁ : ℤ) ^ (h7.m * q - a q t * h7.l q u) * (h7.c₁ : ℤ) ^ (a q t * h7.l q u)) *
          ((h7.c₁ : ℤ) ^ (h7.m * q - b q t * h7.l q u) * (h7.c₁ : ℤ) ^ (b q t * h7.l q u)) := ?_
       _ = _ := ?_
  · ring
  · simp_rw [← pow_add]
    have intCast_k_le_intCast_n_sub_one : (h7.k q u : ℤ) ≤ (h7.n q - 1 : ℤ) := by
      have := (finProdFinEquiv.symm u).2.isLt
      aesop
    rw [Nat.sub_add_cancel (by grind), Nat.sub_add_cancel
       (by simpa [mul_comm, a, b, l] using (Nat.mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt)
         (((finProdFinEquiv.symm.toFun u).1).isLt))), Nat.sub_add_cancel (by simpa [mul_comm, a, b, l] using
        (Nat.mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt)
        (((finProdFinEquiv.symm.toFun u).1).isLt)))]

lemma house_add_mul_le :
    house (h7.c₁ • (↑(a q t) + b q t • h7.β')) ≤ (|h7.c₁| * |(q : ℤ)|) * (1 + house (h7.β')) := by
  calc _ ≤ house (h7.c₁ • ((a q t : ℤ) : h7.K)) + house (h7.c₁ • ((b q t : ℤ) • h7.β')) := ?_
       _ ≤ house (h7.c₁ : h7.K) * house ((a q t : ℤ) : h7.K) + house (h7.c₁ : h7.K) *
           house ((b q t : ℤ) • h7.β') := ?_
       _ ≤ house (h7.c₁ : h7.K) * house ((a q t : ℤ) : h7.K) + house (h7.c₁ : h7.K) *
           (house ((b q t : ℤ) : h7.K) * house ( h7.β')) := ?_
       _ = |h7.c₁| * |(a q t : ℤ)| + |h7.c₁| * |(b q t : ℤ)| * house (h7.β') := ?_
       _ ≤ |h7.c₁| * |(q : ℤ)| + |h7.c₁| * |(q : ℤ)| * house h7.β' := ?_
       _ = |h7.c₁| * |(q : ℤ)| * (1 + house h7.β') := ?_
  · norm_cast; rw [smul_add]; apply house_add_le
  · refine add_le_add (by grind [house_mul_le]) (by grind [house_mul_le])
  · refine add_le_add (by grind)
      (mul_le_mul (le_refl _) (by grind [house_mul_le]) (house_nonneg _) (house_nonneg _))
  · rw [house_intCast]; rw [house_intCast]; rw [house_intCast]; rw [mul_assoc]
  · refine add_le_add (mul_le_mul (le_refl _) (mod_cast ((finProdFinEquiv.symm.toFun t).1).isLt)
      (Int.cast_nonneg (Int.zero_le_ofNat (a q t))) (Int.cast_nonneg  (abs_nonneg (h7.c₁)))) ?_
    · rw [mul_assoc, mul_assoc]
      apply mul_le_mul (by rfl) ?_ (mul_nonneg (by positivity) (house_nonneg _)) (by simp)
      · apply mul_le_mul (mod_cast ((finProdFinEquiv.symm.toFun t).2).isLt) (le_refl _)
          (house_nonneg _) (by simp)
  · rw [mul_add]; simp only [Int.cast_abs, mul_one]

/-! Moreover, the absolute value of the conjugates of the various coefficients is at most
  `c₂^n (q + q * |β|) ^ (n - 1) * |α| ^ (m q) * |γ| ^ (m q) ≤ c₃^n * n^((n - 1) / 2)`.
-/
include hq0 h2mq in
lemma house_matrixA_le : house ((algebraMap (𝓞 h7.K) h7.K) ((h7.A q) u t)) ≤
    (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2))  := by
  simp only [A, systemCoeffs, RingOfIntegers.restrict, RingOfIntegers.map_mk]
  calc _ = house (((h7.c₁ ^ (h7.n q - 1 - h7.k q u) * h7.c₁ ^ (h7.m * q - a q t * h7.l q u) *
           h7.c₁ ^ (h7.m * q - b q t * h7.l q u)) • (h7.c₁ ^ h7.k q u * h7.c₁ ^ (a q t * h7.l q u) *
           h7.c₁ ^ (b q t * h7.l q u))) • ((↑(a q t) + b q t • h7.β') ^ h7.k q u * h7.α' ^
           (a q t * h7.l q u) * h7.γ' ^ (b q t * h7.l q u))) := ?_
       _ = house ((h7.c₁ ^ ((h7.n q - 1) - h7.k q u) * h7.c₁ ^ (h7.m * q - a q t * h7.l q u) *
           (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u)) • (((h7.c₁ : h7.K) ^ h7.k q u) *
           ((a q t : h7.K) + (b q t) * h7.β') ^ h7.k q u * ((h7.c₁ : h7.K) ^ (a q t * h7.l q u)) *
           h7.α' ^ (a q t * h7.l q u) * ((h7.c₁ : h7.K) ^ (b q t * h7.l q u)) *
           h7.γ' ^ (b q t * h7.l q u))) := ?_
       _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : h7.K) ^
           (h7.m * q - a q t * h7.l q u) * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u))) *
           house (h7.c₁ ^ (h7.k q u) • (↑(a q t) + (b q t) • h7.β') ^ (h7.k q u)) *
           house (h7.c₁ ^ (a q t * h7.l q u) • h7.α' ^ (a q t * h7.l q u)) *
           house (h7.c₁ ^ (b q t * h7.l q u) • h7.γ' ^ (b q t * h7.l q u)) := ?_
       _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : h7.K) ^
           (h7.m * q - a q t * h7.l q u) * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u))) *
           house (h7.c₁ • (↑(a q t) + (b q t) • h7.β')) ^ (h7.k q u) * house (h7.c₁ • h7.α') ^
           (a q t * h7.l q u) * house (h7.c₁ • h7.γ') ^ (b q t * h7.l q u) := ?_
       _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : h7.K) ^
           (h7.m * q - a q t * h7.l q u) * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u))) *
           house (h7.c₁ • (↑(a q t) + b q t • h7.β')) ^ (h7.n q - 1) *
           house (h7.c₁ • h7.α') ^ (h7.m * q) * house (h7.c₁ • h7.γ') ^ (h7.m * q) := ?_
       _ ≤ |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁) ^ (h7.m * q - a q t * h7.l q u) *
           (h7.c₁) ^ (h7.m * q - b q t * h7.l q u)))| * (|h7.c₁| *
           (|(q : ℤ)| * (1 + house (h7.β')))) ^ (h7.n q - 1) * (|h7.c₁| * house (h7.α')) ^
           (h7.m * (2 * (h7.m * h7.n q))) * (|h7.c₁| * house (h7.γ')) ^
           (h7.m * (2 * (h7.m * h7.n q))) := ?_
       _ = |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁) ^ (h7.m * q - a q t * h7.l q u) *
           (h7.c₁) ^ (h7.m * q - b q t * h7.l q u)))| * |h7.c₁ ^ (h7.n q - 1)| •
           (↑|↑q| * (1 + house h7.β')) ^ (h7.n q - 1) * |h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q)))| •
           house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) * |h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q)))|
           • house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
       _ ≤ |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁) ^ (h7.m * q - a q t * h7.l q u) *
           (h7.c₁) ^ (h7.m * q - b q t * h7.l q u)))| * ↑|h7.c₁| ^ ((h7.n q - 1) +
           (2 * h7.m * (2 * (h7.m * h7.n q)))) * (↑|↑q| ^ ((h7.n q ) - 1) * (1 + house h7.β') ^
           (h7.n q - 1) * house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
           house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
       _ = |(h7.c₁) ^ (h7.n q - 1 - h7.k q u)| * |(h7.c₁) ^ (h7.m * q - a q t * h7.l q u)| *
           |(h7.c₁) ^ (h7.m * q - b q t * h7.l q u)| * ↑|h7.c₁| ^ ((h7.n q - 1) +
           (2 * h7.m * (2 * (h7.m * h7.n q)))) * (↑|↑q| ^ ((h7.n q)- 1) * (1 + house h7.β')
           ^ (h7.n q - 1) * house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) * house h7.γ' ^
           (h7.m * (2 * (h7.m * h7.n q)))) := ?_
       _ = |(h7.c₁)| ^ (h7.n q - 1 - h7.k q u) * |(h7.c₁)| ^ (h7.m * q - a q t * h7.l q u) *
           |(h7.c₁)| ^ (h7.m * q - b q t * h7.l q u) * ↑|h7.c₁| ^ ((h7.n q - 1) +  (2 * h7.m *
           (2 * (h7.m * h7.n q)))) * (↑|↑q| ^ ((h7.n q) - 1) * (1 + house h7.β') ^ (h7.n q - 1) *
           house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
           house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
       _ ≤ ↑(h7.c₂) ^ (h7.n q) * (↑|↑q| ^ ((h7.n q ) - 1) * (1 + house h7.β') ^ (h7.n q - 1) *
           house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
           house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
       _ ≤ h7.c₃ ^ (h7.n q : ℝ) * ((Real.sqrt (h7.n q)) ^ ((h7.n q : ℝ)- 1)) := ?_
       _ ≤ (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2)) := ?_
  · unfold c_coeffs
    conv => enter [2, 1]; simp only [Int.zsmul_eq_mul];
    rw [← c₁_pow_sub_one_mul_c₁_pow_mul_c₁_pow_eq]
    rfl
  · rw [smul_assoc]; simp; grind
  · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow,mul_assoc]
    apply le_trans (house_mul_le _ _) (mul_le_mul (by rfl) ?_ (house_nonneg _) (house_nonneg _))
    · rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
      apply le_trans (house_mul_le _ _)
      rw [← mul_assoc]
      apply mul_le_mul (by grind [mul_assoc, house_mul_le]) (by rfl) (house_nonneg _)
        (mul_nonneg (house_nonneg _) (house_nonneg _))
  · simp only [mul_assoc]
    apply mul_le_mul (by rfl) ?_ (by positivity) (by positivity)
    · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, ← mul_pow]
      apply mul_le_mul (house_pow_le _ _) ?_ (by positivity) (by positivity)
      · apply mul_le_mul (house_pow_le _ _) (house_pow_le _ _) (house_nonneg _)
          (pow_nonneg (house_nonneg _) _)
  · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · apply mul_le_mul (by rfl) ?_ (by positivity) (house_nonneg _)
        · refine Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral (isInt_β_bound_low _ _ _) (fun H ↦ ?_), ?_⟩)
          · simp only [zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at H
            cases H with
            | inl hp => apply h7.c₁_ne_zero; exact hp
            | inr hq => apply h7.β'_ne_zero q t 1; rw [pow_one]; exact hq
          · refine (Nat.le_sub_iff_add_le' (h7.one_le_n q hq0 h2mq)).mpr ?_
            · rw [add_comm]; exact (finProdFinEquiv.symm.toFun u).2.isLt
      · apply Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral h7.isIntegral_c₁α h7.c₁α_ne_zero, ?_⟩)
        · rw [mul_comm h7.m q]
          apply mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt)
           (((finProdFinEquiv.symm.toFun u).1).isLt) (Nat.zero_le _) (Nat.zero_le _)
    · apply Bound.pow_le_pow_right_of_le_one_or_one_le
        (Or.inl ⟨one_le_house_of_isIntegral h7.isIntegral_c₁γ h7.c₁γ_ne_zero, ?_⟩)
      · rw [mul_comm h7.m q]
        apply (mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt)
          (((finProdFinEquiv.symm.toFun u).1).isLt) (Nat.zero_le _) (Nat.zero_le _))
  · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · rw [← house_intCast (K := h7.K)]; simp
        · refine pow_le_pow_left₀ (house_nonneg _) ?_ (h7.n q - 1)
          · rw [← mul_assoc]; apply h7.house_add_mul_le q t
      · calc _ ≤ house (h7.c₁ • h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
             _ ≤ (↑|h7.c₁| * house h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
        · refine Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral h7.isIntegral_c₁α h7.c₁α_ne_zero, ?_⟩)
          · apply mul_le_mul (by rfl) ?_ (by simp) (by simp)
            · exact (by have H := h7.q_le_two_mn q h2mq; rw [mul_assoc] at H; exact H )
        · refine pow_le_pow_left₀ (house_nonneg _) ?_ (h7.m * (2 * (h7.m * h7.n q)))
          · calc _ ≤ house (h7.c₁ : h7.K) * house (h7.α') := ?_
                 _ ≤ _ := ?_
            · grind [house_mul_le]
            · simp
    · calc _ ≤ house (h7.c₁ • h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
           _ ≤ (↑|h7.c₁| * house h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
      · refine Bound.pow_le_pow_right_of_le_one_or_one_le
          (Or.inl ⟨one_le_house_of_isIntegral h7.isIntegral_c₁γ h7.c₁γ_ne_zero, ?_⟩)
        · apply mul_le_mul (by rfl) (by grind [h7.q_le_two_mn q h2mq]) (by simp) (by simp)
      refine pow_le_pow_left₀ (house_nonneg _) ?_ (h7.m * (2 * (h7.m * h7.n q)))
      · calc _ ≤ house (h7.c₁ : h7.K)  * house (h7.γ') := ?_
             _ ≤ _ := ?_
        · grind [house_mul_le]
        · simp only [house_intCast, Int.cast_abs, le_refl]
  · rw [zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
        abs_pow, abs_pow]; congr; all_goals simp
  · have := zsmul_mul_mul_distrib |(h7.c₁ ^ (h7.n q - 1))|
         |(h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q))))|
         |(h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q))))| ((↑|↑q| * (1 + house (h7.β'))) ^ (h7.n q - 1))
         ((house h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))))
         ((house h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))))
    simp only [mul_assoc, zsmul_eq_mul] at *
    rw [← this, abs_pow, abs_pow, ← pow_add, ← pow_add]
    apply mul_le_mul (by simp) ?_ (by positivity) (by positivity)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · rw [← pow_add, ← pow_add, Eq.symm (Nat.two_mul (h7.m * (2 * (h7.m * h7.n q))))]
        simp only [Int.cast_pow, Int.cast_abs, le_refl]
      · rw [mul_pow]; simp only [mul_assoc]; simp only [Nat.abs_cast, le_refl]
  · simp only [← pow_add, ← pow_add, Int.cast_abs, Int.cast_pow, Nat.abs_cast, abs_pow,
      ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  · rw [abs_pow, abs_pow, abs_pow]; simp
  · apply mul_le_mul ?_ (by rfl) (by positivity) (?_)
    · rw [← pow_add, ← pow_add, ← pow_add, Int.cast_abs, c₂, Int.cast_pow, Int.cast_abs, ← pow_mul]
      refine pow_le_pow_right₀ (mod_cast h7.one_le_abs_c₁) ?_
      · simp only [add_mul, add_mul, one_mul, mul_assoc,
          (Nat.two_mul (h7.m * (2 * (h7.m * h7.n q)))), add_assoc]
        refine Nat.add_le_add ?_ (Nat.add_le_add ((Nat.sub_le _ _).trans <| by
          simpa [mul_assoc] using Nat.mul_le_mul_left h7.m (h7.q_le_two_mn q h2mq))
            (Nat.add_le_add ((Nat.sub_le _ _).trans <| by
          simpa [mul_assoc] using Nat.mul_le_mul_left h7.m (h7.q_le_two_mn q h2mq)) (by simp)))
        · grind
    · apply pow_nonneg; exact mod_cast (le_trans Int.one_nonneg (h7.one_le_c₂))
  · simp_rw [h7.c₃_pow q, mul_assoc]
    apply mul_le_mul (by rfl) (h7.abs_q_pow_mul_house_le_c₃_pow q hq0 h2mq) (by positivity) ?_
    · apply pow_nonneg; norm_cast; apply le_trans Int.one_nonneg (h7.one_le_c₂)
  · rw [le_iff_eq_or_lt]; left;
    have : Real.sqrt (h7.n q) ^ ((h7.n q : ℝ) - 1) = (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2) := by
      nth_rw 1 [sqrt_eq_rpow, ← rpow_mul, mul_comm, mul_div]
      · simp only [mul_one]
      · simp only [Nat.cast_nonneg]
    rw [← this]

open NumberField

include hq0 h2mq in
lemma hM_ne_zero : h7.A q ≠ 0 := by
  intro H
  let u : Fin _ := ⟨0, h7.m_mul_n_pos q hq0 h2mq⟩
  let t : Fin _ := ⟨0, mul_pos hq0 hq0⟩
  have H_eval : (h7.A q u t).val = 0 := by rw [H]; rfl
  simp only [A, RingOfIntegers.restrict, zsmul_eq_mul, Int.cast_mul, Int.cast_pow] at H_eval
  have hβ : (↑(a q t) + b q t • h7.β' : h7.K) ≠ 0 := fun h ↦ h7.β'_ne_zero q t 1 (by grind)
  revert H_eval
  simp [h7.c₁_ne_zero, h7.alpha'_beta'_gamma'_ne_zero.1, h7.alpha'_beta'_gamma'_ne_zero.2.2]
  grind

include hq0 h2mq in
lemma m_mul_n_lt_q_mul_q : h7.m * h7.n q < q * q :=
  lt_of_lt_of_eq (by grind [h7.m_mul_n_pos q hq0 h2mq]) <|
  (h7.q_sq_eq_two_mn q h2mq).symm.trans (pow_two q)

variable [DecidableEq (h7.K →+* ℂ)]

/-- A non-trivial integer vector (in `𝓞 K`) residing in the kernel of the matrix `A`.
Its existence is guaranteed by Siegel's lemma (`exists_ne_zero_int_vec_house_le`). -/
abbrev η : Fin (q * q) → 𝓞 h7.K := (GSHouse.exists_ne_zero_int_vec_house_le h7.K (h7.A q)
  (h7.hM_ne_zero q hq0 h2mq) (mul_pos (Nat.zero_lt_succ (2 * h7.h + 1))
  (h7.one_le_n q hq0 h2mq)) (h7.m_mul_n_lt_q_mul_q q hq0 h2mq) (Fintype.card_fin _)
  (fun u t ↦ h7.house_matrixA_le q hq0 u t h2mq) (Fintype.card_fin _)).choose

/-- A real-valued bounding constant used to bound the norm (house) of the
solution vector `η`. -/
def c₄ : ℝ := (max 1 ((GSHouse.c₁ h7.K) * GSHouse.c₁ h7.K * 2 * h7.m)) * h7.c₃

/-!
`‖ηₖ‖ ≤ c₄ⁿ * n^((n - 1) / 2)`, for `1 ≤ k ≤ t`.
-/
open house in
include hq0 h2mq in
lemma house_eta_le_c₄_pow : house (algebraMap (𝓞 h7.K) h7.K (h7.η q hq0 h2mq t)) ≤
    h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1)/2)) := by
  calc _ ≤ GSHouse.c₁ h7.K * (GSHouse.c₁ h7.K * ↑(q * q) *
           (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2))) ^
           ((h7.m * h7.n q : ℝ) / (↑(q * q : ℝ) - ↑(h7.m * h7.n q ))) := ?_
       _ = (GSHouse.c₁ h7.K * (GSHouse.c₁ h7.K * 2 * h7.m * (h7.c₃ ^ (h7.n q : ℝ)) * ((h7.n q : ℝ) *
           (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2)))) := ?_
       _ ≤ h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) : ℝ) := ?_
  · exact mod_cast ((GSHouse.exists_ne_zero_int_vec_house_le
    h7.K (h7.A q) (h7.hM_ne_zero q hq0 h2mq) (mul_pos (Nat.zero_lt_succ (2 * h7.h + 1))
    (h7.one_le_n q hq0 h2mq)) (h7.m_mul_n_lt_q_mul_q q hq0 h2mq) (Fintype.card_fin _)
    (fun u t ↦ h7.house_matrixA_le q hq0 u t h2mq) (Fintype.card_fin _)).choose_spec).2.2 t
  · have : (q * q : ℝ) = q^2 := mod_cast (pow_two ↑q).symm
    rw [← pow_two q, this, h7.q_sq_eq_two_mn q h2mq]
    have : (q ^ 2 : ℝ) = 2 * h7.m * h7.n q := mod_cast (h7.q_sq_eq_two_mn q h2mq)
    rw [this]
    have mul_div_sub_eq_one := h7.mul_div_sub_eq_one q hq0 h2mq
    nth_rw 2 [← Nat.cast_mul] at mul_div_sub_eq_one
    rw [mul_div_sub_eq_one, rpow_one, h7.mul_rpow_sub_one_div_two q hq0 h2mq, mul_eq_mul_left_iff]
    left
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    have one_le_house_c₁ : 1 ≤ GSHouse.c₁ h7.K := one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr
      (Module.finrank_pos)) (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))
    refine (mul_right_inj' (by grind)).mpr ?_
    · grind [h7.mul_rpow_sub_one_div_two q hq0 h2mq, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  · rw [h7.mul_rpow_sub_one_div_two q hq0 h2mq, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · rw [c₄, mul_rpow (le_of_lt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
        (le_of_lt (lt_of_lt_of_le (by norm_num) h7.one_le_c₃))]
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · have hn : (1 : ℝ) ≤ (h7.n q : ℝ) := mod_cast h7.one_le_n q hq0 h2mq
        have hpow : (max 1 (GSHouse.c₁ h7.K * GSHouse.c₁ h7.K * 2 * ↑h7.m) : ℝ) ≤
          (max 1 (GSHouse.c₁ h7.K * GSHouse.c₁ h7.K * 2 * ↑h7.m)) ^ (h7.n q : ℝ) := by
          simpa [Real.rpow_one] using (rpow_le_rpow_of_exponent_le (le_max_left (1 : ℝ) _) hn)
        exact (le_max_right (1 : ℝ) _).trans hpow
      · apply rpow_nonneg (le_trans zero_le_one h7.one_le_c₃)
    · apply rpow_nonneg; simp only [Nat.cast_nonneg]

end Setup

end
end


/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/



/-!
This PR is the third component in the formalization of the Gelfond-Schneider Theorem
(Hilbert's Seventh Problem). It connects the algebraically constructed auxiliary function `R(x)`
to its analytical properties, establishing the exact order of vanishing and the fundamental lower
bound on the norm of its non-zero derivative evaluation.

Following the argument in Loo-Keng Hua's "Introduction to Number Theory"
Chapter 17.9, equations (4) and (5)), we define the minimal non-vanishing derivative
order $r$ and scale the evaluation to an algebraic integer to compute its norm.
-/

section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
 (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

/-!
Since the numbers `ρ₁, ..., ρₜ` are distinct, the function `R(x)`
is not identically zero. For suppose otherwise, then on expanding the right
hand side of `R` we have `η₁ρ₁ + η₂ρ₂ᵏ + ... + ηₜρₜᵏ = 0`, a contradiction.
-/

lemma eq_iff_finProdFinEquiv_symm_ext (i j : Fin (q * q)) : i = j ↔
    (finProdFinEquiv.symm.1 i).1 = (finProdFinEquiv.symm.1 j).1 ∧
    ((finProdFinEquiv.symm.1 i).2 : Fin q) = (finProdFinEquiv.symm.1 j).2 := by
  rw [← Prod.ext_iff, Equiv.toFun_as_coe, EmbeddingLike.apply_eq_iff_eq]

namespace Setup

omit [DecidableEq (h7.K →+* ℂ)] in
lemma rho_injective (i j : Fin (q * q)) (hij : i ≠ j) : ρ h7 q i ≠ ρ h7 q j := by
  rw [ne_eq, eq_iff_finProdFinEquiv_symm_ext q, not_and'] at hij
  simp only [ρ, not_or, ne_eq, mul_eq_mul_right_iff, not_or]
  constructor
  · by_cases Heq : (finProdFinEquiv.symm.1 i).2 = (finProdFinEquiv.symm.1 j).2
    · unfold a b
      rw [Heq]
      intro H
      apply (hij Heq)
      simp only [Equiv.toFun_as_coe, nsmul_eq_mul, add_left_inj, Nat.cast_inj] at H
      exact Fin.eq_of_val_eq H
    · let i2 : ℕ := (finProdFinEquiv.symm.toFun i).2 + 1
      let j2 : ℕ := (finProdFinEquiv.symm.toFun j).2 + 1
      let i1 : ℕ := (finProdFinEquiv.symm.toFun i).1 + 1
      let j1 : ℕ := (finProdFinEquiv.symm.toFun j).1 + 1
      rw [← ne_eq]
      change i1 + i2 • h7.β ≠ j1 + j2 • h7.β
      intros H
      apply h7.hirr (i1 - j1) (j2 - i2)
      have : i1 + i2 • h7.β = j1 + j2 • h7.β ↔ (↑i1 - ↑j1) /(↑j2 - ↑i2 : ℂ) = h7.β := by
        calc _ ↔ ↑i1 - ↑j1 + ↑i2 • h7.β - ↑j2 • h7.β = 0 := ?_
             _ ↔ ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • h7.β = 0 := ?_
             _ ↔ ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • h7.β) := ?_
             _ ↔ ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • h7.β := ?_
             _ ↔ (↑i1 - ↑j1) /(↑j2 - ↑i2 : ℂ) = h7.β := ?_
        · grind
        · rw [sub_eq_add_neg]; simp only [nsmul_eq_mul]; rw [← neg_mul, add_assoc, ← add_mul]
          simp only [smul_eq_mul];rw [← sub_eq_add_neg]
        · rw [add_eq_zero_iff_eq_neg]
        · refine Eq.congr_right (?_); simp only [smul_eq_mul]; rw [← neg_mul];simp only [neg_sub]
        · rw [div_eq_iff, mul_comm,smul_eq_mul]
          intros HC
          apply (fun HC ↦ Heq (Fin.eq_of_val_eq (Nat.succ_inj.mp HC)))
          rw [sub_eq_zero] at HC; simp only [Nat.cast_inj] at HC; exact HC.symm
      rw [this] at H
      rw [H.symm]
      simp only [Int.cast_sub, Int.cast_natCast]
  · exact mt
      (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2

abbrev V := vandermonde (fun t ↦ h7.ρ q t)

omit [DecidableEq (h7.K →+* ℂ)] in
lemma vandermonde_det_ne_zero : det (h7.V q) ≠ 0 := by
  by_contra H
  rw [V, det_vandermonde_eq_zero_iff] at H
  obtain ⟨i, j, ⟨hij, hij'⟩⟩ := H
  apply h7.rho_injective q i j hij' hij

open Differentiable Complex

abbrev R : ℂ → ℂ := fun x ↦ ∑ t, (canonicalEmbedding h7.K)
  ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) h7.σ * exp (h7.ρ q t * x)

/-!
We introduce the integral function
  `R(x) = η₁ e^(ρ₁ x) + … + ηₜ e^(ρₜ x)` (2)
where the coefficients `η₁, …, ηₜ` are determined by the following conditions.


Thus, we see from (2) that

  `R(x) = a_{n,ℓ}(x - ℓ)ⁿ + a_{n+1,ℓ}(x - ℓ)ⁿ⁺¹ + ⋯,    1 ≤ ℓ ≤ m,` (3)

where `a_{n,ℓ}, a_{n+1,ℓ}, ...` are not all zero. Hence, there must be a natural
number `r` such that `R⁽ᵏ⁾(ℓ) = 0, 0 ≤ k ≤ r - 1, 1 ≤ ℓ ≤ m`. But for
`1 ≤ ℓ₀ ≤ m` we have `R⁽ʳ⁾(ℓ₀) ≠ 0` so that we see from (3) that `r ≥ n`.
-/

lemma cexp_mul (c x : ℂ) : deriv (fun x ↦ cexp (c * x)) x = c * cexp (c * x) := by
  rw [deriv_cexp (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp [deriv_const', deriv_id'', mul_comm]

def iteratedDeriv_R (k' : ℕ) : deriv^[k'] (fun x ↦ (h7.R q hq0 h2mq) x) =
    fun x ↦ ∑ t, (h7.σ ((h7.η q hq0 h2mq) t)) * exp (h7.ρ q t * x) * (h7.ρ q t)^k' := by
  induction k' with
  | zero => simp only [pow_zero, mul_one]; rfl
  | succ k hk =>
    rw [← iteratedDeriv_eq_iterate] at *
    simp only [iteratedDeriv_succ]
    conv => enter [1]; rw [hk]
    ext x
    rw [_root_.deriv, fderiv_fun_sum]
    · simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, fderiv_eq_smul_deriv,
      deriv_mul_const_field', deriv_const_mul_field', smul_eq_mul, one_mul]
      rw [Finset.sum_congr rfl]
      intros t ht
      · rw [mul_assoc, mul_assoc, mul_eq_mul_left_iff, map_eq_zero]; left
        rw [cexp_mul, mul_assoc, (pow_succ' (h7.ρ q t) k)]
        · rw [mul_comm, mul_assoc, mul_eq_mul_left_iff, Eq.symm (pow_succ' (h7.ρ q t) k)]; left; rfl
    · intros i hi
      apply mul (by fun_prop) (differentiable_const (h7.ρ q i ^ k))

lemma iteratedDeriv_R_eq_zero (hR : h7.R q hq0 h2mq = 0) (z : ℂ) (k' : ℕ) :
    deriv^[k'] (fun z ↦ h7.R q hq0 h2mq z) z = 0 := by
  rw [hR, ← iteratedDeriv_eq_iterate, iteratedDeriv]
  simp

lemma vecMul_V_eq_zero (hR : h7.R q hq0 h2mq = 0) :
    (h7.V q).vecMul (fun t ↦ h7.σ ((h7.η q hq0 h2mq) t)) = 0 := by
  ext k
  have hk : deriv^[k] (fun x ↦ h7.R q hq0 h2mq x) 0 = 0 :=
    h7.iteratedDeriv_R_eq_zero (hR := hR) _ _ _ _ _
  rw [h7.iteratedDeriv_R q hq0 h2mq k] at hk
  simpa [of_apply, Matrix.vecMul, dotProduct, V, mul_comm] using hk

lemma ηvec_eq_zero (hVecMulEq0 : (h7.V q).vecMul (fun t ↦ h7.σ ((h7.η q hq0 h2mq) t)) = 0) :
    (fun t ↦ h7.σ ((h7.η q hq0 h2mq) t )) = 0 := by
  apply eq_zero_of_vecMul_eq_zero
    (h7.vandermonde_det_ne_zero q) hVecMulEq0

lemma hbound_sigma : h7.η q hq0 h2mq ≠ 0 :=
  (GSHouse.exists_ne_zero_int_vec_house_le h7.K (h7.A q)
  (h7.hM_ne_zero q hq0 h2mq) (mul_pos (Nat.zero_lt_succ (2 * h7.h + 1))
  (h7.one_le_n q hq0 h2mq)) (h7.m_mul_n_lt_q_mul_q q hq0 h2mq) (Fintype.card_fin _)
  (fun u t ↦ h7.house_matrixA_le q hq0 u t h2mq) (Fintype.card_fin _)).choose_spec.1

lemma R_ne_zero : h7.R q hq0 h2mq ≠ 0 := by
  intro H
  have HC := ηvec_eq_zero h7 q hq0 h2mq (vecMul_V_eq_zero h7 q hq0 h2mq H)
  apply hbound_sigma h7 q hq0 h2mq
  ext t
  simpa [η, FaithfulSMul.algebraMap_eq_zero_iff] using congr_fun HC t

variable (hγ : h7.α ^ h7.β = h7.σ h7.γ')

omit [DecidableEq (h7.K →+* ℂ)] in
lemma systemCoeffs_map_eq_exp_mul :
  Complex.exp (h7.ρ q t * h7.l q u) * (h7.ρ q t ^ (h7.k q u : ℕ) *
  Complex.log h7.α ^ (-(h7.k q u) : ℤ)) = h7.σ (h7.systemCoeffs q u t) := by
  calc _ = cexp (h7.ρ q t * h7.l q u) * (((↑(a q t) + ↑(b q t) • h7.β) *
          Complex.log h7.α) ^ (h7.k q u : ℕ) * Complex.log h7.α ^ (-↑(h7.k q u) : ℤ)) := ?_
       _ = cexp (h7.ρ q t * h7.l q u) * ((↑(a q t) + ↑(b q t) • h7.β) ^ (h7.k q u : ℕ) *
          ((Complex.log h7.α) ^ (h7.k q u : ℕ) * Complex.log h7.α ^ (-(h7.k q u) : ℤ))) := ?_
       _ = cexp (h7.ρ q t * h7.l q u) * ((↑(a q t) + ↑(b q t) • h7.β) ^ (h7.k q u : ℕ)) := ?_
       _ = h7.σ (h7.systemCoeffs q u t) := ?_
  · nth_rw 2 [ρ]
  · rw [mul_pow, mul_assoc]
  ·  have h_log_ne : Complex.log h7.α ≠ 0 :=
      mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg Complex.exp h) h7.htriv.2
     aesop
  · rw [h7.habc.2.1, mul_comm, systemCoeffs, mul_assoc]
    simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul, mul_eq_mul_left_iff,
      pow_eq_zero_iff', ne_eq]; left
    rw [← h7.habc.1, ← h7.habc.2.2, ρ, ← cpow_nat_mul]
    have : h7.α ^ ((a q t * h7.l q u)) * h7.α ^ (↑(b q t * h7.l q u) * h7.β) =
           h7.α ^ ((a q t * h7.l q u) + (↑(b q t * h7.l q u) * h7.β)) := by
      rw [cpow_add _ _ h7.htriv.1]
      · rw [cpow_nat_mul]
        simp only [mul_eq_mul_right_iff, pow_eq_zero_iff', cpow_eq_zero_iff, ne_eq, mul_eq_zero,
          not_or]; left; rw [cpow_nat_mul, cpow_natCast]; exact pow_mul' h7.α (a q t) (h7.l q u)
    rw [this]; clear this
    · rw [cpow_def_of_ne_zero h7.htriv.1 _]
      · congr 1; rw [mul_rotate, mul_assoc]; simp only [nsmul_eq_mul, Nat.cast_mul]
        nth_rw 3 [mul_comm]; rw [mul_assoc]; grind

include hq0 h2mq in
lemma systemCoeffs_deriv :
    (Complex.log h7.α)^(-(h7.k q u) : ℤ) * deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u) =
    ∑ t, h7.σ ↑((h7.η q hq0 h2mq) t) * h7.σ (h7.systemCoeffs q u t) := by
  rw [iteratedDeriv_R, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  simp only [mul_eq_mul_left_iff, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := systemCoeffs_map_eq_exp_mul h7 q u t
  unfold l at this
  rw [mul_assoc]
  unfold l
  exact this

lemma coeffs_mulVec_A_eq : h7.σ (h7.c_coeffs q) * ((Complex.log h7.α)^ (-(h7.k q u) : ℤ) *
    deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u)) = h7.σ ((h7.A q *ᵥ (h7.η q hq0 h2mq)) u) := by
  rw [systemCoeffs_deriv h7 q hq0 u h2mq]
  unfold Matrix.mulVec dotProduct
  simp only [← map_mul, ← map_sum]
  congr 1
  rw [Finset.mul_sum]
  simp only [Int.cast_mul, Int.cast_pow, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intros x hx
  simp only [A, RingOfIntegers.restrict, zsmul_eq_mul, RingOfIntegers.map_mk]
  push_cast
  ring

lemma coeffs_mul_deriv_eq_zero : h7.σ (h7.c_coeffs q) * ((Complex.log h7.α)^ (-(h7.k q u) : ℤ) *
    deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u)) = 0 := by
  rw [coeffs_mulVec_A_eq]
  have hMt0 := (GSHouse.exists_ne_zero_int_vec_house_le h7.K (h7.A q)
    (hM_ne_zero h7 q hq0 h2mq) (mul_pos ((Nat.zero_lt_succ (2 * h7.h + 1)))
    (h7.one_le_n q hq0 h2mq)) (h7.m_mul_n_lt_q_mul_q q hq0 h2mq) (Fintype.card_fin _)
    (fun u t ↦ house_matrixA_le h7 q hq0 u t h2mq) (Fintype.card_fin _)).choose_spec.2.1
  simp [η, FaithfulSMul.algebraMap_eq_zero_iff]
  aesop

/-!After defining the auxiliary function R we consider the
first nonzero derivative at an integer ℓ₀.

  `(log α)⁻ʳ R⁽ʳ⁾(ℓ₀) = ρ`.

where r is the smallest integer such that `R⁽ʳ⁾(ℓ₀) ≠ 0`.-/

lemma exists_min_analyticOrderAt :
  let s : Finset (Fin (h7.m)) := Finset.univ
  ∃ l₀' ∈ s, (∃ y, (analyticOrderAt (h7.R q hq0 h2mq) (l₀' + 1)) = y ∧
  (∀ (l' : Fin (h7.m)), l' ∈ s → y ≤ (analyticOrderAt (h7.R q hq0 h2mq) (l' + 1)))) := by
  intro s
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image s
   (fun x ↦ analyticOrderAt (h7.R q hq0 h2mq) (x + 1))
   ⟨⟨0, Nat.zero_lt_succ (2 * h7.h + 1)⟩, Finset.mem_univ _⟩
  exact ⟨x, hx, _, rfl, hmin⟩

abbrev l₀' : Fin (h7.m) := (exists_min_analyticOrderAt h7 q hq0 h2mq).choose

abbrev l₀_prop := (exists_min_analyticOrderAt h7 q hq0 h2mq).choose_spec.2

abbrev r' := (l₀_prop h7 q hq0 h2mq).choose

lemma r'_spec :
    let s : Finset (Fin (h7.m)) := Finset.univ
    analyticOrderAt (h7.R q hq0 h2mq) ↑↑(h7.l₀' q hq0 h2mq + 1 : ℂ) =
    h7.r' q hq0 h2mq ∧ ∀ l' ∈ s, h7.r' q hq0 h2mq ≤ analyticOrderAt (h7.R q hq0 h2mq) (↑↑l' + 1) :=
  (h7.l₀_prop q hq0 h2mq).choose_spec

end Setup
end

end


/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/



/-! The goal of this file is to establish the critical lower bound for the proof of the
Gelfond-Schneider Theorem. Having constructed an auxiliary exponential polynomial
`R(x)` that vanishes to high order at specific points, we now isolate the first non-vanishing
derivative of `R(x)` and use its algebraic properties to bound it away from zero.

## Main Objective

To derive a contradiction, we need two opposing bounds on the size of the derivatives of `R(x)`.
This file is entirely dedicated to constructing the lower bound.
-/

section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
 (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup

lemma iteratedkDeriv_R_eq_zero (k : Fin (h7.n q)) (l' : Fin h7.m) :
    deriv^[k] (h7.R q hq0 h2mq) (l' + 1) = 0 := by
  have h1 := h7.coeffs_mul_deriv_eq_zero q hq0 (finProdFinEquiv ⟨l', k⟩) h2mq
  simp only [Setup.k, Setup.l, Equiv.toFun_as_coe, Equiv.symm_apply_apply,
    Int.cast_mul, Int.cast_pow, map_mul, map_pow, map_intCast, _root_.zpow_neg, zpow_natCast,
    Nat.cast_add, Nat.cast_one, ← mul_assoc] at h1
  refine (mul_eq_zero.mp h1).resolve_left (fun h_zero ↦ ?_)
  have h_log : Complex.log h7.α ≠ 0 := fun h ↦
    h7.htriv.2 (by simpa [exp_log h7.htriv.1] using congrArg exp h)
  simp only [mul_eq_zero, inv_eq_zero, pow_eq_zero_iff'] at h_zero
  revert h_zero
  simp [h7.c₁_ne_zero, h_log]

open AnalyticOnNhd

lemma order_neq_top : ∀ (l' : Fin (h7.m)), analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) ≠ ⊤ := by
  intros l' H
  rw [analyticOrderAt_eq_top_iff_eq_zero] at H
  · apply h7.R_ne_zero q hq0 h2mq (by aesop)
  fun_prop

lemma order_neq_top_min_one : ∀ z : ℂ, analyticOrderAt (h7.R q hq0 h2mq) z ≠ ⊤ := by
  intros l' H
  rw [analyticOrderAt_eq_top_iff_eq_zero] at H
  · apply h7.R_ne_zero
    · rw [funext_iff]
      intros z
      rw [funext_iff] at H
      apply H z
  intros z
  fun_prop

lemma exists_analyticOrderAt_R_eq_some (z : ℂ) :
    ∃ r, (analyticOrderAt (h7.R q hq0 h2mq) z) = some r := by
  have : (analyticOrderAt (h7.R q hq0 h2mq) z) ≠ ⊤ :=
    h7.order_neq_top_min_one q hq0 h2mq z
  revert this
  cases (analyticOrderAt (h7.R q hq0 h2mq) z) with
  | top => grind
  | coe => aesop

def R_order (z : ℂ) : ℕ := (exists_analyticOrderAt_R_eq_some h7 q hq0 h2mq z).choose

def R_order_prop {z : ℂ} := (exists_analyticOrderAt_R_eq_some h7 q hq0 h2mq z).choose_spec

lemma R_order_eq (z) : (analyticOrderAt (h7.R q hq0 h2mq) z) = h7.R_order q hq0 h2mq z :=
  (exists_analyticOrderAt_R_eq_some h7 q hq0 h2mq z).choose_spec

lemma r_exists : ∃ r, r' h7 q hq0 h2mq = some r := by
  have H := order_neq_top_min_one h7 q hq0 h2mq (l₀' h7 q hq0 h2mq + 1)
  have : r' h7 q hq0 h2mq ≠ ⊤ := by rw [(r'_spec h7 q hq0 h2mq).1] at H; exact H
  revert this
  cases r' h7 q hq0 h2mq with
  | top => grind
  | coe => aesop

def r := (r_exists h7 q hq0 h2mq).choose

abbrev r_spec : h7.r' q hq0 h2mq = ↑(h7.r q hq0 h2mq) :=
  (r_exists h7 q hq0 h2mq).choose_spec

abbrev r_prop :
  let s : Finset (Fin (h7.m)) := Finset.univ
  analyticOrderAt (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) = h7.r q hq0 h2mq ∧
  ∀ l' ∈ s, h7.r q hq0 h2mq ≤ analyticOrderAt (h7.R q hq0 h2mq) (↑↑l' + 1) := by
  intros s
  rw [← h7.r_spec q hq0 h2mq]
  apply h7.r'_spec q hq0 h2mq

lemma r_div_q_geq_0 : 0 ≤ (h7.r q hq0 h2mq) / q := by simp_all only [zero_le]


def cρ : ℤ := abs (h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁^(2*h7.m * q))

abbrev systemCoeffs_r : h7.K := (a q t + b q t • h7.β')^(h7.r q hq0 h2mq) *
 h7.α' ^(a q t * (h7.l₀' q hq0 h2mq + 1)) * h7.γ' ^(b q t * (h7.l₀' q hq0 h2mq + 1))

lemma systemCoeffs_ne_zero_r : h7.systemCoeffs_r q hq0 t h2mq ≠ 0 := by
  unfold systemCoeffs_r
  intros H
  simp only [mul_eq_zero, pow_eq_zero_iff'] at H
  cases H with
  | inl H1 =>
    cases H1 with
    | inl H1 =>
      rcases H1 with ⟨h1, h2⟩
      apply (h7.β'_ne_zero q t (h7.r q hq0 h2mq))
      rw [h1]
      simp only [pow_eq_zero_iff', ne_eq, true_and]
      exact h2
    | inr H2 => exact h7.alpha'_beta'_gamma'_ne_zero.1 H2.1
  | inr H2 =>
    exfalso
    exact h7.alpha'_beta'_gamma'_ne_zero.2.2 H2.1

def ρᵣ : ℂ := (Complex.log h7.α)^(-(h7.r q hq0 h2mq) : ℤ) *
  deriv^[h7.r q hq0 h2mq] (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1)

lemma systemCoeffs_map_eq_exp_mul_r :
  exp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) *
  h7.ρ q t ^ (h7.r q hq0 h2mq : ℕ) *
  Complex.log h7.α ^ (-(h7.r q hq0 h2mq) : ℤ) = h7.σ (h7.systemCoeffs_r q hq0 t h2mq) := by
    nth_rw 2 [ρ]
    rw [mul_pow, mul_assoc, mul_assoc]
    have hlog : Complex.log h7.α ≠ 0 := by
      intro h
      exact h7.htriv.2 (by simpa [Complex.exp_log h7.htriv.1] using congrArg Complex.exp h)
    have : Complex.log h7.α ^ (h7.r q hq0 h2mq : ℕ) *
      Complex.log h7.α ^ (-h7.r q hq0 h2mq : ℤ) = 1 := by
      simp [_root_.zpow_neg, zpow_natCast, hlog]
    rw [this]; clear this
    rw [mul_one]
    unfold systemCoeffs_r
    rw [mul_comm]
    change _ = h7.σ ((↑(a q t) + b q t • h7.β') ^ (h7.r q hq0 h2mq : ℕ)
      * (h7.α' ^ (a q t * (h7.l₀' q hq0 h2mq + 1))) * (h7.γ' ^ (b q t * (h7.l₀' q hq0 h2mq + 1))))
    rw [map_mul]
    rw [map_mul]
    nth_rw 1 [mul_assoc]
    have : h7.σ ((↑(a q t) + (b q t) • h7.β') ^ (h7.r q hq0 h2mq)) =
        (↑(a q t) + ↑(b q t) * h7.β) ^ ((h7.r q hq0 h2mq)) := by
      simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul]
      simp_all only [a, b]
      congr
      rw [h7.habc.2.1]
    rw [this]; clear this
    rw [map_pow, map_pow]
    have : (↑(a q t) + (b q t) • h7.β) ^
      (h7.r q hq0 h2mq) * cexp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) =
        (↑(a q t) + ↑(b q t) * h7.β)^(h7.r q hq0 h2mq) *
          cexp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) := by
      simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
        Fin.coe_modNat,
        Fin.coe_divNat, Nat.cast_add, Nat.cast_one, nsmul_eq_mul,b, a]
    rw [this]; clear this
    simp only [mul_eq_mul_left_iff, pow_eq_zero_iff']
    left
    rw [ρ]
    have : cexp (( ↑(a q t) + (b q t) • h7.β) * Complex.log h7.α * (h7.l₀' q hq0 h2mq + 1)
        ) =
        cexp ((↑(a q t) + ↑(b q t) • h7.β) * Complex.log h7.α * (h7.l₀' q hq0 h2mq +1)) := by
          aesop
    rw [this];clear this
    have : h7.σ h7.α' ^ ((a q t) * (h7.l₀' q hq0 h2mq + 1)) *
       h7.σ h7.γ' ^ ((b q t) * (h7.l₀' q hq0 h2mq + 1)) =
       h7.α ^ ((a q t) * (h7.l₀' q hq0 h2mq + 1)) *
       (h7.σ h7.γ')^ ((b q t) * (h7.l₀' q hq0 h2mq + 1)) := by
      simp only [mul_eq_mul_right_iff, pow_eq_zero_iff',
        map_eq_zero, ne_eq, mul_eq_zero, not_or]
      left
      congr
      rw [← h7.habc.1]
    rw [← h7.habc.1]
    have : h7.σ h7.γ' = h7.α^h7.β := by rw [h7.habc.2.2]
    rw [this]; clear this
    have : Complex.exp (Complex.log h7.α) = h7.α :=
      Complex.exp_log h7.htriv.1
    clear this
    rw [← cpow_nat_mul]
    have : cexp ((↑(a q t) + (b q t) • h7.β) *
      Complex.log h7.α * (h7.l₀' q hq0 h2mq +1)) =
        h7.α ^ ((a q t) * (h7.l₀' q hq0 h2mq + 1)) *
        h7.α ^ (↑((b q t) * (h7.l₀' q hq0 h2mq +1 )) * h7.β) ↔
      cexp ((↑(a q t) + (b q t) • h7.β) *
      Complex.log h7.α * (h7.l₀' q hq0 h2mq + 1)) =
        h7.α ^ (((a q t) * (h7.l₀' q hq0 h2mq +1)) +
         ((↑(b q t) * (h7.l₀' q hq0 h2mq + 1)) * h7.β)) := by
        rw [cpow_add]
        · simp only [nsmul_eq_mul, Nat.cast_mul]
          norm_cast
        exact h7.htriv.1
    rw [this]; clear this
    rw [cpow_def_of_ne_zero]
    · have hmul :
          Complex.log h7.α *
            (↑(a q t) * (h7.l₀' q hq0 h2mq + 1) +
              ((b q t) * (h7.l₀' q hq0 h2mq + 1)) * h7.β) =
            (↑(a q t) + (b q t) • h7.β) * Complex.log h7.α * (h7.l₀' q hq0 h2mq + 1) := by
        simp [nsmul_eq_mul]
        ring
      simp [hmul]
    · exact h7.htriv.1

def deriv_R_k_eval_at_l0' :
  deriv^[h7.r q hq0 h2mq] (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) =
  ∑ t, h7.σ ((h7.η q hq0 h2mq) t) *
  cexp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) * (h7.ρ q t) ^ (h7.r q hq0 h2mq) := by
  rw [iteratedDeriv_R]

lemma systemCoeffs_deriv_r :
   (Complex.log h7.α)^(-h7.r q hq0 h2mq : ℤ) * deriv^[h7.r q hq0 h2mq]
   (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) =
 ∑ t, h7.σ ↑((h7.η q hq0 h2mq) t) * h7.σ (h7.systemCoeffs_r q hq0 t h2mq) := by
  rw [h7.deriv_R_k_eval_at_l0' q hq0 h2mq, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  unfold η
  simp only [mul_eq_mul_left_iff, map_eq_zero,
    FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := systemCoeffs_map_eq_exp_mul_r h7 q hq0 t h2mq
  rw [← this]

def rho := ∑ t : Fin (q * q), (h7.η q hq0 h2mq t) * (h7.systemCoeffs_r q hq0 t h2mq)

def rho_eq_ρᵣ : h7.σ (rho h7 q hq0 h2mq) = ρᵣ h7 q hq0 h2mq := by
  unfold rho ρᵣ
  rw [systemCoeffs_deriv_r]
  simp only [map_sum, map_mul, nsmul_eq_mul, map_pow, map_add, map_natCast]

lemma cρ_ne_zero : h7.cρ q hq0 h2mq ≠ 0 := by
  apply abs_ne_zero.mpr <| mul_ne_zero _ _
  all_goals apply pow_ne_zero _ (h7.c₁_ne_zero)

/-!
This number lies in $K,$ and ${c_1}^{r+2mq}\rho$ is an integer in $K$
-/

lemma ρ_is_int :
  IsIntegral ℤ (h7.cρ q hq0 h2mq • rho h7 q hq0 h2mq) := by
  unfold rho cρ systemCoeffs_r
  have : h7.c₁ ^ (2 * h7.m * q) = h7.c₁ ^ (h7.m * q)
  * h7.c₁ ^ (h7.m * q) := by
      rw [← pow_add]; ring
  rw [this]
  rcases abs_choice (h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) with H1 | H2
  · rw [← mul_assoc, H1, Finset.smul_sum]
    apply IsIntegral.sum
    intros x hx
    rw [zsmul_eq_mul]
    nth_rw 1 [mul_comm]
    rw [mul_assoc]
    apply IsIntegral.mul
    · exact RingOfIntegers.isIntegral_coe ((h7.η q hq0 h2mq) x)
    · rw [mul_comm, ← zsmul_eq_mul]
      have triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
         ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
        simp only [zsmul_eq_mul, Int.cast_mul]; ring
      have := triple_comm h7.K
        (h7.c₁^(h7.r q hq0 h2mq) : ℤ)
        (h7.c₁^(h7.m * q) : ℤ)
        (h7.c₁^(h7.m * q) : ℤ)
        (((a q x : ℕ) + b q x • h7.β')^(h7.r q hq0 h2mq))
        (h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)))
        (h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))
      have : IsIntegral ℤ
         ((h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) •
        ((↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
          h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
          h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) =
       IsIntegral ℤ
         (h7.c₁ ^ (h7.r q hq0 h2mq) • (↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
          h7.c₁ ^ (h7.m * q) • h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
          h7.c₁ ^ (h7.m * q) • h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1))) := by
        rw [← this]
      simp_rw [this]
      apply IsIntegral.mul
      · refine IsIntegral.mul ?_ ?_
        · have hbase : IsIntegral ℤ (↑h7.c₁ * (↑(a q x) + b q x • h7.β')) := by
            rw [mul_add]
            refine (IsIntegral.add (R := ℤ) (A := h7.K) ?_ ?_)
            · simpa [mul_assoc, mul_comm, mul_left_comm] using
                (IsIntegral.mul (IsIntegral.Nat h7.K (a q x)) (IsIntegral.Cast h7.K h7.c₁))
            · simpa [zsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
                (IsIntegral.mul (IsIntegral.Nat h7.K (b q x)) h7.isIntegral_c₁β)
          simpa [Nat.mul_one] using
            (h7.isIntegral_c₁_pow_smul_pow
              (u := (↑(a q x) + b q x • h7.β'))
              (n := h7.r q hq0 h2mq) (k := 1) (a := h7.r q hq0 h2mq) (l := 1)
              (by simp) hbase)
        · refine h7.isIntegral_c₁_pow_smul_pow
            (u := h7.α') (n := h7.m) (k := q) (a := a q x) (l := h7.l₀' q hq0 h2mq + 1) ?_ ?_
          · rw [mul_comm]
            exact Nat.mul_le_mul (h7.l₀' q hq0 h2mq).isLt
              (finProdFinEquiv.symm.toFun x).1.isLt
          · simpa [zsmul_eq_mul] using h7.isIntegral_c₁α
      · refine h7.isIntegral_c₁_pow_smul_pow
          (u := h7.γ') (n := h7.m) (k := q) (a := b q x) (l := h7.l₀' q hq0 h2mq + 1) ?_ ?_
        · rw [mul_comm]
          exact Nat.mul_le_mul (h7.l₀' q hq0 h2mq).isLt
            (finProdFinEquiv.symm.toFun x).2.isLt
        · simpa [zsmul_eq_mul] using h7.isIntegral_c₁γ
  · rw [Finset.smul_sum]
    apply IsIntegral.sum
    intro x hx
    have hmul :
        IsIntegral ℤ
          (h7.c₁ ^ (h7.r q hq0 h2mq) • (↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
            h7.c₁ ^ (h7.m * q) • h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
            h7.c₁ ^ (h7.m * q) • h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1))) := by
      refine IsIntegral.mul ?_ ?_
      · refine IsIntegral.mul ?_ ?_
        · have hbase : IsIntegral ℤ (↑h7.c₁ * (↑(a q x) + b q x • h7.β')) := by
            rw [mul_add]
            refine IsIntegral.add (R := ℤ) (A := h7.K) ?_ ?_
            · simpa [mul_assoc, mul_comm, mul_left_comm] using
                (IsIntegral.mul (IsIntegral.Nat h7.K (a q x)) (IsIntegral.Cast h7.K h7.c₁))
            · simpa [zsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
                (IsIntegral.mul (IsIntegral.Nat h7.K (b q x)) h7.isIntegral_c₁β)
          simpa [Nat.mul_one] using
            (h7.isIntegral_c₁_pow_smul_pow
              (u := (↑(a q x) + b q x • h7.β'))
              (n := h7.r q hq0 h2mq) (k := 1) (a := h7.r q hq0 h2mq) (l := 1)
              (by simp) hbase)
        · refine h7.isIntegral_c₁_pow_smul_pow
            (u := h7.α') (n := h7.m) (k := q) (a := a q x) (l := h7.l₀' q hq0 h2mq + 1) ?_ ?_
          · rw [mul_comm]
            exact Nat.mul_le_mul (h7.l₀' q hq0 h2mq).isLt
              (finProdFinEquiv.symm.toFun x).1.isLt
          · simpa [zsmul_eq_mul] using h7.isIntegral_c₁α
      · refine h7.isIntegral_c₁_pow_smul_pow
          (u := h7.γ') (n := h7.m) (k := q) (a := b q x) (l := h7.l₀' q hq0 h2mq + 1) ?_ ?_
        · rw [mul_comm]
          exact Nat.mul_le_mul (h7.l₀' q hq0 h2mq).isLt
            (finProdFinEquiv.symm.toFun x).2.isLt
        · simpa [zsmul_eq_mul] using h7.isIntegral_c₁γ
    have hη : IsIntegral ℤ (↑((h7.η q hq0 h2mq) x) : h7.K) :=
      RingOfIntegers.isIntegral_coe ((h7.η q hq0 h2mq) x)
    have hnegScaled :
        IsIntegral ℤ
          ((↑(-(h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) : ℤ) : h7.K) *
            ((↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
              h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
              h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) := by
      have hscaled :
          IsIntegral ℤ
            ((↑(h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q) : ℤ) : h7.K) *
              ((↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
                h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
                h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) := by
        convert hmul using 1
        grind
      convert (IsIntegral.neg hscaled) using 1
      grind
    have habs :
        |h7.c₁ ^ (h7.r q hq0 h2mq) * (h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q))| =
          -(h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) := by
      simpa [mul_assoc] using H2
    rw [habs, zsmul_eq_mul]
    have hmulInt :
        IsIntegral ℤ
          (((↑(-(h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) : ℤ) : h7.K) *
              ((↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
                h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
                h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) *
            (↑((h7.η q hq0 h2mq) x) : h7.K)) := by
      exact IsIntegral.mul hnegScaled hη
    convert hmulInt using 1
    all_goals first | rfl | ring | simp only [mul_assoc, mul_comm, mul_left_comm]

def c1ρ : 𝓞 h7.K := RingOfIntegers.restrict _
  (fun _ => (ρ_is_int h7 q hq0 h2mq)) ℤ

lemma one_le_c1rho : 1 ≤ ↑(h7.cρ q hq0 h2mq) := by
  apply Int.one_le_abs
  by_contra H
  simp only [mul_eq_zero, pow_eq_zero_iff', ne_eq,
    OfNat.ofNat_ne_zero, false_or, not_or] at H
  cases H with
  | inl h1 => apply (h7.c₁_ne_zero); exact h1.1
  | inr h2 => apply (h7.c₁_ne_zero); exact h2.1

lemma one_le_norm_c1rho : 1 ≤ norm (h7.cρ q hq0 h2mq) := by
  have := one_le_c1rho h7 q hq0 h2mq
  have : |(h7.cρ q hq0 h2mq)| = ‖(h7.cρ q hq0 h2mq : ℤ)‖ := by
    simp only [Int.cast_abs]
    exact rfl
  rw [← this]
  simp only [Int.cast_abs, ge_iff_le]
  have := Int.one_le_abs (z := h7.cρ q hq0 h2mq)
  norm_cast
  apply this
  exact cρ_ne_zero h7 q hq0 h2mq

lemma zero_le_c1rho : 0 ≤ ↑(h7.cρ q hq0 h2mq) :=
  Int.le_of_lt (one_le_c1rho h7 q hq0 h2mq)

lemma cρ_le_abs_cρ :
    (h7.cρ q hq0 h2mq) ≤ abs (h7.cρ q hq0 h2mq):= le_abs_self _

lemma abs_cρ_le_norm_cρ :
    abs (h7.cρ q hq0 h2mq) ≤ norm (h7.cρ q hq0 h2mq) := by
  simp only [Int.cast_abs]
  rfl

lemma norm_cρ_le_house_cρ : norm (h7.cρ q hq0 h2mq) ≤
  house (h7.cρ q hq0 h2mq : h7.K) := by
  rw [house_intCast]
  simp only [Int.cast_abs]
  exact Preorder.le_refl ‖h7.cρ q hq0 h2mq‖

lemma norm_cρ_pos : 0 < ‖h7.cρ q hq0 h2mq‖ := by
  rw [norm_pos_iff]
  have := h7.cρ_ne_zero q hq0 h2mq
  unfold cρ at this
  exact this

lemma one_le_norm_cρ_pow : 1 ≤ ‖h7.cρ q hq0 h2mq‖ ^ Module.finrank ℚ h7.K := by
  rw [one_le_pow_iff_of_nonneg]
  · simpa using h7.one_le_norm_c1rho q hq0 h2mq
  · exact norm_nonneg _
  · exact Nat.ne_of_gt Module.finrank_pos

end Setup

end

end


/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/



section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
 (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

open Set AnalyticAt AnalyticOnNhd


namespace Setup

lemma exists_nonzero_iteratedFDeriv : deriv^[h7.r q hq0 h2mq]
 (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) ≠ 0 := by
  have Hrprop := (h7.r_prop q hq0 h2mq).1
  obtain ⟨l₀, y, r, h1, h2⟩ := (h7.exists_min_analyticOrderAt q hq0 h2mq)
  have hA1 : AnalyticAt ℂ (h7.R q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1) := by fun_prop
  grind [analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero hA1]

lemma ρᵣ_nonzero : ρᵣ h7 q hq0 h2mq ≠ 0 := by
  unfold ρᵣ
  simp only [_root_.zpow_neg, zpow_natCast, mul_eq_zero, inv_eq_zero,
    pow_eq_zero_iff', ne_eq, not_or, not_and, Decidable.not_not]
  refine ⟨fun hlog => ?_, h7.exists_nonzero_iteratedFDeriv q hq0 h2mq⟩
  · by_contra H
    have : Complex.log h7.α ≠ 0 :=
      mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2
    apply this; exact hlog

lemma rho_nonzero : rho h7 q hq0 h2mq ≠ 0 := by
  intros H
  apply_fun h7.σ at H
  rw [rho_eq_ρᵣ] at H
  simp only [map_zero] at H
  apply h7.ρᵣ_nonzero
  exact H

lemma norm_Algebra_norm_rho_nonzero :
  ‖(Algebra.norm ℚ) (rho h7 q hq0 h2mq)‖ ≠ 0 := by
  rw [norm_ne_zero_iff, Algebra.norm_ne_zero_iff]
  intros H
  apply_fun h7.σ at H
  rw [rho_eq_ρᵣ] at H
  simp only [map_zero] at H
  apply ρᵣ_nonzero h7 q hq0 h2mq
  exact H

lemma c1rho_neq_0 : h7.c1ρ q hq0 h2mq ≠ 0 := by
  intros H
  injection H with H1
  simp only [zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at H1
  cases H1 with
  | inl hp => apply cρ_ne_zero h7 q hq0 h2mq; exact hp
  | inr hq =>
    apply_fun h7.σ at hq
    rw [rho_eq_ρᵣ] at hq
    simp only [map_zero] at hq
    apply ρᵣ_nonzero h7 q hq0 h2mq
    exact hq

lemma house_geq_1 : 1 ≤ house (h7.c1ρ q hq0 h2mq : h7.K) := by
  apply one_le_house_of_isIntegral (RingOfIntegers.isIntegral_coe (h7.c1ρ q hq0 h2mq))
  simp only [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  rw [← ne_eq]
  exact c1rho_neq_0 h7 q hq0 h2mq

lemma eq5zero : 1 ≤ norm
    (Algebra.norm ℚ ((algebraMap (𝓞 h7.K) h7.K) (h7.c1ρ q hq0 h2mq))) := by
  have := ρ_is_int h7 q hq0 h2mq
  have := Algebra.isIntegral_norm ℚ this
  have H1 : 0 ≤ ‖(Algebra.norm ℤ) (h7.c1ρ q hq0 h2mq)‖ := by
    positivity
  have H2 : 0 ≠ ‖(Algebra.norm ℤ) (h7.c1ρ q hq0 h2mq)‖ := by
    have := c1rho_neq_0 h7 q hq0 h2mq
    symm
    intros H
    apply this
    rw [norm_eq_zero] at H
    simp only [Algebra.norm_eq_zero_iff] at H
    exact H
  have : 0 < ‖(Algebra.norm ℤ) (h7.c1ρ q hq0 h2mq)‖ := by
    exact lt_of_le_of_ne H1 H2
  rw [← Algebra.coe_norm_int] at *
  simp only [Int.norm_cast_rat, ge_iff_le] at *
  rw [← Int.norm_cast_real] at *
  simp only [Real.norm_eq_abs] at *
  norm_cast at *

def c₅ : ℝ := ((abs (h7.c₁) + 1) ^ (((↑(h7.h) * (1+4 * h7.m^2)))))

omit [DecidableEq (h7.K →+* ℂ)] in
lemma c5nonneg : 0 < h7.c₅ := by
    unfold c₅
    apply pow_pos
    simp only [Int.cast_abs]
    refine add_pos_of_nonneg_of_pos ?_ ?_
    · simp only [abs_nonneg]
    · simp only [zero_lt_one]

------
lemma order_geq_n_foo (l' : Fin (h7.m)) :
  (∀ k', k' < h7.n q → deriv^[k'] (h7.R q hq0 h2mq) (l' + 1) = 0)
   → h7.n q ≤ analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) := by
  intros H
  apply le_analyticOrderAt_iff_iteratedDeriv_eq_zero
  · fun_prop
  · apply order_neq_top h7 q hq0 h2mq l'
  exact H

lemma order_geq_n : ∀ l' : Fin (h7.m),
    h7.n q ≤ analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) := by
  intros l'
  apply order_geq_n_foo
  intros k hk
  have H := h7.iteratedkDeriv_R_eq_zero q hq0 h2mq ⟨k,hk⟩ l'
  rw [H]

lemma n_le_r : h7.n q ≤ h7.r q hq0 h2mq := by
  have := h7.r_prop q hq0 h2mq
  obtain ⟨hr,hprop⟩ := this
  have := h7.order_geq_n q hq0 h2mq (h7.l₀' q hq0 h2mq)
  have H : h7.n q ≤ (h7.r q hq0 h2mq : ℕ∞) → h7.n q ≤ h7.r q hq0 h2mq := by
    simp only [Nat.cast_le, imp_self]
  apply H
  rw [← hr]
  apply this

lemma r_ne_zero : h7.r q hq0 h2mq ≠ 0 := by
  have H := n_le_r h7 q hq0 h2mq
  have : 0 < h7.n q := by
    unfold n; simp only [Nat.div_pos_iff, Nat.ofNat_pos,
    mul_pos_iff_of_pos_left]
    refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩
  aesop

/-!so that

$$
|N(\rho)| > c_1^{-h(r+2mq)} > c_5^{-r}.
$$-/

lemma eq5 : h7.c₅ ^ (-(h7.r q hq0 h2mq) : ℝ) < norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := by
  simp only [Real.rpow_neg_natCast, _root_.zpow_neg, zpow_natCast]
  have h1 : 1 ≤ ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖ *
      ‖(Algebra.norm ℚ) (rho h7 q hq0 h2mq)‖ := by
    have := eq5zero h7 q hq0 h2mq
    unfold c1ρ at this
    unfold RingOfIntegers.restrict at this
    simp only [zsmul_eq_mul] at this
    simp only [RingOfIntegers.map_mk, map_mul, norm_mul] at this
    have H := Algebra.norm_algebraMap (S := h7.K) (h7.cρ q hq0 h2mq : ℚ)
    simp only [map_intCast] at H
    simp only [norm_pow, ge_iff_le]
    rw [H] at this
    simp only [norm_pow, Int.norm_cast_rat] at this
    exact this
  have h2 : ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖⁻¹
    ≤ norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := by
    have : 0 < ‖ (h7.cρ q hq0 h2mq)^ Module.finrank ℚ h7.K‖ := by
      rw [norm_pos_iff]
      simp only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not]
      intros H
      by_contra H1
      apply h7.cρ_ne_zero q hq0 h2mq
      exact H
    rw [← mul_le_mul_iff_right₀ this]
    · rw [mul_inv_cancel₀]
      · simp_all only [norm_pow]
      · simp only [norm_pow, ne_eq, pow_eq_zero_iff', norm_eq_zero,
          not_and, Decidable.not_not]
        intros H
        rw [H] at this
        simp only [norm_pow, norm_zero] at this
        rw [zero_pow] at this
        · by_contra H1
          simp_all only [norm_pow, lt_self_iff_false]
        · simp_all only [norm_pow]
          have : 0 < Module.finrank ℚ h7.K := by
            exact Module.finrank_pos
          simp_all only [norm_zero, ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [pow_zero, one_mul, zero_lt_one, lt_self_iff_false]
  calc _ = _ := ?_
       h7.c₅ ^ ((-h7.r q hq0 h2mq : ℤ)) <
        abs (h7.c₁)^ ((- h7.h : ℤ) * (h7.r q hq0 h2mq + 2 * h7.m * q) ) := ?_
       _ ≤ ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖⁻¹ := ?_
       _ ≤ norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := ?_
  · simp only [_root_.zpow_neg, zpow_natCast]
  · simp only [_root_.zpow_neg, zpow_natCast, neg_mul]
    rw [inv_lt_inv₀]
    · rw [mul_add]
      have : (h7.h : ℤ) * h7.r q hq0 h2mq + h7.h
      * (2 * h7.m * ↑q) = h7.h * h7.r q hq0 h2mq + h7.h * 2 * h7.m * ↑q := by
        rw [mul_assoc, mul_assoc, mul_assoc]
      rw [this]
      have : ((h7.h : ℤ) * h7.r q hq0 h2mq + ↑(h7.h) * 2 * ↑(h7.m) * ↑q)  =
         ((h7.h : ℤ) * (↑(h7.r q hq0 h2mq) + 2 * ↑(h7.m) * ↑q)) :=
         by ring
      rw [this]
      dsimp [c₅]
      norm_cast
      nth_rw 2 [pow_mul]
      have :  (((abs (h7.c₁) + 1) ^ h7.h) ^ (1 + 4 * h7.m ^ 2)) ^ h7.r q hq0 h2mq=
        ((abs (h7.c₁) + 1) ^ (h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq)) := by
          rw [pow_mul]
          rw [pow_mul]
      rw [this]; clear this
      calc _ ≤ abs (h7.c₁) ^ (h7.h * (h7.r q hq0 h2mq + 2 * h7.m * q^2)):= ?_
           _ ≤ abs (h7.c₁) ^ (h7.h * (h7.r q hq0 h2mq + 4 * h7.m ^ 2 * h7.n q)) := ?_
           _ ≤ abs (h7.c₁) ^( h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq) := ?_
           _ < (abs (h7.c₁) + 1) ^ (h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq) := ?_
      · refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ h7
        · simp only [mul_assoc]
          refine Nat.mul_le_mul (le_refl _) ?_
          · rw [q_sq_eq_two_mn h7 q h2mq]
            simp only [add_le_add_iff_left, Nat.ofNat_pos, mul_le_mul_iff_right₀]
            refine Nat.mul_le_mul (le_refl _) ?_
            · trans
              · have : q ≤ q^2 := by
                 refine Nat.le_pow ?_
                 simp only [Nat.ofNat_pos]
                apply this
              · rw [q_sq_eq_two_mn h7 q h2mq]
      · simp only [mul_assoc]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ h7
        · refine Nat.mul_le_mul (le_refl _) ?_
          · rw [q_sq_eq_two_mn h7 q h2mq]
            simp only [add_le_add_iff_left]
            have : 2 * (h7.m * (2 * h7.m * h7.n q))=
              4 * h7.m ^ 2 * h7.n q := by
              rw [mul_assoc, mul_assoc]
              ring
            rw [this]
            simp only [mul_assoc,le_refl]
      · rw [mul_add]
        rw [mul_add]
        rw [add_mul]
        simp only [mul_one]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ h7
        · simp only [add_le_add_iff_left]
          simp only [mul_assoc]
          refine Nat.mul_le_mul (le_refl _) ?_
          · simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
            refine Nat.mul_le_mul (le_refl _) ?_
            · exact n_le_r h7 q hq0 h2mq
      · refine pow_lt_pow_left₀ ?_ ?_ ?_
        · simp only [lt_add_iff_pos_right, zero_lt_one]
        · simp only [abs_nonneg]
        · intros H
          simp only [mul_eq_zero, Nat.add_eq_zero_iff,
            one_ne_zero, OfNat.ofNat_ne_zero,
            Nat.pow_eq_zero, ne_eq, not_false_eq_true, and_true,
             false_or, false_and, or_false] at H
          rcases H with h1 | h2
          · have : 0 ≠ h7.h := by
              symm ;apply Nat.pos_iff_ne_zero.mp
              dsimp [h]
              exact Module.finrank_pos
            apply this
            exact h1.symm
          · apply r_ne_zero h7 q hq0 h2mq
            exact h2
    · unfold c₅
      trans
      · have : (0 : ℝ) < 1 := by simp only [zero_lt_one]
        apply this
      · apply one_lt_pow₀
        · refine one_lt_pow₀ ?_ ?_
          · simp only [Int.cast_abs, lt_add_iff_pos_left, abs_pos, ne_eq, Int.cast_eq_zero]
            rw [← ne_eq]
            exact c₁_ne_zero h7
          · simp only [ne_eq, mul_eq_zero, Nat.add_eq_zero_iff, one_ne_zero, OfNat.ofNat_ne_zero,
            Nat.pow_eq_zero, not_false_eq_true, and_true, false_or, false_and, or_false]
            · unfold h
              have : 0 < Module.finrank ℚ h7.K := Module.finrank_pos
              simp_all only [norm_pow, ne_eq]
              apply Aesop.BuiltinRules.not_intro
              intro a
              simp_all only [pow_zero, one_mul, inv_one, lt_self_iff_false]
        · exact r_ne_zero h7 q hq0 h2mq
    · have : 1 ≤ abs (h7.c₁) ^ (↑(h7.h) *
       ((↑(h7.r q hq0 h2mq)) + 2 * ↑(h7.m) * (↑q))) := by
        refine one_le_pow₀ ?_
        have : 1 ≤ h7.c₁ := h7.one_le_c₁
        exact one_le_abs_c₁ h7
      calc (0 : ℝ) < 1 := by simp only [zero_lt_one]
           (1 : ℝ) ≤ abs (h7.c₁) ^ (↑(h7.h) *
           ((↑(h7.r q hq0 h2mq)) + 2 * ↑(h7.m) * (↑q))) := mod_cast this
  · unfold cρ
    simp only [neg_mul, _root_.zpow_neg]
    simp only [Int.cast_abs, norm_pow]
    rw [Int.norm_eq_abs]
    simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow, abs_abs]
    rw [← abs_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add]
    · rw [← Real.rpow_mul]
      · rw [mul_comm]
        norm_cast
        simp only [Int.cast_pow, Int.cast_abs, abs_pow]
        unfold h
        simp only [le_refl]
      · exact mod_cast (le_trans Int.one_nonneg (h7.one_le_c₁))
    · rw [lt_iff_le_and_ne]
      refine ⟨mod_cast (le_trans Int.one_nonneg (h7.one_le_c₁)), fun H ↦ ?_⟩
      · apply c₁_ne_zero h7
        symm
        exact mod_cast H
  · exact h2

lemma c_coeffspow_r :
  ((h7.c₁) ^ (h7.r q hq0 h2mq) * (h7.c₁) ^ (h7.m * q) * (h7.c₁) ^ (h7.m * q)) =
  ((h7.c₁) ^ ((h7.r q hq0 h2mq)) *
  (h7.c₁) ^ (h7.m * q - (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))) *
  (h7.c₁) ^ (h7.m * q - ((b q t * (↑(h7.l₀' q hq0 h2mq) + 1))))) •
  (h7.c₁) ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
  (h7.c₁) ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) := by
    rw [← one_mul (h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq : ℕ) + 1)))]
    have triple_comm_int (a b c : ℤ) (x y z : ℤ) :
      ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
     simp only [zsmul_eq_mul, Int.cast_mul]; ring
    simp only [mul_assoc]
    rw [ smul_mul_assoc
          (h7.c₁ ^ h7.r q hq0 h2mq *
            (h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
              h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1))))
          (1 * h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))
          (h7.c₁ ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))]
    rw [Int.mul_assoc 1 (h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))
          (h7.c₁ ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))]
    simp only [← mul_assoc]
    rw [triple_comm_int]
    congr
    · simp only [Int.zsmul_eq_mul, mul_one]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (h7.m * q - (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))
      + (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))) = (h7.m * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm h7.m]
        apply mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt) ?_ (Nat.zero_le _) (Nat.zero_le _)
        · exact (h7.l₀' q hq0 h2mq).isLt
      rw [this]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (h7.m * q - (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))
        + (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))) = (h7.m * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm h7.m]
        apply mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt) ?_ (Nat.zero_le _) (Nat.zero_le _)
        · exact (h7.l₀' q hq0 h2mq).isLt
      rw [this]

end Setup

end

end


/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/



section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
  (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup

/-! On the other hand `house (ρ) ≤ t c₄ⁿ n⁽ⁿ⁻¹⁾⁄₂ (c₆q)ʳ c₇^q ≤ c₈ʳ r⁽ʳ⁺³⁾⁄₂`.
-/

lemma one_le_c₄ : 1 ≤ h7.c₄ := one_le_mul_of_one_le_of_one_le
  (le_max_left 1 (GSHouse.c₁ h7.K * GSHouse.c₁ h7.K * 2 * ↑(h7.m))) (h7.one_le_c₃)

def c₆ : ℝ := (|↑h7.c₁| * (1 + house h7.β'))

omit [DecidableEq (h7.K →+* ℂ)] in
lemma c₆_nonneg : 0 ≤ h7.c₆ := by
  unfold c₆ house; positivity

omit [DecidableEq (h7.K →+* ℂ)] in
lemma one_le_c₆ : 1 ≤ h7.c₆ := by
  unfold c₆
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · norm_cast; exact one_le_abs_c₁ h7
  · simp only [le_add_iff_nonneg_right]
    exact house_nonneg h7.β'

def c₇ : ℝ := ((((|↑h7.c₁| * |↑h7.c₁| *
  (|↑h7.c₁| * (house h7.α' * (|↑h7.c₁| * house h7.γ'))))) ^ h7.m))

omit [DecidableEq (h7.K →+* ℂ)] in
lemma one_le_c₇ : 1 ≤ h7.c₇ := by
  unfold c₇
  have hc : 0 ≤ h7.c₁ := le_trans Int.one_nonneg h7.one_le_c₁
  have house_num_mul_int (α : h7.K) (c' : ℤ) (hc' : 0 ≤ c') :
      house ((c' : h7.K) * α) = |(c' : ℝ)| * house α := by
    lift c' to ℕ using hc'
    simpa using house_nat_mul α c'
  have hα : 1 ≤ |(h7.c₁ : ℝ)| * house h7.α' := by
    rw [← house_num_mul_int (α := h7.α') (c' := h7.c₁) hc, ← smul_eq_mul]
    exact one_le_house_of_isIntegral (mod_cast h7.isIntegral_c₁α) (mod_cast h7.c₁α_ne_zero)
  have hγ : 1 ≤ |(h7.c₁ : ℝ)| * house h7.γ' := by
    rw [← house_num_mul_int (α := h7.γ') (c' := h7.c₁) hc, ← smul_eq_mul]
    exact one_le_house_of_isIntegral (mod_cast h7.isIntegral_c₁γ) (mod_cast h7.c₁γ_ne_zero)
  have hbase :
      1 ≤ |(h7.c₁ : ℝ)| * |(h7.c₁ : ℝ)| *
        (|(h7.c₁ : ℝ)| * (house h7.α' * (|(h7.c₁ : ℝ)| * house h7.γ'))) := by
    calc
      1 ≤ (|(h7.c₁ : ℝ)| * |(h7.c₁ : ℝ)|) *
            ((|(h7.c₁ : ℝ)| * house h7.α') * (|(h7.c₁ : ℝ)| * house h7.γ')) := by
          refine one_le_mul_of_one_le_of_one_le
            (one_le_mul_of_one_le_of_one_le
              (by
                norm_cast
                exact one_le_abs_c₁ h7)
              (by
                norm_cast
                exact one_le_abs_c₁ h7))
            (one_le_mul_of_one_le_of_one_le hα hγ)
      _ = |(h7.c₁ : ℝ)| * |(h7.c₁ : ℝ)| *
            (|(h7.c₁ : ℝ)| * (house h7.α' * (|(h7.c₁ : ℝ)| * house h7.γ'))) := by
          ring
  calc
    (1 : ℝ) = 1 ^ h7.m := by simp
    _ ≤ (|(h7.c₁ : ℝ)| * |(h7.c₁ : ℝ)| *
          (|(h7.c₁ : ℝ)| * (house h7.α' * (|(h7.c₁ : ℝ)| * house h7.γ')))) ^ h7.m := by
        refine pow_le_pow_left₀ (by positivity) hbase h7.m

lemma r_qt_0 : 0 < h7.r q hq0 h2mq :=
  Nat.zero_lt_of_ne_zero (h7.r_ne_zero q hq0 h2mq)

lemma one_le_r : 1 ≤  h7.r q hq0 h2mq :=
  Nat.zero_lt_of_ne_zero (h7.r_ne_zero q hq0 h2mq)

lemma cρ_abs_eq : |h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (2 * h7.m * q)| =
  h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (2 * h7.m * q) := by
    rw [abs_eq_self]
    apply mul_nonneg (pow_nonneg (le_trans Int.one_nonneg h7.one_le_c₁) _)
    · apply pow_nonneg (le_trans Int.one_nonneg h7.one_le_c₁)

lemma eq6a : house (rho h7 q hq0 h2mq) ≤
  (q*q) *(h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
        (h7.c₆* q) ^(h7.r q hq0 h2mq) * (h7.c₇)^(q : ℤ)) := by
  calc _ ≤ norm (h7.cρ q hq0 h2mq : ℝ) * house (rho h7 q hq0 h2mq) := ?_
       _ ≤ (norm (h7.cρ q hq0 h2mq : ℝ))  *
          house (∑ t, ( ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) *
        ((h7.systemCoeffs_r q hq0 t h2mq)))) := ?_
       _ ≤ (norm (h7.cρ q hq0 h2mq : ℝ)) *
         ∑ t, house ( ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) *
       ((h7.systemCoeffs_r q hq0 t h2mq))) := ?_
       _ = (∑ t, house ((h7.cρ q hq0 h2mq) *
         (algebraMap (𝓞 h7.K) h7.K ((h7.η q hq0 h2mq) t) *
          h7.systemCoeffs_r q hq0 t h2mq))) := ?_
       _ = ∑ t, house ((algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq t) *
        (↑h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
          (↑h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
            (h7.c₁ ^ h7.r q hq0 h2mq • (↑(a q t) + b q t • h7.β') ^ h7.r q hq0 h2mq *
              (h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.α' ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
                h7.c₁ ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.γ' ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))))))) := ?_
       _ ≤ ∑ t, house ((algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq t)) *
        (house (((h7.c₁ : h7.K) ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))) *
          (house (((h7.c₁ : h7.K) ^
              (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))) *
            (house (((h7.c₁ : h7.K) ^ h7.r q hq0 h2mq •
              (↑(a q t) + b q t • h7.β') ^ h7.r q hq0 h2mq)) *
              (house (((h7.c₁ : h7.K) ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.α' ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))) *
                (house ((h7.c₁ : h7.K) ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.γ' ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))
                  ))))) := ?_
       _ ≤ (∑ t, h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
        (↑|h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1))| *
        (↑|h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1))| *
          (((|h7.c₁| * (|(q : ℤ)| * (1 + house (h7.β')))) ^ (h7.r q hq0 h2mq)) *
             house ((h7.c₁ • h7.α')) ^ (h7.m * q) *
             house ((h7.c₁ • h7.γ')) ^ (h7.m * q))))) := ?_
       _ ≤ ∑ (t : Fin (q * q)), h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
          (↑|h7.c₁| ^ (h7.m * q) *
          (↑|h7.c₁| ^ (h7.m * q) *
          ((|h7.c₁|^ (h7.r q hq0 h2mq) *
            (|(q : ℤ)|^ (h7.r q hq0 h2mq) * (1 + house (h7.β')) ^ (h7.r q hq0 h2mq)) *
             ((|h7.c₁|^ (h7.m * q) * house (h7.α') ^ (h7.m * q)) *
             (|h7.c₁|^ (h7.m * q)  * house h7.γ' ^ (h7.m * q))))))) := ?_
       _ ≤  (q*q) *(h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
        (h7.c₆* q) ^(h7.r q hq0 h2mq) * (h7.c₇)^(q : ℤ)) := ?_
  · rw [← one_mul (house (h7.rho q hq0 h2mq))]
    apply mul_le_mul
    · exact h7.one_le_norm_c1rho q hq0 h2mq
    · simp only [one_mul, le_refl]
    · exact house_nonneg (h7.rho q hq0 h2mq)
    · simp only [norm_nonneg]
  · unfold rho
    simp only [le_refl]
  · apply mul_le_mul (le_refl _)
    · exact
      house_sum_le_sum_house Finset.univ fun i ↦
        (algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq i)
        * h7.systemCoeffs_r q hq0 i h2mq
    · exact
      house_nonneg (∑ t, (algebraMap (𝓞 h7.K) h7.K)
        (h7.η q hq0 h2mq t) * h7.systemCoeffs_r q hq0 t h2mq)
    · exact norm_nonneg (h7.cρ q hq0 h2mq)
  · rw [mul_sum]
    apply Finset.sum_congr rfl
    intros i hi
    have  house_num_mul_int (α : h7.K) (c' : ℤ) (hc : 0 ≤ c') :
    house ((c' : h7.K) * α) = |(c' : ℝ)| * house (α) := by
        lift c' to ℕ using hc
        simpa using house_nat_mul α c'
    rw [house_num_mul_int
    (α := ((algebraMap (𝓞 h7.K) h7.K)
    (h7.η q hq0 h2mq i) * h7.systemCoeffs_r q hq0 i h2mq))]
    · simp only [Real.norm_eq_abs]
    · exact zero_le_c1rho h7 q hq0 h2mq
  · apply Finset.sum_congr rfl
    intros t ht
    rw [Algebra.left_comm (↑(h7.cρ q hq0 h2mq))
      (h7.η q hq0 h2mq t) (h7.systemCoeffs_r q hq0 t h2mq)]
    simp only [← zsmul_eq_mul]
    unfold systemCoeffs_r
    unfold cρ
    rw [cρ_abs_eq]
    have : h7.c₁ ^ (2 * h7.m * q) = h7.c₁ ^ (h7.m * q)
     * h7.c₁ ^ (h7.m * q) := by
       rw [← pow_add]; ring
    rw [this]; clear this
    have := h7.c_coeffspow_r q hq0 t h2mq
    simp only [mul_assoc] at this
    rw [this]; clear this
    rw [Int.mul_comm (h7.c₁ ^ h7.r q hq0 h2mq)
     (h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
    h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))]
    simp only [mul_assoc]
    simp only [nsmul_eq_mul, zsmul_eq_mul,
     Int.cast_mul, Int.cast_pow]
    simp only [mul_assoc]
    simp only [Int.cast_eq]
    ring_nf
  · refine Finset.sum_le_sum ?_
    intro t ht
    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg (le_refl _) ?_ (house_nonneg _) (by positivity)

    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg (le_refl _) ?_ (house_nonneg _) (by positivity)

    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg (le_refl _) ?_ (house_nonneg _) (by positivity)

    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg ?_ ?_ (house_nonneg _) (by positivity)
    · simp [nsmul_eq_mul, zsmul_eq_mul, smul_eq_mul, Int.cast_pow]
    · trans
      · exact house_mul_le _ _
      ·
        refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) (by positivity) <;>
          simp [house]
  · apply Finset.sum_le_sum
    intros t ht
    apply mul_le_mul
    · apply h7.house_eta_le_c₄_pow q hq0 t h2mq
    · simp only [mul_assoc]
      apply mul_le_mul
      · norm_cast
        rw [house_intCast]
      · apply mul_le_mul
        · norm_cast
          rw [house_intCast]
        · apply mul_le_mul
          · simp only [nsmul_eq_mul, smul_eq_mul]
            rw [← mul_pow]
            rw [mul_add]
            calc _ ≤  house ((↑h7.c₁ * ↑(a q t) + ↑h7.c₁ *
                  (↑(b q t) * h7.β'))) ^ h7.r q hq0 h2mq :=?_
                 _ ≤  (↑|h7.c₁| * (↑|↑q| * (1 + house h7.β'))) ^ h7.r q hq0 h2mq := ?_
            · apply house_pow_le _ _
            · rw [← mul_add]
              rw [pow_le_pow_iff_left₀]
              · have := house_add_mul_le h7 q t
                simp only [mul_assoc] at *
                norm_cast at *
                simp only [nsmul_eq_mul, zsmul_eq_mul] at this
                exact this
              · apply house_nonneg
              · unfold house
                positivity
              · exact r_ne_zero h7 q hq0 h2mq
            · simp only [Int.cast_abs, Nat.abs_cast, Int.cast_natCast, le_refl]
          · apply mul_le_mul
            · simp only [smul_eq_mul, zsmul_eq_mul]
              rw [← mul_pow]
              trans
              · apply house_pow_le _ _
              apply Bound.pow_le_pow_right_of_le_one_or_one_le
                (Or.inl ⟨one_le_house_of_isIntegral ?_ ?_, ?_⟩)
              · rw [← smul_eq_mul]
                exact mod_cast h7.isIntegral_c₁α
              · rw [← smul_eq_mul]
                exact mod_cast h7.c₁α_ne_zero
              · rw [mul_comm h7.m  q]
                apply mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt) ?_ (Nat.zero_le _) (Nat.zero_le _)
                · exact (h7.l₀' q hq0 h2mq).isLt
            · simp only [smul_eq_mul, zsmul_eq_mul]
              rw [← mul_pow]
              trans
              · apply house_pow_le _ _
              apply Bound.pow_le_pow_right_of_le_one_or_one_le
                (Or.inl ⟨one_le_house_of_isIntegral ?_ ?_, ?_⟩)
              · rw [← smul_eq_mul]
                exact mod_cast h7.isIntegral_c₁γ
              · rw [← smul_eq_mul]
                exact mod_cast h7.c₁γ_ne_zero
              · rw [mul_comm h7.m  q]
                apply mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt) ?_ (Nat.zero_le _) (Nat.zero_le _)
                · exact (h7.l₀' q hq0 h2mq).isLt
            · apply house_nonneg
            · unfold house; positivity
          · unfold house; positivity
          · unfold house; positivity
        · unfold house; positivity
        · positivity
      · unfold house; positivity
      · positivity
    · unfold house; positivity
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        · exact le_trans zero_le_one (h7.one_le_c₄)
      · positivity
  · apply Finset.sum_le_sum
    intros t ht
    apply mul_le_mul
    · simp only [Real.rpow_natCast, le_refl]
    · apply mul_le_mul
      · simp only [abs_pow, Int.cast_pow, Int.cast_abs]
        refine pow_le_pow_right₀ ?_ ?_
        · norm_cast; exact one_le_abs_c₁ h7
        · exact Nat.sub_le (h7.m * q) (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))
      · apply mul_le_mul
        · simp only [abs_pow, Int.cast_pow, Int.cast_abs]
          refine pow_le_pow_right₀ ?_ ?_
          · norm_cast; exact one_le_abs_c₁ h7
          · exact Nat.sub_le (h7.m * q) (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))
        · nth_rw 1 [mul_assoc]
          apply mul_le_mul
          · rw [← mul_pow]; rw [← mul_pow]
          · apply mul_le_mul
            · simp only [zsmul_eq_mul, Int.cast_abs]
              rw [← mul_pow]
              refine pow_le_pow_left₀ ?_ ?_ (h7.m * q)
              · apply house_nonneg
              · trans
                · apply house_mul_le
                · simp only [house_intCast, Int.cast_abs, le_refl]
            · simp only [zsmul_eq_mul, Int.cast_abs]
              rw [← mul_pow]
              refine pow_le_pow_left₀ ?_ ?_ (h7.m * q)
              · apply house_nonneg
              · trans
                · apply house_mul_le
                · simp only [house_intCast, Int.cast_abs, le_refl]
            · unfold house; positivity
            · unfold house; positivity
          · unfold house; positivity
          · unfold house; positivity
        · unfold house; positivity
        · positivity
      · unfold house; positivity
      · positivity
    · unfold house; positivity
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        · exact le_trans zero_le_one (h7.one_le_c₄)
      · positivity
  · simp only [ sum_const, card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    apply mul_le_mul
    · simp only [Nat.cast_mul, le_refl]
    · nth_rw 4 [mul_assoc]
      apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · simp only [← mul_assoc]
        rw [← mul_pow]
        simp only [mul_assoc]
        rw [← mul_pow]
        rw [← mul_pow]
        rw [← mul_pow]
        simp only [Int.cast_abs,
        Nat.abs_cast, Int.cast_natCast, zpow_natCast]
        rw [mul_comm ((1 + house h7.β') ^ h7.r q hq0 h2mq)
          ((|↑h7.c₁| * (house h7.α' * (|↑h7.c₁| * house h7.γ'))) ^ (h7.m * q))]
        nth_rw 3 [← mul_assoc]
        rw [mul_comm ((q:ℝ) ^ h7.r q hq0 h2mq)
         ((|↑h7.c₁| * (house h7.α' * (|↑h7.c₁| * house h7.γ'))) ^ (h7.m * q))]
        nth_rw 2 [← mul_assoc]
        rw [mul_comm  (|(h7.c₁ : ℝ)| ^ h7.r q hq0 h2mq)
          ((|(h7.c₁ : ℝ)| * (house h7.α' * (|(h7.c₁ : ℝ)| *
           house h7.γ'))) ^ (h7.m * q) * (q : ℝ) ^ h7.r q hq0 h2mq)]
        nth_rw 1 [← mul_assoc]
        rw [mul_comm  ((h7.c₆ * ↑q) ^ h7.r q hq0 h2mq) (h7.c₇ ^ q)]
        simp only [mul_assoc]
        rw [← mul_pow]
        rw [← mul_pow]
        nth_rw 1 [← mul_assoc]
        rw [← mul_pow]
        rw [pow_mul]
        rw [← mul_comm  (q : ℝ)  h7.c₆]
        unfold c₇ c₆
        simp only [mul_assoc]
        rfl
      · unfold house; positivity
      · apply mul_nonneg
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · exact le_trans zero_le_one (h7.one_le_c₄)
        · positivity
    · apply mul_nonneg
      · apply mul_nonneg
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · exact le_trans zero_le_one (h7.one_le_c₄)
        · positivity
      · unfold house; positivity
    · positivity

theorem bound_n_le_r' : ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) ≤
     ((h7.r q hq0 h2mq : ℝ)^((1/2) * ((h7.r q hq0 h2mq : ℝ) + 1))) := by
      calc _ ≤ ((h7.r q hq0 h2mq : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) := ?_
           _ ≤ ((h7.r q hq0 h2mq : ℝ)^((1/2)* ((h7.r q hq0 h2mq : ℝ) + 1))) := ?_
      · refine Real.rpow_le_rpow ?_ ?_ ?_
        · simp only [Nat.cast_nonneg]
        · simp only [Nat.cast_le]; exact n_le_r h7 q hq0 h2mq
        · refine div_nonneg ?_ ?_
          · norm_cast
            exact Nat.le_add_left 0 (h7.n q + 1)
          · simp only [Nat.ofNat_nonneg]
      · apply Real.rpow_le_rpow_of_exponent_le_or_ge
        left
        · simp only [Nat.one_le_cast, one_div]
          refine ⟨r_qt_0 h7 q hq0 h2mq, ?_⟩
          · ring_nf
            simp only [one_div, add_le_add_iff_left,
             inv_pos, Nat.ofNat_pos, mul_le_mul_iff_left₀, Nat.cast_le]
            exact n_le_r h7 q hq0 h2mq

lemma bound_n_le_r :
  (h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) ≤
  ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ)) *
    ((h7.r q hq0 h2mq : ℝ)^((1/2)* ((h7.r q hq0 h2mq : ℝ) + 1))))) := by
    apply mul_le_mul
    · simp only [Real.rpow_natCast]
      refine pow_le_pow_right₀ (one_le_c₄ h7) (n_le_r h7 q hq0 h2mq)
    · exact bound_n_le_r' h7 q hq0 h2mq
    · apply Real.rpow_nonneg
      simp only [Nat.cast_nonneg]
    · apply Real.rpow_nonneg
      exact le_trans zero_le_one (h7.one_le_c₄)

lemma q_le_2sqrtmr : q^2 ≤ 2*h7.m*h7.r q hq0 h2mq := by
  trans
  · apply h7.q_sq_le_two_mn q h2mq
  refine Nat.mul_le_mul (le_refl _) (n_le_r h7 q hq0 h2mq)

lemma sqt_etc : Real.sqrt (2*h7.m*(h7.r q hq0 h2mq)) =
  Real.sqrt (2*h7.m) * (h7.r q hq0 h2mq : ℝ)^(1/2 : ℝ) := by
    rw [Real.sqrt_mul]
    · congr
      exact Real.sqrt_eq_rpow ↑(h7.r q hq0 h2mq)
    · positivity

def c₈ : ℝ := (h7.c₆ * √(2 * ↑h7.m) * h7.c₇ ^ (2 * h7.m) * h7.c₄ * (2 * ↑h7.m))

omit [DecidableEq (h7.K →+* ℂ)] in
lemma c7_nonneg : 0 ≤ h7.c₇ := by
  unfold c₇ house
  positivity

lemma c8_nonneg : 0 ≤ h7.c₈ := by
  unfold c₈
  apply mul_nonneg ?_ (by positivity)
  · apply mul_nonneg ?_ (le_trans zero_le_one (h7.one_le_c₄))
    · apply mul_nonneg (mul_nonneg (c₆_nonneg h7) (by simp)) (pow_nonneg (c7_nonneg h7) _)

lemma c8_geq_one : 1 ≤ h7.c₈ := by
  unfold c₈
  have : 1 ≤ h7.c₆ := h7.one_le_c₆
  have : 1 ≤ h7.c₇ := h7.one_le_c₇
  have := h7.one_le_c₄
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le
      · apply one_le_mul_of_one_le_of_one_le
        · (expose_names; exact this_1)
        · rw [Real.one_le_sqrt]
          apply one_le_mul_of_one_le_of_one_le (by grind) ?_
          · simp only [Nat.one_le_cast]
            exact Nat.le_of_ble_eq_true rfl
      · (expose_names; exact one_le_pow₀ this_2)
    · exact this
  · apply one_le_mul_of_one_le_of_one_le (by grind) ?_
    · simp only [Nat.one_le_cast]
      exact Nat.le_of_ble_eq_true rfl

lemma zero_lt_r : 0 < h7.r q hq0 h2mq :=
  r_qt_0 h7 q hq0 h2mq

theorem q_sq2_neq_1 (m q : ℕ) (_ : 0 < q)
    (h2mq : 2 * m ∣ q ^ 2) : q ^ 2 ≠ 1 := by
  intro hq2eq1
  have hdiv1 : 2 * m ∣ 1 := by
    exact (Nat.ModEq.dvd_iff
     (congrFun (congrArg HMod.hMod hq2eq1) (q ^ 2)) h2mq).mp h2mq
  cases m with
  | zero => simp [*] at hdiv1
  | succ m' =>
    have h_two_eq_one : 2 * (m'.succ) = 1 := Nat.eq_one_of_dvd_one hdiv1
    have h_ge_two : 2 * (m'.succ) ≥ 2 := by
      calc
        2 * (m'.succ) = 2 + 2 * m' := by
          simp only [Nat.succ_eq_add_one]
          ring_nf
        _ ≥ 2 := Nat.le_add_right _ _
    have absurd_le : 1 ≥ 2 := by rwa [h_two_eq_one] at h_ge_two
    have gt21 : 2 > 1 := by decide
    exact (Nat.not_le_of_gt gt21) absurd_le

theorem eq6b.extracted_1_1 :
  q * q ≤ (2 * h7.m : ℝ) ^ (h7.r q hq0 h2mq: ℝ) * (h7.r q hq0 h2mq: ℝ) := by
    calc _ = (q^2: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) * (h7.n q: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) ^ (h7.n q: ℝ) := ?_
         _ ≤ ((2*h7.m: ℝ)^(h7.r q hq0 h2mq: ℝ)) := ?_
         _ ≤ (2 * ↑h7.m : ℝ) ^ (h7.r q hq0 h2mq: ℝ) * (h7.r q hq0 h2mq: ℝ) := ?_
    · grind
    · norm_cast; exact h7.q_sq_le_two_mn q h2mq
    · have : (2 * ↑h7.m) * h7.n q ≤ (2 * ↑h7.m) ^h7.n q := by
        refine Nat.mul_le_pow ?_ (h7.n q)
        simp only [ne_eq, mul_eq_one,
          OfNat.ofNat_ne_one, false_and, not_false_eq_true]
      simp only [Real.rpow_natCast, ge_iff_le]
      exact mod_cast this
    · apply Real.rpow_le_rpow_of_exponent_le
      · have : 1 ≤ 2 * (h7.m : ℝ) := by
              unfold m
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
              ring_nf
              refine le_add_of_le_of_nonneg ?_ ?_
              · simp only [Nat.one_le_ofNat]
              · positivity
        exact this
      · norm_cast; exact n_le_r h7 q hq0 h2mq
    · nth_rw 1 [← mul_one (a:= (2 * (h7.m : ℝ)) ^ (h7.r q hq0 h2mq : ℝ))]
      apply mul_le_mul (by grind) (mod_cast (h7.one_le_r q hq0 h2mq)) (by grind) (by positivity)

theorem eq6b.extracted_1_2 :
  q * q ≤ (2 * h7.m : ℝ) ^ (h7.r q hq0 h2mq: ℝ) := by
    calc _ = (q^2: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) * (h7.n q: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) ^ (h7.n q: ℝ) := ?_
         _ ≤ ((2*h7.m: ℝ)^(h7.r q hq0 h2mq: ℝ)) := ?_
    · grind
    · norm_cast; exact h7.q_sq_le_two_mn q h2mq
    · have : (2 * ↑h7.m) * h7.n q ≤ (2 * ↑h7.m) ^h7.n q := by
        refine Nat.mul_le_pow ?_ (h7.n q)
        simp only [ne_eq, mul_eq_one,
          OfNat.ofNat_ne_one, false_and, not_false_eq_true]
      simp only [Real.rpow_natCast, ge_iff_le]
      exact mod_cast this
    · apply Real.rpow_le_rpow_of_exponent_le
      · have : 1 ≤ 2 * (h7.m : ℝ) := by
              unfold m
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
              ring_nf
              refine le_add_of_le_of_nonneg ?_ ?_
              · simp only [Nat.one_le_ofNat]
              · positivity
        exact this
      · norm_cast
        exact n_le_r h7 q hq0 h2mq

open Real

include h2mq in
lemma q_eq_sqrtmn : q = Real.sqrt (2 * h7.m* h7.n q) := by
  norm_cast
  rw [← h7.q_sq_eq_two_mn q h2mq]
  simp only [Nat.cast_pow, Nat.cast_nonneg, sqrt_sq]

set_option linter.style.multiGoal false in
lemma eq6b : (q*q) * ((((h7.c₄ ^ (h7.n q : ℝ) *
  ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)))) *
  (h7.c₆* q) ^(h7.r q hq0 h2mq) * (h7.c₇)^q)) ≤
  h7.c₈^(h7.r q hq0 h2mq : ℝ) *
   (h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) + 3/2) := by
  calc
       _ ≤ (((2*h7.m)^(h7.r q hq0 h2mq : ℝ))* ((h7.r q hq0 h2mq)) *
           ((((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ)) *
           ((h7.r q hq0 h2mq : ℝ)^((1/2)* ((h7.r q hq0 h2mq : ℝ) + 1))))) *
           (((h7.c₆* Real.sqrt (2*h7.m) *
           (h7.r q hq0 h2mq: ℝ)^(1/2 : ℝ)) ^(h7.r q hq0 h2mq: ℝ)) *
           ((h7.c₇)^(2*h7.m))^(h7.r q hq0 h2mq: ℝ)))) := ?_
       _ ≤ h7.c₈^(h7.r q hq0 h2mq : ℝ) *
         (h7.r q hq0 h2mq : ℝ)^((h7.r q hq0 h2mq : ℝ) + 3/2) := ?_
  · -- keep your existing first block unchanged
    apply mul_le_mul (eq6b.extracted_1_1 h7 q hq0 h2mq)
    · simp only [mul_assoc]
      apply mul_le_mul
      · simp only [Real.rpow_natCast]
        refine pow_le_pow_right₀ (one_le_c₄ h7) (n_le_r h7 q hq0 h2mq)
      · apply mul_le_mul
        · exact bound_n_le_r' h7 q hq0 h2mq
        · apply mul_le_mul
          · simp only [Real.rpow_natCast]
            refine pow_le_pow_left₀ ?_ ?_ (h7.r q hq0 h2mq)
            · unfold c₆ house; positivity
            · refine mul_le_mul_of_nonneg_left ?_ ?_
              · have := h7.q_eq_sqrtmn q h2mq
                calc _ ≤ √(2 * ↑h7.m) * ↑(h7.n q) ^ (1 / 2 : ℝ) := ?_
                     _ ≤ √(2 * ↑h7.m) * ↑(h7.r q hq0 h2mq) ^ (1 / 2 : ℝ) := ?_
                · rw [this]
                  rw [Real.sqrt_mul]
                  refine mul_le_mul_of_nonneg_left ?_ ?_
                  · rw [le_iff_lt_or_eq]
                    right
                    exact Real.sqrt_eq_rpow ↑(h7.n q)
                  · simp only [Nat.ofNat_nonneg, Real.sqrt_nonneg]
                  grind
                · refine mul_le_mul_of_nonneg_left ?_ ?_
                  · apply Real.rpow_le_rpow
                    · simp only [Nat.cast_nonneg]
                    · simp only [Nat.cast_le]
                      exact n_le_r h7 q hq0 h2mq
                    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
                  · simp only [Nat.ofNat_nonneg, Real.sqrt_nonneg]
              · unfold c₆ house; positivity
          · simp only [Real.rpow_natCast]
            rw [← pow_mul]
            refine pow_le_pow_right₀ ?_ ?_
            · exact one_le_c₇ h7
            · trans
              · apply h7.q_le_two_mn q h2mq
              apply mul_le_mul (le_refl _) (n_le_r h7 q hq0 h2mq)
                (by positivity) (by positivity)
          · unfold c₇ house; positivity
          · unfold c₆ house; positivity
        · unfold c₇ c₆ house; positivity
        · positivity
      · unfold c₆ c₇ house; positivity
      · simp only [Real.rpow_natCast]
        unfold c₄
        apply pow_nonneg
        simp only [lt_sup_iff, zero_lt_one, true_or,
          mul_nonneg_iff_of_pos_left]
        exact le_trans zero_le_one (h7.one_le_c₃)
    · unfold c₆ c₇ house
      · apply mul_nonneg
        · apply mul_nonneg
          · simp only [Real.rpow_natCast]
            · apply mul_nonneg
              · apply pow_nonneg
                exact le_trans zero_le_one (h7.one_le_c₄)
              · positivity
          · positivity
        · positivity
    · positivity
  · -- keep your existing second block unchanged
    nth_rw 2 [Real.mul_rpow]
    nth_rw 4 [mul_comm]
    nth_rw 2 [mul_assoc]
    simp only [← mul_assoc]
    nth_rw 3 [mul_assoc]
    nth_rw 1 [← mul_comm]
    rw [mul_comm ((2 * (h7.m : ℝ)) ^ (h7.r q hq0 h2mq : ℝ)) (h7.r q hq0 h2mq : ℝ)]
    nth_rw 3 [← Real.rpow_one ((h7.r q hq0 h2mq))]
    simp only [← mul_assoc]
    nth_rw 1  [← Real.rpow_add]
    simp only [mul_assoc]
    rw [← Real.mul_rpow]
    rw [← mul_assoc]
    rw [← mul_assoc]
    nth_rw 8 [mul_comm]
    rw [mul_rotate]
    nth_rw 1 [← mul_assoc]
    nth_rw 1 [← mul_assoc]
    rw [← Real.mul_rpow]
    nth_rw 1 [mul_assoc]
    nth_rw 1 [mul_assoc]
    nth_rw 3 [← mul_assoc]
    nth_rw 1  [← Real.rpow_mul]
    nth_rw 1  [← Real.rpow_add]
    nth_rw 7 [mul_comm]
    simp only [← mul_assoc]
    nth_rw 1 [← Real.mul_rpow]
    apply mul_le_mul
    · unfold c₈
      simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
        Real.rpow_natCast, le_refl]
    · ring_nf
      simp only [le_refl]
    · positivity
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      · apply h7.c8_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · apply h7.c₆_nonneg
          · simp only [Nat.ofNat_nonneg,
            Real.sqrt_mul, Real.sqrt_pos, Nat.ofNat_pos,
            mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
        · apply pow_nonneg
          · apply h7.c7_nonneg
      · exact le_trans zero_le_one (h7.one_le_c₄)
    · positivity
    · simp only [Nat.cast_pos]
      apply h7.zero_lt_r
    · simp only [Nat.cast_nonneg]
    · apply mul_nonneg
      · exact c₆_nonneg h7
      · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
        Real.sqrt_pos, Nat.ofNat_pos,
        mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
    · apply mul_nonneg
      · apply pow_nonneg
        · exact c7_nonneg h7
      · exact le_trans zero_le_one (h7.one_le_c₄)
    · apply pow_nonneg
      · exact c7_nonneg h7
    · exact le_trans zero_le_one (h7.one_le_c₄)
    · simp only [Nat.cast_pos]
      exact r_qt_0 h7 q hq0 h2mq
    · apply mul_nonneg
      · exact c₆_nonneg h7
      · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
        Real.sqrt_pos, Nat.ofNat_pos,
        mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
    · positivity

lemma eq6 : house (rho h7 q hq0 h2mq) ≤ h7.c₈^(h7.r q hq0 h2mq : ℝ) *
(h7.r q hq0 h2mq : ℝ)^((h7.r q hq0 h2mq : ℝ) + 3/2) := by
  trans
  · apply h7.eq6a q hq0 h2mq
  exact h7.eq6b q hq0 h2mq


end Setup

end

end


/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/


section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt Differentiable Complex


noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
 (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup

/-
We formalize the existence of a function R' : ℂ → ℂ,
analytic in a neighborhood of l' + 1,
such that R(z) = (z - (l' + 1))^r * R'(z) in a neighborhood of l' + 1.
so this o is (I hope) R_order l' -/
lemma exists_analyticOn_factor_R_at_add_one (l' : Fin h7.m) :
  ∃ (R' : ℂ → ℂ) (U : Set ℂ),
    U ∈ nhds (l' + 1 : ℂ) ∧
    (l' + 1 : ℂ) ∈ U ∧
    (∀ z ∈ U, h7.R q hq0 h2mq z = (z - (l' + 1)) ^ (h7.r q hq0 h2mq) * R' z) ∧
    AnalyticOn ℂ R' U := by
  have hRanalytic : AnalyticAt ℂ (h7.R q hq0 h2mq) (l' + 1 : ℂ) := by
    fun_prop
  have hAO := (AnalyticAt.analyticOrderAt_eq_natCast
      (f := h7.R q hq0 h2mq) (z₀ := (l' + 1 : ℂ))
      (n := h7.R_order q hq0 h2mq (l' + 1)) hRanalytic).1
      (h7.R_order_eq q hq0 h2mq (l' + 1))
  rcases hAO with ⟨R'', horder, -, hfilter⟩
  let o : ℕ := h7.R_order q hq0 h2mq (l' + 1)
  have ho : h7.r q hq0 h2mq ≤ o := by
    rcases h7.r_prop q hq0 h2mq with ⟨_, hr⟩
    simpa [o, ge_iff_le, h7.R_order_eq q hq0 h2mq (l' + 1)] using hr l'
  rcases (Filter.eventually_iff_exists_mem).1 hfilter with ⟨U, hU, hU_prop⟩
  rcases AnalyticAt.exists_mem_nhds_analyticOnNhd horder with ⟨U2, hU2, hU2prop⟩
  refine ⟨(fun z => (z - (l' + 1)) ^ (o - h7.r q hq0 h2mq) * R'' z), U ∩ U2,
  Filter.inter_mem hU hU2, mem_of_mem_nhds (Filter.inter_mem hU hU2), ?_, ?_⟩
  · intro z hz
    calc
      h7.R q hq0 h2mq z = (z - (l' + 1)) ^ o * R'' z := by
        simpa [smul_eq_mul] using hU_prop z hz.1
      _ = (z - (l' + 1)) ^ (h7.r q hq0 h2mq) *
        ((z - (l' + 1)) ^ (o - h7.r q hq0 h2mq) * R'' z) := by
        rw [← Nat.add_sub_of_le ho, pow_add]
        simp [mul_assoc, mul_left_comm, mul_comm]
  · intro z hz
    have hpow : AnalyticAt ℂ (fun z : ℂ => (z - (l' + 1)) ^ (o - h7.r q hq0 h2mq)) z := by
      exact (AnalyticAt.sub analyticAt_id analyticAt_const).pow (o - h7.r q hq0 h2mq)
    exact (hpow.mul (hU2prop z hz.2)).analyticWithinAt

noncomputable def analyticFactorR (l' : Fin h7.m) : ℂ → ℂ :=
  (exists_analyticOn_factor_R_at_add_one h7 q hq0 h2mq l').choose

noncomputable def analyticFactorNhds (l' : Fin h7.m) : Set ℂ :=
  (exists_analyticOn_factor_R_at_add_one h7 q hq0 h2mq l').choose_spec.choose

lemma analyticFactorR_spec (l' : Fin h7.m) :
    analyticFactorNhds h7 q hq0 h2mq l' ∈ nhds (l' + 1 : ℂ) ∧
    (l' + 1 : ℂ) ∈ analyticFactorNhds h7 q hq0 h2mq l' ∧
    (∀ z ∈ analyticFactorNhds h7 q hq0 h2mq l',
      h7.R q hq0 h2mq z = (z - (l' + 1)) ^ h7.r q hq0 h2mq * analyticFactorR h7 q hq0 h2mq l' z) ∧
    AnalyticOn ℂ (analyticFactorR h7 q hq0 h2mq l') (analyticFactorNhds h7 q hq0 h2mq l') :=
  (exists_analyticOn_factor_R_at_add_one h7 q hq0 h2mq l').choose_spec.choose_spec

noncomputable def R_mul_pow_neg (l' : Fin h7.m) (z : ℂ) : ℂ :=
  h7.R q hq0 h2mq z * (z - (l' + 1)) ^ (-(h7.r q hq0 h2mq : ℤ))

def analyticExtensionR (l' : Fin (h7.m)) : ℂ → ℂ :=
  let R'U := analyticFactorR h7 q hq0 h2mq l'
  let R'R := R_mul_pow_neg h7 q hq0 h2mq l'
  let U := analyticFactorNhds h7 q hq0 h2mq l'
  letI : ∀ z, Decidable (z ∈ U) := by
    intros z
    exact Classical.propDecidable (z ∈ U)
  fun z ↦
    if z = l' + 1 then
      R'U z
    else
      R'R z

lemma analyticExtensionR_eq_analyticFactorR_on_nhds (l' : Fin (h7.m)) :
  let U := h7.analyticFactorNhds q hq0 h2mq l'
  ∀ z ∈ U, h7.analyticExtensionR q hq0 h2mq l' z = h7.analyticFactorR q hq0 h2mq l' z := by
  intros U z hz
  unfold Setup.analyticExtensionR
  split_ifs with h
  · rfl
  · unfold R_mul_pow_neg
    rw [(analyticFactorR_spec h7 q hq0 h2mq l').2.2.1 z hz, mul_right_comm,
        ← zpow_natCast, ← zpow_add₀ (sub_ne_zero.mpr h)]
    simp

lemma analyticExtensionR_eq_R_mul_pow_neg (l' : Fin h7.m) :
    ∀ z ∈ {z : ℂ | z ≠ l' + 1},
      h7.analyticExtensionR q hq0 h2mq l' z = h7.R_mul_pow_neg q hq0 h2mq l' z := by
  intro z hz
  unfold Setup.analyticExtensionR
  split_ifs with h
  · exact (hz h).elim
  · rfl

lemma R_mul_pow_neg_analyticOn (l' : Fin h7.m) :
    let R'R := h7.R_mul_pow_neg q hq0 h2mq l'
    AnalyticOn ℂ R'R {z | z ≠ l' + 1} := by
  unfold R_mul_pow_neg
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mono
    · have : ∀ (z : ℂ), AnalyticAt ℂ (h7.R q hq0 h2mq) z := by fun_prop
      · apply analyticOn_univ.mpr (fun x a ↦ this x)
    simp only [Set.subset_univ]
  · apply AnalyticOn.zpow (AnalyticOn.sub analyticOn_id analyticOn_const)
    exact fun z hz ↦ sub_ne_zero.mpr hz


lemma analyticExtensionR_analyticAt (l' : Fin (h7.m)) :
  ∀ z : ℂ, AnalyticAt ℂ (analyticExtensionR h7 q hq0 h2mq l') z := by
  intro z
  by_cases hz : z = l' + 1
  · rcases analyticFactorR_spec h7 q hq0 h2mq l' with ⟨hU, -, -, hA⟩
    have hAt :
      AnalyticAt ℂ (analyticFactorR h7 q hq0 h2mq l') z :=
      AnalyticOn.analyticAt
        (f := analyticFactorR h7 q hq0 h2mq l')
        (z := z) (s := analyticFactorNhds h7 q hq0 h2mq l')
        hA (hU := by simpa [hz] using hU)
    refine hAt.congr ?_
    refine Filter.eventually_of_mem (by simpa [hz] using hU) ?_
    intro w hw
    symm
    exact (analyticExtensionR_eq_analyticFactorR_on_nhds h7 q hq0 h2mq l' _ hw)
  · have hU : ({w : ℂ | w ≠ l' + 1} : Set ℂ) ∈ nhds z :=
      IsOpen.mem_nhds isOpen_ne (by simpa using hz)
    have hAt :
      AnalyticAt ℂ (R_mul_pow_neg h7 q hq0 h2mq l') z :=
      AnalyticOn.analyticAt
        (f := R_mul_pow_neg h7 q hq0 h2mq l')
        (z := z) (s := {w : ℂ | w ≠ l' + 1})
        (R_mul_pow_neg_analyticOn h7 q hq0 h2mq l')
        (hU := hU)
    refine hAt.congr ?_
    refine Filter.eventually_of_mem hU ?_
    intro w hw
    symm
    exact (analyticExtensionR_eq_R_mul_pow_neg h7 q hq0 h2mq l' _ hw)

lemma R_eq_pow_mul_analyticExtensionR (l' : Fin h7.m) (z : ℂ) :
    h7.R q hq0 h2mq z = (z - (l' + 1)) ^ h7.r q hq0 h2mq *
    h7.analyticExtensionR q hq0 h2mq l' z := by
  unfold Setup.analyticExtensionR
  split_ifs with h
  · exact h ▸ (analyticFactorR_spec h7 q hq0 h2mq l').2.2.1 _
      (analyticFactorR_spec h7 q hq0 h2mq l').2.1
  · unfold R_mul_pow_neg
    rw [mul_left_comm, ← zpow_natCast, ← zpow_add₀ (sub_ne_zero.mpr h),
        add_neg_cancel, zpow_zero, mul_one]

def evaluationPoints : Finset ℂ :=
   Finset.image (fun (k': ℕ) ↦ (k' + 1 : ℂ)) (Finset.range h7.m)

lemma mem_evaluationPoints_iff {z : ℂ} :
    z ∈ h7.evaluationPoints ↔ ∃ k : Fin h7.m, z = k + 1 := by
  simp [evaluationPoints, Finset.mem_image, Fin.exists_iff]
  grind

def evaluationPoints_compl : Set ℂ := (h7.evaluationPoints)ᶜ


lemma S_U_isOpen : IsOpen (evaluationPoints_compl h7) :=
  isOpen_compl_iff.mpr (Finset.isClosed _)


lemma S.U_nhds :
  ∀ z, z ∈ evaluationPoints_compl h7 → (evaluationPoints_compl h7) ∈ nhds z :=
  fun z hz ↦ IsOpen.mem_nhds (S_U_isOpen h7) hz

lemma sub_ne_zero_of_mem_evaluationPoints_compl {z : ℂ}
    (hz : z ∈ h7.evaluationPoints_compl) (k : Fin h7.m) :
    z - (k + 1 : ℂ) ≠ 0 := by
  rw [sub_ne_zero]
  exact fun h => hz (h7.mem_evaluationPoints_iff |>.mpr ⟨k, h⟩)

def auxiliaryRemainderRestricted : ℂ → ℂ := fun z ↦
  (h7.R q hq0 h2mq) z * (h7.r q hq0 h2mq).factorial *
    ((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq) : ℤ)) *
    (∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
      (((h7.l₀' q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq))

lemma auxiliaryRemainderRestricted_analyticOn_evaluationPoints_compl :
    AnalyticOn ℂ (h7.auxiliaryRemainderRestricted q hq0 h2mq) (h7.evaluationPoints_compl) := by
  unfold auxiliaryRemainderRestricted
  refine .mul (.mul (.mul ?_ analyticOn_const) ?_) ?_
  · have : ∀ (z : ℂ), AnalyticAt ℂ (h7.R q hq0 h2mq) z := by fun_prop
    apply AnalyticOn.mono (f:=(h7.R q hq0 h2mq)) (s:=(evaluationPoints_compl h7))
    · apply analyticOn_univ.mpr fun x a ↦ this x
    simp only [Set.subset_univ]
  · refine AnalyticOn.zpow (AnalyticOn.sub analyticOn_id analyticOn_const) fun z hz ↦ ?_
    exact sub_ne_zero_of_mem_evaluationPoints_compl h7 hz _
  · apply Finset.analyticOn_fun_prod
    intros u hu
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hu
    apply AnalyticOn.fun_pow
    refine AnalyticOn.div (analyticOn_const) ?_ ?_
    · refine DifferentiableOn.analyticOn ?_ (S_U_isOpen h7)
      fun_prop
    · exact fun z hz ↦ sub_ne_zero_of_mem_evaluationPoints_compl h7 hz ⟨u, hu.1⟩

lemma auxiliaryRemainderRestricted_AnalyticAt (z : ℂ) (hz : z ∈ evaluationPoints_compl h7) :
    AnalyticAt ℂ (h7.auxiliaryRemainderRestricted q hq0 h2mq) z :=
  AnalyticOn.analyticAt (f:=(h7.auxiliaryRemainderRestricted q hq0 h2mq)) (z := z)
    (s := evaluationPoints_compl h7)
    (auxiliaryRemainderRestricted_analyticOn_evaluationPoints_compl h7 q hq0 h2mq)
    (hU:= S.U_nhds h7 z hz)

def auxRemainderAtL0 : ℂ → ℂ := fun z ↦
  (h7.analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq)) z * ((h7.r q hq0 h2mq).factorial)  *
    (∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
    (((h7.l₀' q hq0 h2mq +1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq))

def auxRemainderAtL (l' : Fin (h7.m)) : ℂ → ℂ := fun z ↦
  (h7.analyticExtensionR q hq0 h2mq l') z *
    (h7.r q hq0 h2mq).factorial *
    ((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq) : ℤ)) *
    (∏ k' ∈ (Finset.range (h7.m) \ ({↑(h7.l₀' q hq0 h2mq : ℕ)} ∪ {↑(l' : ℕ)})),
      (((h7.l₀' q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq)) *
    (((h7.l₀' q hq0 h2mq + 1)- (l' + 1)) ^ (h7.r q hq0 h2mq))

def S : ℂ → ℂ :=
  fun z ↦
    if H : ∃ (k' : Fin (h7.m)), z = (k' : ℂ) + 1 then
      if z = (h7.l₀' q hq0 h2mq + 1) then
        h7.auxRemainderAtL0 q hq0 h2mq z
      else
        h7.auxRemainderAtL q hq0 h2mq (H.choose) z
    else
      h7.auxiliaryRemainderRestricted q hq0 h2mq z

lemma SR_eq_SRl0 {z : ℂ} :
  z ∈ (evaluationPoints_compl h7) →
  (h7.auxRemainderAtL0 q hq0 h2mq) z = (h7.auxiliaryRemainderRestricted q hq0 h2mq) z := by
  intro hz
  let a : ℂ := (h7.l₀' q hq0 h2mq : ℂ) + 1
  have hne : z - a ≠ 0 := by
   simpa [a] using
    sub_ne_zero_of_mem_evaluationPoints_compl h7 hz (h7.l₀' q hq0 h2mq)
  have hpow :
    (z - a) ^ (h7.r q hq0 h2mq) *
    (z - a) ^ (-(h7.r q hq0 h2mq : ℤ)) = (1 : ℂ) := by
   rw [← zpow_natCast, ← zpow_add₀ hne, add_neg_cancel, zpow_zero]
  unfold auxRemainderAtL0 auxiliaryRemainderRestricted
  rw [h7.R_eq_pow_mul_analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq) z]
  calc
  (h7.analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq)) z *
    ↑((h7.r q hq0 h2mq).factorial) *
    ∏ k' ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
      (((h7.l₀' q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^
      (h7.r q hq0 h2mq)
    =
    ((z - a) ^ (h7.r q hq0 h2mq) * (z - a) ^ (-(h7.r q hq0 h2mq : ℤ))) *
      ((h7.analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq)) z *
      ↑((h7.r q hq0 h2mq).factorial) *
      ∏ k' ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
        (((h7.l₀' q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^
        (h7.r q hq0 h2mq)) := by
    simp [hpow]
    grind
  _ =
    ((z - a) ^ (h7.r q hq0 h2mq) *
      (h7.analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq)) z) *
      ↑((h7.r q hq0 h2mq).factorial) *
      (z - a) ^ (-(h7.r q hq0 h2mq : ℤ)) *
      ∏ k' ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
      (((h7.l₀' q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^
        (h7.r q hq0 h2mq) := by
    ac_rfl





--fix l+1
lemma SR_eq_SRl {z : ℂ} (l' : Fin (h7.m)) (hl : l' ≠ h7.l₀' q hq0 h2mq) :
    z ∈ (evaluationPoints_compl h7) →
    (h7.auxRemainderAtL q hq0 h2mq l') z = (h7.auxiliaryRemainderRestricted q hq0 h2mq) z := by
  intros hz
  unfold evaluationPoints_compl at *
  dsimp [auxiliaryRemainderRestricted, auxRemainderAtL]
  nth_rw 3 [mul_assoc]
  simp only [_root_.zpow_neg, zpow_natCast]
  dsimp [evaluationPoints] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists,
    not_and] at hz
  have := R_eq_pow_mul_analyticExtensionR h7 q hq0 h2mq l' z
  try simp only at this
  rw [this]; clear this
  simp only [← mul_assoc]
  nth_rw 8 [mul_comm]
  rw [mul_assoc  (h7.analyticExtensionR q hq0 h2mq (l') z) ((z - (↑↑(l') + 1)) ^ h7.r q hq0 h2mq)]
  rw [mul_comm ((z - (↑↑(l') + 1)) ^ h7.r q hq0 h2mq) ↑(h7.r q hq0 h2mq).factorial]
  unfold analyticExtensionR
  simp only [mul_assoc]
  have : l' < h7.m := by simp only [Fin.is_lt]
  have H := (hz l' this)
  try simp only at H
  have : 1 =  (z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ ↑(h7.r q hq0 h2mq) *
      (z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ (-↑((h7.r q hq0 h2mq) : ℤ)) := by
    simp only [_root_.zpow_neg, zpow_natCast]
    symm
    apply Complex.mul_inv_cancel
    intros Hz
    simp only [pow_eq_zero_iff', ne_eq] at Hz
    have : (h7.l₀' q hq0 h2mq) < h7.m :=  by simp only [Fin.is_lt]
    have H := hz  ↑((h7.l₀' q hq0 h2mq)) this
    apply H
    rw [sub_eq_add_neg] at Hz
    rw [add_eq_zero_iff_eq_neg] at Hz
    simp only [neg_neg] at Hz
    symm
    rw [Hz.1]
  split
  · rename_i H
    rw [H]
    simp only [add_sub_add_right_eq_sub, sub_self,
      mul_eq_mul_left_iff, Nat.cast_eq_zero]
    left; left
    rw [zero_pow]
    simp only [zero_mul, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', ne_eq]
    right
    right
    constructor
    by_contra HR
    apply hl
    (expose_names; exact False.elim (hz (↑l') this_1 (id (Eq.symm H))))
    (expose_names; exact fun a ↦ hz (↑l') this_1 (id (Eq.symm H)))
    (expose_names; exact fun a ↦ hz (↑l') this_1 (id (Eq.symm H)))
  · nth_rw 6 [← mul_assoc]
    nth_rw 5 [← mul_assoc]
    nth_rw 8 [mul_comm]
    simp only [mul_assoc]
    simp only [mul_eq_mul_left_iff, inv_eq_zero,
      pow_eq_zero_iff', ne_eq, Nat.cast_eq_zero]
    left
    left
    left
    rw [mul_comm]
    nth_rw 2 [mul_comm]
    clear this
    have H :=  Finset.prod_union
      (s₁:= Finset.range h7.m \ ({↑(h7.l₀' q hq0 h2mq) }∪ {↑l'}))
      (s₂:= {↑l'})
      (f:= fun k' ↦ ((↑↑(h7.l₀' q hq0 h2mq) + 1 -
       (↑k' + 1)) / (z - (↑k' + 1))) ^ h7.r q hq0 h2mq)
      (by aesop)
    have : Finset.range h7.m \ ({↑(h7.l₀' q hq0 h2mq) }∪ {↑l'}) ∪ {↑l'}
     = Finset.range h7.m \ {(↑(h7.l₀' q hq0 h2mq))} := by grind

    simp only [Finset.prod_singleton] at H
    rw [this] at H
    rw [H]; clear H this
    rw [mul_comm]
    simp only [mul_assoc]
    congr
    simp only [add_sub_add_right_eq_sub]
    rw [← inv_mul_eq_div, mul_pow, mul_comm]
    simp only [← mul_assoc]
    rw [← mul_pow, mul_inv_cancel₀]
    · simp only [one_pow, one_mul]
    grind only


lemma S_eq_restricted_of_mem_compl {z : ℂ} :
  z ∈ (evaluationPoints_compl h7) →
  h7.auxiliaryRemainderRestricted q hq0 h2mq z = h7.S q hq0 h2mq z := by
  intros hz
  unfold evaluationPoints_compl at *
  unfold S
  split
  · rename_i H1
    exact (hz (h7.mem_evaluationPoints_iff |>.mpr H1)).elim
  · rfl

lemma dist_nat_cast_lt_one (n m : ℕ) : dist (n : ℂ) (m : ℂ) < 1 ↔ n = m := by
  apply Iff.intro
  rw [Complex.dist_eq]
  by_cases H : m ≤ n
  · have : norm (((n : ℂ)) - (m : ℂ)) = (n - m : ℕ) := by
     norm_cast
    rw [this]
    simp only [Nat.cast_lt_one]
    intros H'
    grind
  · have : norm (((n : ℂ)) - (m : ℂ)) = norm ((m : ℂ) - (n : ℂ)) := by
      calc _ = norm (-((m : ℂ) - (n : ℂ))) := ?_
           _ = norm (((m : ℂ)) - (n : ℂ)) := ?_
      · simp only [neg_sub]
      · symm
        rw [← norm_neg]
    rw [this]
    have : norm (((m : ℂ)) - (n : ℂ)) = (m - n : ℕ) := by
     simp only [not_le] at H
     have : n ≤ m := by grind
     norm_cast
    rw [this]
    simp only [Nat.cast_lt_one]
    intros H'
    grind
  · aesop


--SR_analytic_S.U follow this for srl0 too
lemma SRl_is_analytic_at_ball_of_radius_one (l' : Fin (h7.m)) (hl : l' ≠ h7.l₀' q hq0 h2mq) :
  AnalyticOn ℂ (h7.auxRemainderAtL q hq0 h2mq l') (Metric.ball ((l' : ℂ) + 1) 1) := by
  unfold auxRemainderAtL
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mul ?_ ?_
    · apply AnalyticOn.mul ?_ ?_
      · have := h7.analyticExtensionR_analyticAt q hq0 h2mq
        try simp only at this
        apply AnalyticOn.mul (AnalyticOnNhd.analyticOn fun x a ↦ this l' x) analyticOn_const
      · apply AnalyticOn.fun_zpow
        · apply AnalyticOn.mono
          · refine analyticOn_univ_iff_differentiable.mpr ?_
            refine (fun_sub_iff_left ?_).mpr ?_
            simp only [differentiable_const]
            simp only [differentiable_fun_id]
          · exact fun ⦃a⦄ a ↦ trivial
        · intros z hz
          simp only [Metric.mem_ball] at hz
          apply sub_ne_zero_of_ne
          intro H
          rw [H] at hz
          simp only [dist_add_right] at hz
          have : ((h7.l₀' q hq0 h2mq : ℕ) : ℂ)≠ ((l' : ℕ) : ℂ) := by
            intros HC
            apply hl
            simp only [Nat.cast_inj] at HC
            symm
            aesop
          rw [← dist_pos] at this
          have Hdist := ( dist_nat_cast_lt_one ((h7.l₀' q hq0 h2mq)) ↑↑l').1
          have Hdist := Hdist hz
          rw [Hdist] at this
          aesop
    · apply Finset.analyticOn_fun_prod
      intros u hu
      try simp only at hu
      apply AnalyticOn.fun_pow (AnalyticOn.div analyticOn_const
         (DifferentiableOn.analyticOn (by fun_prop) Metric.isOpen_ball) (fun x hx ↦ ?_))
      · simp only [Metric.mem_ball] at hx
        simp only [Finset.mem_union, Finset.mem_sdiff,
          Finset.mem_range, Finset.mem_singleton] at hu
        cases' hu with h1 h2
        · intros HC
          simp only [not_or] at h2
          obtain ⟨hu, hul0⟩ := h2
          rw [sub_eq_zero] at HC
          rw [HC] at hx
          simp only [dist_add_right] at hx
          rw [← ne_eq] at *
          have Hdist := ( dist_nat_cast_lt_one u ↑↑l').1
          have Hdist := Hdist hx
          rw [Hdist] at hx
          simp only [dist_self, zero_lt_one] at hx
          exact hul0 Hdist
  · exact analyticOn_const


lemma SRl0_is_analytic_at_ball_of_radius_one :
  AnalyticOn ℂ (h7.auxRemainderAtL0 q hq0 h2mq)
    (Metric.ball (h7.l₀' q hq0 h2mq + 1) 1) := by
  unfold Setup.auxRemainderAtL0
  refine AnalyticOn.mul ?_ ?_
  · refine AnalyticOn.mul ?_ analyticOn_const
    have hA := h7.analyticExtensionR_analyticAt q hq0 h2mq
    exact AnalyticOnNhd.analyticOn (fun z hz ↦ hA (h7.l₀' q hq0 h2mq) z)
  · apply Finset.analyticOn_fun_prod
    intro u hu
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hu
    refine (AnalyticOn.fun_pow (𝕜 := ℂ) (n := h7.r q hq0 h2mq) ?_)
    refine AnalyticOn.div (𝕜 := ℂ) analyticOn_const
      (AnalyticOn.sub analyticOn_id analyticOn_const) ?_
    intro z hz hzero
    have hz1 : dist ((u : ℂ) + 1) ((h7.l₀' q hq0 h2mq : ℂ) + 1) < 1 := by
      have hz' : z = (u : ℂ) + 1 := sub_eq_zero.mp hzero
      simpa [Metric.mem_ball, hz'] using hz
    have hz0 : dist (u : ℂ) (h7.l₀' q hq0 h2mq : ℂ) < 1 := by
      simpa [dist_add_right] using hz1
    have hu' : u = (h7.l₀' q hq0 h2mq : ℕ) :=
      (dist_nat_cast_lt_one u (h7.l₀' q hq0 h2mq : ℕ)).1 hz0
    exact hu.2 hu'

lemma AnalyticAtEq (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ) :
  (hU : U ∈ nhds z) → z ∈ U → (∀ z ∈ U, f z = g z) →
     AnalyticAt ℂ f z → AnalyticAt ℂ g z := by
    intros hU _ hfg hf
    exact hf.congr (Filter.eventually_of_mem hU hfg)

lemma holS :
  ∀ z, AnalyticAt ℂ (h7.S q hq0 h2mq) z := by
  intro z
  by_cases H : ∃ k' : Fin h7.m, z = (k' : ℂ) + 1
  · rcases H with ⟨l', hl'⟩
    by_cases Hzl0 : z = (h7.l₀' q hq0 h2mq : ℂ) + 1
    · refine AnalyticAtEq
        (f := h7.auxRemainderAtL0 q hq0 h2mq)
        (g := h7.S q hq0 h2mq)
        (U := Metric.ball ((h7.l₀' q hq0 h2mq : ℂ) + 1) 1)
        (z := z)
        ?_ ?_ ?_ ?_
      · rw [Hzl0]
        exact Metric.ball_mem_nhds _ zero_lt_one
      · rw [Hzl0]
        simp [Metric.mem_ball]
      · intro w hw
        by_cases hw0 : w = (h7.l₀' q hq0 h2mq : ℂ) + 1
        · unfold S
          let Hw : ∃ k' : Fin h7.m, w = (k' : ℂ) + 1 := ⟨h7.l₀' q hq0 h2mq, hw0⟩
          simp [Hw, hw0]
        · have hwCompl : w ∈ evaluationPoints_compl h7 := by
            intro hwEval
            rcases (h7.mem_evaluationPoints_iff).1 hwEval with ⟨k, rfl⟩
            have hdist : dist (k : ℂ) (h7.l₀' q hq0 h2mq : ℂ) < 1 := by
              have : dist ((k : ℂ) + 1) ((h7.l₀' q hq0 h2mq : ℂ) + 1) < 1 := by
                simpa [Metric.mem_ball] using hw
              simpa [dist_add_right] using this
            have hk : (k : ℕ) = (h7.l₀' q hq0 h2mq : ℕ) :=
              (dist_nat_cast_lt_one (k : ℕ) (h7.l₀' q hq0 h2mq : ℕ)).1 hdist
            exact hw0 (by simpa [hk])
          exact (h7.SR_eq_SRl0 q hq0 h2mq hwCompl).trans
            (h7.S_eq_restricted_of_mem_compl q hq0 h2mq hwCompl)
      · have hU :
          Metric.ball ((h7.l₀' q hq0 h2mq : ℂ) + 1) 1 ∈ nhds z := by
          simpa [Hzl0] using
            (Metric.ball_mem_nhds ((h7.l₀' q hq0 h2mq : ℂ) + 1) zero_lt_one)
        exact AnalyticOn.analyticAt
          (f := h7.auxRemainderAtL0 q hq0 h2mq)
          (s := Metric.ball ((h7.l₀' q hq0 h2mq : ℂ) + 1) 1)
          (z := z)
          (h7.SRl0_is_analytic_at_ball_of_radius_one q hq0 h2mq)
          (hU := hU)
    · refine AnalyticAtEq
        (f := h7.auxRemainderAtL q hq0 h2mq l')
        (g := h7.S q hq0 h2mq)
        (U := Metric.ball ((l' : ℂ) + 1) 1)
        (z := z)
        ?_ ?_ ?_ ?_
      · rw [hl']
        exact Metric.ball_mem_nhds _ zero_lt_one
      · rw [hl']
        simp [Metric.mem_ball]
      · intro w hw
        by_cases hw1 : w = (l' : ℂ) + 1
        · unfold S
          let Hw : ∃ k' : Fin h7.m, w = (k' : ℂ) + 1 := ⟨l', hw1⟩
          have hw_ne_l0 : w ≠ (h7.l₀' q hq0 h2mq : ℂ) + 1 := by
            intro hw0
            apply Hzl0
            calc
              z = (l' : ℂ) + 1 := hl'
              _ = w := by simpa [hw1]
              _ = (h7.l₀' q hq0 h2mq : ℂ) + 1 := hw0
          have hchoose : Hw.choose = l' := by
            apply Fin.ext
            have hEq : ((Hw.choose : Fin h7.m) : ℂ) + 1 = (l' : ℂ) + 1 := by
              calc
                ((Hw.choose : Fin h7.m) : ℂ) + 1 = w := by simpa using Hw.choose_spec.symm
                _ = (l' : ℂ) + 1 := hw1
            have hNat : (Hw.choose : ℕ) = (l' : ℕ) := by
              have := congrArg (fun x : ℂ => x - 1) hEq
              simpa using this
            simpa using hNat
          simp [Hw, hw_ne_l0, hchoose]
        · have hwCompl : w ∈ evaluationPoints_compl h7 := by
            intro hwEval
            rcases (h7.mem_evaluationPoints_iff).1 hwEval with ⟨k, rfl⟩
            have hdist : dist (k : ℂ) (l' : ℂ) < 1 := by
              have : dist ((k : ℂ) + 1) ((l' : ℂ) + 1) < 1 := by
                simpa [Metric.mem_ball] using hw
              simpa [dist_add_right] using this
            have hk : (k : ℕ) = (l' : ℕ) :=
              (dist_nat_cast_lt_one (k : ℕ) (l' : ℕ)).1 hdist
            exact hw1 (by simpa [hk])
          have hl_ne : l' ≠ h7.l₀' q hq0 h2mq := by
            intro hEq
            apply Hzl0
            simpa [hl', hEq]
          exact (h7.SR_eq_SRl q hq0 h2mq l' hl_ne hwCompl).trans
            (h7.S_eq_restricted_of_mem_compl q hq0 h2mq hwCompl)
      · have hl_ne : l' ≠ h7.l₀' q hq0 h2mq := by
          intro hEq
          apply Hzl0
          simp [hl', hEq]
        have hU : Metric.ball ((l' : ℂ) + 1) 1 ∈ nhds z := by
          rw [hl']
          exact Metric.ball_mem_nhds _ zero_lt_one
        exact (h7.SRl_is_analytic_at_ball_of_radius_one q hq0 h2mq l' hl_ne).analyticAt hU
  · have hzCompl : z ∈ evaluationPoints_compl h7 := by
      intro hzEval
      exact H ((h7.mem_evaluationPoints_iff).1 hzEval)
    refine AnalyticAtEq
      (f := h7.auxiliaryRemainderRestricted q hq0 h2mq)
      (g := h7.S q hq0 h2mq)
      (U := evaluationPoints_compl h7)
      (z := z)
      ?_ ?_ ?_ ?_
    · exact S.U_nhds h7 z hzCompl
    · exact hzCompl
    · intro w hw
      exact h7.S_eq_restricted_of_mem_compl q hq0 h2mq hw
    · exact h7.auxiliaryRemainderRestricted_AnalyticAt q hq0 h2mq z hzCompl


lemma hcauchy :
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(0, h7.m * (1 + (h7.r q hq0 h2mq / q))),
    (z - (h7.l₀' q hq0 h2mq + 1 : ℂ))⁻¹ * (h7.S q hq0 h2mq) z) =
    (h7.S q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) := by
  apply two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := (∅ : Set ℂ))
  · simpa using (Set.countable_empty : Set.Countable (∅ : Set ℂ))
  · have hmpos : (0 : ℝ) < h7.m := by
      simp only [Nat.cast_pos]
      exact Nat.zero_lt_succ (2 * h7.h + 1)
    have hdivpos : (0 : ℝ) < (h7.r q hq0 h2mq : ℝ) / q := by
      exact div_pos (by exact_mod_cast r_qt_0 h7 q hq0 h2mq) (by exact_mod_cast hq0)
    have hmul : (h7.m : ℝ) < h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / q) := by
      have h1 : (1 : ℝ) < 1 + (h7.r q hq0 h2mq : ℝ) / q := by linarith
      simpa [one_mul] using mul_lt_mul_of_pos_left h1 hmpos
    have hle : (((h7.l₀' q hq0 h2mq : ℕ) + 1 : ℕ) : ℝ) ≤ h7.m := by
      exact_mod_cast Nat.succ_le_of_lt (h7.l₀' q hq0 h2mq).isLt
    have hz : ‖(h7.l₀' q hq0 h2mq + 1 : ℂ)‖ < h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / q) := by
      norm_cast
      exact lt_of_le_of_lt hle hmul
    simpa [Metric.mem_ball, dist_zero_right] using hz
  · intro x hx
    simpa using
      (DifferentiableAt.differentiableWithinAt (AnalyticAt.differentiableAt (holS h7 q hq0 h2mq x))).continuousWithinAt
  · intro x hx
    simpa using AnalyticAt.differentiableAt (holS h7 q hq0 h2mq x)


lemma S_eq_SR_on_circle : ∀ (z : ℂ) (hz : z ∈ Metric.sphere 0
    (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)))),
  h7.S q hq0 h2mq z = h7.auxiliaryRemainderRestricted q hq0 h2mq z := by
  intros z hz
  unfold S
  split
  · rename_i H1
    obtain ⟨k',hk'⟩ := H1
    have : norm z ≤ h7.m := by
      rw [hk']
      norm_cast
      apply Fin.isLt
    simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [hz] at this
    by_contra HC
    apply absurd (this)
    simp only [not_le]
    nth_rw 1 [← mul_one (a:=(h7.m:ℝ))]
    apply mul_lt_mul' (le_refl _)
    · simp only [lt_add_iff_pos_right]
      refine div_pos ?_ ?_
      · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
      · simp only [Nat.cast_pos]; exact hq0
    · simp only [zero_le_one]
    · simp only [Nat.cast_pos];exact Nat.zero_lt_succ (2 * h7.h + 1)
  · rfl

end Setup

end

end


/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/


--public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAnalytic

section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
  (t : Fin (q * q)) (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup

def c₉ : ℝ := Real.exp (|1 + ‖h7.β‖| *  ‖Complex.log h7.α‖ * (↑h7.m : ℝ))

lemma c9_pos : 0 < h7.c₉ := Real.exp_pos _

lemma c9_nonneg : 0 ≤ h7.c₉ := by
  rw [le_iff_lt_or_eq]
  left
  exact Real.exp_pos _

lemma c9_gt_1 : 1 ≤ h7.c₉ := by
  apply Real.one_le_exp
  positivity

def c₁₁ : ℝ := (↑h7.m ^ (h7.m - 1))

lemma one_le_c11 : 1 ≤ h7.c₁₁ :=
  (one_le_pow_iff_of_nonneg (by simp) (by unfold m; grind)).mpr (mod_cast h7.one_le_m)

lemma c11_nonneg : 0 ≤ h7.c₁₁ := le_trans zero_le_one (one_le_c11 h7)

variable [DecidableEq (h7.K →+* ℂ)]

variable {z : ℂ} {l₀ : ℝ} (hz : (z : ℂ) ∈ Metric.sphere 0 (h7.m * (1 + (h7.r q hq0 h2mq / q))))
  (hl0 : (l₀ : ℝ) < (h7.m : ℝ) * (1 + h7.r q hq0 h2mq / q))

lemma norm_hz (hz : z ∈ Metric.sphere 0 ((h7.m : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)))) :
    ‖z‖ ≤ ‖(h7.m : ℝ)‖ * ‖1 + (h7.r q hq0 h2mq : ℝ) / (q: ℝ)‖ := by
  simp only [mem_sphere_iff_norm, sub_zero] at hz
  rw [hz, ← norm_mul, Real.norm_eq_abs]
  exact le_abs_self _



include hz in
lemma abs_Rb : norm ((h7.R q hq0 h2mq) z) ≤ (q * q) * ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) *
    (h7.r q hq0 h2mq) ^ (((h7.r q hq0 h2mq : ℝ ) + 1) / 2)) *
    (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) := by
  calc _ ≤ ∑ t, ((house ((((algebraMap (𝓞 h7.K) h7.K)
             ((h7.η q hq0 h2mq) t))))) * ‖cexp (h7.ρ q t * z)‖) := ?_
       _ ≤ ∑ t : Fin (q*q), (h7.c₄ ^ (h7.n q : ℝ)) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2)
           * Real.exp ‖(h7.ρ q t * z)‖ := ?_
       _ ≤ ∑ t : Fin (q*q), (h7.c₄ ^ (h7.n q : ℝ)) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) *
           Real.exp (norm ((q : ℝ) * (1 + norm h7.β) * ‖Complex.log h7.α‖ * (h7.m : ℝ) *
           ((1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))))) := ?_
       _ ≤ (q * q) * ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) * (h7.r q hq0 h2mq) ^
           (((h7.r q hq0 h2mq : ℝ ) + 1) / 2)) * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) := ?_
  · unfold R
    simp only [canonicalEmbedding.apply_at]
    trans
    · apply norm_sum_le
    simp only [Complex.norm_mul]
    apply Finset.sum_le_sum
    intros i hi
    simp only [norm_pos_iff, ne_eq, exp_ne_zero, not_false_eq_true, mul_le_mul_iff_left₀]
    apply norm_embedding_le_house
  · refine sum_le_sum ?_
    intro i hi
    refine mul_le_mul ?_ ?_ ?_ ?_
    · simpa using (house_eta_le_c₄_pow h7 q hq0 i h2mq)
    · simpa using (Complex.norm_exp_le_exp_norm (h7.ρ q i * z))
    · simp
    · apply mul_nonneg
      · exact Real.rpow_nonneg (le_trans zero_le_one (h7.one_le_c₄)) _
      · exact Real.rpow_nonneg (by simpa using (Nat.cast_nonneg (h7.n q))) _
  · apply sum_le_sum
    intros i hi
    apply mul_le_mul
    · have lemma82 := house_eta_le_c₄_pow h7 q hq0 i h2mq
      unfold house at lemma82
      apply Preorder.le_refl _
    · unfold ρ
      simp only [nsmul_eq_mul, norm_mul, Real.exp_le_exp]
      calc
           _ ≤  (‖↑(a q i : ℂ)‖ + ‖↑(b q i) * h7.β‖) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ ≤  (‖(q : ℤ)‖ + ‖q * h7.β‖) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ ≤ (‖(q : ℤ)‖ + ((‖↑(q : ℤ)‖ * ‖h7.β‖))) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ = (‖(q : ℤ)‖ * ((1 + ‖h7.β‖))) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ ≤ ‖(q : ℤ)‖ * ‖1 + ‖h7.β‖‖ * ‖Complex.log h7.α‖* ‖(↑h7.m : ℝ)‖ *
               ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ := ?_

           _ ≤ ‖(q : ℝ)‖ * ‖1 + ‖h7.β‖‖ * ‖Complex.log h7.α‖ * ‖(↑h7.m : ℝ)‖ *
               ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ := by
                simp only [mul_assoc]; simp_all
      · gcongr; apply norm_add_le
      · gcongr
        · simp only [RCLike.norm_natCast, _root_.norm_natCast, Nat.cast_le]
          exact ((finProdFinEquiv.symm.toFun i).1).isLt
        · simp only [Complex.norm_mul, RCLike.norm_natCast]
          apply mul_le_mul ?_ (by rfl) (by simp) (by simp)
          · simp only [Nat.cast_le]
            exact ((finProdFinEquiv.symm.toFun i).2).isLt
      · gcongr; simp
      · congr
        nth_rw 1 [← mul_one (a:=(‖(q : ℤ)‖))]
        rw [mul_add]
      · simp only [mul_assoc]
        apply mul_le_mul
        · simp only [le_refl]
        · gcongr
          · exact le_abs_self (1 + ‖h7.β‖)
          · exact h7.norm_hz q hq0 h2mq hz
        · positivity
        · simp only [Int.norm_natCast, Nat.cast_nonneg]
      simp only [Real.norm_eq_abs]
      simp only [Nat.abs_cast, abs_norm, le_refl]
    · exact Real.exp_nonneg ‖h7.ρ q i * z‖
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        exact le_trans zero_le_one (h7.one_le_c₄)
      · apply Real.rpow_nonneg
        simp only [Nat.cast_nonneg]
  · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    apply mul_le_mul (by rfl) ?_ ?_ (by positivity)
    · apply mul_le_mul
      · apply mul_le_mul
        · simp only [Real.rpow_natCast]
          refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
          left
          exact ⟨one_le_c₄ h7, n_le_r h7 q hq0 h2mq⟩
        · calc _ ≤ (h7.r q hq0 h2mq : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) := ?_
               _ ≤ (h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq :ℝ) + 1) / 2) := ?_
          · apply Real.rpow_le_rpow
            · simp only [Nat.cast_nonneg]
            · simp only [Nat.cast_le]; exact n_le_r h7 q hq0 h2mq
            · refine div_nonneg ?_ ?_
              · norm_cast
                simp
              · simp only [Nat.ofNat_nonneg]
          · apply Real.rpow_le_rpow_of_exponent_le
            · simp only [Nat.one_le_cast]
              trans
              · apply h7.one_le_n q hq0 h2mq
              exact n_le_r h7 q hq0 h2mq
            · refine (div_le_div_iff_of_pos_right ?_).mpr ?_
              · simp only [Nat.ofNat_pos]
              · simp only [add_le_add_iff_right, Nat.cast_le]
                exact n_le_r h7 q hq0 h2mq
        · apply Real.rpow_nonneg; simp only [Nat.cast_nonneg]
        · apply Real.rpow_nonneg; exact le_trans zero_le_one (h7.one_le_c₄)
      · rw [Real.rpow_def_of_pos (x:= h7.c₉)]
        · calc _ ≤ Real.exp ( |1 + ‖h7.β‖| *  ‖Complex.log h7.α‖ * (↑h7.m) *
                   |(q : ℝ) * (1 + ↑(h7.r q hq0 h2mq) / ↑q)|) := ?_
               _ ≤ Real.exp (Real.log h7.c₉ * (↑(h7.r q hq0 h2mq) + ↑q)) := ?_

          · simp only [Real.exp_le_exp]
            rw [norm_mul];rw [norm_mul];rw [norm_mul];rw [norm_mul]
            have : ‖(q : ℝ)‖ * ‖1 + ‖h7.β‖‖ *  ‖‖Complex.log h7.α‖‖ * ‖(h7.m : ℝ)‖ *
                   ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ =
                   ‖1 + ‖h7.β‖‖ *  ‖‖Complex.log h7.α‖‖ * ‖(h7.m : ℝ)‖ *
                   ‖(q : ℝ)‖ * ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ := by
                simp only [Real.norm_eq_abs, mul_eq_mul_right_iff, abs_eq_zero]
                left
                rw [mul_assoc, mul_assoc, mul_comm]
                simp only [mul_assoc]
            simp only [mul_assoc] at this
            simp only [mul_assoc]
            rw [this]
            simp only [Real.norm_eq_abs]
            rw [← abs_mul]
            have : (q : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / q) =
                       (((q : ℝ) + (h7.r q hq0 h2mq : ℝ))) := by
                        ring_nf
                        simp only [mul_assoc]
                        nth_rw 2 [mul_comm]
                        simp only [← mul_assoc]
                        simp only [add_right_inj]
                        rw [mul_inv_cancel₀]
                        simp only [one_mul]
                        simp only [ne_eq, Nat.cast_eq_zero]
                        rw [← ne_eq]
                        exact Nat.ne_zero_of_lt hq0
            rw [this]
            simp
          · simp only [mul_assoc, Real.exp_le_exp]
            have : |((h7.r q hq0 h2mq) + q : ℝ)| = (↑(h7.r q hq0 h2mq) + ↑q) := by
              simp only [abs_eq_self]; positivity
            rw [← this]
            simp only [c₉, Real.log_exp, mul_assoc]
            gcongr
            have : (q : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / q) =
                       (((q : ℝ) + (h7.r q hq0 h2mq : ℝ))) := by
                        ring_nf
                        simp only [mul_assoc]
                        nth_rw 2 [mul_comm]
                        simp only [← mul_assoc]
                        simp only [add_right_inj]
                        rw [mul_inv_cancel₀]
                        · simp only [one_mul]
                        simp only [ne_eq, Nat.cast_eq_zero]
                        rw [← ne_eq]
                        exact Nat.ne_zero_of_lt hq0
            rw [this]
            rw [add_comm]
        · unfold c₉; apply Real.exp_pos
      · positivity
      · apply mul_nonneg (Real.rpow_nonneg _ _) (Real.rpow_nonneg (by positivity) _)
        exact le_trans zero_le_one (h7.one_le_c₄)
    · simp only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs]
      apply mul_nonneg
        (mul_nonneg (pow_nonneg (le_trans zero_le_one (h7.one_le_c₄)) _) (by positivity))
        (Real.exp_nonneg _)

def c₁₀ : ℝ := (2*h7.m* h7.c₄* h7.c₉* h7.c₉^(2*h7.m : ℝ))

lemma c10_nonneg : 0 ≤ h7.c₁₀ := by
  unfold c₁₀
  apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (le_trans zero_le_one (h7.one_le_c₄))) (c9_nonneg h7))
  · apply Real.rpow_nonneg; exact c9_nonneg h7

lemma one_le_c10 : 1 ≤ h7.c₁₀ := by
  unfold c₁₀
  have hm : (1 : ℝ) ≤ h7.m := by exact_mod_cast h7.one_le_m
  have h1 : (1 : ℝ) ≤ (2 : ℝ) * h7.m := by nlinarith
  have h2 : 1 ≤ (2 : ℝ) * h7.m * h7.c₄ := by
    simpa [mul_assoc] using one_le_mul_of_one_le_of_one_le h1 h7.one_le_c₄
  have h3 : 1 ≤ (2 : ℝ) * h7.m * h7.c₄ * h7.c₉ := by
    simpa [mul_assoc] using one_le_mul_of_one_le_of_one_le h2 h7.c9_gt_1
  have h4 : 1 ≤ h7.c₉ ^ (2 * h7.m : ℝ) := by
    exact Real.one_le_rpow (h7.c9_gt_1) (by positivity)
  simpa [mul_assoc] using one_le_mul_of_one_le_of_one_le h3 h4

lemma abs_R : (q * q) * ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) * (h7.r q hq0 h2mq) ^
      (((h7.r q hq0 h2mq : ℝ ) + 1) / 2)) * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) ≤
      (h7.c₁₀)^ (h7.r q hq0 h2mq : ℝ) * (h7.r q hq0 h2mq : ℝ) ^
      (1/2 * ((h7.r q hq0 h2mq) + 3 : ℝ)) := by
    calc _ ≤ (2 * h7.m : ℝ )^(h7.r q hq0 h2mq : ℝ) *(h7.r q hq0 h2mq : ℝ)*
             ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) * (h7.r q hq0 h2mq : ℝ) ^
             (((h7.r q hq0 h2mq : ℝ) + 1) / 2)) * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) := ?_
         _ ≤ (h7.c₁₀ ^ (h7.r q hq0 h2mq : ℝ)) * (h7.r q hq0 h2mq : ℝ) ^
             (1/2 * (h7.r q hq0 h2mq + 3) : ℝ) := ?_
    · apply mul_le_mul (eq6b.extracted_1_1 h7 q hq0 h2mq) le_rfl ?_ (by positivity)
      (apply mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one h7.one_le_c₄) _)
        (by positivity)) (Real.rpow_nonneg (c9_nonneg h7) _))
    · unfold c₁₀
      nth_rw 2 [Real.mul_rpow _ (by apply Real.rpow_nonneg (c9_nonneg h7) ((2 * ↑h7.m : ℝ)))]
      · nth_rw 2 [Real.mul_rpow _ (by grind [c9_nonneg h7])]
        · nth_rw 2 [Real.mul_rpow (by positivity) (by apply le_trans zero_le_one (h7.one_le_c₄))]
          · simp only [← mul_assoc, mul_assoc ((2*h7.m : ℝ) ^ (h7.r q hq0 h2mq : ℝ))
                (h7.r q hq0 h2mq : ℝ) (h7.c₄ ^ (h7.r q hq0 h2mq : ℝ)),
                mul_comm (h7.r q hq0 h2mq : ℝ) (h7.c₄ ^ (h7.r q hq0 h2mq : ℝ))]
            simp only [mul_assoc]; nth_rw 3 [← mul_assoc]
            apply mul_le_mul (by rfl) ?_ ?_ (by positivity)
            · apply mul_le_mul (by simp) ?_
                (mul_nonneg (by positivity) (Real.rpow_nonneg (c9_nonneg h7) _))
                (Real.rpow_nonneg (le_trans zero_le_one (h7.one_le_c₄)) _)
              · rw [Real.rpow_add (by grind [c9_pos h7]), mul_comm, mul_assoc]
                · apply mul_le_mul (by rfl) ?_ ?_ (Real.rpow_nonneg (c9_nonneg h7) _)
                  · apply mul_le_mul ?_ ?_ (by positivity)
                      (by apply Real.rpow_nonneg (Real.rpow_nonneg (c9_nonneg h7) _) _)
                    · rw [← Real.rpow_mul (c9_nonneg h7)]
                      · apply Real.rpow_le_rpow_of_exponent_le (c9_gt_1 h7)
                        · exact mod_cast le_trans (h7.q_le_two_mn q h2mq)
                           (mul_le_mul (by rfl) (n_le_r h7 q hq0 h2mq) (by positivity)
                           (by positivity))
                    · nth_rw 1 [← Real.rpow_one ((h7.r q hq0 h2mq))]
                      rw [← Real.rpow_add]
                      · exact Real.rpow_le_rpow_of_exponent_le
                          (by simp; grind [r_qt_0 h7 q hq0 h2mq]) (by ring_nf; simp)
                      · simp; grind [r_qt_0 h7 q hq0 h2mq]
                  · apply mul_nonneg (Real.rpow_nonneg (c9_nonneg h7) _) (mul_nonneg (by simp)
                      (by apply Real.rpow_nonneg (by simp)))
            · apply mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (h7.one_le_c₄)) _)
               (mul_nonneg (by positivity) (Real.rpow_nonneg (c9_nonneg h7) _))
        · apply mul_nonneg (by positivity) (le_trans zero_le_one (h7.one_le_c₄))
      · apply mul_nonneg (mul_nonneg (by positivity) (le_trans zero_le_one (h7.one_le_c₄)))
          (c9_nonneg h7)

lemma norm_sub_l0_lower_bound_on_sphere
    (hz : z ∈ Metric.sphere 0 ((h7.m : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)))) :
    (h7.m * (h7.r q hq0 h2mq : ℝ)) / (q : ℝ) ≤ ‖z - ((h7.l₀' q hq0 h2mq : ℂ) + 1)‖ := by
  calc (h7.m * (h7.r q hq0 h2mq : ℝ)) / (q : ℝ)
    _ = (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) - h7.m : ℝ) := ?_
    _ ≤ ‖z‖ - ‖(h7.l₀' q hq0 h2mq : ℂ) + 1‖ := ?_
    _ ≤ ‖z - ((h7.l₀' q hq0 h2mq : ℂ) + 1)‖ := ?_
  · ring
  · simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [hz]
    simp only [tsub_le_iff_right]
    have : h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))
            - ((h7.l₀' q hq0 h2mq : ℝ) + 1) =
           h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))
            + (- ((h7.l₀' q hq0 h2mq : ℝ) + 1)) := rfl
    norm_cast
    simp only [Nat.cast_add, Nat.cast_one, ge_iff_le]
    rw [this, add_assoc]
    simp only [le_add_iff_nonneg_right, le_neg_add_iff_add_le, add_zero]
    exact_mod_cast Fin.isLt _
  · apply norm_sub_norm_le z

include hz in
lemma norm_z_minus_km_lower_bound_on_sphere (km : Fin (h7.m)) :
  h7.m * h7.r q hq0 h2mq / q ≤ ‖z - ((km: ℂ) + 1)‖  := by
  have hz' : ‖z‖ = h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) := by
    simpa [mem_sphere_iff_norm, sub_zero] using hz
  have hkm' : (km : ℝ) ≤ h7.m := le_of_lt (by simp [Nat.cast_lt])
  have hkm : ‖(km : ℂ)‖ ≤ (h7.m : ℝ) := by simp
  calc _ = (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) - h7.m : ℝ) := by ring
       _ = ‖z‖ - norm (h7.m : ℂ) := by simp [hz', sub_eq_add_neg]
       _ ≤ ‖z‖ - ‖(km : ℂ) + 1‖ := ?_
       _ ≤ ‖z - ((km : ℂ) + 1)‖ := by simp [norm_sub_norm_le z ((km : ℂ) + 1)]
  · simp only [tsub_le_iff_right]
    · rw [sub_eq_add_neg, ← tsub_le_iff_left, sub_eq_add_neg]
      simp only [neg_add_rev, neg_neg, add_neg_cancel_comm_assoc, RCLike.norm_natCast]
      exact_mod_cast Fin.isLt _

lemma prod_bound {ι} (f : ι → ℝ) (s : Finset ι) (C : ℝ) (hC : ∀ x ∈ s, 0 ≤ f x)
   (h : ∀ x ∈ s, f x ≤ C) :  ∏ x ∈ s, f x ≤ C ^ s.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod hC h

include hz h2mq in
lemma abs_denom : norm (((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq : ℤ))) *
  ∏ km ∈ (Finset.range (h7.m) \ {(h7.l₀' q hq0 h2mq : ℕ)}),
    (((((h7.l₀' q hq0 h2mq : ℂ) + 1 - ((km + 1 : ℂ))) / ((z - ((km + 1 : ℂ))))) ^
      (h7.r q hq0 h2mq))))
    ≤ (h7.c₁₁) ^ (h7.r q hq0 h2mq : ℝ) *
      (q / (h7.r q hq0 h2mq)) ^ (h7.m * h7.r q hq0 h2mq : ℝ) := by
  let C : ℝ := (h7.m * (↑q / (↑h7.m * ↑(h7.r q hq0 h2mq)))) ^ h7.r q hq0 h2mq
  calc
    _ ≤ norm (z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq : ℤ)) *
        norm (∏ km ∈ Finset.range (h7.m) \ {(h7.l₀' q hq0 h2mq : ℕ)},
          (((h7.l₀' q hq0 h2mq : ℕ) + 1 - ((km : ℕ) + 1)) / (z - ((km : ℕ) + 1))) ^
            (h7.r q hq0 h2mq)) := by
          simp only [_root_.zpow_neg, zpow_natCast, Complex.norm_mul, norm_inv, norm_pow, norm_prod,
            Complex.norm_div, add_sub_add_right_eq_sub, le_refl]
    _ ≤ (h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) ^ (-(h7.r q hq0 h2mq : ℤ)) *
        norm (∏ km ∈ Finset.range (h7.m) \ {(h7.l₀' q hq0 h2mq : ℕ)},
          (((h7.l₀' q hq0 h2mq : ℕ) + 1 - ((km : ℕ) + 1)) / (z - ((km : ℕ) + 1))) ^
            (h7.r q hq0 h2mq)) := by
          apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · simp only [_root_.zpow_neg, zpow_natCast]
            refine inv_anti₀ ?_ ?_
            · refine pow_pos ?_ (h7.r q hq0 h2mq)
              refine Real.sqrt_ne_zero'.mp ?_
              refine (Real.sqrt_ne_zero (by positivity)).mpr ?_
              refine div_ne_zero ?_ ?_
              · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
                refine ⟨?_, ?_⟩
                · rw [← ne_eq]
                  exact Ne.symm (Nat.zero_ne_add_one (2 * h7.h + 1))
                · simp_rw [h7.r_ne_zero]
                  aesop
              · have : 0 < (q : ℝ) := by exact_mod_cast hq0
                exact Ne.symm (ne_of_lt this)
            · refine (pow_le_pow_iff_left₀ (by positivity) (by positivity)
                (r_ne_zero h7 q hq0 h2mq)).mpr ?_
              · grind [h7.norm_z_minus_km_lower_bound_on_sphere q hq0 h2mq hz]
          · rw [norm_prod]
    _ ≤ ((h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ))⁻¹) ^ ((h7.r q hq0 h2mq : ℤ)) *
         ∏ x ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
      (‖(((h7.l₀' q hq0 h2mq : ℕ) + 1 - ((x : ℕ) + 1)) : ℂ)‖ *
       (↑q / (↑h7.m * ↑(h7.r q hq0 h2mq)))) ^ h7.r q hq0 h2mq := by
          apply mul_le_mul
          · simp only [_root_.zpow_neg, zpow_natCast]
            rw [le_iff_eq_or_lt]
            left
            ring
          · rw [norm_prod]
            apply Finset.prod_le_prod
            · intro x hx
              rw [norm_pow, ← norm_pow]
              positivity
            · intro x hx
              simp only [norm_pow]
              rw [div_eq_mul_inv]
              refine (pow_le_pow_iff_left₀ ?_ ?_ (r_ne_zero h7 q hq0 h2mq)).mpr ?_
              · positivity
              · positivity
              · simp only [Complex.norm_mul]
                apply mul_le_mul
                · simp
                · simp only [norm_inv]
                  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hx
                  let x' : Fin h7.m := ⟨x, hx.1⟩
                  have hxnorm := norm_z_minus_km_lower_bound_on_sphere h7 q hq0 h2mq hz x'
                  unfold x' at hxnorm
                  try simp only at hxnorm
                  rw [← one_div_le_one_div]
                  · simp only [one_div, inv_div, div_inv_eq_mul, one_mul]
                    exact hxnorm
                  · refine div_pos ?_ ?_
                    · norm_cast
                    · apply mul_pos
                      · unfold m
                        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
                        apply add_pos
                        · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
                          unfold h
                          exact Module.finrank_pos
                        · simp only [Nat.ofNat_pos]
                      · simp only [Nat.cast_pos]
                        exact r_qt_0 h7 q hq0 h2mq
                  · simp only [mem_sphere_iff_norm, sub_zero] at hz
                    simp only [inv_pos]
                    calc
                      _ < ↑h7.m * ↑(h7.r q hq0 h2mq) / ↑q := by
                            apply mul_pos
                            · apply mul_pos
                              · unfold m
                                simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
                                apply add_pos
                                · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
                                  unfold h
                                  exact Module.finrank_pos
                                · simp only [Nat.ofNat_pos]
                              · simp only [Nat.cast_pos]
                                exact r_qt_0 h7 q hq0 h2mq
                            · simp only [inv_pos, Nat.cast_pos]
                              exact hq0
                      _ ≤ ‖z - (↑x + 1)‖ := hxnorm
                · positivity
                · positivity
          · apply norm_nonneg
          · simp only [zpow_natCast]
            apply pow_nonneg
            simp only [inv_div]
            positivity
    _ ≤ ((h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ))⁻¹) ^ ((h7.r q hq0 h2mq : ℝ)) *
        C ^ Finset.card (Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)}) := by
          simp only [zpow_natCast, inv_div]
          apply mul_le_mul (by simp only [Real.rpow_natCast, le_refl]) ?_ (by positivity) (by positivity)
          apply prod_bound
          · intro x hx
            positivity
          · intro x hx
            unfold C
            refine (pow_le_pow_iff_left₀ (by positivity) (by positivity)
              (r_ne_zero h7 q hq0 h2mq)).mpr ?_
            simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hx
            have : ‖(h7.l₀' q hq0 h2mq : ℂ) + 1 - (↑x + 1)‖ ≤ (h7.m : ℝ) := by
              simp only [add_sub_add_right_eq_sub]
              rw [← Complex.norm_natCast]
              obtain ⟨y, hy⟩ := (h7.l₀' q hq0 h2mq)
              obtain ⟨hx1, hx2⟩ := hx
              simp only [RCLike.norm_natCast]
              by_cases H : x ≤ y
              · have : ‖(y : ℂ) - (x : ℂ)‖ = ((y - x) : ℕ) := by
                  rw [← Complex.norm_natCast]
                  norm_cast
                rw [this]
                simp only [Nat.cast_le, tsub_le_iff_right, ge_iff_le]
                linarith
              · have : ‖(y : ℂ) - (x : ℂ)‖ = ((x - y) : ℕ) := by
                  calc
                    _ = ‖(x : ℂ) - (y : ℂ)‖ := by rw [← norm_neg]; simp only [neg_sub]
                    _ = ((x - y) : ℕ) := by
                          rw [← Complex.norm_natCast]
                          norm_cast
                          grind
                rw [this]
                simp only [Nat.cast_le, tsub_le_iff_right, ge_iff_le]
                linarith
            exact mul_le_mul this (le_refl _) (by positivity) (by positivity)
    _ ≤ (h7.c₁₁) ^ (h7.r q hq0 h2mq : ℝ) *
        (q / (h7.r q hq0 h2mq)) ^ (h7.m * h7.r q hq0 h2mq : ℝ) := by
          simp only [inv_div, Real.rpow_natCast]
          have : #(Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)}) = (h7.m - 1) := by grind
          rw [this]
          unfold C
          rw [← pow_mul]
          nth_rw 5 [mul_comm]
          rw [mul_pow, pow_mul]
          simp only [← mul_assoc]
          nth_rw 2 [mul_comm]
          simp only [mul_assoc]
          rw [← pow_add]
          unfold c₁₁
          have H1 : (h7.r q hq0 h2mq + (((h7.m : ℝ) - 1) : ℝ) * h7.r q hq0 h2mq) =
              (h7.m * h7.r q hq0 h2mq : ℝ) := by ring_nf
          apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
          simp only [← Real.rpow_natCast]
          have : ↑(h7.m - 1) = (((h7.m : ℝ) - 1) : ℝ) := Nat.cast_pred (by grind)
          simp only [Nat.cast_add, Nat.cast_mul]
          rw [this, H1]
          apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          refine (div_le_div_iff_of_pos_left (by simp only [Nat.cast_pos]; exact hq0)
            (mul_pos (by simp only [Nat.cast_pos]; exact Nat.zero_lt_succ (2 * h7.h + 1))
              (by simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq))
            (by simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq)).mpr ?_
          norm_cast
          nth_rw 1 [← one_mul (a := h7.r q hq0 h2mq)]
          exact mul_le_mul (one_le_m h7) (le_refl _) (Nat.zero_le _) (Nat.zero_le _)









def c₁₂ : ℝ := (2*h7.m : ℝ)^(h7.m/2 : ℝ) * h7.c₁₀ * h7.c₁₁

lemma one_le_c12 : 1 ≤ h7.c₁₂ := by
  unfold c₁₂
  refine one_le_mul_of_one_le_of_one_le ?_ (h7.one_le_c11)
  apply one_le_mul_of_one_le_of_one_le ?_ (h7.one_le_c10)
  · refine Real.one_le_rpow ?_ (by positivity)
    · apply one_le_mul_of_one_le_of_one_le (by aesop) ?_
      · simp only [Nat.one_le_cast]; exact h7.one_le_m

lemma c12_nonneg : 0 ≤ h7.c₁₂ := by
  simpa [c₁₂] using
    mul_nonneg (mul_nonneg (by positivity) (c10_nonneg h7)) h7.c11_nonneg




lemma S_norm_bound : ∀ (hz : z ∈ Metric.sphere 0 (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)))),
  norm (h7.S q hq0 h2mq z) ≤ (h7.c₁₂)^(h7.r q hq0 h2mq : ℝ)*
    (h7.r q hq0 h2mq : ℝ) ^
              ((((h7.r q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))) := by
  intros hz
  calc
    _ = norm ((h7.R q hq0 h2mq z) * ((h7.r q hq0 h2mq).factorial) *
        (((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq) : ℤ)) *
        ∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
         (((h7.l₀' q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq)) : ℂ) := ?_

    _ = (h7.r q hq0 h2mq).factorial *
        (norm ((h7.R q hq0 h2mq) z) *
        norm ( (1/(z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (h7.r q hq0 h2mq))) *
        norm ( (∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
         (((h7.l₀' q hq0 h2mq + 1)- (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq)) : ℂ)) := ?_

    _ ≤ (h7.r q hq0 h2mq).factorial *
        ((h7.c₁₀)^(h7.r q hq0 h2mq : ℝ) *
        (h7.r q hq0 h2mq : ℝ)^(1/2*(h7.r q hq0 h2mq + 3 : ℝ)) *
        (h7.c₁₁)^(h7.r q hq0 h2mq : ℝ) *
        (q / h7.r q hq0 h2mq : ℝ)^(h7.m * h7.r q hq0 h2mq : ℝ)) := ?_

    _ ≤ (h7.c₁₂)^(h7.r q hq0 h2mq : ℝ)*(h7.r q hq0 h2mq : ℝ) ^
        ((((h7.r q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))) := ?_

  · rw [h7.S_eq_SR_on_circle q hq0 h2mq z hz]
    unfold auxiliaryRemainderRestricted
    simp only [mul_assoc]
  · nth_rewrite 2 [mul_assoc]
    nth_rewrite 2 [← mul_assoc]
    rw [mul_comm  ↑(h7.r q hq0 h2mq).factorial  ‖h7.R q hq0 h2mq z‖]
    simp only [mul_assoc, _root_.zpow_neg, zpow_natCast,
    Complex.norm_mul, norm_natCast, norm_inv, norm_pow,
      norm_prod, Complex.norm_div, one_div]
  · apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
    · rw [mul_assoc, mul_assoc]
      · apply mul_le_mul (le_trans (h7.abs_Rb q hq0 h2mq hz) (abs_R h7 q hq0 h2mq)) ?_
            (by positivity) ?_
        · simp only [one_div, norm_inv, norm_pow, norm_prod, Complex.norm_div]
          have := abs_denom h7 q hq0 h2mq hz
          simp only [_root_.zpow_neg, zpow_natCast, Complex.norm_mul, norm_inv, norm_pow, norm_prod,
            Complex.norm_div, Real.rpow_natCast] at this
          simp only [Real.rpow_natCast, ge_iff_le]
          exact this
        · apply mul_nonneg (Real.rpow_nonneg (c10_nonneg h7) _) (by positivity)
  · simp only [← mul_assoc]
    rw [mul_comm]
    unfold c₁₂
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    nth_rw 7 [mul_comm]
    simp only [← mul_assoc]
    rw [mul_comm]
    nth_rw 3 [mul_comm]
    ring_nf
    simp only [mul_assoc]
    apply mul_le_mul
    · simp only [Real.rpow_natCast, le_refl]

    · apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · calc _ ≤ (Real.sqrt (2*h7.m * h7.r q hq0 h2mq : ℝ))^(h7.r q hq0 h2mq * h7.m : ℝ) *
                 ((↑(h7.r q hq0 h2mq : ℝ))⁻¹ ^ (h7.m * h7.r q hq0 h2mq : ℝ) *
                (h7.r q hq0 h2mq).factorial *
                (h7.r q hq0 h2mq : ℝ)^((1/2 : ℝ)*(h7.r q hq0 h2mq + 3 : ℝ))) := ?_

             _≤ (Real.sqrt (2*h7.m : ℝ)^((h7.m * h7.r q hq0 h2mq : ℝ)) *
                ((h7.r q hq0 h2mq : ℝ)^(1/2 : ℝ))^((h7.m * h7.r q hq0 h2mq : ℝ)))*
                ((h7.r q hq0 h2mq : ℝ)^(h7.r q hq0 h2mq : ℝ) *
                (↑(h7.r q hq0 h2mq : ℝ))⁻¹ ^ (h7.m * h7.r q hq0 h2mq : ℝ) *
                (h7.r q hq0 h2mq : ℝ)^((1/2 : ℝ)*(h7.r q hq0 h2mq + 3 : ℝ))) :=?_

             _= ((↑h7.m * 2 : ℝ) ^ ((h7.m : ℝ) * (1 / 2: ℝ))) ^ (h7.r q hq0 h2mq : ℝ)*

              (h7.r q hq0 h2mq : ℝ) ^
              ((((h7.r q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))) := ?_

        · rw [Real.mul_rpow]
          simp only [mul_assoc]
          apply mul_le_mul
          have := h7.sqt_etc q hq0 h2mq
          have := h7.q_le_2sqrtmr q hq0 h2mq
          apply Real.rpow_le_rpow
          · simp only [Nat.cast_nonneg]
          · rw [h7.q_eq_sqrtmn q h2mq]
            simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg,
              Real.sqrt_mul, Nat.ofNat_nonneg]
            simp only [mul_assoc]
            apply mul_le_mul
            · simp only [le_refl]
            · apply mul_le_mul
              · simp only [le_refl]
              · simp only [Nat.cast_nonneg, Real.sqrt_le_sqrt_iff, Nat.cast_le]
                exact n_le_r h7 q hq0 h2mq
              · positivity
              · positivity
            · positivity
            · positivity
          · positivity
          · ring_nf
            simp only [one_div, le_refl]
          · positivity
          · positivity
          · positivity
          · positivity
        · rw [h7.sqt_etc q hq0 h2mq]
          rw [Real.mul_rpow]
          apply mul_le_mul
          · rw [mul_comm (h7.m : ℝ) (h7.r q hq0 h2mq : ℝ)]
          · rw [mul_comm]
            nth_rw 5 [mul_comm]
            apply mul_le_mul
            · simp only [le_refl]
            · rw [mul_comm]
              apply mul_le_mul
              · norm_cast
                exact Nat.factorial_le_pow (h7.r q hq0 h2mq)
              · simp only [le_refl]
              · positivity
              · positivity
            · positivity
            · positivity
          · positivity
          · positivity
          · positivity
          · positivity
        · rw [← Real.rpow_mul]
          rw [← Real.rpow_mul]
          rw [Real.sqrt_eq_rpow]
          rw [← Real.rpow_mul]
          rw [mul_comm (h7.m : ℝ) (1/2)]
          rw [mul_comm (h7.m : ℝ) 2]
          simp only [mul_assoc]
          congr
          rw [Real.inv_rpow]
          rw [← mul_assoc]
          rw [← Real.rpow_add]
          rw [← Real.rpow_neg]
          rw [← Real.rpow_add]
          rw [← Real.rpow_add]
          · ring_nf
          · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
          · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
          · simp only [Nat.cast_nonneg]
          · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
          · simp only [Nat.cast_nonneg]
          · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]
          · positivity
          · simp only [Nat.cast_nonneg]
        · ring_nf
          simp only [one_div, Real.rpow_natCast, le_refl]
      · positivity
      · apply Real.rpow_nonneg
        apply h7.c10_nonneg
    · apply mul_nonneg
      · apply Real.rpow_nonneg
        exact c10_nonneg h7
      · positivity
    · apply Real.rpow_nonneg
      exact h7.c11_nonneg
    · positivity
    · exact c10_nonneg h7
    · apply mul_nonneg
      · positivity
      · exact c10_nonneg h7
    · apply c11_nonneg

def systemCoeffsff_foo_S : ρᵣ h7 q hq0 h2mq =
  Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq : ℤ)) *
   (h7.S q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1) := by
  dsimp [ρᵣ]
  congr
  have HAE : ∀ (z : ℂ), AnalyticAt ℂ (h7.R q hq0 h2mq) z := by
    intros z
    fun_prop
  let R₁ : ℂ → ℂ := analyticExtensionR h7 q hq0 h2mq ((h7.l₀' q hq0 h2mq))
  have HR1 : ∀ (z : ℂ), AnalyticAt ℂ R₁ z := by
    unfold R₁
    intros z
    apply analyticExtensionR_analyticAt h7 q hq0 h2mq (h7.l₀' q hq0 h2mq) z
  have hR₁ : ∀ (z : ℂ), (h7.R q hq0 h2mq) z =
    ((z - (h7.l₀' q hq0 h2mq + 1)) ^ (h7.r q hq0 h2mq)) * (R₁ z) := by
    intros z
    rw [h7.R_eq_pow_mul_analyticExtensionR]
  have hr : h7.r q hq0 h2mq ≤ h7.r q hq0 h2mq := by rfl
  have :
   ∃ R₂ : ℂ → ℂ, (∀ z : ℂ, AnalyticAt ℂ R₂ z) ∧
    (∀ z, deriv^[(h7.r q hq0 h2mq)] (R h7 q hq0 h2mq) z =
   (z - ( l₀' h7 q hq0 h2mq + 1))^((h7.r q hq0 h2mq)-(h7.r q hq0 h2mq)) *
    ((h7.r q hq0 h2mq).factorial/((h7.r q hq0 h2mq)-(h7.r q hq0 h2mq)).factorial * R₁ z +
       (z - ( l₀' h7 q hq0 h2mq + 1))* R₂ z)) := by
    apply iterated_deriv_mul_pow_sub_of_analytic (z₀ := l₀' h7 q hq0 h2mq + 1)
        --HAE
        HR1 hR₁ (r := r h7 q hq0 h2mq) (k := r h7 q hq0 h2mq) hr
  simp only [tsub_self, pow_zero, Nat.factorial_zero,
  Nat.cast_one, div_one, one_mul] at this
  have := this
  obtain ⟨R2,hR⟩ := this
  clear this
  obtain ⟨hR1, hR2⟩ := hR
  rw [hR2]
  unfold R₁
  symm
  dsimp [S]
  simp only [add_left_inj, Nat.cast_inj, exists_apply_eq_apply', ↓reduceDIte]
  dsimp
  · unfold auxRemainderAtL0
    simp only [add_sub_add_right_eq_sub]
    rw [mul_comm   ↑(h7.r q hq0 h2mq).factorial
      (h7.analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1))]
    nth_rw 2 [← mul_one
      (a := (h7.analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1)) *
      ↑(h7.r q hq0 h2mq).factorial) ]
    congr
    simp only [mul_one, sub_self, zero_mul, add_zero]
    nth_rw 2 [← mul_one (a:= h7.analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq)
      ((h7.l₀' q hq0 h2mq : ℂ) + 1) * ↑(h7.r q hq0 h2mq).factorial)]
    congr
    have H1 :  ∏ x ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)}, 1 = (1 : ℂ) := by
      simp only [prod_const_one]
    congr
    rw [← H1]
    apply Finset.prod_congr
    rfl
    intros x hx
    rw [div_self]
    simp only [one_pow]
    have : ∀ x ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
      ↑↑(h7.l₀' q hq0 h2mq) ≠ x := by
        intros x hx
        grind only [= Finset.mem_sdiff, = Finset.mem_singleton]
    have := this x hx
    intros HC
    rw [sub_eq_zero] at HC
    norm_cast at HC

lemma eq7 (l' : Fin (h7.m)) :
    ρᵣ h7 q hq0 h2mq = Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq) : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
    (∮ z in C(0, h7.m * (1 + (h7.r q hq0 h2mq / q))), (z - (h7.l₀' q hq0 h2mq + 1))⁻¹ *
    (h7.S q hq0 h2mq) z)) :=
  h7.hcauchy q hq0 h2mq ▸ systemCoeffsff_foo_S h7 q hq0 h2mq

def c₁₃ : ℝ :=((‖Complex.log h7.α‖⁻¹ + 1)*h7.m*(2 + 1/h7.m)*h7.c₁₂)

lemma c13_nonneg : 0 ≤ h7.c₁₃ := by
  unfold c₁₃
  apply mul_nonneg (by positivity) (h7.c12_nonneg)

lemma one_le_c13 : 1 ≤ h7.c₁₃ := by
  unfold c₁₃
  refine one_le_mul_of_one_le_of_one_le ?_ (h7.one_le_c12)
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · rw [add_comm]
      refine le_add_of_le_of_nonneg (le_refl _) (by positivity)
    · simp only [Nat.one_le_cast]; exact Nat.le_of_ble_eq_true rfl
  · simp only [one_div]
    refine le_add_of_le_of_nonneg (by aesop) (by positivity)

def Cnum : ℝ := ((h7.m * (h7.r q hq0 h2mq : ℝ)) / (q : ℝ))⁻¹ * (h7.c₁₂ ^ (h7.r q hq0 h2mq : ℝ)*
  (h7.r q hq0 h2mq : ℝ) ^ ((((h7.r q hq0 h2mq : ℝ)* (((3 : ℝ) - h7.m) / 2 : ℝ)) + (3 / 2 : ℝ))))

lemma hf : ∀ z ∈ Metric.sphere 0 (h7.m * (1 + ↑(h7.r q hq0 h2mq : ℝ) / ↑q)),
    ‖(z - ((↑(h7.l₀' q hq0 h2mq) : ℂ) + 1))⁻¹ * (h7.S q hq0 h2mq z)‖ ≤ h7.Cnum q hq0 h2mq := by
  intros z hz
  simp only [Complex.norm_mul, norm_inv, Cnum]
  apply mul_le_mul ?_ (S_norm_bound h7 q hq0 h2mq hz) (by positivity) (by positivity)
  · apply inv_anti₀ ?_ (h7.norm_sub_l0_lower_bound_on_sphere q hq0 h2mq hz)
    · refine Real.sqrt_ne_zero'.mp ?_
      · refine (Real.sqrt_ne_zero (by positivity)).mpr ?_
        refine div_ne_zero ?_ (Ne.symm (ne_of_lt (mod_cast hq0)))
        · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
          refine ⟨by simp [m], by simp_rw [h7.r_ne_zero]; simp only [not_false_eq_true]⟩

lemma eq8 :
    norm (ρᵣ h7 q hq0 h2mq) ≤ (h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) *
    ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) * ((3 - (h7.m : ℝ))) / 2 + 3 / 2)) := by

  have hR : 0 ≤ (h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q) : ℝ) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply add_nonneg zero_le_one
    apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

  have H := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR
    (h7.hf q hq0 h2mq)

  calc _ = norm (Complex.log h7.α ^ (-(h7.r q hq0 h2mq : ℤ)) * ((2 * Real.pi) * I)⁻¹ * ∮ (z : ℂ) in
           C(0, h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)), (z - ↑((h7.l₀' q hq0 h2mq : ℂ) + 1))⁻¹ *
           (h7.S q hq0 h2mq z)) := ?_

       _ = norm (Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq : ℤ))) *
           norm ((2 * Real.pi * I)⁻¹) * norm (∮ (z : ℂ) in
           C(0, h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)),
           (z - ↑((h7.l₀' q hq0 h2mq : ℂ) + 1))⁻¹ * (h7.S q hq0 h2mq z)) := ?_

       _ ≤ ((norm ((Complex.log h7.α))^ (-(h7.r q hq0 h2mq : ℤ)))) * (h7.m : ℝ) *
           (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) * (h7.c₁₂) ^ (h7.r q hq0 h2mq : ℝ) *
           ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) * (3 - h7.m : ℝ) / 2 + 3 / 2) *
           ((q : ℝ) / (((h7.m : ℝ) * (h7.r q hq0 h2mq : ℝ))))) := ?_

       _ ≤ (h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) * ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           ((3 - (h7.m : ℝ))) / 2 + 3 / 2)) := ?_

  · rw [h7.eq7 q hq0 h2mq]
    · simp only [mul_assoc]
    exact (h7.l₀' q hq0 h2mq)
  · simp only [_root_.zpow_neg, zpow_natCast, _root_.mul_inv_rev,
    norm_inv, norm_pow, norm_real, Real.norm_eq_abs, norm_ofNat, norm_mul]
  · simp only [mul_assoc]
    simp only [_root_.zpow_neg, zpow_natCast, norm_inv, norm_pow, _root_.mul_inv_rev, inv_I, neg_mul,
      norm_neg, Complex.norm_mul, norm_I, norm_real, Real.norm_eq_abs, one_mul, norm_ofNat]
    · apply mul_le_mul
      · simp only [le_refl]
      · simp only [_root_.mul_inv_rev, inv_I, neg_mul, smul_eq_mul, norm_neg, Complex.norm_mul,
          norm_I, norm_inv, norm_real, Real.norm_eq_abs, norm_ofNat, one_mul] at H
        simp only [mul_assoc] at *
        trans
        · apply H
        simp only [Real.rpow_natCast]
        apply mul_le_mul
        · simp only [le_refl]
        · unfold Cnum
          --simp only [← mul_assoc]
          nth_rw 2 [mul_comm]
          simp only [mul_assoc]
          simp only [Real.rpow_natCast, inv_div]
          ring_nf;
          simp only [le_refl]
        · unfold Cnum
          apply mul_nonneg
          · positivity
          · apply mul_nonneg
            · positivity
            · apply mul_nonneg
              · apply Real.rpow_nonneg
                · exact c12_nonneg h7
              · positivity
        · simp only [Nat.cast_nonneg]
      · positivity
      · simp only [inv_nonneg, norm_nonneg, pow_nonneg]
  · simp only [_root_.zpow_neg, zpow_natCast, mul_assoc]
    nth_rw 5 [← mul_comm]
    unfold c₁₃
    rw [Real.mul_rpow, Real.mul_rpow, Real.mul_rpow]
    simp only [mul_assoc]
    apply mul_le_mul
    · rw [← norm_inv, ← inv_pow, ← norm_inv]
      simp only [Real.rpow_natCast]
      apply pow_le_pow_left₀
      simp only [norm_inv, inv_nonneg, norm_nonneg]
      simp only [norm_inv, le_add_iff_nonneg_right, zero_le_one]
    · apply mul_le_mul
      · nth_rw 1 [← Real.rpow_one (x:= h7.m)]
        apply Real.rpow_le_rpow_of_exponent_le
        · unfold m; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          rw [le_iff_lt_or_eq]
          left
          trans
          apply one_lt_two
          simp only [lt_add_iff_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
          unfold h; exact Module.finrank_pos
        · simp only [Nat.one_le_cast]
          exact one_le_r h7 q hq0 h2mq
      · simp only [← mul_assoc]
        nth_rw 1 [mul_comm]
        nth_rw 6 [mul_comm]
        apply mul_le_mul
        · simp only [le_refl]
        · simp only [mul_assoc]
          rw [mul_comm]
          nth_rw 4 [mul_comm]
          simp only [mul_assoc]
          apply mul_le_mul ?_ ?_ (by positivity) (Real.rpow_nonneg (c12_nonneg h7) _)
          · simp only [Real.rpow_natCast, le_refl]
          · ring_nf
            rw [mul_rotate]
            simp only [mul_assoc]
            nth_rw 2 [← mul_assoc]
            rw [inv_mul_cancel₀]
            simp only [one_mul]
            nth_rw 1 [← mul_assoc]
            rw [inv_mul_cancel₀]
            simp only [one_mul]
            calc _ ≤ (h7.m : ℝ)⁻¹ + (2*(h7.m : ℝ)*(h7.r q hq0 h2mq : ℝ))
                      * ((h7.m : ℝ)⁻¹ * (h7.r q hq0 h2mq : ℝ)⁻¹) :=?_
                 _ ≤ (2 + (h7.m : ℝ)⁻¹) ^ (h7.r q hq0 h2mq : ℝ) := ?_
            · simp only [add_le_add_iff_left]
              apply mul_le_mul ?_ (le_refl _) (by positivity) (by positivity)
              · norm_cast
                trans
                apply h7.q_le_two_mn q h2mq
                apply mul_le_mul (le_refl _) (n_le_r h7 q hq0 h2mq) (by positivity) (by positivity)
            · ring_nf
              rw [mul_inv_cancel₀]
              simp only [one_mul]
              rw [mul_inv_cancel₀]
              simp only [one_mul]
              nth_rw 1 [← Real.rpow_one (x:=(2 + (h7.m : ℝ)⁻¹))]
              apply Real.rpow_le_rpow_of_exponent_le
              · refine le_add_of_le_of_nonneg ?_ (by positivity)
                · simp only [Nat.one_le_ofNat]
              · simp only [Nat.one_le_cast]
                exact one_le_r h7 q hq0 h2mq
              · simp only [ne_eq, Nat.cast_eq_zero]; exact r_ne_zero h7 q hq0 h2mq
              · simp only [ne_eq, Nat.cast_eq_zero]
                exact Nat.ne_zero_of_lt (h7.one_le_m)
            · simp only [ne_eq, Nat.cast_eq_zero];exact r_ne_zero h7 q hq0 h2mq
            · simp only [ne_eq, Nat.cast_eq_zero]
              exact Nat.ne_zero_of_lt hq0
        · apply mul_nonneg
          · apply mul_nonneg
            · positivity
            · apply Real.rpow_nonneg (c12_nonneg h7)
          · positivity
        · positivity
      · apply mul_nonneg
        · positivity
        · apply mul_nonneg
          · apply Real.rpow_nonneg (c12_nonneg h7)
          · positivity
      · positivity
    · apply mul_nonneg (by positivity)
      · apply mul_nonneg (by positivity)
          (mul_nonneg (Real.rpow_nonneg (c12_nonneg h7) _) (by positivity))
    · apply Real.rpow_nonneg
      rw [add_comm]
      trans
      apply zero_le_one
      refine le_add_of_le_of_nonneg ?_ ?_
      · simp only [le_refl]
      · simp only [inv_nonneg, norm_nonneg]
    · rw [add_comm]
      trans
      apply zero_le_one
      refine le_add_of_le_of_nonneg ?_ ?_
      · simp only [le_refl]
      · simp only [inv_nonneg, norm_nonneg]
    · simp only [Nat.cast_nonneg]
    · positivity
    · positivity
    · positivity
    · exact c12_nonneg h7

def c₁₄ : ℝ := (h7.c₈^((h7.h-1)) * h7.c₁₃)

lemma c14_nonneg : 1 ≤ h7.c₁₄ :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ h7.c8_geq_one) h7.one_le_c13

include u t in
lemma use6and8 : norm ((Algebra.norm ℚ (rho h7 q hq0 h2mq))) ≤ (h7.c₁₄)^(h7.r q hq0 h2mq : ℝ) *
    (h7.r q hq0 h2mq : ℝ)^((-(h7.r q hq0 h2mq : ℝ))/2 + 3 * (h7.h)/2) := by

  calc _ ≤  ‖ρᵣ h7 q hq0 h2mq‖ * (house (rho h7 q hq0 h2mq)) ^ (((h7.h) - 1 )) := ?_

       _ ≤ (h7.c₈ ^ h7.r q hq0 h2mq * ↑(h7.r q hq0 h2mq :ℝ) ^
          ((h7.r q hq0 h2mq : ℝ) + 3 / 2))^((h7.h) -1) *
          ((h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) *
           ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           ((3 - (h7.m : ℝ))) / 2 + 3 / 2))) := ?_

       _ ≤ ((h7.c₁₄)^(h7.r q hq0 h2mq : ℝ)) * (↑(h7.r q hq0 h2mq: ℝ))^(
         (((h7.h: ℝ) - 1)) * ((h7.r q hq0 h2mq : ℝ) + 3/2) +
         ((((h7.r q hq0 h2mq : ℝ) * (3 - (h7.m : ℝ))) / 2) + 3 / 2)) := ?_

       _ = ((h7.c₁₄)^(h7.r q hq0 h2mq: ℝ)) * (↑(h7.r q hq0 h2mq: ℝ))^(
         ((-(h7.r q hq0 h2mq : ℝ))/2) + 3 * (h7.h)/ 2) := ?_

  · have := norm_norm_le_norm_mul_house_pow (K := h7.K) (α := (h7.rho q hq0 h2mq)) h7.σ
    rw [← rho_eq_ρᵣ]
    unfold h
    simp only [← Real.rpow_natCast] at *
    exact this
  · nth_rw 2 [mul_comm]
    apply mul_le_mul
    · apply eq8 h7 q hq0 h2mq
    · have := h7.eq6 q hq0 h2mq
      simp only [← Real.rpow_natCast] at *
      apply Real.rpow_le_rpow
      · exact house_nonneg (h7.rho q hq0 h2mq)
      · exact this
      · simp only [Nat.cast_nonneg]
    · apply pow_nonneg; exact house_nonneg (h7.rho q hq0 h2mq)
    · apply mul_nonneg
      · apply Real.rpow_nonneg
        exact h7.c13_nonneg
      · positivity
  · unfold c₁₄
    simp only [← Real.rpow_natCast] at *
    rw [Real.mul_rpow]
    rw [← Real.rpow_mul]
    nth_rw 3 [mul_comm]
    nth_rw 1 [← Real.rpow_mul]
    nth_rw 5 [mul_comm]
    simp only [← mul_assoc]
    nth_rw  2 [mul_assoc]
    rw [← Real.rpow_add]
    rw [mul_comm]
    simp only [← mul_assoc]
    rw [Real.rpow_mul]
    rw [← Real.mul_rpow]
    nth_rw 7 [mul_comm]
    nth_rw 2 [mul_comm]
    apply mul_le_mul
    · simp only [Real.rpow_natCast]
      simp only [le_refl]
    · rw [le_iff_lt_or_eq]
      right
      congr
      refine Nat.cast_pred ?_
      unfold h; exact Module.finrank_pos
    · positivity
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      apply mul_nonneg
      · apply pow_nonneg
        exact c8_nonneg h7
      · exact h7.c13_nonneg
    · exact h7.c13_nonneg
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      exact c8_nonneg h7
    · exact c8_nonneg h7
    · simp only [Nat.cast_pos]
      exact r_qt_0 h7 q hq0 h2mq
    · simp only [Nat.cast_nonneg]
    · exact c8_nonneg h7
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      exact c8_nonneg h7
    · apply Real.rpow_nonneg
      simp only [Nat.cast_nonneg]
  · unfold m
    simp only [mul_eq_mul_left_iff]
    left
    have : ((h7.h : ℝ) - 1) * ((h7.r q hq0 h2mq : ℝ) + 3/2) +
    ((h7.r q hq0 h2mq : ℝ) * (3 - (h7.m : ℝ)) / 2 + 3 / 2) =
    (-(h7.r q hq0 h2mq : ℝ)) / 2 + 3 * (h7.h) / 2 := by
     unfold m
     push_cast
     ring
    rw [← this]
    unfold m
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

def c₁₅ : ℝ := h7.c₁₄ * h7.c₅

lemma c15_nonneg : 0 ≤ h7.c₁₅ := by
  unfold c₁₅; exact mul_nonneg (zero_le_one.trans h7.c14_nonneg) (c5nonneg h7).le

lemma c15_geg_1 : 1 ≤ h7.c₁₅ := by
  unfold c₁₅ c₅
  exact one_le_mul_of_one_le_of_one_le h7.c14_nonneg (one_le_pow₀ (by simp))

theorem norm_pos_rho : 0 < ‖(Algebra.norm ℚ) (h7.rho q hq0 h2mq)‖ := by
  rw [norm_pos_iff, ne_eq, Algebra.norm_eq_zero_iff]
  rintro H
  apply ρᵣ_nonzero h7 q hq0 h2mq
  simpa [← rho_eq_ρᵣ]

lemma eq5inv :
    norm ((Algebra.norm ℚ) (h7.rho q hq0 h2mq)) ⁻¹ < h7.c₅ ^ ((h7.r q hq0 h2mq : ℝ)) := by
  have h := eq5 h7 q hq0 h2mq
  rw [← inv_lt_inv₀] at h
  · simpa [← Real.rpow_neg] using h
  · exact norm_pos_rho h7 q hq0 h2mq
  · simp only [Real.rpow_neg_natCast, _root_.zpow_neg, zpow_natCast, inv_pos]
    apply pow_pos (c5nonneg h7)

include u t in
lemma use5 : (h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq : ℝ) - 3 * h7.h) / 2) <
  (h7.c₁₅) ^ (h7.r q hq0 h2mq : ℝ) := by
  let r : ℝ := h7.r q hq0 h2mq
  let N : ℝ := ‖(Algebra.norm ℚ) (h7.rho q hq0 h2mq)‖
  let B : ℝ := r ^ (-r / 2 + 3 * h7.h / 2)

  have hrpos : 0 < r := by
    dsimp [r]
    exact_mod_cast r_qt_0 h7 q hq0 h2mq
  have hNpos : 0 < N := by
    simpa [N] using norm_pos_rho h7 q hq0 h2mq
  have hBpos : 0 < B := by
    dsimp [B]
    exact Real.rpow_pos_of_pos hrpos _

  have h68 : N ≤ h7.c₁₄ ^ r * B := by
    dsimp [N, r, B]
    simpa using (use6and8 h7 q hq0 u t h2mq)

  have htmp :
        N * B⁻¹ ≤ (h7.c₁₄ ^ r * B) * B⁻¹ :=
      mul_le_mul_of_nonneg_right h68 (inv_nonneg.mpr (le_of_lt hBpos))

  have h1 : N * B⁻¹ ≤ h7.c₁₄ ^ r := by
    simpa [mul_assoc, mul_inv_cancel₀ hBpos.ne', mul_one] using htmp

  have hle : B⁻¹ ≤ N⁻¹ * (h7.c₁₄ ^ r) := by
    have htmp :
        N⁻¹ * (N * B⁻¹) ≤ N⁻¹ * (h7.c₁₄ ^ r) :=by
      apply mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (le_of_lt hNpos))
    grind [mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]

  have hltN : N⁻¹ < h7.c₅ ^ r := by
    dsimp [N, r]
    simpa using (eq5inv h7 q hq0 h2mq)

  have hApos : 0 < h7.c₁₄ ^ r := by
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one h7.c14_nonneg) _

  have hmulrpow : (h7.c₁₅) ^ r = (h7.c₁₄ ^ r) * (h7.c₅ ^ r) := by
    unfold c₁₅
    rw [Real.mul_rpow (le_trans zero_le_one h7.c14_nonneg) (c5nonneg h7).le]

  calc
    (h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq : ℝ) - 3 * h7.h) / 2)
        = B⁻¹ := by
            dsimp [B, r]
            rw [show (((h7.r q hq0 h2mq : ℝ) - 3 * h7.h) / 2) =
                - (-(h7.r q hq0 h2mq : ℝ) / 2 + 3 * h7.h / 2) by ring]
            rw [Real.rpow_neg (le_of_lt (by
              exact_mod_cast r_qt_0 h7 q hq0 h2mq))]
    _ ≤ N⁻¹ * (h7.c₁₄ ^ r) := hle
    _ = (h7.c₁₄ ^ r) * N⁻¹ := by ring
    _ < (h7.c₁₄ ^ r) * (h7.c₅ ^ r) := mul_lt_mul_of_pos_left hltN hApos
    _ = (h7.c₁₅) ^ r := hmulrpow.symm
    _ = (h7.c₁₅) ^ (h7.r q hq0 h2mq : ℝ) := by rfl

end Setup


end

end


/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/



section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
  (t : Fin (q * q)) (h2mq : 2 * h7.m ∣ q ^ 2) [DecidableEq (h7.K →+* ℂ)]

namespace Setup

/-- The Gelfond-Schneider Theorem (Hilbert's Seventh Problem). -/
theorem transcendental_cpow_of_isAlgebraic_of_irrational (α β : ℂ)
    (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
    (htriv : α ≠ 0 ∧ α ≠ 1) (hirr : ∀ i j : ℤ, β ≠ i / j) :
    Transcendental ℚ (α ^ β) := fun hγ => by

  obtain ⟨K, hK, hNK, σ, hd, α', β', γ', habc⟩ :=
    exists_common_field_of_isAlgebraic α β (α^β) hα hβ hγ
  have h7 : Setup :=
    Setup.mk α β K σ α' β' γ' hirr htriv hα hβ habc hd
  haveI : DecidableEq (h7.K →+* ℂ) := h7.hd
  let q : ℕ := 2 * h7.m * ((6 * h7.h) * Nat.ceil (h7.c₁₅ ^ 4))
  have hq0 : 0 < q := by
    simp only [q, CanonicallyOrderedAdd.mul_pos, Nat.ofNat_pos, Nat.ceil_pos,true_and]
    refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), ?_⟩
    refine ⟨Module.finrank_pos, ?_⟩
    · apply pow_pos
      grind [h7.c15_geg_1]

  have h2mq : 2 * h7.m ∣ q ^ 2 := by
    rw [pow_two, mul_assoc]; exact dvd_mul_right _ _

  let u : Fin (h7.m * h7.n q) := ⟨0, by
    apply mul_pos (Nat.zero_lt_succ (2 * h7.h + 1));
    apply Nat.div_pos (Nat.le_of_dvd (Nat.pow_pos hq0) h2mq) ?_
    · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      exact Nat.zero_lt_succ (2 * h7.h + 1)⟩

  let t : Fin (q * q) := ⟨0, mul_pos hq0 hq0⟩

  -- have hnr : (h7.n q : ℝ) ≤ (h7.r q hq0 h2mq : ℝ) :=
  --   mod_cast n_le_r h7 q hq0 h2mq

  have H1 : (2 * h7.m) * (6 * h7.h) ≤ q := by
    unfold q
    apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
    · nth_rw 1 [← mul_one (a := 6* h7.h)]
      apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
      · simp only [Nat.one_le_ceil_iff];
        apply pow_pos
        grind [h7.c15_geg_1]

  have H2 : (2 * h7.m) * h7.c₁₅ ^ 4 ≤ q := by
    simp only [q, mul_assoc, Nat.cast_mul, Nat.cast_ofNat, Nat.ofNat_pos, mul_le_mul_iff_right₀]
    apply mul_le_mul (le_refl _) ?_ ?_ (by positivity)
    · nth_rw 1 [← one_mul (a := (h7.c₁₅ ^ 4) )]
      nth_rw 1 [← mul_assoc]
      apply mul_le_mul ?_ (Nat.le_ceil (h7.c₁₅ ^ 4)) (by positivity) (by positivity)
      · unfold h;
        refine one_le_mul_of_one_le_of_one_le (Nat.one_le_ofNat) ?_
        · norm_cast
          grind [Module.finrank_pos]
    · apply pow_nonneg
      grind [h7.c15_geg_1]

  have H3 : 6* h7.h ≤ h7.n q := by
    unfold n
    calc _ ≤ ((2 * h7.m) * (6 * h7.h)) ^ 2 / (2 * h7.m) := ?_
         _ ≤  h7.n q := ?_
    · refine (Nat.le_div_iff_mul_le ?_).mpr ?_
      · have : 0 < h7.h := by grind [Module.finrank_pos]
        apply mul_pos (by aesop) (Nat.zero_lt_succ (2 * h7.h + 1))
      · rw [mul_comm, Nat.pow_two]
        apply Nat.le_mul_self
    · unfold n q
      refine Nat.div_le_div_right (Nat.pow_le_pow_left H1 2)

  have H4 : (h7.c₁₅)^4 ≤ (h7.n q : ℝ) := by
    unfold n q
    refine Nat.ceil_le.mp ?_
    refine (Nat.le_div_iff_mul_le ?_).mpr ?_
    · have : 0 < h7.h := by
        grind [Module.finrank_pos]
      apply mul_pos (by aesop) (Nat.zero_lt_succ (2 * h7.h + 1))
    · rw [mul_comm, mul_pow]
      apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · rw [Nat.pow_two]; apply Nat.le_mul_self
      · rw [Nat.pow_two]
        simp only [← mul_assoc]
        nth_rw 2 [mul_comm]
        simp only [← mul_assoc]
        nth_rw 2 [mul_comm]
        simp only [mul_assoc]
        nth_rw 1 [← one_mul (a := ⌈h7.c₁₅ ^ 4⌉₊)]
        rw [← Nat.pow_two]
        simp only [← mul_assoc]
        apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · have : 0 < h7.h := by
            unfold h; exact Module.finrank_pos
          unfold h at *
          refine Nat.one_le_iff_ne_zero.mpr ?_
          refine Nat.mul_ne_zero_iff.mpr ?_
          · constructor
            · simp only [ne_eq, mul_eq_zero,
               OfNat.ofNat_ne_zero, false_or, or_false]
              rw [← ne_eq]
              exact Nat.ne_zero_of_lt this
            · exact Nat.ne_zero_of_lt this
        · rw [Nat.pow_two]; apply Nat.le_mul_self

  have H5 : 6* h7.h ≤ h7.r q hq0 h2mq := H3.trans (n_le_r h7 q hq0 h2mq)

  have H6 : (h7.c₁₅)^4 ≤ h7.r q hq0 h2mq := by
    trans
    · apply H4
    simp only [Nat.cast_le]
    exact n_le_r h7 q hq0 h2mq

  apply absurd (use5 h7 q hq0 u t h2mq) ?_
  · simp only [Real.rpow_natCast, not_lt]
    rw [← Real.rpow_le_rpow_iff (z:= ( ((↑(h7.r q hq0 h2mq) - 3 * ↑h7.h) / 2) : ℝ)⁻¹)]
    rw [← Real.rpow_mul, mul_inv_cancel₀]
    simp only [inv_div, Real.rpow_one]
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    have : h7.c₁₅ ^ ((h7.r q hq0 h2mq : ℝ) * (2 / (↑(h7.r q hq0 h2mq) - 3 * ↑h7.h))) ≤
       h7.c₁₅ ^ (4 : ℝ)  := by
        apply Real.rpow_le_rpow_of_exponent_le
        · exact c15_geg_1 h7
        · rw [mul_div]
          ring_nf
          simp only [mul_assoc]
          rw [mul_comm]
          simp only [mul_assoc]
          refine (inv_mul_le_iff₀' ?_).mpr ?_
          · calc _ < ↑h7.h * 3 := ?_
                 _ ≤ ((h7.h * 6 - ↑h7.h * 3) : ℝ) := ?_
                 _ ≤ (h7.r q hq0 h2mq : ℝ) - h7.h * 3 := ?_
            · have : 0 < h7.h := by
                grind [Module.finrank_pos]
              simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_right, Nat.cast_pos, gt_iff_lt]
              grind
            · ring_nf; simp only [le_refl]
            · simp only [tsub_le_iff_right, sub_add_cancel]
              rw [mul_comm]
              norm_cast
          · rw [sub_eq_neg_add]
            rw [mul_add]
            simp only [mul_neg, le_neg_add_iff_add_le]
            calc _ ≤  2 *  (6 * (↑h7.h)) + 2 * (h7.r q hq0 h2mq : ℝ) := ?_
                 _ ≤  2 * (h7.r q hq0 h2mq : ℝ) + 2 * (h7.r q hq0 h2mq : ℝ) := ?_
                 _ ≤  4 * (h7.r q hq0 h2mq : ℝ) := ?_

            · simp only [add_le_add_iff_right]; ring_nf; simp only [le_refl]
            · simp only [add_le_add_iff_right]
              apply mul_le_mul (le_refl _) (by norm_cast) (by positivity) (by positivity)
            · ring_nf; simp only [le_refl]
    trans
    apply this
    simp only [Real.rpow_ofNat]
    apply H6
    · exact c15_nonneg h7
    · apply div_ne_zero
      · have : 3 * h7.h < (h7.r q hq0 h2mq : ℝ) := by
          calc _ < (6 * h7.h : ℝ)  := by norm_cast; grind [Module.finrank_pos]
               _ ≤ (h7.r q hq0 h2mq :ℝ) := by norm_cast;
        grind
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    · positivity
    · apply pow_nonneg (c15_nonneg h7)
    · positivity
    · have Hh : 0 < h7.h := by unfold h; exact Module.finrank_pos
      unfold h at *
      simp only [inv_div, Nat.ofNat_pos, div_pos_iff_of_pos_left, sub_pos, gt_iff_lt]
      have : 3 * h7.h < (h7.r q hq0 h2mq : ℝ) := by
          calc _ < (6 * h7.h : ℝ)  := ?_
               _ ≤ (h7.r q hq0 h2mq : ℝ) := by norm_cast
          · norm_cast
            refine Nat.mul_lt_mul_of_pos_right ?_ Hh; simp only [Nat.reduceLT]
      unfold h at *
      exact this

end Setup

/-!
A formalization of a proof that `√2 ^ √2` is transcendental.
-/
lemma sqrt2sqrt_is_transcendental : Transcendental ℚ ((√2 : ℂ)^ (√2 : ℂ)) := by
  apply Setup.transcendental_cpow_of_isAlgebraic_of_irrational √2 √2
  · refine IsAlgebraic.of_aeval ?_ (fun H ↦ ?_) ?_ ?_
    · exact Polynomial.X ^ 2 - Polynomial.C 1
    · have : ((((Polynomial.X ^ 2 - Polynomial.C 1) : ℚ[X])).natDegree : ℕ) = 2 := by {
        refine (degree_eq_iff_natDegree_eq_of_pos ?_).mp ?_
        · simp only [Nat.ofNat_pos]
        · rw [Polynomial.degree_sub_C]
          · simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
          simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.ofNat_pos]
      }
      have HC : 2 ≠ 0 := by {simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]}
      apply HC
      rw [← this, ← H]
    · simp only [map_one, Nat.ofNat_pos, leadingCoeff_X_pow_sub_one,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true]
    · simp only [map_one, map_sub, map_pow, aeval_X]
      norm_cast
      rw [Real.sq_sqrt (x:=2)]
      · ring_nf
        exact isAlgebraic_one
      · positivity
  · refine IsAlgebraic.of_aeval ?_ (fun H ↦ ?_) ?_ ?_
    · exact Polynomial.X ^ 2 - Polynomial.C 1
    · have : ((((Polynomial.X ^ 2 - Polynomial.C 1) : ℚ[X])).natDegree : ℕ) = 2 := by {
        refine (degree_eq_iff_natDegree_eq_of_pos ?_).mp ?_
        · simp only [Nat.ofNat_pos]
        · rw [Polynomial.degree_sub_C]
          · simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
          simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.ofNat_pos]
      }
      have HC : 2 ≠ 0 := by {simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]}
      apply HC
      rw [← this, ← H]
    · simp only [map_one, Nat.ofNat_pos, leadingCoeff_X_pow_sub_one,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true]
    · simp only [map_one, map_sub, map_pow, aeval_X]
      norm_cast
      rw [Real.sq_sqrt (x:=2)]
      · ring_nf
        exact isAlgebraic_one
      · positivity
  · simp only [ne_eq, ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
    not_false_eq_true, ofReal_eq_one, Real.sqrt_eq_one, OfNat.ofNat_ne_one, and_self]
  · have :=  irrational_sqrt_two
    unfold Irrational at this
    simp only [Set.mem_range, not_exists] at this
    intros i j
    let x : ℚ := (i : ℚ)/ (j : ℚ)
    intros H
    have := this x
    unfold x at this
    apply this
    symm
    norm_num
    norm_cast at H
    rw [H]
    simp_all only [Rat.cast_inj, forall_eq]

end

end


/-- From the `α ^ β` form of Gelfond–Schneider (principal branch) to the logarithmic form for an
arbitrary non-zero logarithm `l`: pick `m` with `|Im l| < m π`, so that `l / m` is the principal
logarithm of `α := exp (l / m)`; then `exp (b * l) = α ^ (m * b)`. -/
theorem gs_log_form_of_cpow_form
    (hGS : ∀ α β : ℂ, IsAlgebraic ℚ α → IsAlgebraic ℚ β → (α ≠ 0 ∧ α ≠ 1) →
      (∀ i j : ℤ, β ≠ i / j) → Transcendental ℚ (α ^ β))
    (b l : ℂ) (hb : IsAlgebraic ℚ b) (hbq : ∀ q : ℚ, b ≠ (q : ℂ))
    (hl : IsAlgebraic ℚ (Complex.exp l)) (hl0 : l ≠ 0) :
    Transcendental ℚ (Complex.exp (b * l)) := by
  set m : ℕ := ⌈|l.im| / Real.pi⌉₊ + 1 with hm_def
  have hm0 : 0 < m := Nat.succ_pos _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hbound : |l.im| < m * Real.pi := by
    have h1 : |l.im| / Real.pi < m := by
      have := Nat.le_ceil (|l.im| / Real.pi)
      rw [hm_def]; push_cast; linarith
    rwa [div_lt_iff₀ Real.pi_pos] at h1
  set w : ℂ := l / m with hw
  have hwim : w.im = l.im / m := by rw [hw, Complex.div_natCast_im]
  have hw_lt : |w.im| < Real.pi := by
    rw [hwim, abs_div, abs_of_pos hmR, div_lt_iff₀ hmR]; linarith
  have hw_lo : -Real.pi < w.im := by linarith [neg_abs_le w.im]
  have hw_hi : w.im ≤ Real.pi := by linarith [le_abs_self w.im]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hlw : l = m * w := by rw [hw]; field_simp
  -- α = exp w is algebraic, non-zero, and not 1
  have hα : IsAlgebraic ℚ (Complex.exp w) := by
    refine IsAlgebraic.of_pow hm0 ?_
    rw [← Complex.exp_nat_mul, ← hlw]; exact hl
  have hα0 : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  have hα1 : Complex.exp w ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    have him : w.im = n * (2 * Real.pi) := by
      rw [hn]; simp [Complex.mul_im]
    have hn0 : n = 0 := by
      by_contra hne
      have : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
      have : 2 * Real.pi ≤ |w.im| := by
        rw [him, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        nlinarith [Real.pi_pos]
      linarith [Real.pi_pos]
    apply hl0
    rw [hlw, hn, hn0]; simp
  -- β = m * b is algebraic and irrational
  have hβ : IsAlgebraic ℚ ((m : ℂ) * b) := by
    have h := (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (m : ℚ)).mul hb
    simpa using h
  have hβirr : ∀ i j : ℤ, (m : ℂ) * b ≠ i / j := by
    intro i j h
    apply hbq ((i : ℚ) / (j * m))
    push_cast
    rw [div_mul_eq_div_div, ← h]; field_simp
  -- exp (b * l) = (exp w) ^ (m * b)
  have hkey : Complex.exp (b * l) = Complex.exp w ^ ((m : ℂ) * b) := by
    rw [Complex.cpow_def_of_ne_zero hα0, Complex.log_exp hw_lo hw_hi, hlw]; ring_nf
  rw [hkey]
  exact hGS _ _ hα hβ ⟨hα0, hα1⟩ hβirr


/-- `Schanuel.gelfond_schneider`: for a non-zero logarithm `l` of an algebraic number and an
algebraic irrational `b`, `exp (b * l)` is transcendental. Karatarakis's theorem above is the
`α ^ β` (principal branch) form; the bridge lemma passes to an arbitrary logarithm. -/
theorem solution (b l : ℂ) (hb : IsAlgebraic ℚ b) (hbq : ∀ q : ℚ, b ≠ (q : ℂ))
    (hl : IsAlgebraic ℚ (Complex.exp l)) (hl0 : l ≠ 0) :
    Transcendental ℚ (Complex.exp (b * l)) :=
  gs_log_form_of_cpow_form (fun α β => Setup.transcendental_cpow_of_isAlgebraic_of_irrational α β)
    b l hb hbq hl hl0

#print axioms solution
