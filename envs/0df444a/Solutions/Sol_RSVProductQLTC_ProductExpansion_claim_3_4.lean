-- Prove2me | solution 1 for RSVProductQLTC.ProductExpansion.claim_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T21:24:11.603082+00:00
-- url     : https://prove2.me/submissions/fbc8b98c-dcc8-4850-92a2-52390cac9a7e

import Mathlib
import Definitions.Def_RSVProductQLTC_ProductExpansion_projectiveRS
import Definitions.Def_GoodQLTC_dualCode
set_option autoImplicit false
open Module RSVProductQLTC.ProductExpansion Finset

theorem dual_finrank {E Ω : Type} [Field E] [Fintype Ω] [DecidableEq Ω] (C : Submodule E (Ω → E)) :
    finrank E (GoodQLTC.dualCode C) = Fintype.card Ω - finrank E C := by
  let B : LinearMap.BilinForm E (Ω → E) := dotProductBilin E E
  have hB : B.Nondegenerate := by
    constructor
    · intro x hx
      ext i
      have := hx (Pi.single i 1)
      simpa [B, dotProductBilin] using this
    · intro x hx
      ext i
      have := hx (Pi.single i 1)
      simpa [B, dotProductBilin] using this
  have h := LinearMap.BilinForm.finrank_orthogonal hB C
  have e : B.orthogonal C = GoodQLTC.dualCode C := by
    ext y
    simp [LinearMap.BilinForm.mem_orthogonal_iff, GoodQLTC.dualCode, B, dotProductBilin]
  rw [← e, h]; simp

theorem sum_pow_top {K : Type} [Field K] [Fintype K] :
    ∑ x : K, x ^ (Fintype.card K - 1) = -1 := by
  classical
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hi : Fintype.card K - 1 ≠ 0 := by omega
  let φ : Kˣ ↪ K := ⟨fun x ↦ x, Units.val_injective⟩
  have : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using! isUnit_iff_ne_zero
  calc
    ∑ x : K, x ^ (Fintype.card K - 1) = ∑ x ∈ univ \ {(0 : K)}, x ^ (Fintype.card K - 1) := by
      rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hi, add_zero]
    _ = ∑ x : Kˣ, (x ^ (Fintype.card K - 1) : K) := by simp [φ, ← this, univ.sum_map φ]
    _ = -1 := by rw [FiniteField.sum_pow_units K, if_pos (dvd_refl _)]

def vec {K E : Type} [Field K] [Field E] (ι : K →+* E) (d j : ℕ) : Option K → E := fun a =>
    ι (projectiveRep a 0) ^ j * ι (projectiveRep a 1) ^ (d - j)

theorem vec_some {K E : Type} [Field K] [Field E] (ι : K →+* E) (d j : ℕ) (x : K) :
    vec ι d j (some x) = ι x ^ j := by
  simp [vec, projectiveRep]

theorem vec_none {K E : Type} [Field K] [Field E] (ι : K →+* E) (d j : ℕ) (hj : j ≤ d) :
    vec ι d j none = if j = d then 1 else 0 := by
  simp only [vec, projectiveRep]
  by_cases h : j = d
  · subst h; simp
  · have : d - j ≠ 0 := by omega
    simp [h, this]

theorem pairing_zero {K E : Type} [Field K] [Fintype K] [Field E] (ι : K →+* E) (d j k : ℕ)
    (hd : d ≤ Fintype.card K - 1) (hj : j ≤ d) (hk : k ≤ Fintype.card K - 1 - d) :
    vec ι d j ⬝ᵥ vec ι (Fintype.card K - 1 - d) k = 0 := by
  classical
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  unfold dotProduct
  rw [Fintype.sum_option, vec_none ι _ _ hj, vec_none ι _ _ hk]
  simp only [vec_some]
  have hs : ∑ x : K, ι x ^ j * ι x ^ k = ι (∑ x : K, x ^ (j + k)) := by
    simp [map_sum, pow_add]
  rw [hs]
  by_cases hm : j + k < Fintype.card K - 1
  · rw [FiniteField.sum_pow_lt_card_sub_one K _ hm]
    have : ¬ (j = d ∧ k = Fintype.card K - 1 - d) := by omega
    by_cases h1 : j = d
    · have : k ≠ Fintype.card K - 1 - d := by omega
      simp [h1, this]
    · simp [h1]
  · have h1 : j = d := by omega
    have h2 : k = Fintype.card K - 1 - d := by omega
    have h3 : j + k = Fintype.card K - 1 := by omega
    rw [h3, sum_pow_top]
    simp [h1, h2]

theorem vec_li {K E : Type} [Field K] [Fintype K] [Field E] (ι : K →+* E) (d : ℕ)
    (hd : d ≤ Fintype.card K - 1) : LinearIndependent E (fun j : Fin (d + 1) => vec ι d j.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let p : Polynomial E := ∑ j : Fin (d + 1), Polynomial.C (c j) * Polynomial.X ^ j.val
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := fun x : K => ι x)
      ι.injective
    · intro x
      have := congrFun hc (some x)
      simp only [Finset.sum_apply, Pi.smul_apply, vec_some, smul_eq_mul, Pi.zero_apply] at this
      simpa [p, Polynomial.eval_finsetSum] using this
    · have : p.natDegree ≤ d := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro j _
        refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        rw [Polynomial.natDegree_X_pow]; omega
      have h2 : d < Fintype.card K := by have := Fintype.one_lt_card (α := K); omega
      convert lt_of_le_of_lt this h2
  intro j
  have := congrArg (fun q => Polynomial.coeff q j.val) hp
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at this
  simpa [Fin.val_inj] using this

theorem solution {K E : Type} [Field K] [Fintype K] [Field E] [Fintype E]
    (ι : K →+* E) (d : ℕ) (hd : d ≤ Fintype.card K - 1) :
    GoodQLTC.dualCode (projectiveRS ι d) = projectiveRS ι (Fintype.card K - 1 - d) := by
  classical
  have hle : projectiveRS ι (Fintype.card K - 1 - d) ≤ GoodQLTC.dualCode (projectiveRS ι d) := by
    unfold projectiveRS
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show vec ι _ k.val ∈ _
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩
      exact pairing_zero ι d j k hd (by omega) (by omega)
    · simp
    · intro a b _ _ ha hb; rw [add_dotProduct, ha, hb, add_zero]
    · intro c a _ ha; rw [smul_dotProduct, ha, smul_zero]
  have hfr : ∀ e, e ≤ Fintype.card K - 1 → finrank E (projectiveRS ι e) = e + 1 := by
    intro e he
    unfold projectiveRS
    have := finrank_span_eq_card (vec_li ι e he)
    exact this.trans (by simp)
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [dual_finrank, hfr d hd, hfr _ (by omega)]
  simp
  have : 1 < Fintype.card K := Fintype.one_lt_card
  omega
