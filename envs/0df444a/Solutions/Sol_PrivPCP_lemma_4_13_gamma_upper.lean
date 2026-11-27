-- Prove2me | solution 1 for PrivPCP.lemma_4_13_gamma_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:52:53.60285+00:00
-- url     : https://prove2.me/submissions/bee1a4ee-c14d-447f-a947-3b3c9538597b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PrivPCP_Supplement_gammaF
import Theorems.Thm_PrivPCP_Supplement_theorem_4_12
import Theorems.Thm_PrivPCP_lemma_4_13_dx_ne_zero
import Theorems.Thm_PrivPCP_lemma_4_13_dependent


namespace PrivPCP.G1

open MvPolynomial

lemma coord_ne_zero {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] (x y : L)
    (F : MvPolynomial (Fin 2) K) (hF : Irreducible F) (i j : Fin 2) (hij : i ≠ j)
    (hFj : 0 < F.degreeOf j)
    (hker : RingHom.ker (MvPolynomial.aeval (R := K) ![x, y]).toRingHom = Ideal.span {F}) :
    (![x, y] : Fin 2 → L) i ≠ 0 := by
  intro h0
  have hmem : (X i : MvPolynomial (Fin 2) K) ∈ RingHom.ker (MvPolynomial.aeval (R := K) ![x, y]).toRingHom := by
    rw [RingHom.mem_ker]; simpa using h0
  rw [hker, Ideal.mem_span_singleton] at hmem
  obtain ⟨G, hG⟩ := hmem
  have hG0 : G ≠ 0 := by rintro rfl; rw [mul_zero] at hG; exact X_ne_zero i hG
  have := degreeOf_mul_eq (n := j) hF.ne_zero hG0
  rw [← hG, degreeOf_X, if_neg (Ne.symm hij)] at this
  omega

lemma pow_D_ne_zero {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] (q : ℕ) [CharP L q]
    (z : L) (hz : z ≠ 0) (hD : KaehlerDifferential.D K L z ≠ 0) (n : ℕ) (hn : ¬ q ∣ n) :
    KaehlerDifferential.D K L (z ^ n) ≠ 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul L]
  have hn' : (n : L) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff L q]
  exact smul_ne_zero hn' (smul_ne_zero (pow_ne_zero _ hz) hD)

end PrivPCP.G1

open PrivPCP.G1 MvPolynomial in
theorem solution : ∃ C : ℝ, ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
    Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
    ∀ F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q)),
    Irreducible F → 0 < F.degreeOf 0 → 0 < F.degreeOf 1 → F.degreeOf 0 < q → F.degreeOf 1 < q →
    ∀ (L : Type) [Field L] [Algebra (AlgebraicClosure (ZMod q)) L] (x y : L),
    RingHom.ker (MvPolynomial.aeval (R := AlgebraicClosure (ZMod q)) ![x, y]).toRingHom =
      Ideal.span {F} →
    IntermediateField.adjoin (AlgebraicClosure (ZMod q)) {x, y} = ⊤ →
    PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y (Nat.card S₁) (Nat.card S₂) ≠ ⊤ ∧
    ((PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y (Nat.card S₁) (Nat.card S₂)).toNat : ℝ) ≤
      C * (((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
          ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) +
        ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ)) := by
  obtain ⟨C', H412⟩ := PrivPCP.Supplement.theorem_4_12
  refine ⟨max C' 1, ?_⟩
  intro q _ S₁ S₂ hcop F hF hF0 hF1 haq hbq L _ _ x y hker hadj
  have hcard : ∀ S : Subgroup (ZMod q)ˣ, Nat.card S ∣ q - 1 := by
    intro S
    have := Subgroup.card_subgroup_dvd_card S
    rwa [Nat.card_eq_fintype_card (α := (ZMod q)ˣ), ZMod.card_units] at this
  have hq2 := (Fact.out : q.Prime).two_le
  have hNdvd : Nat.card S₁ * Nat.card S₂ ∣ q - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (hcard S₁) (hcard S₂)
  have hN : Nat.card S₁ * Nat.card S₂ < q := by
    have := Nat.le_of_dvd (by omega) hNdvd; omega
  have hn1 : 0 < Nat.card S₁ := Nat.card_pos
  have hn2 : 0 < Nat.card S₂ := Nat.card_pos
  have hn1q : ¬ q ∣ Nat.card S₁ := by
    intro h; have := Nat.le_of_dvd hn1 h; have := Nat.le_of_dvd (by omega) (hcard S₁); omega
  have hn2q : ¬ q ∣ Nat.card S₂ := by
    intro h; have := Nat.le_of_dvd hn2 h; have := Nat.le_of_dvd (by omega) (hcard S₂); omega
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
  haveI : CharP L q := charP_of_injective_algebraMap
    (algebraMap (AlgebraicClosure (ZMod q)) L).injective q
  have hx0 : x ≠ 0 := coord_ne_zero x y F hF 0 1 (by decide) hF1 hker
  have hy0 : y ≠ 0 := coord_ne_zero x y F hF 1 0 (by decide) hF0 hker
  obtain ⟨hDx, hDy⟩ := PrivPCP.lemma_4_13_dx_ne_zero q F hF hF0 hF1 haq hbq L x y hker hadj
  have hDxn := pow_D_ne_zero q x hx0 hDx _ hn1q
  have hDyn := pow_D_ne_zero q y hy0 hDy _ hn2q
  have hS0 : 0 ≤ (((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
      ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) +
      ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ)) := by positivity
  by_cases hind : ∀ r s : ℤ, (∃ c : AlgebraicClosure (ZMod q), c ≠ 0 ∧
      (x ^ Nat.card S₁) ^ r * (y ^ Nat.card S₂) ^ s =
        algebraMap (AlgebraicClosure (ZMod q)) L c) → r = 0 ∧ s = 0
  · obtain ⟨hfin, hle, hmax⟩ := H412 q F (F.degreeOf 0) (F.degreeOf 1) hF rfl rfl hF0 hF1 L x y hker hadj
      (Nat.card S₁) (Nat.card S₂) hn1 hn2 hN hind hDxn hDyn
    refine ⟨hfin, ?_⟩
    have e : ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ) = (F.degreeOf 0 : ℝ) * F.degreeOf 1 := by push_cast; ring
    rw [e] at hS0 ⊢
    calc _ ≤ _ := hle
      _ ≤ _ := hmax
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
  · push Not at hind
    obtain ⟨r, s, hc, hrs⟩ := hind
    obtain ⟨hfin, hle⟩ := PrivPCP.lemma_4_13_dependent q S₁ S₂ hcop F hF hF0 hF1 haq hbq L x y hker hadj
      ⟨r, s, fun h => hrs h.1 |> fun h' => h' h.2, hc⟩
    refine ⟨hfin, ?_⟩
    have h1 : (((PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y (Nat.card S₁)
        (Nat.card S₂)).toNat : ℕ) : ℝ) ≤ ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ) := by exact_mod_cast hle
    have h2 : ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ) ≤
        (((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
          ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) +
          ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ)) := by
      have : 0 ≤ ((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
          ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by positivity
      linarith
    have h3 : (((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
          ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) +
          ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ)) ≤ max C' 1 *
        (((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
          ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) +
          ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ)) := by
      have := mul_le_mul_of_nonneg_right (le_max_right C' 1) hS0
      linarith
    linarith


