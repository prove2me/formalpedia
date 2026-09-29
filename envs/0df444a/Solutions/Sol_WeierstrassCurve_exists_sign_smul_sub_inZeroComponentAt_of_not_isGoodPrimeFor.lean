-- Prove2me | solution 1 for WeierstrassCurve.exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e05dc56b-5207-535a-98da-1b8638b88859

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub
import Theorems.Thm_WeierstrassCurve_exists_torsionBy_residueChar_not_inZeroComponentAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
open scoped WeierstrassCurve.Affine

noncomputable section

namespace WLightEB

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

section Sign

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

private def pairSign (t₁ t₂ : X) (ht : t₁ ≠ t₂)
    (hperm : ∀ g : G, (g • t₁ = t₁ ∧ g • t₂ = t₂) ∨ (g • t₁ = t₂ ∧ g • t₂ = t₁)) : G →* ℤˣ where
  toFun g := if g • t₁ = t₁ then 1 else -1
  map_one' := by simp
  map_mul' g h := by
    rcases hperm h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rcases hperm g with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;>
      simp [mul_smul, h1, g1, g2, ht.symm]

variable {t₁ t₂ : X} {ht : t₁ ≠ t₂}
  {hperm : ∀ g : G, (g • t₁ = t₁ ∧ g • t₂ = t₂) ∨ (g • t₁ = t₂ ∧ g • t₂ = t₁)}

private theorem pairSign_apply_of_smul_eq {g : G} (hg : g • t₁ = t₁) : pairSign t₁ t₂ ht hperm g = 1 := by
  simp [pairSign, hg]

private theorem pairSign_apply_of_smul_ne {g : G} (hg : g • t₁ ≠ t₁) : pairSign t₁ t₂ ht hperm g = -1 := by
  simp [pairSign, hg]

private theorem smul_eq_of_pairSign_eq_one {g : G} (hg : pairSign t₁ t₂ ht hperm g = 1) {s : X}
    (hs : s = t₁ ∨ s = t₂) : g • s = s := by
  have h1 : g • t₁ = t₁ := by
    by_contra hne
    rw [pairSign_apply_of_smul_ne hne] at hg
    exact absurd hg (by decide)
  rcases hperm g with ⟨_, h2⟩ | ⟨h1', _⟩
  · rcases hs with rfl | rfl
    · exact h1
    · exact h2
  · exact absurd (h1.symm.trans h1') ht

private theorem smul_ne_of_pairSign_eq_neg_one {g : G} (hg : pairSign t₁ t₂ ht hperm g = -1) {s : X}
    (hs : s = t₁ ∨ s = t₂) : g • s ≠ s := by
  have h1 : g • t₁ ≠ t₁ := fun heq => by
    rw [pairSign_apply_of_smul_eq heq] at hg
    exact absurd hg (by decide)
  rcases hperm g with ⟨h1', _⟩ | ⟨h1', h2'⟩
  · exact absurd h1' h1
  · rcases hs with rfl | rfl
    · rw [h1']; exact ht.symm
    · rw [h2']; exact ht

end Sign

section Tangent

private theorem tangentQuad_eq {F : Type*} [Field F] (a₁ a₂ a₃ a₄ a₆ x₀ y₀ x y : F)
    (heq : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hFy : 2 * y₀ + a₁ * x₀ + a₃ = 0) (hFx : a₁ * y₀ = 3 * x₀ ^ 2 + 2 * a₂ * x₀ + a₄) :
    (y - y₀) ^ 2 + a₁ * (y - y₀) * (x - x₀) - (3 * x₀ + a₂) * (x - x₀) ^ 2 =
      (x - x₀) ^ 3 - (y₀ ^ 2 + a₁ * x₀ * y₀ + a₃ * y₀ - (x₀ ^ 3 + a₂ * x₀ ^ 2 + a₄ * x₀ + a₆)) := by
  linear_combination heq - (x - x₀) * hFx - (y - y₀) * hFy

private theorem slope_mem_and_residue_root (A : ValuationSubring (AlgebraicClosure ℚ))
    {a₁ c : AlgebraicClosure ℚ} (ha₁ : a₁ ∈ A) (hc : c ∈ A)
    {s d F₀ : AlgebraicClosure ℚ}
    (hQ : (s ^ 2 + a₁ * s - c) * d ^ 2 = d ^ 3 - F₀)
    (hd : A.valuation d < 1) (hsh : A.valuation F₀ < A.valuation d ^ 2) :
    ∃ hs : s ∈ A, IsLocalRing.residue A ⟨s, hs⟩ ^ 2 +
        IsLocalRing.residue A ⟨a₁, ha₁⟩ * IsLocalRing.residue A ⟨s, hs⟩ -
        IsLocalRing.residue A ⟨c, hc⟩ = 0 := by
  have hd0 : A.valuation d ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsh
    exact (not_lt_zero : ¬ A.valuation F₀ < 0) hsh
  have hdpos : 0 < A.valuation d := zero_lt_iff.mpr hd0
  have hd2pos : 0 < A.valuation d ^ 2 := pow_pos hdpos 2

  have hh : A.valuation (s ^ 2 + a₁ * s - c) < 1 := by
    have h1 : A.valuation ((s ^ 2 + a₁ * s - c) * d ^ 2) < A.valuation d ^ 2 := by
      rw [hQ]
      apply Valuation.map_sub_lt
      · rw [Valuation.map_pow]
        exact pow_lt_pow_right_of_lt_one₀ hdpos hd (by norm_num)
      · exact hsh
    rw [Valuation.map_mul, Valuation.map_pow] at h1
    by_contra hge
    push Not at hge
    have : A.valuation d ^ 2 ≤ A.valuation (s ^ 2 + a₁ * s - c) * A.valuation d ^ 2 := by
      calc A.valuation d ^ 2 = 1 * A.valuation d ^ 2 := (one_mul _).symm
        _ ≤ A.valuation (s ^ 2 + a₁ * s - c) * A.valuation d ^ 2 :=
          mul_le_mul_of_nonneg_right hge (le_of_lt hd2pos)
    exact (not_lt.mpr this) h1

  have hs : s ∈ A := by
    rw [← A.valuation_le_one_iff]
    by_contra hgt
    push Not at hgt
    have hspos : 0 < A.valuation s := lt_trans zero_lt_one hgt
    have hsq : A.valuation (a₁ * s - c) < A.valuation (s ^ 2) := by
      rw [Valuation.map_pow, sq]
      apply Valuation.map_sub_lt
      · rw [Valuation.map_mul]
        calc A.valuation a₁ * A.valuation s ≤ 1 * A.valuation s :=
              mul_le_mul_of_nonneg_right (A.valuation_le_one ⟨a₁, ha₁⟩) (le_of_lt hspos)
          _ = A.valuation s := one_mul _
          _ < A.valuation s * A.valuation s := by
              simpa using mul_lt_mul_of_pos_right hgt hspos
      · calc A.valuation c ≤ 1 := A.valuation_le_one ⟨c, hc⟩
          _ < A.valuation s := hgt
          _ = 1 * A.valuation s := (one_mul _).symm
          _ < A.valuation s * A.valuation s := mul_lt_mul_of_pos_right hgt hspos
    have heqv : A.valuation (s ^ 2 + a₁ * s - c) = A.valuation (s ^ 2) := by
      rw [add_sub_assoc]
      exact Valuation.map_add_eq_of_lt_left _ hsq
    have : (1 : A.ValueGroup) < A.valuation (s ^ 2) := by
      rw [Valuation.map_pow]
      calc (1 : A.ValueGroup) < A.valuation s := hgt
        _ = 1 * A.valuation s := (one_mul _).symm
        _ < A.valuation s * A.valuation s := mul_lt_mul_of_pos_right hgt hspos
        _ = A.valuation s ^ 2 := (sq _).symm
    exact absurd (heqv ▸ hh) (not_lt.mpr (le_of_lt this))
  refine ⟨hs, ?_⟩

  have hmem : (⟨s, hs⟩ ^ 2 + ⟨a₁, ha₁⟩ * ⟨s, hs⟩ - ⟨c, hc⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [A.valuation_lt_one_iff]
    exact hh
  have := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  simp at this
  exact this

private theorem root_dichotomy {F : Type*} [Field F] {a c r₁ r₂ : F}
    (h₁ : r₁ ^ 2 + a * r₁ - c = 0) (h₂ : r₂ ^ 2 + a * r₂ - c = 0) :
    r₁ = r₂ ∨ r₁ = -a - r₂ := by
  have : (r₁ - r₂) * (r₁ - (-a - r₂)) = 0 := by linear_combination h₁ - h₂
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem root_ne_conj {F : Type*} [Field F] {a c r : F}
    (h : r ^ 2 + a * r - c = 0) (hdisc : a ^ 2 + 4 * c ≠ 0) : r ≠ -a - r := by
  intro hr
  apply hdisc
  linear_combination (-4 : F) * h + (2 * r + a) * hr

end Tangent

section Centre

private theorem smul_criticalCentre_eq (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ}
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    σ x₀ = x₀ ∧ σ y₀ = y₀ := by

  have hFy' : 2 * σ y₀ + (W.a₁ : AlgebraicClosure ℚ) * σ x₀ + W.a₃ = 0 := by
    have h := congrArg σ hFy
    simpa only [map_add, map_mul, map_intCast, map_ofNat, map_zero] using h
  have hFx' : (W.a₁ : AlgebraicClosure ℚ) * σ y₀ = 3 * σ x₀ ^ 2 + 2 * W.a₂ * σ x₀ + W.a₄ := by
    have h := congrArg σ hFx
    simpa only [map_add, map_mul, map_pow, map_intCast, map_ofNat] using h

  have hbad' : A.valuation (σ y₀ ^ 2 + W.a₁ * σ x₀ * σ y₀ + W.a₃ * σ y₀
      - (σ x₀ ^ 3 + W.a₂ * σ x₀ ^ 2 + W.a₄ * σ x₀ + W.a₆)) < 1 := by
    have hmap : σ (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
        = σ y₀ ^ 2 + W.a₁ * σ x₀ * σ y₀ + W.a₃ * σ y₀
          - (σ x₀ ^ 3 + W.a₂ * σ x₀ ^ 2 + W.a₄ * σ x₀ + W.a₆) := by
      simp only [map_sub, map_add, map_mul, map_pow, map_intCast]
    rw [← hmap, ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A hσ]
    exact hbad

  set dd := σ x₀ - x₀ with hdd
  have hcube : 2 * ((σ y₀ ^ 2 + W.a₁ * σ x₀ * σ y₀ + W.a₃ * σ y₀
        - (σ x₀ ^ 3 + W.a₂ * σ x₀ ^ 2 + W.a₄ * σ x₀ + W.a₆))
      - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))) = dd ^ 3 := by
    rw [hdd]
    linear_combination (-((W.a₁ : AlgebraicClosure ℚ) * σ x₀ + W.a₃ + 2 * y₀) / 2) * hFy
      + (σ x₀ - x₀) * hFx + (((W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ + 2 * σ y₀) / 2) * hFy'
      + (σ x₀ - x₀) * hFx'

  have h2A : (2 : AlgebraicClosure ℚ) ∈ A := by exact_mod_cast natCast_mem A 2
  have hvdd : A.valuation dd < 1 := by
    have h3 : A.valuation dd ^ 3 < 1 := by
      rw [← Valuation.map_pow, ← hcube, Valuation.map_mul]
      calc A.valuation 2 * _ ≤ 1 * _ :=
            mul_le_mul_of_nonneg_right (A.valuation_le_one ⟨2, h2A⟩) zero_le'
        _ < 1 := by
            rw [one_mul]
            exact Valuation.map_sub_lt _ hbad' hbad
    by_contra hge
    push Not at hge
    exact (not_lt.mpr (one_le_pow₀ hge)) h3

  have hb₂ : (W.b₂ : AlgebraicClosure ℚ) = (W.a₁ : AlgebraicClosure ℚ) ^ 2 + 4 * W.a₂ := by
    simp only [WeierstrassCurve.b₂]; push_cast; ring
  have hroot : dd * (6 * (σ x₀ + x₀) + W.b₂) = 0 := by
    rw [hdd, hb₂]
    linear_combination (-2) * hFx' + (W.a₁ : AlgebraicClosure ℚ) * hFy' + 2 * hFx
      - (W.a₁ : AlgebraicClosure ℚ) * hFy
  have hσx : σ x₀ = x₀ := by
    rcases mul_eq_zero.mp hroot with h | h
    · exact sub_eq_zero.mp h
    ·
      exfalso
      have h6 : 6 * dd = -((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) := by
        rw [hdd]; linear_combination h
      have h6A : (6 : AlgebraicClosure ℚ) ∈ A := by exact_mod_cast natCast_mem A 6
      have : A.valuation (6 * dd) < 1 := by
        rw [Valuation.map_mul]
        calc A.valuation 6 * A.valuation dd ≤ 1 * A.valuation dd :=
              mul_le_mul_of_nonneg_right (A.valuation_le_one ⟨6, h6A⟩) zero_le'
          _ < 1 := by rw [one_mul]; exact hvdd
      rw [h6, Valuation.map_neg, hnode] at this
      exact lt_irrefl _ this
  refine ⟨hσx, ?_⟩
  have h2 : (2 : AlgebraicClosure ℚ) * (σ y₀ - y₀) = 0 := by
    rw [hσx] at hFy'
    linear_combination hFy' - hFy
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · exact sub_eq_zero.mp h

end Centre

section Assembly

private theorem equation_cast (W : WeierstrassCurve ℤ) {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y) :
    y ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * x * y + (W.a₃ : AlgebraicClosure ℚ) * y =
      x ^ 3 + (W.a₂ : AlgebraicClosure ℚ) * x ^ 2 + (W.a₄ : AlgebraicClosure ℚ) * x + (W.a₆ : AlgebraicClosure ℚ) := by
  have hE := h.left
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  exact hE

private theorem slope_data (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ}
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : AlgebraicClosure ℚ} (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hX : A.valuation (x - x₀) < 1)
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2)
    (ha₁A : ((W.a₁ : ℤ) : AlgebraicClosure ℚ) ∈ A) (hcA : (3 * x₀ + (W.a₂ : AlgebraicClosure ℚ)) ∈ A) :
    ∃ hs : (y - y₀) / (x - x₀) ∈ A,
      IsLocalRing.residue A ⟨(y - y₀) / (x - x₀), hs⟩ ^ 2 +
        IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ * IsLocalRing.residue A ⟨(y - y₀) / (x - x₀), hs⟩ -
        IsLocalRing.residue A ⟨3 * x₀ + (W.a₂ : AlgebraicClosure ℚ), hcA⟩ = 0 := by
  have hd0 : x - x₀ ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero, zero_pow two_ne_zero] at hsh
    exact (not_lt_zero : ¬ A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 0) hsh
  have hsd : (y - y₀) / (x - x₀) * (x - x₀) = y - y₀ := div_mul_cancel₀ _ hd0
  have hQ : (((y - y₀) / (x - x₀)) ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * ((y - y₀) / (x - x₀)) -
      (3 * x₀ + (W.a₂ : AlgebraicClosure ℚ))) * (x - x₀) ^ 2 = (x - x₀) ^ 3 - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
    have hring : (((y - y₀) / (x - x₀)) ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * ((y - y₀) / (x - x₀)) -
        (3 * x₀ + (W.a₂ : AlgebraicClosure ℚ))) * (x - x₀) ^ 2 =
        ((y - y₀) / (x - x₀) * (x - x₀)) ^ 2 +
          (W.a₁ : AlgebraicClosure ℚ) * ((y - y₀) / (x - x₀) * (x - x₀)) * (x - x₀) -
          (3 * x₀ + (W.a₂ : AlgebraicClosure ℚ)) * (x - x₀) ^ 2 := by ring
    rw [hring, hsd]
    exact tangentQuad_eq (W.a₁ : AlgebraicClosure ℚ) W.a₂ W.a₃ W.a₄ W.a₆ x₀ y₀ x y (equation_cast W h) hFy hFx
  exact slope_mem_and_residue_root A ha₁A hcA hQ hX hsh

private theorem exists_sign_smul_sub_inZeroComponentAt (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ ψ : ↥(A.decompositionSubgroup ℚ) →* ℤˣ,
      (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → ψ σ = 1) ∧
      ∀ σ : ↥(A.decompositionSubgroup ℚ),
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, p • y = 0 →
          W.InZeroComponentAt A
            ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • y - ((ψ σ : ℤˣ) : ℤ) • y) := by
  have hp : p.Prime := Fact.out
  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction W hp hΔ hpΔ hpc₄ A hA
  have hvΔ :=
    WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre W A hx₀ hy₀ hFy hFx hnode hbad
  have ha₁A : ((W.a₁ : ℤ) : AlgebraicClosure ℚ) ∈ A := intCast_mem A _
  have hcA : (3 * x₀ + (W.a₂ : AlgebraicClosure ℚ)) ∈ A :=
    add_mem (mul_mem (by exact_mod_cast natCast_mem A 3) hx₀) (intCast_mem A _)
  have hb₂ : (W.b₂ : AlgebraicClosure ℚ) = (W.a₁ : AlgebraicClosure ℚ) ^ 2 + 4 * W.a₂ := by
    simp only [WeierstrassCurve.b₂]; push_cast; ring

  have hdiscA : ((W.a₁ : AlgebraicClosure ℚ) ^ 2 + 4 * (3 * x₀ + (W.a₂ : AlgebraicClosure ℚ))) ∈ A :=
    add_mem (pow_mem ha₁A 2) (mul_mem (by exact_mod_cast natCast_mem A 4) hcA)
  have hdisc : IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ ^ 2 +
      4 * IsLocalRing.residue A ⟨3 * x₀ + (W.a₂ : AlgebraicClosure ℚ), hcA⟩ ≠ 0 := by
    intro h0
    have hres : IsLocalRing.residue A ⟨_, hdiscA⟩ = 0 := by
      have : (⟨_, hdiscA⟩ : A) = ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ ^ 2 +
          (⟨3 * x₀ + (W.a₂ : AlgebraicClosure ℚ), hcA⟩ + ⟨3 * x₀ + (W.a₂ : AlgebraicClosure ℚ), hcA⟩ +
            ⟨3 * x₀ + (W.a₂ : AlgebraicClosure ℚ), hcA⟩ + ⟨3 * x₀ + (W.a₂ : AlgebraicClosure ℚ), hcA⟩) :=
        Subtype.ext (by push_cast; ring)
      rw [this]
      simp only [map_add, map_pow]
      linear_combination h0
    have hlt : A.valuation ((W.a₁ : AlgebraicClosure ℚ) ^ 2 + 4 * (3 * x₀ + (W.a₂ : AlgebraicClosure ℚ))) < 1 :=
      (A.valuation_lt_one_iff ⟨_, hdiscA⟩).mp ((IsLocalRing.residue_eq_zero_iff _).mp hres)
    have heq : (W.a₁ : AlgebraicClosure ℚ) ^ 2 + 4 * (3 * x₀ + (W.a₂ : AlgebraicClosure ℚ)) = (W.b₂ : AlgebraicClosure ℚ) + 12 * x₀ := by
      rw [hb₂]; ring
    rw [heq, hnode] at hlt
    exact lt_irrefl _ hlt

  obtain ⟨P₁, hP₁⟩ :=
    WeierstrassCurve.exists_torsionBy_residueChar_not_inZeroComponentAt W hp hΔ hpΔ hpc₄ A hA
  have hP₁tor : p • (P₁ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
    have h := (Submodule.mem_torsionBy_iff (R := ℤ) _ _).mp P₁.2
    rwa [natCast_zsmul] at h
  rcases hq : (P₁ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) with _ | @⟨x₁, y₁, h₁⟩
  · exfalso; apply hP₁; rw [hq]; exact Or.inl rfl
  rw [hq] at hP₁ hP₁tor
  have hX₁ : A.valuation (x₁ - x₀) < 1 :=
    (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre W A hx₀ hy₀ hFy hFx hnode
      hbad h₁).mp hP₁
  have hsh₁ : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x₁ - x₀) ^ 2 := by
    rw [← hvΔ]
    exact (WeierstrassCurve.valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt W hp hΔ hpΔ
      hpc₄ A hA hx₀ hy₀ hFy hFx hnode hbad hp hp2 h₁ hP₁tor hX₁).1
  obtain ⟨hs₁, hroot₁⟩ := slope_data W A hFy hFx h₁ hX₁ hsh₁ ha₁A hcA

  have hfixA : ∀ (g : ↥(A.decompositionSubgroup ℚ)) (z : AlgebraicClosure ℚ) (hz : z ∈ A),
      (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) z = z →
        g • IsLocalRing.residue A ⟨z, hz⟩ = IsLocalRing.residue A ⟨z, hz⟩ := by
    intro g z hz hgz
    rw [← IsLocalRing.ResidueField.residue_smul]
    congr 1
    exact Subtype.ext hgz
  have hperm : ∀ g : ↥(A.decompositionSubgroup ℚ),
      (g • IsLocalRing.residue A ⟨_, hs₁⟩ = IsLocalRing.residue A ⟨_, hs₁⟩ ∧
        g • (-IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ - IsLocalRing.residue A ⟨_, hs₁⟩) =
          -IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ - IsLocalRing.residue A ⟨_, hs₁⟩) ∨
      (g • IsLocalRing.residue A ⟨_, hs₁⟩ =
          -IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ - IsLocalRing.residue A ⟨_, hs₁⟩ ∧
        g • (-IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ - IsLocalRing.residue A ⟨_, hs₁⟩) =
          IsLocalRing.residue A ⟨_, hs₁⟩) := by
    intro g
    have hga : g • IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ =
        IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ := hfixA g _ ha₁A (map_intCast _ _)
    have hgc : g • IsLocalRing.residue A ⟨3 * x₀ + (W.a₂ : AlgebraicClosure ℚ), hcA⟩ =
        IsLocalRing.residue A ⟨3 * x₀ + (W.a₂ : AlgebraicClosure ℚ), hcA⟩ := by
      refine hfixA g _ hcA ?_
      rw [map_add, map_mul, map_ofNat, map_intCast,
        (smul_criticalCentre_eq W A hFy hFx hnode hbad g.2).1]

    have hgroot : (g • IsLocalRing.residue A ⟨_, hs₁⟩) ^ 2 +
        IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ * (g • IsLocalRing.residue A ⟨_, hs₁⟩) -
        IsLocalRing.residue A ⟨3 * x₀ + (W.a₂ : AlgebraicClosure ℚ), hcA⟩ = 0 := by
      have h := congrArg (fun r => g • r) hroot₁
      simp only [smul_sub, smul_add, smul_mul', smul_pow', smul_zero, hga, hgc] at h
      exact h
    rcases root_dichotomy hgroot hroot₁ with h | h
    · left
      refine ⟨h, ?_⟩
      rw [smul_sub, smul_neg, hga, h]
    · right
      refine ⟨h, ?_⟩
      rw [smul_sub, smul_neg, hga, h]
      ring
  have ht : IsLocalRing.residue A ⟨_, hs₁⟩ ≠
      -IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ - IsLocalRing.residue A ⟨_, hs₁⟩ :=
    root_ne_conj hroot₁ hdisc

  classical
  refine ⟨pairSign _ _ ht hperm, ?_, ?_⟩
  ·
    intro g hg
    apply pairSign_apply_of_smul_eq
    have h1 := MonoidHom.mem_ker.mp hg
    exact RingEquiv.congr_fun h1 (IsLocalRing.residue A ⟨_, hs₁⟩)
  · intro g P hPtor

    rcases Int.units_eq_one_or (pairSign _ _ ht hperm g) with hψ | hψ
    ·
      rw [hψ, Units.val_one, one_zsmul]
      by_cases hP0 : W.InZeroComponentAt A P
      · exact WeierstrassCurve.inZeroComponentAt_sub W A
          (WeierstrassCurve.inZeroComponentAt_smul W A g.2 hP0) hP0
      · rcases hPq : P with _ | @⟨x, y, h⟩
        · exfalso; apply hP0; rw [hPq]; exact Or.inl rfl
        rw [hPq] at hP0 hPtor
        have hX : A.valuation (x - x₀) < 1 :=
          (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre W A hx₀ hy₀ hFy hFx
            hnode hbad h).mp hP0
        have hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2 := by
          rw [← hvΔ]
          exact (WeierstrassCurve.valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt W hp hΔ
            hpΔ hpc₄ A hA hx₀ hy₀ hFy hFx hnode hbad hp hp2 h hPtor hX).1
        obtain ⟨hs, hroot⟩ := slope_data W A hFy hFx h hX hsh ha₁A hcA

        obtain ⟨h', hsm⟩ : ∃ h', (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • Point.some x y h = Point.some ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x) ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y) h' :=
          ⟨_, rfl⟩
        rw [hsm]
        have hgx₀ := (smul_criticalCentre_eq W A hFy hFx hnode hbad g.2).1
        have hgy₀ := (smul_criticalCentre_eq W A hFy hFx hnode hbad g.2).2
        have hlev : A.valuation ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x - x₀) = A.valuation (x - x₀) := by
          conv_lhs => rw [← hgx₀, ← map_sub]
          exact ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A g.2 _
        have hXg : A.valuation ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x - x₀) < 1 := by
          rw [hlev]; exact hX
        have hslope : ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y - y₀) / ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x - x₀) = (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((y - y₀) / (x - x₀)) := by
          rw [map_div₀, map_sub, map_sub, hgx₀, hgy₀]

        have hsg : (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((y - y₀) / (x - x₀)) ∈ A := (g • (⟨_, hs⟩ : A)).2
        have hres_s : IsLocalRing.residue A ⟨_, hs⟩ = IsLocalRing.residue A ⟨_, hs₁⟩ ∨
            IsLocalRing.residue A ⟨_, hs⟩ =
              -IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ - IsLocalRing.residue A ⟨_, hs₁⟩ :=
          root_dichotomy hroot hroot₁
        have hfix : g • IsLocalRing.residue A ⟨_, hs⟩ = IsLocalRing.residue A ⟨_, hs⟩ :=
          smul_eq_of_pairSign_eq_one hψ hres_s
        have hbr : A.valuation (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y - y₀) / ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x - x₀) - (y - y₀) / (x - x₀)) < 1 := by
          rw [hslope]
          have hmem : (g • (⟨_, hs⟩ : A) - ⟨_, hs⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
            rw [← IsLocalRing.residue_eq_zero_iff, map_sub, IsLocalRing.ResidueField.residue_smul,
              hfix, sub_self]
          exact (A.valuation_lt_one_iff _).mp hmem
        exact (WeierstrassCurve.inZeroComponentAt_sub_of_level_eq_of_branch_eq W A hx₀ hy₀ hFy hFx
          hnode hbad h' h hXg hX hlev (by rw [hlev]; exact hsh) hbr).1
    ·
      rw [hψ, Units.val_neg, Units.val_one, neg_one_zsmul, sub_neg_eq_add]
      by_cases hP0 : W.InZeroComponentAt A P
      · have hneg : W.InZeroComponentAt A (-P) := by
          exact WeierstrassCurve.inZeroComponentAt_sub W A (Or.inl rfl) hP0
        simpa using WeierstrassCurve.inZeroComponentAt_sub W A
          (WeierstrassCurve.inZeroComponentAt_smul W A g.2 hP0) hneg
      · rcases hPq : P with _ | @⟨x, y, h⟩
        · exfalso; apply hP0; rw [hPq]; exact Or.inl rfl
        rw [hPq] at hP0 hPtor
        have hX : A.valuation (x - x₀) < 1 :=
          (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre W A hx₀ hy₀ hFy hFx
            hnode hbad h).mp hP0
        have hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2 := by
          rw [← hvΔ]
          exact (WeierstrassCurve.valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt W hp hΔ
            hpΔ hpc₄ A hA hx₀ hy₀ hFy hFx hnode hbad hp hp2 h hPtor hX).1
        obtain ⟨hs, hroot⟩ := slope_data W A hFy hFx h hX hsh ha₁A hcA
        obtain ⟨h', hsm⟩ : ∃ h', (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • Point.some x y h = Point.some ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x) ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y) h' :=
          ⟨_, rfl⟩
        rw [hsm]
        have hgx₀ := (smul_criticalCentre_eq W A hFy hFx hnode hbad g.2).1
        have hgy₀ := (smul_criticalCentre_eq W A hFy hFx hnode hbad g.2).2
        have hlev : A.valuation ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x - x₀) = A.valuation (x - x₀) := by
          conv_lhs => rw [← hgx₀, ← map_sub]
          exact ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A g.2 _
        have hXg : A.valuation ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x - x₀) < 1 := by
          rw [hlev]; exact hX
        have hslope : ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y - y₀) / ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x - x₀) = (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((y - y₀) / (x - x₀)) := by
          rw [map_div₀, map_sub, map_sub, hgx₀, hgy₀]
        have hsg : (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((y - y₀) / (x - x₀)) ∈ A := (g • (⟨_, hs⟩ : A)).2
        have hres_s : IsLocalRing.residue A ⟨_, hs⟩ = IsLocalRing.residue A ⟨_, hs₁⟩ ∨
            IsLocalRing.residue A ⟨_, hs⟩ =
              -IsLocalRing.residue A ⟨(W.a₁ : AlgebraicClosure ℚ), ha₁A⟩ - IsLocalRing.residue A ⟨_, hs₁⟩ :=
          root_dichotomy hroot hroot₁
        have hmove : g • IsLocalRing.residue A ⟨_, hs⟩ ≠ IsLocalRing.residue A ⟨_, hs⟩ :=
          smul_ne_of_pairSign_eq_neg_one hψ hres_s

        have hbr : A.valuation (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y - y₀) / ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x - x₀) - (y - y₀) / (x - x₀)) = 1 := by
          rw [hslope]
          have hnot : ¬ A.valuation ((g • (⟨_, hs⟩ : A) - ⟨_, hs⟩ : A) : AlgebraicClosure ℚ) < 1 := by
            intro hlt
            apply hmove
            have hmem := (A.valuation_lt_one_iff _).mpr hlt
            rw [← IsLocalRing.residue_eq_zero_iff, map_sub, IsLocalRing.ResidueField.residue_smul,
              sub_eq_zero] at hmem
            exact hmem
          rcases A.valuation_lt_one_or_eq_one (g • (⟨_, hs⟩ : A) - ⟨_, hs⟩) with hlt | heq1
          · exact absurd hlt hnot
          · exact heq1
        exact (WeierstrassCurve.inZeroComponentAt_add_of_level_eq_of_branch_ne W A hx₀ hy₀ hFy hFx
          hnode hbad h' h hXg hX hlev (by rw [hlev]; exact hsh) hbr).1

end Assembly

end WLightEB

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hbad : ¬ W.IsGoodPrimeFor p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ ψ : ↥(A.decompositionSubgroup ℚ) →* ℤˣ,
      (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → ψ σ = 1) ∧
      ∀ σ : ↥(A.decompositionSubgroup ℚ),
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, p • y = 0 →
          W.InZeroComponentAt A
            ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • y - ((ψ σ : ℤˣ) : ℤ) • y) := by
  have hpΔ : (p : ℤ) ∣ W.Δ := by simpa [WeierstrassCurve.IsGoodPrimeFor] using hbad
  exact WLightEB.exists_sign_smul_sub_inZeroComponentAt p hp2 W hΔ hpΔ (hW p Fact.out hpΔ) A hA

end S_WeierstrassCurve_exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor
end P2MW
export P2MW.S_WeierstrassCurve_exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor (solution)
