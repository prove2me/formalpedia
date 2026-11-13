-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.bessel_bound_of_inner_beta_zeta_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:27:57.566574+00:00
-- url     : https://prove2.me/submissions/03f18723-e4bb-4eaf-87dd-cc6590416ed0

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/TwoFamilies.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S16_PairingBessel.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_RepresentationTheory_card_index_mul_sum_induced_family_degree_sq
import Theorems.Thm_OddOrder_Peterfalvi_S16_pair_cross_orthogonal

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- The source difference `Ind 1_H - ζ` is virtual when the `Ind 1_H`
source term is virtual and the distinguished `ζ` is irreducible. -/
theorem sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L :=
  Submodule.sub_mem _ hindZ hzeta_irr.mem_ZIrr

/-- Virtuality of `Ind 1_H` and irreducibility of `ζ` supply the
virtual-character input needed by the Dade bridge for `β`. -/
theorem beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.beta ∈ ZIrr G :=
  H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr
    (H78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

/-- The Dade image defining `β` is supported on the corresponding Dade support. -/
theorem beta_support_subset_dadeSupport (H78 : Hypothesis78 G A L) :
    H78.beta.support ⊆ H78.hyp76.hyp71.hyp.dadeSupport := by
  intro g hg
  by_contra hnot
  exact hg (by
    rw [H78.beta_def]
    exact H78.hyp76.hyp71.isDadeMap.map_eq_zero_of_not_mem_dadeSupport
      H78.indMinusZetaSupp g hnot)

/-- Variant of `sourceDiffNormEvaluation_of_inner_values` using irreducibility of
the chosen `ζ` instead of a raw self-inner-product evaluation. -/
theorem sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.SourceDiffNormEvaluation :=
  H78.sourceDiffNormEvaluation_of_inner_values
    hind_norm hzeta_ind hind_zeta
    (H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr)

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- If `Γ` has Peterfalvi's residual norm formula, its upper bound follows. -/
theorem gammaNormSq_le_of_normQuadraticCorrection_eq
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hgamma : H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD) :
    H78.smallIndex → H78.gammaNormSq hBD ≤ (H78.complementIndex : ℝ) - 1 := by
  intro hsmall
  rw [hgamma]
  have hh_nonneg : 0 ≤ (H78.kernelOrder : ℝ) := by positivity
  have hquad := H78.normQuadraticCorrection_nonneg_of_smallIndex hBD hsmall
  have hprod : 0 ≤ (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD :=
    mul_nonneg hh_nonneg hquad
  linarith

/-- Exact quadratic norm formulas are enough to package Peterfalvi (7.8.b)'s
`NormEstimates`.  This isolates the remaining character-theoretic work to proving
those two formulas from (7.7.b), `BetaDecomp`, and `‖β‖² = e + 1`. -/
theorem normEstimates_of_normQuadraticCorrection_eqs
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hgamma : H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD) :
    H78.NormEstimates hBD where
  zetaNuRho_norm_sq_ge :=
    H78.zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq hBD hzeta
  gamma_norm_sq_le :=
    H78.gammaNormSq_le_of_normQuadraticCorrection_eq hBD hgamma

/-- Once the orthogonal expansion of `‖β‖²` is known, the residual norm formula
for `Γ` is just the arithmetic rearrangement in Peterfalvi (7.8.b). -/
theorem gammaNormSq_eq_of_betaNormSq_expand
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hbetaNorm : H78.betaNormSq = (H78.complementIndex : ℝ) + 1)
    (hexpand : H78.betaNormSq =
      2 +
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) + H78.gammaNormSq hBD) :
    H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD := by
  have hh_ne : (H78.kernelOrder : ℝ) ≠ 0 := by
    exact_mod_cast H78.kernelOrder_pos.ne'
  have he_ne : (H78.complementIndex : ℝ) ≠ 0 := by
    exact_mod_cast H78.complementIndex_pos.ne'
  rw [hbetaNorm] at hexpand
  have hquad :
      (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD =
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) := by
    rw [normQuadraticCorrection]
    field_simp [hh_ne, he_ne]
  rw [hquad]
  linarith

/-- Irreducibility and distinctness of the source `S`-family give its
orthogonality matrix. -/
theorem sourceZeta_orthogonal_of_irreducible_distinct (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j) :
    ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0 := by
  intro i hi j hj
  by_cases hij : i = j
  · rw [if_pos hij, hij]
  · rw [if_neg hij]
    let χ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
      ⟨H78.hyp76.zeta i, hirr i hi⟩
    let ψ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
      ⟨H78.hyp76.zeta j, hirr j hj⟩
    have hne : χ ≠ ψ := by
      intro hχψ
      exact hdistinct i hi j hj hij (congrArg
        (fun θ : OddOrder.RepresentationTheory.IrreducibleCharacter L =>
          (θ : ClassFunction L ℂ)) hχψ)
    simpa [χ, ψ, hne] using
      (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite χ ψ)

/-- Irreducibility of the source `S`-family makes every source norm nonzero. -/
theorem sourceZeta_norm_ne_of_irreducible (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0 := by
  intro i hi
  let χ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
    ⟨H78.hyp76.zeta i, hirr i hi⟩
  have hχ : ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) = 1 := by
    simpa [χ] using
      (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite χ χ)
  rw [hχ]
  norm_num

/-- Source-side beta norm data give Peterfalvi's residual norm formula for `Γ`. -/
theorem gammaNormSq_eq_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD :=
  H78.gammaNormSq_eq_of_betaNormSq_expand hBD
    (H78.betaNormSq_eq_complementIndex_add_one hsrc)
    (H78.betaNormSq_eq_of_source_orthogonal hBD
      horth hnorm_ne hzeta_degree hdegree_sum hzeta_irr)

/-- Once the remaining `(ζ^ν)^ρ` quadratic formula is supplied, the source-side
beta norm data package Peterfalvi (7.8.b)'s `NormEstimates`. -/
theorem normEstimates_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD :=
  H78.normEstimates_of_normQuadraticCorrection_eqs hBD hzeta
    (H78.gammaNormSq_eq_of_source_orthogonal hBD hsrc
      horth hnorm_ne hzeta_degree hdegree_sum hzeta_irr)

/-- Version of `normEstimates_of_source_orthogonal` using the natural source
hypotheses that the `S`-family consists of distinct irreducible characters. -/
theorem normEstimates_of_irreducible_source_data
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD := by
  have hzeta_mem : H78.zetaDistinct ∈ (Finset.univ.erase H78.ind1H) := by
    simp [H78.zetaDistinct_ne_ind1H]
  exact H78.normEstimates_of_source_orthogonal hBD hsrc
    (H78.sourceZeta_orthogonal_of_irreducible_distinct hirr hdistinct)
    (H78.sourceZeta_norm_ne_of_irreducible hirr)
    hzeta_degree hdegree_sum (hirr H78.zetaDistinct hzeta_mem) hzeta

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/TwoFamilies.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section OrthogonalIntegerDecomposition

variable {ι : Type*}

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- Integer-coefficient Pythagoras bridge used in Peterfalvi (7.10): if a class
function decomposes as an orthogonal integer combination plus an orthogonal
residual, then an upper bound on its norm bounds the sum of the diagonal weights
for every nonzero coefficient. -/
theorem sum_weights_le_of_orthogonal_integer_decomposition
    (B : Finset ι) (v : ι → ClassFunction G ℂ) (x : ι → ℤ) (m : ι → ℝ)
    (Γ Γ₁ : ClassFunction G ℂ) (M : ℝ)
    (hΓ : Γ = (∑ i ∈ B, (((x i : ℝ) : ℂ) • v i)) + Γ₁)
    (horth : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) = if i = j then (m i : ℂ) else 0)
    (hΓ₁ : ∀ i ∈ B, ClassFunction.inner Γ₁ (v i) = 0)
    (hm_nonneg : ∀ i ∈ B, 0 ≤ m i)
    (hx_nonzero : ∀ i ∈ B, x i ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ M) :
    (∑ i ∈ B, m i) ≤ M := by
  classical
  have hpyth := inner_self_orthogonalSum_add_re (G := G) B v
    (fun i => (x i : ℝ)) m Γ₁ horth hΓ₁
  have hΓ_norm : (ClassFunction.inner Γ Γ).re =
      (∑ i ∈ B, (x i : ℝ) ^ 2 * m i) +
        (ClassFunction.inner Γ₁ Γ₁).re := by
    rw [hΓ]
    exact hpyth
  have hsum_le_sq : (∑ i ∈ B, m i) ≤
      ∑ i ∈ B, (x i : ℝ) ^ 2 * m i := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hcases : x i ≤ -1 ∨ 1 ≤ x i := by
      have hxi := hx_nonzero i hi
      omega
    have hx_sq : (1 : ℝ) ≤ (x i : ℝ) ^ 2 := by
      rcases hcases with hle | hge
      · have hle' : (x i : ℝ) ≤ -1 := by exact_mod_cast hle
        nlinarith
      · have hge' : (1 : ℝ) ≤ x i := by exact_mod_cast hge
        nlinarith
    simpa [one_mul] using mul_le_mul_of_nonneg_right hx_sq (hm_nonneg i hi)
  have hΓ₁_nonneg : 0 ≤ (ClassFunction.inner Γ₁ Γ₁).re :=
    inner_self_re_nonneg Γ₁
  rw [hΓ_norm] at hΓ_bound
  linarith

open scoped Classical in
/-- Rational-valued version of the integer-coefficient Pythagoras bridge.  This
matches the `𝓑`-sum in Peterfalvi (7.10), whose weights are rational ratios such
as `(h_j - 1) / e_j`, while the norm inequality lives in `ℝ`. -/
theorem sum_rat_weights_le_of_orthogonal_integer_decomposition
    (B : Finset ι) (v : ι → ClassFunction G ℂ) (x : ι → ℤ) (m : ι → ℚ)
    (Γ Γ₁ : ClassFunction G ℂ) (M : ℚ)
    (hΓ : Γ = (∑ i ∈ B, (((x i : ℝ) : ℂ) • v i)) + Γ₁)
    (horth : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) = if i = j then (m i : ℂ) else 0)
    (hΓ₁ : ∀ i ∈ B, ClassFunction.inner Γ₁ (v i) = 0)
    (hm_nonneg : ∀ i ∈ B, 0 ≤ m i)
    (hx_nonzero : ∀ i ∈ B, x i ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (M : ℝ)) :
    (∑ i ∈ B, m i) ≤ M := by
  have horth_real : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) =
        if i = j then (((m i : ℝ) : ℂ)) else 0 := by
    intro i hi j hj
    simpa using horth i hi j hj
  have hm_nonneg_real : ∀ i ∈ B, 0 ≤ (m i : ℝ) := by
    intro i hi
    exact_mod_cast hm_nonneg i hi
  have hreal := sum_weights_le_of_orthogonal_integer_decomposition
    B v x (fun i => (m i : ℝ)) Γ Γ₁ (M : ℝ) hΓ horth_real hΓ₁ hm_nonneg_real
    hx_nonzero hΓ_bound
  have hcast : ((∑ i ∈ B, m i) : ℝ) ≤ (M : ℝ) := by
    simpa using hreal
  exact_mod_cast hcast

end OrthogonalIntegerDecomposition

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S16_PairingCoherence.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- The zeta family of `h78` is the placed induced family (definitional). -/
theorem h78_zeta_eq (i : Fin (data.n + 1)) :
    (data.h78 hG).hyp76.zeta i = data.zeta i := rfl

/-- The distinguished index of `h78` is `0` (definitional). -/
theorem h78_zetaDistinct_eq : (data.h78 hG).zetaDistinct = 0 := rfl

/-- The principal index of `h78` is `ind1H` (definitional). -/
theorem h78_ind1H_eq : (data.h78 hG).ind1H = data.ind1H := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is irreducible** (Frobenius kernel induction,
[Is] Thm 6.34). -/
theorem h78_zeta_irreducible :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) := by
  have := data.kernelIn_normal
  rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

/-- **The induced principal `ζ_{ind1H} = Ind 1_H` is a virtual character.** -/
theorem h78_ind_mem_ZIrr :
    (data.h78 hG).hyp76.zeta (data.h78 hG).ind1H ∈ ZIrr ↥L := by
  have := data.kernelIn_normal
  rw [data.h78_ind1H_eq, data.h78_zeta_eq]
  exact ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr

/-- **The `(7.8)` coherent source set equals the (12.1) family `S`.** -/
theorem h78_sourceSet_eq : (data.h78 hG).sourceSet = data.typeIHyp.Sset := by
  have := data.kernelIn_normal
  ext φ
  constructor
  · rintro ⟨idx, hidx, rfl⟩
    exact data.zeta_mem_Sset hidx
  · rintro ⟨θ', hθ'_ne, rfl⟩
    obtain ⟨j, hj⟩ := data.cover θ'
    have hj' : data.zeta j = ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ) := hj
    refine ⟨j, ?_, hj'⟩
    intro hjind
    apply induce_ne_trivialChar_induce data.kernelIn θ' hθ'_ne
    rw [← hj', show j = data.ind1H from hjind]
    change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
      = ClassFunction.induce data.kernelIn
        ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
          ClassFunction _ ℂ)
    rw [data.triv]

/-- **The bundle coherence as an `IsCoherent` over the `(7.8)` `sourceSet`** (transport along
`h78_sourceSet_eq`, keeping the same extension `ν`). -/
noncomputable def isCoherentSourceSet :
    OddOrder.Peterfalvi.S07.IsCoherent data.typeIHyp.tau (data.h78 hG).sourceSet
      data.typeIHyp.A where
  nonzero := (data.h78_sourceSet_eq hG).symm ▸ data.coh.nonzero
  extension := data.coh.extension
  extension_inner_eq := fun φ ψ hφ hψ => data.coh.extension_inner_eq φ ψ
    (data.h78_sourceSet_eq hG ▸ hφ) (data.h78_sourceSet_eq hG ▸ hψ)
  extends_on_supported := fun φ hφ => data.coh.extends_on_supported φ
    (data.h78_sourceSet_eq hG ▸ hφ)
  extension_mem_ZIrr := fun φ hφ => data.coh.extension_mem_ZIrr φ
    (data.h78_sourceSet_eq hG ▸ hφ)

/-- **Each nontrivial family member induces irreducibly** (general-index form of
`h78_zeta_irreducible`). -/
theorem zeta_irreducible_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
  have := data.kernelIn_normal
  rw [data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
    (data.theta_ne_trivial hi)

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_PairingBessel.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- `e = [L : H]` as the `subgroupOf` index (bundle form). -/
theorem complementIndex_eq :
    (data.h78 hG).complementIndex = (data.kernelIn).index :=
  complementIndex_eq_subgroupOf_index (data.h78 hG)

/-- `h = |H|` (bundle form). -/
theorem kernelOrder_eq :
    (data.h78 hG).kernelOrder = Nat.card ↥data.kernelIn := by
  rw [show (data.h78 hG).kernelOrder = Nat.card data.kernel from rfl]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.kernel_le).toEquiv).symm

/-- **`ζ_{ind1H}(1) = e`** (the induced principal degree). -/
theorem zeta_ind1H_apply_one :
    (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) (1 : ↥L)
      = ((data.h78 hG).complementIndex : ℂ) := by
  have := data.kernelIn_normal
  rw [data.complementIndex_eq hG]
  change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ) (1 : ↥L)
    = ((data.kernelIn).index : ℂ)
  rw [data.triv]
  exact induce_trivialChar_apply_eq_index data.kernelIn (Subgroup.one_mem _)

/-- **`‖ζ_{ind1H}‖² = e`** (the induced principal norm). -/
theorem zeta_ind1H_normSq :
    ClassFunction.inner ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H))
      ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H))
      = ((data.h78 hG).complementIndex : ℂ) := by
  have := data.kernelIn_normal
  rw [data.complementIndex_eq hG]
  change ClassFunction.inner
      (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ))
      (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ))
    = ((data.kernelIn).index : ℂ)
  rw [data.triv]
  exact induce_trivialChar_normSq_eq_index data.kernelIn

/-- **`ζ_0(1) = e`** (the distinguished degree, bundle form). -/
theorem zeta_zero_apply_one :
    (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct) (1 : ↥L)
      = ((data.h78 hG).complementIndex : ℂ) := by
  rw [data.complementIndex_eq hG]
  exact data.deg0

/-- **The (7.8) source-side norm evaluation** `‖Ind 1_H − ζ‖² = e + 1`. -/
theorem sourceDiffNormEvaluation :
    (data.h78 hG).SourceDiffNormEvaluation := by
  have := data.kernelIn_normal
  refine (data.h78 hG).sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
    (data.zeta_ind1H_normSq hG) ?_ ?_ (data.h78_zeta_irreducible hG)
  · exact induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj 0 data.ind1H
      (Ne.symm data.ind1H_ne_zero)
  · exact induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj data.ind1H 0
      data.ind1H_ne_zero

set_option backward.isDefEq.respectTransparency false in
/-- **The (1.5.d) family degree-square sum** in the `star` form consumed by the
(7.8.b) `NormEstimates` producer: `Σ_{i ≠ ind1H} ζ_i(1)·(ζ_i(1))*/‖ζ_i‖² = (h−1)·e`. -/
theorem degree_sum_star :
    (∑ i ∈ (Finset.univ.erase (data.h78 hG).ind1H),
        (data.h78 hG).hyp76.zeta i (1 : ↥L)
          * star ((data.h78 hG).hyp76.zeta i (1 : ↥L)) /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i))
      = (((data.h78 hG).kernelOrder : ℂ) - 1) * ((data.h78 hG).complementIndex : ℂ) := by
  have := data.kernelIn_normal
  have hstar : ∀ i ∈ Finset.univ.erase (data.h78 hG).ind1H,
      (data.h78 hG).hyp76.zeta i (1 : ↥L)
          * star ((data.h78 hG).hyp76.zeta i (1 : ↥L)) /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i)
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) ^ 2 /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i) := by
    intro i _
    have hreal : star ((data.h78 hG).hyp76.zeta i (1 : ↥L))
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) := by
      rw [data.h78_zeta_eq]
      exact induce_apply_one_star data.kernelIn (data.θ i)
    rw [hreal, sq]
  have h := family_degree_sum data.kernelIn data.θ data.inj data.cover data.ind1H data.triv
  calc (∑ i ∈ (Finset.univ.erase (data.h78 hG).ind1H),
        (data.h78 hG).hyp76.zeta i (1 : ↥L)
          * star ((data.h78 hG).hyp76.zeta i (1 : ↥L)) /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i))
      = ∑ i ∈ (Finset.univ.erase (data.h78 hG).ind1H),
          (data.h78 hG).hyp76.zeta i (1 : ↥L) ^ 2 /
            ClassFunction.inner ((data.h78 hG).hyp76.zeta i)
              ((data.h78 hG).hyp76.zeta i) := Finset.sum_congr rfl hstar
    _ = ((data.kernelIn).index : ℂ) * ((Nat.card ↥data.kernelIn : ℂ) - 1) := h
    _ = (((data.h78 hG).kernelOrder : ℂ) - 1) * ((data.h78 hG).complementIndex : ℂ) := by
        rw [data.complementIndex_eq hG, data.kernelOrder_eq hG]
        ring

/-- **`2e + 1 ≤ h`** (`smallIndex`): the Frobenius kernel of odd order is more than
twice the complement. -/
theorem smallIndex : (data.h78 hG).smallIndex := by
  have := data.kernelIn_normal
  have hKodd : Odd (Nat.card ↥data.kernelIn) :=
    (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)).of_dvd_nat
      (Subgroup.card_subgroup_dvd_card _)
  have hCodd : Odd (Nat.card ↥data.C) :=
    (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)).of_dvd_nat
      (Subgroup.card_subgroup_dvd_card data.C)
  have hfrobB := OddOrder.Peterfalvi.S14.frobenius_two_mul_card_complement_add_one_le_card_kernel
    data.hFrob hKodd hCodd data.hFrob.ne_bot_kernel
  change 2 * (data.h78 hG).complementIndex + 1 ≤ (data.h78 hG).kernelOrder
  have hcompl : Nat.card ↥data.kernelIn * Nat.card ↥data.C = Nat.card ↥L :=
    data.hFrob.isComplement.card_mul_card
  have hce : (data.h78 hG).complementIndex = Nat.card ↥data.C := by
    change Nat.card ↥L / Nat.card data.kernel = Nat.card ↥data.C
    rw [show Nat.card data.kernel = Nat.card ↥data.kernelIn from
        (data.kernelOrder_eq hG) ▸ rfl,
      ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
  rw [data.kernelOrder_eq hG, hce]
  exact hfrobB

/-- `d_{ind1H} = 1` for the constructor-computed `hyp76.d`. -/
theorem hyp76_d_ind1H_eq_one : (data.h78 hG).hyp76.d ((data.h78 hG).ind1H) = 1 := by
  have := data.kernelIn_normal
  change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ) (1 : ↥L) /
      ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) = 1
  rw [← data.zeta_deg_match, div_self (induce_apply_one_ne_zero _ (data.θ 0))]

/-- The coherence agreement in constructor-computed `d`/`psiSupp` form (the
`hagree'` input of the `cCoeff` evaluations). -/
theorem hagree_hyp76 (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∀ i : Fin (data.n + 1), i ≠ 0 → i ≠ (data.h78 hG).ind1H →
      (data.h78 hG).hyp76.hyp71.τ ((data.h78 hG).hyp76.psiSupp i)
        = (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
          - (data.h78 hG).hyp76.d i • (data.h78 hG).nu ((data.h78 hG).hyp76.zeta 0) := by
  have := data.kernelIn_normal
  intro i hi0 hii
  have hz0 : ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (data.θ 0)
  have hdeq : (data.h78 hG).hyp76.d i = data.d i := by
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) = data.d i
    rw [div_eq_iff hz0]; exact data.zeta_deg i
  have hsub : (data.h78 hG).hyp76.psiSupp i
      = (⟨data.zeta i - data.d i • data.zeta 0, data.psi_support hG i⟩ :
        OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ
          (typeIA L data.typeIHyp.typeI) L) := by
    apply Subtype.ext
    change data.zeta i - (data.h78 hG).hyp76.d i • data.zeta 0
      = data.zeta i - data.d i • data.zeta 0
    rw [hdeq]
  rw [hsub, hdeq]
  exact data.hagree hG i hi0 hii

/-- **The (7.8.b) quadratic norm identity** `‖ζ_0^{νρ}‖² = Q(a) + (1 − e/h)` for the
bundle (the `hzeta` input of `NormEstimates`), discharged from the Dade-family facts
exactly as in `zetaNuRhoNormSqGeOfDade`. -/
theorem zetaNuRhoNormSq_eq_normQuad (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).zetaNuRhoNormSq =
      (data.h78 hG).normQuadraticCorrection (data.betaDecomp hG) +
        (1 - ((data.h78 hG).complementIndex : ℝ) / ((data.h78 hG).kernelOrder : ℝ)) := by
  have := data.kernelIn_normal
  have hz0 : ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (data.θ 0)
  have hz0_compl : ClassFunction.induce data.kernelIn
      (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) = ((data.h78 hG).complementIndex : ℂ) :=
    data.zeta_zero_apply_one hG
  refine zetaNuRhoNormSq_eq_normQuad_of_facts (data.h78 hG) (data.betaDecomp hG) rfl
    (induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj) ?_ ?_ ?_ ?_ ?_
    (data.zeta_ind1H_normSq hG) (data.zeta_ind1H_apply_one hG) ?_
  · -- `c_{ind1H} = a − 1`.
    rw [cCoeff_nu_zeta_zero_ind1H_eq (data.h78 hG) (data.h78 hG).nu rfl
      (data.hyp76_d_ind1H_eq_one hG)]
    show ClassFunction.inner (data.h78 hG).beta
        ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta 0)) = ((data.betaDecomp hG).a : ℂ) - 1
    have ha := Classical.choose_spec (exists_betaDecomp_a (data.h78 hG)
      (Submodule.sub_mem _
        (ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr)
        (ClassFunction.induce_mem_ZIrr _ (data.θ 0).property.mem_ZIrr))
      (data.coh.extension_mem_ZIrr _ (Submodule.subset_span
        (data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)))))
    have hBDa : ((data.betaDecomp hG).a : ℂ)
        = ClassFunction.inner (data.h78 hG).beta
            ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta 0)) + 1 := ha
    rw [hBDa]; ring
  · -- `c_i = −d_i` for the non-distinguished, non-`ind1H` indices.
    exact fun i hi0 hii => cCoeff_nu_zeta_zero_eq_neg_d (data.h78 hG).hyp76 (data.h78 hG).nu
      (data.hagree_hyp76 hG) (data.h78 hG).nu_isometry (Ne.symm data.ind1H_ne_zero)
      (fun i hi => induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj i 0 hi)
      data.zeta_zero_norm_one i hi0 hii
  · -- `d_i` is real.
    intro i
    change star (ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L))
      = ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L)
    rw [star_div₀, induce_apply_one_star, induce_apply_one_star]
  · -- `ζ_i(1)` is real.
    exact fun i => induce_apply_one_star data.kernelIn (data.θ i)
  · -- `d_i = ζ_i(1)/e`.
    intro i
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L)
      = ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L)
        / ((data.h78 hG).complementIndex : ℂ)
    rw [hz0_compl]
  · -- The `Ioi`-sum `G = e(h−1) − e²`.
    rw [data.complementIndex_eq hG,
      show ((data.h78 hG).kernelOrder : ℂ) = (Nat.card ↥data.kernelIn : ℂ) from by
        rw [data.kernelOrder_eq hG]]
    exact family_degree_sum_Ioi data.kernelIn data.θ data.inj data.cover data.ind1H
      data.ind1H_ne_zero data.triv
      (by rw [← data.complementIndex_eq hG]; exact hz0_compl) data.zeta_zero_norm_one

/-- **The (7.8.b) `NormEstimates` of the bundle**: both the `ζ`-lower bound
`1 − e/h ≤ ‖ζ_0^{νρ}‖²` and the residual bound `‖Γ‖² ≤ e − 1`. -/
theorem normEstimates (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).NormEstimates (data.betaDecomp hG) := by
  have := data.kernelIn_normal
  refine (data.h78 hG).normEstimates_of_irreducible_source_data (data.betaDecomp hG)
    (data.sourceDiffNormEvaluation hG) ?_ ?_ (data.zeta_zero_apply_one hG)
    (data.degree_sum_star hG) (data.zetaNuRhoNormSq_eq_normQuad hG)
  · -- Every non-`ind1H` member is irreducible.
    intro i hi
    exact data.zeta_irreducible_at hG (Finset.mem_erase.mp hi).1
  · -- Distinct indices give distinct characters.
    intro i _ j _ hij heq
    exact hij (data.inj heq)

/-- `d_0 = 1` (the distinguished source is linear: `ζ_0(1) = e = [L:H]·θ_0(1)`). -/
theorem d_zero_eq_one : data.d 0 = 1 := by
  have := data.kernelIn_normal
  have h := data.zeta_deg 0
  have hz0 : data.zeta 0 (1 : ↥L) ≠ 0 := induce_apply_one_ne_zero _ (data.θ 0)
  have h2 : data.d 0 * data.zeta 0 (1 : ↥L) = 1 * data.zeta 0 (1 : ↥L) := by
    rw [one_mul, ← h]
  exact mul_right_cancel₀ hz0 h2

/-- `d_i` is a positive natural (the source degree). -/
theorem exists_d_natCast (i : Fin (data.n + 1)) :
    ∃ m : ℕ, 0 < m ∧ data.d i = (m : ℂ) := by
  obtain ⟨m, hm, hcast⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  exact ⟨m, hm, hcast⟩

/-- `star (d_i) = d_i`. -/
theorem d_star (i : Fin (data.n + 1)) : star (data.d i) = data.d i := by
  obtain ⟨m, -, hm⟩ := data.exists_d_natCast i
  rw [hm, star_natCast]

end TypeICoherent78Data

section Pairing

variable [Finite G] {L M : Subgroup G}

variable (dataL : TypeICoherent78Data L) (dataM : TypeICoherent78Data M)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

omit [Finite G] in
/-- Left additivity of the inner product over a finite sum. -/
private theorem inner_sum_left' {ι : Type*} [Fintype G] [Invertible (Nat.card G : ℂ)]
    (s : Finset ι) (f : ι → ClassFunction G ℂ) (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (∑ i ∈ s, f i) ψ = ∑ i ∈ s, ClassFunction.inner (f i) ψ := by
  rw [OddOrder.RepresentationTheory.inner_conj_symm, inner_sum_right, star_sum]
  exact Finset.sum_congr rfl fun i _ =>
    (OddOrder.RepresentationTheory.inner_conj_symm ψ (f i)).symm

/-- **The `β`-pairing is constant along the family** (Peterfalvi's
`(β_M^τ, (φ_i − a_iφ)^τ) = 0`): for `i ≠ ind1H` on the `L`-side,
`⟨β_M, φ_i^ν⟩ = d_i·⟨β_M, φ_0^ν⟩` — the difference `ψ_i^{τ₁}` is a Dade image in
`Ã(L)`, disjoint from `supp β_M ⊆ Ã(M)`. -/
theorem inner_beta_nu_zeta_eq
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H) :
    ClassFunction.inner ((dataM.h78 hG).beta)
        ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i))
      = dataL.d i * ClassFunction.inner ((dataM.h78 hG).beta)
          ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta 0)) := by
  have := dataL.kernelIn_normal
  by_cases hi0 : i = 0
  · subst hi0
    rw [dataL.d_zero_eq_one, one_mul]
    rfl
  -- `⟨β_M, τ₁ψ_i⟩ = 0` by the disjoint Dade supports.
  have hdisj := (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).dadeSupport_disjoint
  have hpsi_img_supp : ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)
      - dataL.d i • (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta 0)).support
      ⊆ (dataL.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
    have hagree := dataL.hagree hG i hi0 hi
    change (dataL.coh.extension (dataL.zeta i)
      - dataL.d i • dataL.coh.extension (dataL.zeta 0)).support
      ⊆ dataL.typeIHyp.dadeData.dade.dadeSupport
    rw [← hagree]
    intro g hg
    rw [ClassFunction.mem_support] at hg
    by_contra hgnot
    have hdade := (dataL.typeIHyp.dadeData.dade.fullDadeIsometryData
).toDadeIsometryData.isDadeMap
    exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)
  have hzero : ClassFunction.inner ((dataM.h78 hG).beta)
      ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)
        - dataL.d i • (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta 0)) = 0 := by
    apply ClassFunction.inner_eq_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp hdisj.symm
      ((dataM.h78 hG).beta_support_subset_dadeSupport hg₁)
      (hpsi_img_supp hg₂)
  rw [ClassFunction.inner_sub_right,
    OddOrder.RepresentationTheory.inner_smul_right, dataL.d_star, sub_eq_zero] at hzero
  exact hzero

/-- Reversed orientation of `pair_cross_orthogonal`: `⟨χ_j^ν, φ_i^ν⟩ = 0`. -/
theorem pair_cross_orthogonal'
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H)
    {j : Fin (dataM.n + 1)} (hj : j ≠ dataM.ind1H) :
    ClassFunction.inner ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j))
      ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)) = 0 := by
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    pair_cross_orthogonal dataL dataM hG hL hM hnc hi hj, star_zero]

set_option backward.isDefEq.respectTransparency false in
/-- **The residual `Γ_M` pairs with the `L`-family exactly as `β_M` does**: for
`i ≠ ind1H`, `⟨Γ_M, φ_i^ν⟩ = d_i·a` where `a = ⟨β_M, φ_0^ν⟩` — the `1_G`, `ζ_M^ν`,
and weighted-`M`-sum components of `β_M` are all orthogonal to the `L`-family. -/
theorem inner_gamma_nu_zeta_eq
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H) :
    ClassFunction.inner ((dataM.betaDecomp hG).Gamma)
        ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i))
      = dataL.d i * ClassFunction.inner ((dataM.h78 hG).beta)
          ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta 0)) := by
  have := dataL.kernelIn_normal
  have hi_h78 : i ≠ (dataL.h78 hG).ind1H := by rw [dataL.h78_ind1H_eq]; exact hi
  set phi := (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i) with hphi
  -- `Γ_M = β_M − 1_G + ζ_M^ν − a_M•W_M` from the (7.8.a) decomposition.
  have hβ := (dataM.betaDecomp hG).beta_eq
  have hΓ_eq : (dataM.betaDecomp hG).Gamma
      = (dataM.h78 hG).beta - Hypothesis71.constOne G
        + (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta ((dataM.h78 hG).zetaDistinct))
        - ((dataM.betaDecomp hG).a : ℂ) • (dataM.h78 hG).weightedNuSum := by
    rw [hβ]; abel
  -- `⟨1_G, φ_i^ν⟩ = 0` (conjugate of the `L`-side `orth_one`).
  have h1G : ClassFunction.inner (Hypothesis71.constOne G) phi = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      (dataL.betaDecomp hG).orth_one i hi_h78, star_zero]
  -- `⟨ζ_M^ν, φ_i^ν⟩ = 0` (family-wide cross-orthogonality, `j = 0`).
  have hzetaM : ClassFunction.inner
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta ((dataM.h78 hG).zetaDistinct)))
      phi = 0 :=
    pair_cross_orthogonal' dataL dataM hG hL hM hnc hi (Ne.symm dataM.ind1H_ne_zero)
  -- `⟨W_M, φ_i^ν⟩ = 0` (cross-orthogonality against every `M`-member).
  have hWM : ClassFunction.inner ((dataM.h78 hG).weightedNuSum) phi = 0 := by
    rw [show (dataM.h78 hG).weightedNuSum
        = ∑ j ∈ (Finset.univ.erase (dataM.h78 hG).ind1H),
            ((dataM.h78 hG).hyp76.zeta j (1 : ↥M) /
              ((dataM.h78 hG).hyp76.zeta ((dataM.h78 hG).zetaDistinct) (1 : ↥M) *
                ClassFunction.inner ((dataM.h78 hG).hyp76.zeta j)
                  ((dataM.h78 hG).hyp76.zeta j))) •
              (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j) from rfl,
      inner_sum_left' _ _ _]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [ClassFunction.inner_smul_left,
      pair_cross_orthogonal' dataL dataM hG hL hM hnc hi
        (by rw [← dataM.h78_ind1H_eq hG]; exact (Finset.mem_erase.mp hj).1),
      mul_zero]
  rw [hΓ_eq, ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, h1G, hzetaM, ClassFunction.inner_smul_left, hWM, mul_zero,
    sub_zero, add_zero, sub_zero]
  exact inner_beta_nu_zeta_eq dataL dataM hG hL hM hnc hi

/-- **The single-branch (14.14) Bessel bound**: if `⟨β_M, φ^{τ₁}⟩ ≠ 0` (the
`L`-family is paired by the `M`-side `β`), then `(h_L − 1)/e_L ≤ e_M − 1`.
The `L`-family Bessel inequality against `‖Γ_M‖² ≤ e_M − 1` ((7.8.b)), with the
degree-square sum `Σ d_i² = (h_L − 1)/e_L`
(`card_index_mul_sum_induced_family_degree_sq`). -/
theorem _root_.solution
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    (hpair : ClassFunction.inner ((dataM.h78 hG).beta)
        ((dataL.h78 hG).nu
          ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct))) ≠ 0) :
    ((Nat.card ↥dataL.kernelIn : ℚ) - 1) / (((dataL.kernelIn).index : ℕ) : ℚ)
      ≤ (((dataM.h78 hG).complementIndex : ℕ) : ℚ) - 1 := by
  classical
  have := dataL.kernelIn_normal
  have := dataM.kernelIn_normal
  -- The pairing value is an integer `a ≠ 0`.
  have hβZ : (dataM.h78 hG).beta ∈ ZIrr G :=
    (dataM.h78 hG).beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (dataM.h78_ind_mem_ZIrr hG) (dataM.h78_zeta_irreducible hG)
  have hζZ : (dataL.h78 hG).nu
      ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct)) ∈ ZIrr G :=
    (dataL.h78 hG).nu_zetaDistinct_mem_ZIrr_of_isCoherent
      (dataL.isCoherentSourceSet hG) rfl
  obtain ⟨a, ha⟩ := ClassFunction.inner_mem_ZIrr_int hβZ hζZ
  have ha_ne : a ≠ 0 := by
    intro h0
    apply hpair
    rw [ha, h0, Int.cast_zero]
  -- The weighted family vector `v = Σ d_i φ_i^ν` and its coefficients.
  set v : ClassFunction G ℂ := ∑ i ∈ Finset.univ.erase dataL.ind1H,
    dataL.d i • ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)) with hv
  -- Pairwise orthonormality of the `φ_i^ν`.
  have hON : ∀ i ∈ Finset.univ.erase dataL.ind1H, ∀ j ∈ Finset.univ.erase dataL.ind1H,
      ClassFunction.inner ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i))
        ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta j))
      = if i = j then 1 else 0 := by
    intro i hi j hj
    rw [(dataL.h78 hG).nu_isometry i j (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact (dataL.h78 hG).zeta_inner_self_eq_one_of_irreducible
        (dataL.zeta_irreducible_at hG (Finset.mem_erase.mp hi).1)
    · rw [if_neg hij]
      exact induce_family_orthogonal_of_injective dataL.kernelIn dataL.θ dataL.inj i j hij
  -- `⟨v, v⟩ = Σ d_i²`.
  have hS : ClassFunction.inner v v
      = ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hv, inner_sum_left']
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ClassFunction.inner_smul_left, inner_sum_right]
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by
      rw [OddOrder.RepresentationTheory.inner_smul_right, hON i hi j hj,
        if_neg (Ne.symm hji), mul_zero])]
    rw [OddOrder.RepresentationTheory.inner_smul_right, hON i hi i hi, if_pos rfl,
      dataL.d_star, mul_one, sq]
  -- `Σ d_i² = (h_L − 1)/e_L` (the degree-square sum, ℂ-level).
  have hidx_ne : ((dataL.kernelIn).index : ℂ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := dataL.kernelIn))
  have hdeg_sum := card_index_mul_sum_induced_family_degree_sq dataL.hFrob dataL.θ
    dataL.ind1H dataL.triv dataL.inj dataL.cover
  have hSval : ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2
      = ((Nat.card ↥dataL.kernelIn : ℂ) - 1) / ((dataL.kernelIn).index : ℂ) := by
    rw [eq_div_iff hidx_ne, mul_comm]
    exact hdeg_sum
  -- `⟨Γ_M, v⟩ = a·Σ d_i²`.
  have hΓv : ClassFunction.inner ((dataM.betaDecomp hG).Gamma) v
      = (a : ℂ) * ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hv, inner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [OddOrder.RepresentationTheory.inner_smul_right, dataL.d_star,
      inner_gamma_nu_zeta_eq dataL dataM hG hL hM hnc (Finset.mem_erase.mp hi).1,
      show ClassFunction.inner ((dataM.h78 hG).beta)
          ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta 0)) = (a : ℂ) from ha,
      sq]
    ring
  -- Assemble the rational Bessel bound with a singleton index family.
  set m : ℚ := ((Nat.card ↥dataL.kernelIn : ℚ) - 1) / (((dataL.kernelIn).index : ℕ) : ℚ)
    with hm
  have hm_cast : (m : ℂ) = ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hSval, hm]
    push_cast
    rfl
  have hbound := (dataM.normEstimates hG).gamma_norm_sq_le (dataM.smallIndex hG)
  -- Apply the singleton orthogonal-integer Bessel bridge (7.10 machinery).
  have happly := sum_rat_weights_le_of_orthogonal_integer_decomposition
    (ι := Unit) Finset.univ (fun _ => v) (fun _ => a) (fun _ => m)
    ((dataM.betaDecomp hG).Gamma)
    ((dataM.betaDecomp hG).Gamma - ((a : ℝ) : ℂ) • v)
    ((((dataM.h78 hG).complementIndex : ℕ) : ℚ) - 1)
    (by rw [Fintype.sum_unique (fun _ : Unit => (((a : ℝ) : ℂ)) • v)]; abel)
    (fun i _ j _ => by
      rw [if_pos (Subsingleton.elim i j)]
      exact hS.trans hm_cast.symm)
    (fun i _ => by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hΓv, hS]
      push_cast
      ring)
    (fun i _ => by
      rw [hm]
      have hcard : (1 : ℚ) ≤ (Nat.card ↥dataL.kernelIn : ℚ) := by
        exact_mod_cast Nat.card_pos
      have hidx : (0 : ℚ) < (((dataL.kernelIn).index : ℕ) : ℚ) := by
        exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      exact div_nonneg (by linarith) hidx.le)
    (fun i _ => ha_ne)
    (by
      calc (ClassFunction.inner ((dataM.betaDecomp hG).Gamma)
              ((dataM.betaDecomp hG).Gamma)).re
          = (dataM.h78 hG).gammaNormSq (dataM.betaDecomp hG) := rfl
        _ ≤ ((dataM.h78 hG).complementIndex : ℝ) - 1 := hbound
        _ = (((((dataM.h78 hG).complementIndex : ℕ) : ℚ) - 1 : ℚ) : ℝ) := by push_cast; ring)
  rwa [Fintype.sum_unique (fun _ : Unit => m)] at happly

end Pairing

end OddOrder.Peterfalvi.S16
