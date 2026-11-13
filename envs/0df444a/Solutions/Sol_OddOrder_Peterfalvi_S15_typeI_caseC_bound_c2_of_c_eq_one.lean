-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.typeI_caseC_bound_c2_of_c_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:27:00.887838+00:00
-- url     : https://prove2.me/submissions/e9056cce-0846-4ed1-bd22-5ba77b7c1aed

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/TwoFamilies.lean
--   OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacter.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S16_PairingBessel.lean
--   OddOrder/Peterfalvi/S15_SAndTGrid.lean
--   OddOrder/Peterfalvi/S15_SAndT.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_tauS_mu_row0_vanish_on_V
import Theorems.Thm_OddOrder_Peterfalvi_S15_dadeSupport_betaGrid_disjoint_support_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_coherent_extension_orthogonal_eta_of_mem_Sset

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

-- ===== OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Prime-`TI` row-`0` cross-column distinctness** (issue 9076 piece 4c-4): distinct columns of
row `0` carry distinct `μ`-entries, `μ_{0j} ≠ μ_{0,#1}` for `j ≠ #1`.  This is the cross-column
injectivity of the prime-`TI` residue grid: the `μ_{ij}` are pairwise-distinct irreducibles across
the *whole* grid (Coq: the residues `prTIres i j` are distinct for distinct `(i, j)`).  The
`Hypothesis` structure records only the *within-column* distinctness `mu_col_injective`; this
row-direction distinctness is the missing prime-`TI` fact.  Prime-`TI` theory, cf. issue 9014. -/
theorem Hypothesis.mu_row0_ne [Finite G] (hyp : Hypothesis (G := G)) {j : Fin hyp.p}
    (hj : j ≠ ⟨1, by have := hyp.three_le_p; omega⟩) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j
      ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
  classical
  intro heq
  -- The diagonal value `⟨μ_{0,#1}, μ_{0,#1}⟩ = 1` (irreducibility, `mu_irreducible`).
  have hdiag : OddOrder.RepresentationTheory.ClassFunction.inner
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 1 :=
    (hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩
      ⟨1, by have := hyp.three_le_p; omega⟩).inner_self_eq_one
  -- The off-diagonal (row-`0` cross-column) value `⟨μ_{0j}, μ_{0,#1}⟩ = 0` (`j ≠ #1`) is the
  -- prime-`TI` grounding: the full-grid orthonormality field `mu_orthonormal` (b-side, issues
  -- 9076/3002/9014), discharged in the spine by `Section16CharacterData.muS_orthonormal`
  -- (`muS = columnFamily.mu = residueS.mu2`, cf. `S13_PrimeTIResidueBridge`).
  have hoff : OddOrder.RepresentationTheory.ClassFunction.inner (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 := by
    rw [hyp.mu_orthonormal]
    exact if_neg (fun hc => hj hc.2)
  rw [heq, hdiag] at hoff
  exact one_ne_zero hoff

/-- **Prime-`TI` support pin, proven** (Coq `prDade_sub_TIirr_on`, `PFsection4.v`): the `μ`-column
difference `μ_{0j} − μ_{0,#1}` is supported inside `A₀(S) = A(S) ∪ V^S` — its support meets `S`
only in `P^# ∪ V_S`, because the two prime-`TI` residues share the same `1_S`-part off `A₀(S)` and
it cancels in the difference.  This is the `S`-side instance of Coq `prDade_sub_TIirr_on`
(`μ2_{ij} − μ2_{ik} ∈ 'CF(S, 'A0)`).

**Honest signature (issue 9076, 2026-07-11)**: carries `(hj0 : (j:ℕ) ≠ 0)` — the unrestricted
`∀ j` form is *false* at the trivial column `j = 0` (`μ_{00}(1) = 1 ≠ μ_{0,#1}(1)`, and `1 ∉ A₀`).
The sole consumer `tauS_mu_row0_cross` (S15_SAndT) passes its `_hj`.

**Fully discharged (2026-07-11)**: the support claim is the `(13.18)` grounding field
`mu_diff_support` (issue 9081: producer-supplied by the proven
`Section16CharacterData.muS_diff_support`, Dade-free via `hyp46SmpCore`), and the degree
hypothesis is the proven per-entry degree `mu_apply_one_eq_u` (Pf (13.3)(a): `μ_{ij}(1) = u` for
`j ≠ 0`, via `mu_j_isIndPC` + `H_index_eq_uq`) — the same two steps Coq's `defGamma` uses
(`prDade_sub_TIirr` + the `FTprTIred1` `mulfI`-cancellation, `PFsection13.v:1909`). -/
theorem Hypothesis.tauS_mu_row0_diff_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj0 : (j : ℕ) ≠ 0) :
    (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
  hyp.mu_diff_support ⟨0, hyp.q_prime.pos⟩
    (fun h => hj0 (congrArg Fin.val h))
    (fun h => one_ne_zero (congrArg Fin.val h))
    ((hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j
        (fun h => hj0 (congrArg Fin.val h))).trans
      (hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩
        ⟨1, by have := hyp.three_le_p; omega⟩
        (fun h => one_ne_zero (congrArg Fin.val h))).symm)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacter.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.8)/(5.3) prime-`TI` Dade cross-relation, `S`-side row-`0` form**:
`τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` for `j ≠ 0`.

This is Coq `prDade_sub_TIirr` (`PFsection4.v:870`) `τ(μ2_{ij} − μ2_{ik}) = δ_j·(η_{ij} − η_{ik})`
specialized to row `i = 0`, columns `j` and `#1`, with the `FT`-context sign `δ_j = 1`.  It is the
single deep input behind (13.18.c)'s `j`-independence `gammaGrid_defGamma`.

✅ **Now on the correct Dade map** (issue 9076, 2026-07-08): `τ_S` is `dadeIntegralCharacterMap`
of the honest **`'A0(S)`-Dade** `dadeHypS0` (support `A₀(S) = A(S) ∪ V^S`), **not** the smaller
`'A(S)`-Dade `dadeHypS`.  The `μ`-column difference `μ_{0j} − μ_{01}` is supported on `P^# ∪ V_S`
(Coq `prDade_sub_TIirr_on`), and `V_S ⊄ S' ⊇ A(S)`, so with the old `dadeHypS` map the `V_S`-part
fell in the arbitrary linear-extension region and the statement was **unprovable as stated**; the
`'A0`-Dade correction fixes that (`dadeHypS0` inherits one deep FT-support pin,
`S10.not_isConj_typePACore_typePV`).

The route: `X := τ_S(μ-diff)` has `‖X‖² = 2` (Dade isometry) and `X ∈ ZIrr`; it agrees with
`η_{0j} − η_{01}` on the regular set via `τ_S = Ind_S^G` on `A₀`-supported (`normedTI 'A0`,
`H = ⊥`) + the prime-`TI` `μ`-value `μ_{0j}|_V = ω`-value (Coq `prTIirr_id`, prime-`TI` theory,
cf. 9014); then `X = η_{0j} − η_{01}` by `S16.eta_diff_rigidity` (Peterfalvi (3.8), issue 9076
piece 4b). -/
theorem tauS_mu_row0_cross [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ j
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
  classical
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData) with hD
  by_cases hj1 : j = ⟨1, by have := hyp.three_le_p; omega⟩
  · -- Trivial column `j = #1`: both `μ`- and `η`-differences vanish, and `τ_S 0 = 0`.
    simp only [hj1, sub_self, map_zero]
  · -- `j ≠ #1`: `X := τ_S(μ_{0j} − μ_{0,#1})` is a norm-`2` `ZIrr` character agreeing with
    -- `η_{0j} − η_{0,#1}` on the regular set `V`, so `S16.eta_diff_rigidity` (3.8) pins it.
    have hμaIrr : IsIrreducibleCharacter (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) :=
      hyp.mu_irreducible _ _
    have hμbIrr : IsIrreducibleCharacter
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) :=
      hyp.mu_irreducible _ _
    have hμne : hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ :=
      hyp.mu_row0_ne hj1
    have hsupp := hyp.tauS_mu_row0_diff_support hG j _hj
    have hZIrrS : (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        ∈ ZIrr (↥hyp.S) :=
      (ZIrr (↥hyp.S)).sub_mem hμaIrr.mem_ZIrr hμbIrr.mem_ZIrr
    -- (a) `X ∈ ZIrr G` (Dade sends supported virtual characters to virtual characters, `(2.6.b)`).
    have hXZ : D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) ∈ ZIrr G :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypS0 hG) hsupp hZIrrS
    -- (b) `‖μ_{0j} − μ_{0,#1}‖² = 2` (two distinct irreducibles).
    have hinner : ∀ φ ψ : ClassFunction ↥hyp.S ℂ, IsIrreducibleCharacter φ →
        IsIrreducibleCharacter ψ → ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥hyp.S)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥hyp.S)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have h_ab : ClassFunction.inner (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 := by
      rw [hinner _ _ hμaIrr hμbIrr, if_neg hμne]
    have h_ba : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [hinner _ _ hμbIrr hμaIrr, if_neg (Ne.symm hμne)]
    have hnorm2 : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 2 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h_ab, h_ba,
        hμaIrr.inner_self_eq_one, hμbIrr.inner_self_eq_one]
      ring
    have hX2 : ClassFunction.inner
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩))
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) = 2 := by
      rw [hD, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS0 hG) hsupp hsupp]
      exact hnorm2
    -- (c) `X − (η_{0j} − η_{0,#1})` vanishes on the regular set `V` (prime-`TI` `V`-value pin).
    have hvanish : ∀ x ∈ conjClassSet
          ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
              - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
          - ((1 : ℤ) : ℂ) • (hyp.eta ⟨0, hyp.q_prime.pos⟩ j
              - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) x = 0 := by
      intro x hx
      have hv := hyp.tauS_mu_row0_vanish_on_V hG hnoV j _hj x hx
      simpa [hD] using hv
    -- (3.8) rigidity: a norm-`2` `ZIrr` character agreeing with `η_{0j} − η_{0,#1}` on `V` is it.
    have hrig := OddOrder.Peterfalvi.S16.eta_diff_rigidity hyp hXZ hX2
      ⟨0, hyp.q_prime.pos⟩ hj1 (s := (1 : ℤ)) (Or.inl rfl) hvanish
    rw [Int.cast_one, one_smul] at hrig
    exact hrig

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c), `j`-independence** (`defGamma`): for every column `j ≠ 0`, the bridge residual
`τ_S(β_j) − 1_G + η_{0j}` equals the fixed gap `Γ = GammaGrid` (defined at column `#1`).

This is exactly Peterfalvi (13.18.c)'s "`Γ` is independent of `j`" (Coq `defGamma`,
`PFsection13.v:1905`), **NOT** grid-orthogonality: the previous scaffold field
`Gamma_independent : ⟨Γ, η_{ik}⟩ = 0` was an **overstatement** (issue 3003), refuted by the genuine
(13.18.d) `X + Y` decomposition where `Γ`'s grid-component `X` is nonzero.

Proof (sorry-free glue, one isolated obligation): `τ_S(β_j) − τ_S(β_{#1}) = τ_S(β_j − β_{#1})` by
`ℤ`-linearity of the Dade map (`map_sub`), and `β_j − β_{#1} = μ_{01} − μ_{0j} = −(μ_{0j} − μ_{01})`
(both share the `Ind_{PW₁}^S 1` positive part), so `τ_S(β_j − β_{#1}) = −(η_{0j} − η_{01}) =
η_{01} −
η_{0j}` by the (4.8)/(5.3) cross-relation `tauS_mu_row0_cross`.  Cancelling the `−1_G`'s and
`abel` closes the goal. -/
theorem gammaGrid_defGamma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) (betaGrid hyp j)
        - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + hyp.eta ⟨0, hyp.q_prime.pos⟩ j
      = GammaGrid hG hyp := by
  have hcross := tauS_mu_row0_cross hG hnoV hyp j hj
  have hbeta : betaGrid hyp j - betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩
      = -(hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) := by
    simp only [betaGrid]; abel
  have key : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) (betaGrid hyp j)
      - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
        - hyp.eta ⟨0, hyp.q_prime.pos⟩ j := by
    rw [← map_sub, hbeta, map_neg, hcross]; abel
  simp only [GammaGrid, tauSbetaGrid]
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData) with hD
  rw [← sub_eq_zero, show
      (D (betaGrid hyp j) - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        - (D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
          - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = (D (betaGrid hyp j) - D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩))
        - (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) by abel, key, sub_self]

end OddOrder.Peterfalvi.S15

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

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S15_SAndTGrid.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`β_L^τ` is supported in `Ã(A(L))`**: the input `Ind_H^L 1 − φ` is `A(L)`-supported — at
`1` the value is `e − e = 0` (`induce_apply_one` + the degree hypothesis), and off `1` its
support lies in nontrivial kernel-conjugates (`support`s of both `Ind` terms), which land in
`A(L)` by `H^# ⊆ A(L)` (`sharpSubgroup_H_subset_typeIA`) and the `L`-conjugation invariance of
`A(L)` (`L_normalizes_A`).  Hence the Dade lift agrees with the (2.5) Dade map there
(`dadeIntegralCharacterMap_apply_of_support`), which vanishes off `Ã(A(L)) = dadeSupport`
(`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`). -/
theorem typeIBetaL_support_subset_dadeSupport [Finite G] {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) (φ : ClassFunction ↥L ℂ)
    (hφ : φ ∈ typeISetup.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (typeIBetaL typeISetup φ).support ⊆ typeISetup.dadeData.dade.dadeSupport := by
  classical
  set H' : Subgroup ↥L := (typeISetup.H).subgroupOf L with hH'def
  set ι : ClassFunction ↥L ℂ :=
    ClassFunction.induce H' (trivialClassFunction ↥H') with hιdef
  have hsupp : (ι - φ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typeIA L typeISetup.typeI) L := by
    intro z hz
    have hzne : (ι - φ) z ≠ 0 := hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      apply hzne
      rw [ClassFunction.sub_apply, hιdef, ClassFunction.induce_apply_one,
        trivialClassFunction_apply, mul_one, hdeg]
      have hHeq : H' = (maxNilpotentNormalHall L).subgroupOf L := by
        rw [hH'def]
        change (typeISetup.typeI.typeF.H).subgroupOf L = _
        rw [typeISetup.typeI.typeF.H_eq]
      rw [hHeq, sub_self]
    have hzc : z ∈ OddOrder.RepresentationTheory.ClassFunction.conjugatesInto H' := by
      by_contra hnotc
      apply hzne
      rw [ClassFunction.sub_apply]
      obtain ⟨θ, -, hφeq⟩ := hφ
      have hφz : ClassFunction.induce ((typeISetup.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((typeISetup.typeI.typeF.H).subgroupOf L) ℂ) z = 0 :=
        ClassFunction.induce_eq_zero_of_not_conjugatesInto _ hnotc
      rw [hιdef, ClassFunction.induce_eq_zero_of_not_conjugatesInto _ hnotc, hφeq, hφz,
        sub_zero]
    obtain ⟨c, hc⟩ := hzc
    have hcne : c⁻¹ * z * c ≠ 1 := by
      intro h1
      apply hz1
      have h2 := congrArg (fun w => c * w * c⁻¹) h1
      simpa [mul_assoc] using h2
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    have hmem : ((c⁻¹ * z * c : ↥L) : G) ∈ sharpSubgroup typeISetup.typeI.typeF.H :=
      ⟨Subgroup.mem_subgroupOf.mp hc, fun h1 => hcne (Subtype.ext h1)⟩
    have hA := sharpSubgroup_H_subset_typeIA typeISetup.typeI hmem
    have hconjA := typeISetup.dadeData.dade.L_normalizes_A c hA
    simpa [mul_assoc] using hconjA
  intro x hx
  by_contra hnot
  apply hx
  change typeIBetaL typeISetup φ x = 0
  rw [typeIBetaL,
    show typeISetup.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        typeISetup.dadeData.dade
        (typeISetup.dadeData.dade.fullDadeIsometryData) from rfl,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support _ _ hsupp]
  exact (typeISetup.dadeData.dade.isDadeMap_dadeMap).map_eq_zero_of_not_mem_dadeSupport _ _ hnot

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a), `β_L^τ`-column instance**: the (13.19.a) support disjointness for the specific
`Ã(L)`-supported `β_L^τ = typeIBetaL φ` (`typeIBetaL_support_subset_dadeSupport`), a thin instance
of the general `dadeSupport_betaGrid_disjoint_support`. -/
theorem typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ))
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    Disjoint (typeIBetaL typeISetup φ).support
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
        ((hyp.dadeHypS0 _hG).fullDadeIsometryData)
        (betaGrid hyp j)).support :=
  dadeSupport_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1 typeISetup
    (typeIBetaL typeISetup φ)
    (typeIBetaL_support_subset_dadeSupport typeISetup φ _hφ _hdeg) j hj

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c), first clause (row form), difference core** (Coq `betaLeta`):
`(β_L^τ, η_{0j} − η_{0j'}) = 0` for `j, j' ≠ 0`.  By (13.18.c) `j`-independence
(`gammaGrid_defGamma` at `j` and `j'`), `η_{0j} − η_{0j'} = τ_S(β_{j'}) − τ_S(β_j)`; each
`(β_L^τ, τ_S(β_j))` vanishes by the (13.19.a) support disjointness
(`typeIBetaL_dadeS_betaGrid_disjoint_support`). -/
theorem typeIBetaL_inner_eta_row_sub_eq_zero_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ))
    (j j' : Fin hyp.p) (hj : (j : ℕ) ≠ 0) (hj' : (j' : ℕ) ≠ 0) :
    ClassFunction.inner (typeIBetaL typeISetup φ)
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j - hyp.eta ⟨0, hyp.q_prime.pos⟩ j') = 0 := by
  classical
  have h1 := gammaGrid_defGamma _hG hnoV hyp j hj
  have h2 := gammaGrid_defGamma _hG hnoV hyp j' hj'
  -- `η_{0j} − η_{0j'} = τ_S(β_{j'}) − τ_S(β_j)` from the two `Γ`-identities.
  have hkey : hyp.eta ⟨0, hyp.q_prime.pos⟩ j - hyp.eta ⟨0, hyp.q_prime.pos⟩ j'
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
          ((hyp.dadeHypS0 _hG).fullDadeIsometryData)
          (betaGrid hyp j')
        - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
          ((hyp.dadeHypS0 _hG).fullDadeIsometryData)
          (betaGrid hyp j) := by
    have h3 := h1.trans h2.symm
    rw [← sub_eq_zero] at h3 ⊢
    rw [← h3]
    abel
  rw [hkey, ClassFunction.inner_sub_right,
    ClassFunction.inner_eq_zero_of_disjoint_support
      (typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1
        typeISetup φ _hφ _hdeg j' hj'),
    ClassFunction.inner_eq_zero_of_disjoint_support
      (typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1
        typeISetup φ _hφ _hdeg j hj),
    sub_zero]

/-- **(13.19.c), first clause (row form)**: `(β_L^τ, η_{0j})` is independent of `j ≥ 1` — by
(13.18.c) `j`-independence (`gammaGrid_defGamma`), `η_{0j} − η_{0j'} = τ_S(β_{j'}) − τ_S(β_j)`,
and (13.19.a) support disjointness kills both `(β_L^τ, τ_S(β_·))` terms
(`typeIBetaL_inner_eta_row_sub_eq_zero`). -/
theorem typeIBetaL_eta_row_constant_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
        ClassFunction.inner (typeIBetaL typeISetup φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
          = ClassFunction.inner (typeIBetaL typeISetup φ)
              (hyp.eta ⟨0, hyp.q_prime.pos⟩ j') := by
  intro _ _ j j' hj hj'
  rw [← sub_eq_zero, ← ClassFunction.inner_sub_right]
  have h := typeIBetaL_inner_eta_row_sub_eq_zero_of_c_eq_one _hG hnoV hyp hc1
    typeISetup φ _hφ _hdeg j j' hj hj'
  convert h using 2
  exact Subsingleton.elim _ _

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Bridge**: `β_L^τ = τ₁(Ind_H^L 1_H − ζ_0)` at the distinguished member `ζ_0 = dataL.zeta 0` is
literally the §7.8 `beta` of the bundle (`(dataL.h78 hG).beta = τ(Ind_H^L 1_H − ζ_0)`).  Both are
the Dade image of `Ind_H^L 1_H − ζ_0`; the §9 `Hypothesis71.τ` and the §7 `tau` agree on supported
inputs (`toHypothesis71_tau_apply`), and `ζ_{ind1H} = Ind_H^L 1_H` (`dataL.triv`). -/
theorem typeIBetaL_zeta0_eq_h78_beta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) :
    typeIBetaL dataL.typeIHyp (dataL.zeta 0) = (dataL.h78 hG).beta := by
  have := dataL.kernelIn_normal
  rw [OddOrder.Peterfalvi.S09.Hypothesis78.beta_def]
  change dataL.typeIHyp.tau _ = dataL.typeIHyp.toHypothesis71.τ _
  rw [dataL.typeIHyp.toHypothesis71_tau_apply]
  apply congrArg dataL.typeIHyp.tau
  change ClassFunction.induce ((dataL.typeIHyp.H).subgroupOf L)
      (trivialClassFunction ↥((dataL.typeIHyp.H).subgroupOf L)) - dataL.zeta 0
    = (dataL.h78 hG).hyp76.zeta (dataL.h78 hG).ind1H
      - (dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct
  rw [dataL.h78_ind1H_eq, dataL.h78_zeta_eq, dataL.h78_zetaDistinct_eq, dataL.h78_zeta_eq]
  congr 1
  -- `Ind_H^L 1_H = ζ_{ind1H}` (`θ ind1H = 1_H`, `dataL.triv`)
  change ClassFunction.induce ((dataL.typeIHyp.H).subgroupOf L)
      (trivialClassFunction ↥((dataL.typeIHyp.H).subgroupOf L))
    = ClassFunction.induce dataL.kernelIn (dataL.θ dataL.ind1H : ClassFunction _ ℂ)
  rw [dataL.triv, IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  rfl

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **(13.19.c) case (c2) bound**: if `bLeta = ⟨β_L^τ, η_{01}⟩ ≠ 0` (the `η`-parity is odd),
then `p ≤ e`.  The §7.8 residual `Γ_L = betaDecomp.Gamma` has `⟨Γ_L, η_{0j}⟩ = bLeta` for every
`j ≠ 0` (from `beta_eq`, row constancy (13.19.c), and `1/ζ_0^{τ₁}/W_L ⊥ η`), so the Bessel
inequality against `‖Γ_L‖² ≤ e − 1` ((7.8.b) `normEstimates`) over the `p − 1` orthonormal
`η_{0j}` gives `(p − 1)·bLeta² ≤ ‖Γ_L‖² ≤ e − 1`, hence `p − 1 ≤ e − 1`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nL : ℤ)
    (hnL : ClassFunction.inner (typeIBetaL dataL.typeIHyp (dataL.zeta 0))
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = (nL : ℂ))
    (hnL0 : nL ≠ 0) :
    hyp.p ≤ ((maxNilpotentNormalHall L).subgroupOf L).index := by
  classical
  have := dataL.kernelIn_normal
  have hp0 : (0 : ℕ) < hyp.p := hyp.p_prime.pos
  -- `e = [L:H]` in the two forms.
  have he_eq : (dataL.h78 hG).complementIndex = ((maxNilpotentNormalHall L).subgroupOf L).index :=
      by
    rw [dataL.complementIndex_eq hG]
    congr 1
    change (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  -- degree hypothesis for the row-constancy citation.
  have hdeg0 : dataL.zeta 0 (1 : ↥L)
      = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  -- `Γ_L = β_L^τ − 1 + ζ_0^{τ₁} − a·W_L`.
  have hΓ_eq : (dataL.betaDecomp hG).Gamma
      = (dataL.h78 hG).beta - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        + (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct))
        - ((dataL.betaDecomp hG).a : ℂ) • (dataL.h78 hG).weightedNuSum := by
    rw [(dataL.betaDecomp hG).beta_eq]; abel
  -- `⟨Γ_L, η_{0j}⟩ = nL`  for every `j ≠ 0`.
  have hXη : ∀ (j : Fin hyp.p), (j : ℕ) ≠ 0 →
      ClassFunction.inner (dataL.betaDecomp hG).Gamma (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        = (nL : ℂ) := by
    intro j hj
    -- `⟨β_L^τ, η_{0j}⟩ = ⟨β_L^τ, η_{01}⟩ = nL`  (row constancy).
    have hβη : ClassFunction.inner ((dataL.h78 hG).beta) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        = (nL : ℂ) := by
      rw [← typeIBetaL_zeta0_eq_h78_beta hG dataL,
        typeIBetaL_eta_row_constant_of_c_eq_one hG hnoV hyp hc1
          dataL.typeIHyp (dataL.zeta 0)
          (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) hdeg0 j
          ⟨1, by have := hyp.three_le_p; omega⟩ hj (by simp), hnL]
    -- `⟨1, η_{0j}⟩ = 0`  (`η_{00} = 1`, orthonormal).
    have h1η : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [show OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ by
        rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp,
        if_neg (by rintro ⟨-, h2⟩; exact hj (congrArg Fin.val h2).symm)]
    -- `⟨ζ_0^{τ₁}, η_{0j}⟩ = 0`  (coherent image `⊥ η`).
    have hζη : ClassFunction.inner
        ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct)))
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [show (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct))
          = dataL.coh.extension (dataL.zeta 0) from rfl]
      exact coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
        (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) _ _
    -- `⟨W_L, η_{0j}⟩ = 0`  (each coherent image `⊥ η`).
    have hWη : ClassFunction.inner ((dataL.h78 hG).weightedNuSum)
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [show (dataL.h78 hG).weightedNuSum
          = ∑ i ∈ (Finset.univ.erase (dataL.h78 hG).ind1H),
              ((dataL.h78 hG).hyp76.zeta i (1 : ↥L) /
                ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct) (1 : ↥L) *
                  ClassFunction.inner ((dataL.h78 hG).hyp76.zeta i)
                    ((dataL.h78 hG).hyp76.zeta i))) •
                (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i) from rfl,
        inner_sum_left _ _ _]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [ClassFunction.inner_smul_left,
        show (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)
          = dataL.coh.extension (dataL.zeta i) from rfl,
        coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
          (dataL.zeta_mem_Sset (by
            rw [← dataL.h78_ind1H_eq hG]; exact (Finset.mem_erase.mp hi).1)) _ _, mul_zero]
    rw [hΓ_eq, ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
      ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hβη, h1η, hζη, hWη,
      mul_zero, sub_zero, add_zero, sub_zero]
  -- Bessel bridge over the `p − 1` orthonormal `η_{0j}` (`j ≠ 0`).
  set B : Finset (Fin hyp.p) := Finset.univ.erase ⟨0, hyp.p_prime.pos⟩ with hB
  have hcardB : B.card = hyp.p - 1 := by
    rw [hB, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hbound := (dataL.normEstimates hG).gamma_norm_sq_le (dataL.smallIndex hG)
  have happly := OddOrder.Peterfalvi.S09.sum_rat_weights_le_of_orthogonal_integer_decomposition
    (ι := Fin hyp.p) B (fun j => hyp.eta ⟨0, hyp.q_prime.pos⟩ j) (fun _ => nL) (fun _ => (1 : ℚ))
    ((dataL.betaDecomp hG).Gamma)
    ((dataL.betaDecomp hG).Gamma
      - ∑ j ∈ B, (((nL : ℝ) : ℂ)) • hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
    (((dataL.h78 hG).complementIndex : ℚ) - 1)
    (by abel)
    (fun i _ j _ => by
      rw [OddOrder.Peterfalvi.S16.eta_orthonormal hyp]
      by_cases hij : i = j
      · rw [if_pos ⟨rfl, hij⟩, if_pos hij]; norm_num
      · rw [if_neg (fun h => hij h.2), if_neg hij])
    (fun j hj => by
      have hj0 : (j : ℕ) ≠ 0 := by
        rintro h0; exact (Finset.mem_erase.mp hj).1 (Fin.ext h0)
      rw [ClassFunction.inner_sub_left, inner_sum_left,
        Finset.sum_eq_single_of_mem j hj (fun k _ hkj => by
          rw [ClassFunction.inner_smul_left,
            OddOrder.Peterfalvi.S16.eta_orthonormal hyp,
            if_neg (by rintro ⟨-, h2⟩; exact hkj h2), mul_zero]),
        ClassFunction.inner_smul_left,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp, if_pos ⟨rfl, rfl⟩, mul_one,
        hXη j hj0]
      push_cast; ring)
    (fun _ _ => by norm_num)
    (fun _ _ => hnL0)
    (by
      calc (ClassFunction.inner ((dataL.betaDecomp hG).Gamma)
              ((dataL.betaDecomp hG).Gamma)).re
          = (dataL.h78 hG).gammaNormSq (dataL.betaDecomp hG) := rfl
        _ ≤ ((dataL.h78 hG).complementIndex : ℝ) - 1 := hbound
        _ = (((((dataL.h78 hG).complementIndex : ℚ) - 1 : ℚ)) : ℝ) := by push_cast; ring)
  -- `∑ 1 = p − 1 ≤ e − 1`, hence `p ≤ e`.
  rw [Finset.sum_const, hcardB, nsmul_eq_mul, mul_one] at happly
  have hpe : ((hyp.p : ℚ) - 1) ≤ ((dataL.h78 hG).complementIndex : ℚ) - 1 := by
    have : ((hyp.p - 1 : ℕ) : ℚ) = (hyp.p : ℚ) - 1 := by
      rw [Nat.cast_sub hp0]; norm_num
    rwa [this] at happly
  rw [← he_eq]
  have : (hyp.p : ℚ) ≤ ((dataL.h78 hG).complementIndex : ℚ) := by linarith
  exact_mod_cast this

end OddOrder.Peterfalvi.S15
