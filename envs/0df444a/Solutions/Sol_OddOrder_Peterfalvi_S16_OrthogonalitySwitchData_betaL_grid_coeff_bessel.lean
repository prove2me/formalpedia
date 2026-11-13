-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.betaL_grid_coeff_bessel
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:38:13.1573+00:00
-- url     : https://prove2.me/submissions/4cc7f2c2-3c85-4b9e-a2d4-2354e91635d4

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S16_PairingBessel.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLMBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
import Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_mSide_dadeSupport_avoids_regular

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

/-- The coherent extension of `h78` is the bundle's coherence extension
(definitional). -/
theorem h78_nu_eq : (data.h78 hG).nu = data.coh.extension := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is irreducible** (Frobenius kernel induction,
[Is] Thm 6.34). -/
theorem h78_zeta_irreducible :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) := by
  have := data.kernelIn_normal
  rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

/-- **The conjugate of any nontrivial family member is a family member**:
for `i ≠ ind1H` there is `i' ≠ ind1H` with `ζ_{i'} = ζ̄_i`. -/
theorem exists_conjIndex_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    ∃ i', i' ≠ (data.h78 hG).ind1H ∧
      (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj := by
  have := data.kernelIn_normal
  have hconj_eq : ((data.h78 hG).hyp76.zeta i).conj
      = ClassFunction.induce data.kernelIn
          ((IrreducibleCharacter.conjPerm _ (data.θ i)) : ClassFunction _ ℂ) := by
    rw [data.h78_zeta_eq, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (data.θ i)).symm
  obtain ⟨i', hi'_range⟩ := data.cover (IrreducibleCharacter.conjPerm _ (data.θ i))
  have hi'_conj : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj := by
    rw [data.h78_zeta_eq, hconj_eq]; exact hi'_range
  refine ⟨i', ?_, hi'_conj⟩
  intro hi'1
  -- else `ζ̄_i = ζ_{ind1H} = Ind 1_H` is real, so `ζ_i = Ind 1_H`, contra `i ≠ ind1H`.
  have hind_real : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  refine hi (data.inj ?_)
  have h1 : ((data.h78 hG).hyp76.zeta i).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    rw [← hi'_conj, hi'1]
  calc (data.h78 hG).hyp76.zeta i
      = (((data.h78 hG).hyp76.zeta i).conj).conj := (ClassFunction.conj_conj _).symm
    _ = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by rw [h1, hind_real]

/-- **No nontrivial family member is real** (odd order): `ζ_i ≠ ζ̄_i` for `i ≠ ind1H`. -/
theorem zeta_ne_conj_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hodd : Odd (Nat.card G)) :
    (data.h78 hG).hyp76.zeta i ≠ ((data.h78 hG).hyp76.zeta i).conj := by
  have := data.kernelIn_normal
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial hi)
  have hodd_L : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hK_ne_top : data.kernelIn ≠ ⊤ := by
    intro hKtop
    refine data.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := data.hFrob.isComplement.disjoint
    rw [show (data.typeIHyp.typeI.typeF.H).subgroupOf L = data.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (data.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  -- `ζ_i(1) = [L:H]·θ_i(1) ≥ [L:H] > 1`, so `ζ_i` is nontrivial.
  obtain ⟨di, hdi_pos, hdi⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  have hdeg : (data.h78 hG).hyp76.zeta i (1 : ↥L)
      = ((data.kernelIn).index : ℂ) * (di : ℂ) := by
    rw [data.h78_zeta_eq]
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) = _
    rw [ClassFunction.induce_apply_one, hdi]
  have hne_triv : (⟨(data.h78 hG).hyp76.zeta i, hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (data.h78 hG).hyp76.zeta i = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : ((data.kernelIn).index : ℂ) * (di : ℂ) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    have : (data.kernelIn).index * di = 1 := by exact_mod_cast hone
    have h1 : (data.kernelIn).index = 1 := by
      rcases Nat.eq_one_of_mul_eq_one_right this with h; omega
    omega
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

set_option backward.isDefEq.respectTransparency false in
/-- **`ζ_i − ζ̄_i` is supported on `A(L)`** for any `i ≠ ind1H`. -/
theorem zeta_sub_conj_support_at (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {i i' : Fin (data.n + 1)}
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ((data.h78 hG).hyp76.zeta i - (data.h78 hG).hyp76.zeta i').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
  have := data.kernelIn_normal
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hi', ClassFunction.conj_apply] at hx
  refine (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) x).mpr ⟨?_, ?_⟩
  · by_contra hxH
    apply hx
    rw [(data.h78 hG).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH, star_zero, sub_zero]
  · intro hx1
    apply hx
    rw [hx1]
    -- `ζ_i(1)` is real (`induce_apply_one_star`).
    have hreal : star ((data.h78 hG).hyp76.zeta i (1 : ↥L))
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) := by
      rw [data.h78_zeta_eq]
      exact induce_apply_one_star data.kernelIn (data.θ i)
    rw [hreal, sub_self]

/-- **`ζ_i^ν − ζ̄_i^ν` is supported in the Dade support** for any `i ≠ ind1H`. -/
theorem nu_zeta_sub_conj_support_at (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
        - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')).support
      ⊆ (data.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  have := data.kernelIn_normal
  have hzi_mem : (data.h78 hG).hyp76.zeta i ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]; exact data.zeta_mem_Sset hi
  have hi'_mem : (data.h78 hG).hyp76.zeta i' ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]
    exact data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hsupp' : ((data.h78 hG).hyp76.zeta i
        - (1 : ℂ) • (data.h78 hG).hyp76.zeta i').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
    rw [one_smul]; exact data.zeta_sub_conj_support_at hG hi'
  have hagree := coherence_hagree_dadeMap data.typeIHyp.dadeData.dade
    data.coh hzi_mem hi'_mem (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  have heq : (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
      - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')
      = (data.typeIHyp.dadeData.dade.fullDadeIsometryData).toDadeMap
          ⟨_, (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [data.h78_nu_eq,
      ← one_smul ℂ (data.coh.extension ((data.h78 hG).hyp76.zeta i'))]
    exact hagree.symm
  rw [heq]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  have hdade := (data.typeIHyp.dadeData.dade.fullDadeIsometryData
).toDadeIsometryData.isDadeMap
  exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)

/-- **Each `ζ_i^ν` (`i ≠ ind1H`) is a unit-norm virtual character.** -/
theorem nu_zeta_norm_one {i : Fin (data.n + 1)} (hi : i ≠ (data.h78 hG).ind1H) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)) = 1 := by
  have := data.kernelIn_normal
  rw [(data.h78 hG).nu_isometry i i hi hi]
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial (by rw [← data.h78_ind1H_eq hG]; exact hi))
  exact IsIrreducibleCharacter.inner_self_eq_one hirr

/-- **Each nontrivial family member induces irreducibly** (general-index form of
`h78_zeta_irreducible`). -/
theorem zeta_irreducible_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
  have := data.kernelIn_normal
  rw [data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
    (data.theta_ne_trivial hi)

/-- **`⟨ζ_i^ν, ζ̄_i^ν⟩ = 0`**: the conjugate pair is orthonormal (`ν`-isometry +
distinct irreducibles). -/
theorem nu_zeta_inner_nu_conj_eq_zero (hodd : Odd (Nat.card G))
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')) = 0 := by
  rw [(data.h78 hG).nu_isometry i i' hi hi'_ne]
  have hirr_i := data.zeta_irreducible_at hG hi
  have hirr_i' : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i') :=
    data.zeta_irreducible_at hG (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hne : (data.h78 hG).hyp76.zeta i ≠ (data.h78 hG).hyp76.zeta i' := by
    rw [hi']
    exact data.zeta_ne_conj_at hG hi hodd
  have h := irreducibleCharacter_inner_eq_ite
    (⟨_, hirr_i⟩ : IrreducibleCharacter ↥L) ⟨_, hirr_i'⟩
  rwa [if_neg (fun heq => hne (congrArg Subtype.val heq))] at h

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

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (13.19.b), the `η`-grid orthogonality of *every* coherent image `ζ_k^ν`**
(the Coq `o_tauLeta` for the whole family, not just the distinguished index).  For any family
member `k ≠ ind1H`, the coherent image `ζ_k^ν = (dataM.h78 hG).nu (ζ_k)` is orthogonal to the
entire `η`-grid.  Identical (3.6)–(3.8)/(13.19.b) engine as `caseB_eta_orthogonal_psi`, but with
the distinguished index `zetaDistinct` replaced by an arbitrary `k`: `ζ_k^ν` has unit norm
(`nu_zeta_norm_one`), its conjugate partner `ζ_{k'}^ν` (`exists_conjIndex_at`, generic in the
index) is a distinct unit-norm virtual character (`nu_zeta_inner_nu_conj_eq_zero`), and the
conjugate difference `ζ_k^ν − ζ_{k'}^ν` (supported in `Ã(M)`, `nu_zeta_sub_conj_support_at`,
also generic) vanishes on `Ŵ^G` by the same (13.19.a) Dade-support avoidance `hDadeAvoid`. -/
theorem caseB_eta_orthogonal_nu_zeta_at [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (dataM : TypeICoherent78Data M)
    (hDadeAvoid : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport)
    {k : Fin (dataM.n + 1)} (hk : k ≠ (dataM.h78 hG).ind1H) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j)
        ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)) = 0 := by
  classical
  -- the kernel-index datum for `k` and its conjugate partner `k'`
  have hkne : k ≠ dataM.ind1H := by rwa [dataM.h78_ind1H_eq] at hk
  obtain ⟨k', hk'_ne, hk'⟩ := dataM.exists_conjIndex_at hG hkne
  -- engine inputs from the coherence bundle
  have hpsiZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k) ∈ ZIrr G := by
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hkne))
  have hconjZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k') ∈ ZIrr G := by
    have hk'ne_data : k' ≠ dataM.ind1H := by rw [← dataM.h78_ind1H_eq]; exact hk'_ne
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hk'ne_data))
  have hpsi1 := dataM.nu_zeta_norm_one hG hk
  have hconj1 := dataM.nu_zeta_norm_one hG hk'_ne
  have hcross := dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hkne hk'_ne hk'
  have hsupp := dataM.nu_zeta_sub_conj_support_at hG hkne hk'_ne hk'
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k')) x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx (hsupp (ClassFunction.mem_support.mpr hval))
  exact eta_orthogonal_of_norm_one_pair_vanish hyp hpsiZ hconjZ hpsi1 hconj1 hcross hvanish

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLMBasic.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), the Bessel bound `Σ m_ij² ≤ p q`** (Coq `ub_e`).  With
`m_ij = ⟨β_L, η_ij⟩` and `e_L = |L : H_L| = p q` (`hepq`), the (7.8.a) decomposition
`β_L = 1_G − ζ_0^ν + a·W + Γ_L` (`BetaDecomp.beta_eq`) *projects* onto the `η`-grid as
`⟨β_L, η_ij⟩ = ⟨1_G, η_ij⟩ + ⟨Γ_L, η_ij⟩ = ⟨1_G + Γ_L, η_ij⟩`: the distinguished image
`ζ_0^ν` and *every* member `ζ_k^ν` of the weighted sum `W` are orthogonal to the whole grid
(`caseB_eta_orthogonal_nu_zeta_at`, the Coq `o_tauLeta` for the full family, whose only input is
the (13.19.a) Dade-support avoidance `mSide_dadeSupport_avoids_regular`).  Bessel for the
orthonormal grid `{η_ij}` (`eta_orthonormal`) applied to `φ = 1_G + Γ_L` then gives
`Σ m_ij² ≤ ‖1_G + Γ_L‖² = ‖1_G‖² + ‖Γ_L‖² = 1 + ‖Γ_L‖²`, and `‖Γ_L‖² ≤ e_L − 1`
(`dataL.normEstimates.gamma_norm_sq_le`, the (7.8.b) residual bound), so
`Σ m_ij² ≤ 1 + (p q − 1) = p q`.  This is the honest (13.19.c) grid Bessel bound; the only
external datum is `hepq` (`e_L = p q`, carried by `LHypothesis` at the call site). -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L)
    (hepq : (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q)
    (m : Fin hyp.base.q → Fin hyp.base.p → ℤ)
    (hcoeff : ∀ i j, ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i j) = (m i j : ℂ)) :
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2
      ≤ (hyp.base.p * hyp.base.q : ℤ) := by
  classical
  have := dataL.kernelIn_normal
  set H78 := dataL.h78 hG with hH78
  set BD := dataL.betaDecomp hG with hBD
  -- `ζ_0^ν ⊥ η_ij` and every family member `ζ_k^ν ⊥ η_ij` (Coq `o_tauLeta`, full family).
  have hDadeAvoid := mSide_dadeSupport_avoids_regular (hyp := hyp) hG hnoV hncH0C hLmax dataL
  have hetaNu : ∀ (k : Fin (dataL.n + 1)), k ≠ H78.ind1H →
      ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
        ClassFunction.inner (H78.nu (H78.hyp76.zeta k)) (hyp.base.eta i j) = 0 := by
    intro k hk i j
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      caseB_eta_orthogonal_nu_zeta_at hG hyp.base dataL hDadeAvoid hk i j, star_zero]
  -- `W = weightedNuSum ⊥ η_ij` (linear combination of the `ζ_k^ν`, `k ≠ ind1H`).
  have hWeta : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner H78.weightedNuSum (hyp.base.eta i j) = 0 := by
    intro i j
    rw [show H78.weightedNuSum
        = ∑ k ∈ (Finset.univ.erase H78.ind1H),
            (H78.hyp76.zeta k (1 : ↥L) /
              (H78.hyp76.zeta H78.zetaDistinct (1 : ↥L) *
                ClassFunction.inner (H78.hyp76.zeta k) (H78.hyp76.zeta k))) •
              H78.nu (H78.hyp76.zeta k) from rfl]
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [ClassFunction.inner_smul_left, hetaNu k (Finset.mem_erase.mp hk).1 i j, mul_zero]
  -- **The grid projection**: `⟨β_L, η_ij⟩ = ⟨1_G + Γ_L, η_ij⟩` (the `ζ_0^ν`- and `W`-parts die).
  set phi : ClassFunction G ℂ :=
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + BD.Gamma with hphi
  have hphi_coeff : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner phi (hyp.base.eta i j) = (m i j : ℂ) := by
    intro i j
    rw [← hcoeff i j, hphi,
      show H78.beta = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          - H78.nu (H78.hyp76.zeta H78.zetaDistinct)
          + (BD.a : ℂ) • H78.weightedNuSum + BD.Gamma from BD.beta_eq]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left,
      hetaNu H78.zetaDistinct H78.zetaDistinct_ne_ind1H i j, hWeta i j, mul_zero, sub_zero,
      add_zero]
  -- Pythagorean split for `φ = 1_G + Γ_L` against the orthonormal grid `{η_ij}`.
  set X : ClassFunction G ℂ :=
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j : ℂ) • hyp.base.eta i j with hX
  set Y : ClassFunction G ℂ := phi - X with hY
  have hXeta : ∀ (k : Fin hyp.base.q) (l : Fin hyp.base.p),
      ClassFunction.inner X (hyp.base.eta k l) = (m k l : ℂ) := by
    intro k l
    rw [hX, inner_sum_left]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hik => ?_)]
    · rw [inner_sum_left,
        Finset.sum_eq_single_of_mem l (Finset.mem_univ _) (fun j _ hjl => ?_)]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp.base,
          if_pos ⟨rfl, rfl⟩, mul_one]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp.base,
          if_neg (by rintro ⟨-, rfl⟩; exact hjl rfl), mul_zero]
    · rw [inner_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ClassFunction.inner_smul_left, eta_orthonormal hyp.base,
        if_neg (by rintro ⟨rfl, -⟩; exact hik rfl), mul_zero]
  have hsum_sq : ∀ ψ : ClassFunction G ℂ,
      (∀ (k : Fin hyp.base.q) (l : Fin hyp.base.p),
        ClassFunction.inner ψ (hyp.base.eta k l) = (m k l : ℂ)) →
      ClassFunction.inner ψ X
        = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ) := by
    intro ψ hψ
    rw [hX, inner_sum_right]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_right, hψ i j, star_intCast]
    ring
  have hXY : ClassFunction.inner X Y = 0 := by
    have h := hsum_sq X hXeta
    have h2 : ClassFunction.inner X phi
        = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hsum_sq phi hphi_coeff, star_intCast]
    rw [hY, ClassFunction.inner_sub_right, h2, h, sub_self]
  have hYX : ClassFunction.inner Y X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXY, star_zero]
  have hsplit : ClassFunction.inner phi phi
      = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ)
        + ClassFunction.inner Y Y := by
    have hphiXY : phi = X + Y := by rw [hY]; abel
    calc ClassFunction.inner phi phi
        = ClassFunction.inner (X + Y) (X + Y) := by rw [← hphiXY]
      _ = ClassFunction.inner X X + ClassFunction.inner X Y
          + (ClassFunction.inner Y X + ClassFunction.inner Y Y) := by
          rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
            ClassFunction.inner_add_right]
      _ = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ)
          + ClassFunction.inner Y Y := by
          rw [hXY, hYX, hsum_sq X hXeta]; ring
  -- `⟨Y, Y⟩ ≥ 0`, so `Σ m² ≤ ⟨φ, φ⟩` (real parts).
  have hYY_nonneg : (0 : ℝ) ≤ (ClassFunction.inner Y Y).re :=
    OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_self_re_nonneg Y
  -- `⟨φ, φ⟩ = ‖1_G‖² + ‖Γ_L‖² = 1 + ‖Γ_L‖²` (cross term `1_G ⊥ Γ_L`).
  have hone_gamma : ClassFunction.inner
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) BD.Gamma = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, BD.Gamma_orth_one,
      star_zero]
  have hphiphi : ClassFunction.inner phi phi
      = (1 : ℂ) + ClassFunction.inner BD.Gamma BD.Gamma := by
    rw [hphi, ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right,
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one,
      hone_gamma, BD.Gamma_orth_one, add_zero, zero_add]
  -- `‖Γ_L‖² ≤ e_L − 1 = p q − 1` from the (7.8.b) `NormEstimates` residual bound.
  have hGammaBound : (ClassFunction.inner BD.Gamma BD.Gamma).re
      ≤ (H78.complementIndex : ℝ) - 1 :=
    (dataL.normEstimates hG).gamma_norm_sq_le (dataL.smallIndex hG)
  -- Take real parts and cast to `ℤ`.
  have hre : ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
      + (ClassFunction.inner Y Y).re = 1 + (ClassFunction.inner BD.Gamma BD.Gamma).re := by
    have hcs := congrArg Complex.re (hsplit.symm.trans hphiphi)
    rw [Complex.add_re, Complex.add_re, Complex.intCast_re, Complex.one_re] at hcs
    exact hcs
  have hsq_le_real : ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
      ≤ (hyp.base.p * hyp.base.q : ℤ) := by
    have hepqR : (H78.complementIndex : ℝ) = ((hyp.base.p * hyp.base.q : ℤ) : ℝ) := by
      rw [hH78] at hepq ⊢; rw [hepq]; push_cast; ring
    have : ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
        ≤ 1 + (ClassFunction.inner BD.Gamma BD.Gamma).re := by linarith
    calc ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
        ≤ 1 + (ClassFunction.inner BD.Gamma BD.Gamma).re := this
      _ ≤ 1 + ((H78.complementIndex : ℝ) - 1) := by linarith
      _ = (H78.complementIndex : ℝ) := by ring
      _ = ((hyp.base.p * hyp.base.q : ℤ) : ℝ) := hepqR
  exact_mod_cast hsq_le_real

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
