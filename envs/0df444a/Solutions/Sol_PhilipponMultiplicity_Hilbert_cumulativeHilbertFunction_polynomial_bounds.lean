-- Prove2me | solution 1 for PhilipponMultiplicity.Hilbert.cumulativeHilbertFunction_polynomial_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T07:44:23.596794+00:00
-- url     : https://prove2.me/submissions/bed773a4-54b2-493b-af2c-ee6b38acd20e

import Definitions.Def_PhilipponMultiplicity_HilbertGrowth
import Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertFunction_colon_add
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
set_option autoImplicit false
open scoped BigOperators Topology
open Filter
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.Hilbert
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i


end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_total {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : P.IsHomogeneous (∑ i, D i) := by
  intro a ha
  change (Finsupp.weight (fun _ : M.Variable => (1 : ℕ))) a = _
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => hP a (mem_support_iff.mpr ha) i)

instance degreePiece_finite (D : M.FactorIndex → ℕ) :
    Module.Finite K (Hilbert.degreePiece K M.factorCount M.ambientDimension D) := by
  let W := MvPolynomial.homogeneousSubmodule M.Variable K (∑ i, D i)
  letI : Module.Finite K W := Module.Finite.of_fg
    (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  have hle : Hilbert.degreePiece K M.factorCount M.ambientDimension D ≤ W := by
    intro P hP
    exact M.homogeneous_total ((M.degreePiece_iff P D).mp hP)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)


end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
instance quotientPiece_finite_colon (I : Ideal M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    Module.Finite K (quotientPiece K M.factorCount M.ambientDimension I d) := by
  unfold quotientPiece
  infer_instance


end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem relevant_variables (Q : Ideal M.CoordinateRing)
    (hQ : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ v : ∀ i, Fin (M.ambientDimension i + 1), ∀ i, X ⟨i, v i⟩ ∉ Q := by
  classical
  have hx (i : M.FactorIndex) : ∃ j : Fin (M.ambientDimension i + 1), X ⟨i, j⟩ ∉ Q := by
    by_contra! h
    apply hQ
    apply (iInf_le (blockIdeal K M.factorCount M.ambientDimension) i).trans
    rw [blockIdeal, Ideal.span_le]
    rintro x ⟨j, rfl⟩
    exact h j
  exact Classical.axiomOfChoice hx

theorem variable_product_homogeneous (v : ∀ i, Fin (M.ambientDimension i + 1))
    (d : M.FactorIndex → ℕ) :
    M.IsHomogeneous (∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i) d := by
  classical
  apply (M.degreePiece_iff _ d).mp
  let w := blockWeight M.factorCount M.ambientDimension
  have hx (i : M.FactorIndex) : (X ⟨i, v i⟩ : M.CoordinateRing).IsWeightedHomogeneous w
      (w ⟨i, v i⟩) := isWeightedHomogeneous_X K w ⟨i, v i⟩
  have h := IsWeightedHomogeneous.prod (w := w) Finset.univ
    (fun i => (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i)
    (fun i => d i • blockWeight M.factorCount M.ambientDimension ⟨i, v i⟩)
    (fun i _ => (hx i).pow (d i))
  have heq : (∑ i, d i • blockWeight M.factorCount M.ambientDimension ⟨i, v i⟩) = d := by
    funext i
    simp [blockWeight, Pi.single_apply, Finset.sum_apply, smul_eq_mul]
  rwa [heq] at h

theorem variable_product_notMem (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (v : ∀ i, Fin (M.ambientDimension i + 1)) (hv : ∀ i, X ⟨i, v i⟩ ∉ Q)
    (d : M.FactorIndex → ℕ) : (∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i) ∉ Q := by
  classical
  letI := hQ
  intro h
  obtain ⟨i, hi, hip⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hv i (hQ.mem_of_pow_mem _ hip)


end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- For a relevant homogeneous prime, multiplying by a selected nonzero
coordinate in each block makes the actual Hilbert function monotone. -/
theorem hilbertFunction_mono_relevant_prime (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    Monotone (hilbertFunction K M.factorCount M.ambientDimension Q) := by
  classical
  obtain ⟨v, hv⟩ := relevant_variables M Q hrel
  intro d e hde
  let P : M.CoordinateRing := ∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ (e - d) i
  have hP : M.IsHomogeneous P (e - d) := variable_product_homogeneous M v (e - d)
  have hPnot : P ∉ Q := variable_product_notMem M Q hQ v hv (e - d)
  have hcolon : Q.colon {P} = Q := by
    apply le_antisymm ?_ Ideal.le_colon
    intro f hf
    have hmul : f * P ∈ Q := by
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using hf
    exact (hQ.mem_or_mem hmul).resolve_right hPnot
  have h := hilbertFunction_colon_add M Q hhom P (e - d) hP d
  rw [hcolon, tsub_add_cancel_of_le hde] at h
  omega


end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

private def quotientProjection (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (d : M.FactorIndex → ℕ) :
    (M.CoordinateRing ⧸ I) →ₗ[K] (M.CoordinateRing ⧸ I) :=
  (I.restrictScalars K).liftQ
    ((Ideal.Quotient.mkₐ K I).toLinearMap.comp
      (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d)) (by
        intro P hP
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI P hP d))

private theorem quotientProjection_on_piece (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (d e : M.FactorIndex → ℕ)
    {x : M.CoordinateRing ⧸ I} (hx : x ∈ quotientPiece K M.factorCount M.ambientDimension I e) :
    quotientProjection M I hI d x = if d = e then x else 0 := by
  classical
  obtain ⟨P, hP, rfl⟩ := hx
  change Ideal.Quotient.mk I
    (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d P) = _
  rw [weightedHomogeneousComponent_of_mem hP]
  split_ifs <;> simp

/-- Distinct actual multidegree pieces of a homogeneous quotient are independent. -/
theorem quotientPiece_iSupIndep (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    iSupIndep (quotientPiece K M.factorCount M.ambientDimension I) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hz d hd
  have h := congrArg (quotientProjection M I hI d) hz
  rw [map_sum, map_zero] at h
  have heq : (∑ e ∈ s, quotientProjection M I hI d (v e)) = v d := by
    rw [Finset.sum_eq_single d]
    · simpa using quotientProjection_on_piece M I hI d d (hv d hd)
    · intro e he hed
      rw [quotientProjection_on_piece M I hI d e (hv e he), if_neg (Ne.symm hed)]
    · exact fun hn => False.elim (hn hd)
  exact heq.symm.trans h

instance finite_piece_sum (I : Ideal M.CoordinateRing) (s : Finset (M.FactorIndex → ℕ)) :
    Module.Finite K (⨆ d ∈ s, quotientPiece K M.factorCount M.ambientDimension I d :
      Submodule K (M.CoordinateRing ⧸ I)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : (⨆ d ∈ (∅ : Finset (M.FactorIndex → ℕ)),
        quotientPiece K M.factorCount M.ambientDimension I d :
        Submodule K (M.CoordinateRing ⧸ I)) = ⊥ := by simp
    rw [hz]
    infer_instance
  | @insert d s hd ih =>
    rw [Finset.iSup_insert]
    let := ih
    infer_instance

/-- The actual dimension of a finite sum of quotient pieces is their dimension sum. -/
theorem finrank_quotientPiece_sum (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (s : Finset (M.FactorIndex → ℕ)) :
    Module.finrank K (⨆ d ∈ s, quotientPiece K M.factorCount M.ambientDimension I d :
      Submodule K (M.CoordinateRing ⧸ I)) =
      ∑ d ∈ s, hilbertFunction K M.factorCount M.ambientDimension I d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert d s hd ih =>
    rw [Finset.iSup_insert, Finset.sum_insert hd]
    have hdis := (quotientPiece_iSupIndep M I hI).disjoint_biSup (y := (s : Set _)) hd
    have hzero : quotientPiece K M.factorCount M.ambientDimension I d ⊓
        (⨆ e ∈ s, quotientPiece K M.factorCount M.ambientDimension I e) = ⊥ := by
      simpa only [Finset.mem_coe] using hdis.eq_bot
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (quotientPiece K M.factorCount M.ambientDimension I d)
      (⨆ e ∈ s, quotientPiece K M.factorCount M.ambientDimension I e)
    rw [hzero, finrank_bot, add_zero, ih] at hdim
    exact hdim

theorem mem_multidegreesLe (n : ℕ) (d : M.FactorIndex → ℕ) :
    d ∈ multidegreesLe M n ↔ ∑ i, d i ≤ n := by
  classical
  simp only [multidegreesLe, Finset.mem_filter, Finset.mem_Iic]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  intro i
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans h

theorem sum_blockWeight (e : M.Variable →₀ ℕ) :
    (∑ i, (Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e) i) = e.degree := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => M.blockWeight_apply e i)

theorem restrictTotalDegree_eq_piece_sum (n : ℕ) :
    restrictTotalDegree M.Variable K n =
      ⨆ d ∈ multidegreesLe M n, degreePiece K M.factorCount M.ambientDimension d := by
  classical
  apply le_antisymm
  · intro P hP
    have hdeg := (mem_restrictTotalDegree M.Variable n P).mp hP
    have hsum : (∑ e ∈ P.support, monomial e (coeff e P)) ∈
        ⨆ d ∈ multidegreesLe M n, degreePiece K M.factorCount M.ambientDimension d := by
      apply Submodule.sum_mem
      intro e he
      let d := Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e
      have hd : d ∈ multidegreesLe M n := (mem_multidegreesLe M n d).mpr (by
        rw [sum_blockWeight]
        exact (le_totalDegree he).trans hdeg)
      apply Submodule.mem_iSup_of_mem d
      apply Submodule.mem_iSup_of_mem hd
      exact isWeightedHomogeneous_monomial _ _ _ rfl
    simpa only [← P.as_sum] using hsum
  · refine iSup_le fun d => iSup_le fun hd => ?_
    intro P hP
    apply (mem_restrictTotalDegree M.Variable n P).mpr
    exact (M.homogeneous_total ((M.degreePiece_iff P d).mp hP)).totalDegree_le.trans
      ((mem_multidegreesLe M n d).mp hd)

theorem degreeFiltration_eq_piece_sum (I : Ideal M.CoordinateRing) (n : ℕ) :
    degreeFiltration M I n =
      ⨆ d ∈ multidegreesLe M n, quotientPiece K M.factorCount M.ambientDimension I d := by
  unfold degreeFiltration
  rw [restrictTotalDegree_eq_piece_sum]
  simp only [Submodule.map_iSup, quotientPiece]

instance degreeFiltration_finite (I : Ideal M.CoordinateRing) (n : ℕ) :
    Module.Finite K (degreeFiltration M I n) := by
  unfold degreeFiltration
  infer_instance

/-- The standard total-degree filtration counts the actual multigraded pieces. -/
theorem cumulativeHilbertFunction_eq_sum (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (n : ℕ) :
    cumulativeHilbertFunction M I n =
      ∑ d ∈ multidegreesLe M n, hilbertFunction K M.factorCount M.ambientDimension I d := by
  unfold cumulativeHilbertFunction
  rw [degreeFiltration_eq_piece_sum, finrank_quotientPiece_sum M I hI]

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The diagonal Hilbert function bounds the dimension of the actual
total-degree filtration, with explicit constants and no eventual threshold. -/
theorem cumulativeHilbertFunction_diagonal_bounds
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) (n : ℕ) :
    cumulativeHilbertFunction M Q n ≤
        (n + 1) ^ M.factorCount *
          hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) ∧
      (n + 1) ^ M.factorCount *
          hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) ≤
        cumulativeHilbertFunction M Q (2 * M.factorCount * n) := by
  classical
  let H := hilbertFunction K M.factorCount M.ambientDimension Q
  have hmono : Monotone H := hilbertFunction_mono_relevant_prime M Q hQ hhom hrel
  have hic : (Finset.Iic (fun _ : M.FactorIndex => n)).card = (n + 1) ^ M.factorCount := by
    simp [Pi.card_Iic, Nat.card_Iic, MultiProjectiveSpace.FactorIndex]
  have hcc : (Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n)).card =
      (n + 1) ^ M.factorCount := by
    have hnat : 2 * n + 1 - n = n + 1 := by omega
    simp [Pi.card_Icc, Nat.card_Icc, hnat, MultiProjectiveSpace.FactorIndex]
  constructor
  · rw [cumulativeHilbertFunction_eq_sum M Q hhom]
    calc
      ∑ d ∈ multidegreesLe M n, H d ≤ ∑ d ∈ Finset.Iic (fun _ => n), H d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro _ _ _; exact Nat.zero_le _
      _ ≤ ∑ _d ∈ Finset.Iic (fun _ : M.FactorIndex => n), H (fun _ => n) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hmono (Finset.mem_Iic.mp hd)
      _ = (n + 1) ^ M.factorCount * H (fun _ => n) := by
        rw [Finset.sum_const, nsmul_eq_mul, hic]
        simp
  · rw [cumulativeHilbertFunction_eq_sum M Q hhom]
    have hsub : Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n) ⊆
        multidegreesLe M (2 * M.factorCount * n) := by
      intro d hd
      apply (mem_multidegreesLe M _ d).mpr
      have h := Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => (Finset.mem_Icc.mp hd).2 i)
      have hs : (∑ _i : M.FactorIndex, 2 * n) = 2 * M.factorCount * n := by
        simp [MultiProjectiveSpace.FactorIndex]
        ring
      exact h.trans_eq hs
    calc
      (n + 1) ^ M.factorCount * H (fun _ => n) =
          ∑ _d ∈ Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n), H (fun _ => n) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcc]
        simp
      _ ≤ ∑ d ∈ Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n), H d := by
        apply Finset.sum_le_sum
        intro d hd
        exact hmono (Finset.mem_Icc.mp hd).1
      _ ≤ ∑ d ∈ multidegreesLe M (2 * M.factorCount * n), H d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro _ _ _; exact Nat.zero_le _

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
/-- A relevant homogeneous prime has a nonzero actual Hilbert polynomial. -/
theorem relevant_prime_hilbertPolynomial_ne_zero (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    hilbertPolynomial K M.factorCount M.ambientDimension Q ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := relevant_variables M Q hrel
  intro hz
  have hex := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q hhom)
  rw [hz] at hex
  obtain ⟨d, hd⟩ := hex
  let P : M.CoordinateRing := ∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i
  have hP : P ∉ Q := variable_product_notMem M Q hQ v hv d
  let x : quotientPiece K M.factorCount M.ambientDimension Q d :=
    ⟨Ideal.Quotient.mk Q P, P, (M.degreePiece_iff P d).mpr (variable_product_homogeneous M v d), rfl⟩
  have hx : x ≠ 0 := by
    intro h
    exact hP (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val h))
  letI : Nontrivial (quotientPiece K M.factorCount M.ambientDimension Q d) :=
    ⟨⟨x, 0, hx⟩⟩
  have hpos := Module.finrank_pos (R := K)
    (M := quotientPiece K M.factorCount M.ambientDimension Q d)
  have heq := hd d (fun _ => le_rfl)
  change (MvPolynomial.eval _ (0 : MvPolynomial M.FactorIndex ℚ)) = _ at heq
  rw [map_zero] at heq
  have hzero : hilbertFunction K M.factorCount M.ambientDimension Q d = 0 := by exact_mod_cast heq.symm
  exact (Nat.ne_of_gt hpos) hzero

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.Hilbert

theorem diagonalPolynomial_eq_sum {ι : Type*} (F : MvPolynomial ι ℚ) :
    eval₂ Polynomial.C (fun _ => Polynomial.X) F =
      ∑ e ∈ F.support, Polynomial.monomial e.degree (coeff e F) := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [eval₂_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval₂_monomial]
  have hp : e.prod (fun _ k => (Polynomial.X : Polynomial ℚ) ^ k) =
      Polynomial.X ^ e.degree := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  rw [hp, Polynomial.C_mul_X_pow_eq_monomial]

/-- Nonnegative top coefficients prevent cancellation on the diagonal. -/
theorem diagonalPolynomial_degree_and_leadingCoeff {ι : Type*}
    (F : MvPolynomial ι ℚ) (hF : F ≠ 0)
    (hpos : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F) :
    (eval₂ Polynomial.C (fun _ => Polynomial.X) F).natDegree = F.totalDegree ∧
      0 < (eval₂ Polynomial.C (fun _ => Polynomial.X) F).leadingCoeff := by
  classical
  let P := eval₂ Polynomial.C (fun _ => Polynomial.X) F
  have hle : P.natDegree ≤ F.totalDegree := by
    dsimp only [P]
    rw [diagonalPolynomial_eq_sum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro e he
    exact (Polynomial.natDegree_monomial_le (coeff e F)).trans (le_totalDegree he)
  have hcoef : 0 < P.coeff F.totalDegree := by
    dsimp only [P]
    rw [diagonalPolynomial_eq_sum, Polynomial.finsetSum_coeff]
    obtain ⟨e, he, hdeg⟩ := Finset.exists_mem_eq_sup F.support
      (support_nonempty.mpr hF) Finsupp.degree
    change F.totalDegree = e.degree at hdeg
    have hdeg' : e.degree = F.totalDegree := hdeg.symm
    apply Finset.sum_pos'
    · intro b hb
      rw [Polynomial.coeff_monomial]
      split_ifs with h
      · exact hpos b h
      · exact le_rfl
    · refine ⟨e, he, ?_⟩
      rw [Polynomial.coeff_monomial, if_pos hdeg']
      exact lt_of_le_of_ne (hpos e hdeg') (Ne.symm (mem_support_iff.mp he))
  have hdeg : P.natDegree = F.totalDegree :=
    le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (ne_of_gt hcoef))
  refine ⟨hdeg, ?_⟩
  change 0 < P.leadingCoeff
  simpa only [Polynomial.leadingCoeff, hdeg] using hcoef

theorem diagonalPolynomial_eval {ι : Type*} (F : MvPolynomial ι ℚ) (x : ℚ) :
    (eval₂ Polynomial.C (fun _ => Polynomial.X) F).eval x = eval (fun _ => x) F := by
  classical
  rw [diagonalPolynomial_eq_sum, Polynomial.eval_finsetSum]
  conv_rhs => rw [F.as_sum]
  rw [eval_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Polynomial.eval_monomial, eval_monomial, Finsupp.prod,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

/-- The diagonal of the actual Hilbert function eventually has precisely
the original total degree and a positive leading coefficient. -/
theorem exists_diagonal_hilbertPolynomial
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ P : Polynomial ℚ, P.natDegree = SectionThree.idealDimension M Q ∧
      0 < P.leadingCoeff ∧ ∃ N : ℕ, ∀ n ≥ N,
        P.eval (n : ℚ) =
          (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) := by
  classical
  let F := hilbertPolynomial K M.factorCount M.ambientDimension Q
  have hF : F ≠ 0 := relevant_prime_hilbertPolynomial_ne_zero M Q hQ hhom hrel
  have htop : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F := by
    intro e he
    have h := (multigraded_hilbert_polynomial_top_coefficients K M Q hhom).1 e
    rwa [coeff_homogeneousComponent, if_pos he] at h
  obtain ⟨hdeg, hpos⟩ := diagonalPolynomial_degree_and_leadingCoeff F hF htop
  refine ⟨eval₂ Polynomial.C (fun _ => Polynomial.X) F, hdeg, hpos, ?_⟩
  obtain ⟨d₀, hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q hhom)
  refine ⟨Finset.univ.sup d₀, fun n hn => ?_⟩
  rw [diagonalPolynomial_eval]
  apply hd₀
  intro i
  exact (Finset.le_sup (Finset.mem_univ i)).trans hn

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.Hilbert

theorem polynomial_eventually_two_sided (P : Polynomial ℚ) (hpos : 0 < P.leadingCoeff) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℚ) ^ P.natDegree ≤ P.eval (n : ℚ) ∧
        P.eval (n : ℚ) ≤ C * (n : ℚ) ^ P.natDegree := by
  have hP : P ≠ 0 := by
    intro hz
    simpa [hz] using hpos
  have hdegree : P.degree = (Polynomial.X ^ P.natDegree : Polynomial ℚ).degree := by
    rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hP]
  have hlim := P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (Polynomial.X ^ P.natDegree) hdegree
  have hlim' : Tendsto (fun n : ℕ => P.eval (n : ℚ) / (n : ℚ) ^ P.natDegree)
      atTop (𝓝 P.leadingCoeff) := by
    simpa [Function.comp_def] using hlim.comp (tendsto_natCast_atTop_atTop (R := ℚ))
  have hlo := (tendsto_order.mp hlim').1 (P.leadingCoeff / 2) (by linarith)
  have hhi := (tendsto_order.mp hlim').2 (2 * P.leadingCoeff) (by linarith)
  refine ⟨P.leadingCoeff / 2, 2 * P.leadingCoeff, by positivity, by positivity, ?_⟩
  filter_upwards [hlo, hhi, eventually_ge_atTop 1] with n hnlo hnhi hn
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp := pow_pos hnpos P.natDegree
  exact ⟨(le_div_iff₀ hp).mp hnlo.le, (div_le_iff₀ hp).mp hnhi.le⟩

/-- The Hilbert-polynomial side of the prime dimension comparison:
the actual quotient filtration has matching polynomial growth bounds. -/
theorem cumulativeHilbertFunction_polynomial_bounds
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      c * (n : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) ≤
          (cumulativeHilbertFunction M Q (2 * M.factorCount * n) : ℚ) ∧
        (cumulativeHilbertFunction M Q n : ℚ) ≤
          C * ((n + 1 : ℕ) : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) := by
  obtain ⟨P, hdeg, hpos, N₀, hP⟩ := exists_diagonal_hilbertPolynomial M Q hQ hhom hrel
  obtain ⟨c, C, hc, hC, hbounds⟩ := polynomial_eventually_two_sided P hpos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbounds
  refine ⟨c, C, hc, hC, max N N₀, fun n hn => ?_⟩
  have hp := hN n ((le_max_left N N₀).trans hn)
  rw [hP n ((le_max_right N N₀).trans hn), hdeg] at hp
  obtain ⟨hupper, hlower⟩ := cumulativeHilbertFunction_diagonal_bounds M Q hQ hhom hrel n
  have hu : (cumulativeHilbertFunction M Q n : ℚ) ≤
      ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
        (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) := by
    exact_mod_cast hupper
  have hl : ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
        (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) ≤
      (cumulativeHilbertFunction M Q (2 * M.factorCount * n) : ℚ) := by
    exact_mod_cast hlower
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have hn1 : (n : ℚ) ≤ ((n + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.le_succ n
  have hpow (b : ℕ) : (n : ℚ) ^ b ≤ ((n + 1 : ℕ) : ℚ) ^ b :=
    pow_le_pow_left₀ hn0 hn1 b
  constructor
  · calc
      c * (n : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) =
          (n : ℚ) ^ M.factorCount * (c * (n : ℚ) ^ SectionThree.idealDimension M Q) := by
        rw [pow_add]; ring
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (c * (n : ℚ) ^ SectionThree.idealDimension M Q) :=
        mul_le_mul_of_nonneg_right (hpow M.factorCount) (by positivity)
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) :=
        mul_le_mul_of_nonneg_left hp.1 (by positivity)
      _ ≤ _ := hl
  · calc
      (cumulativeHilbertFunction M Q n : ℚ) ≤ _ := hu
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (C * (n : ℚ) ^ SectionThree.idealDimension M Q) :=
        mul_le_mul_of_nonneg_left hp.2 (by positivity)
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (C * ((n + 1 : ℕ) : ℚ) ^ SectionThree.idealDimension M Q) := by
        gcongr
      _ = _ := by rw [pow_add]; ring

end PhilipponMultiplicity.Hilbert

end

theorem solution
{K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      c * (n : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) ≤
          (cumulativeHilbertFunction M Q (2 * M.factorCount * n) : ℚ) ∧
        (cumulativeHilbertFunction M Q n : ℚ) ≤
          C * ((n + 1 : ℕ) : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) := by
  exact PhilipponMultiplicity.Hilbert.cumulativeHilbertFunction_polynomial_bounds M Q hQ hhom hrel
