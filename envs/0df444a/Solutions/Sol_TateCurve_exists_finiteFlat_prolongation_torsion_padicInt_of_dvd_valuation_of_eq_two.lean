-- Prove2me | solution 1 for TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e1951c35-40d6-54cc-b92f-4111a669315f

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_PadicInt_exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one
import Theorems.Thm_Padic_exists_complete_algClosed_isometry_algebraicClosure
import Theorems.Thm_WeierstrassCurve_Affine_Point_isIntegral_of_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_two
p2m_attr_erase "instance" "PadicInt.KummerCarrier.instFreeA PadicInt.KummerCarrier.instFiniteA"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

open scoped NNReal WeierstrassCurve.Affine
p2m_open "WeierstrassCurve WeierstrassCurve.Affine TateCurve P2MW.S_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_two.TateCurve"

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "isElliptic term summable_term coeffSum b a₄ a₆ curve tateParam_ne_zero tateParam_pow tateParam_offLattice point_inv_eq_neg point_mul_eq_add_or_sub_of_symAddHyps zeta_pow_mod tateTorsionPoint tateTorsionPoint_spec tateTorsionPoint_zero_zero tateTorsionPoint_ne_zero map_pointX_tateParam map_pointY_tateParam eq_or_mul_eq_one_of_pointX_eq SymAddHyps nonsingular_point OffLattice AddParams pointX pointY pointX_zpow_mul pointY_zpow_mul symAddHyps_unconditional"
namespace TwoTorsionProlongation
p2m_open "TateCurve"

section Generic

variable {F : Type*} [Field F] [DecidableEq F]

theorem ps_congr {W : WeierstrassCurve.Affine F} {x x' y y' : F}
    (hx : x = x') (hy : y = y')
    (h : W.Nonsingular x y) (h' : W.Nonsingular x' y') :
    (Point.some x y h : W.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

theorem isRoot_Ψ₂Sq_of_neg_eq {W : WeierstrassCurve.Affine F} {x y : F}
    (h : W.Nonsingular x y)
    (hneg : -(Point.some x y h : W.Point) = Point.some x y h) : W.Ψ₂Sq.IsRoot x := by
  rw [Point.neg_some, Point.some.injEq] at hneg
  have hy : y - W.negY x y = 0 := by rw [hneg.2, sub_self]
  have hsq := sq_sub_negY_eq_eval_Ψ₂Sq h.left
  rw [hy, zero_pow two_ne_zero] at hsq
  exact hsq.symm

theorem eq_of_neg_eq_of_X_eq {W : WeierstrassCurve.Affine F} {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hneg₂ : -(Point.some x₂ y₂ h₂ : W.Point) = Point.some x₂ y₂ h₂) (hx : x₁ = x₂) :
    (Point.some x₁ y₁ h₁ : W.Point) = Point.some x₂ y₂ h₂ := by
  rw [Point.neg_some, Point.some.injEq] at hneg₂
  rcases Y_eq_of_X_eq h₁.left h₂.left hx with hy | hy
  · exact ps_congr hx hy h₁ h₂
  · exact ps_congr hx (hy.trans hneg₂.2) h₁ h₂

theorem two_torsion_exhaust {W : WeierstrassCurve.Affine F} (h4 : (4 : F) ≠ 0)
    {A B C R : W.Point} (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hA : -A = A) (hB : -B = B) (hC : -C = C) (hR : -R = R) :
    R = 0 ∨ R = A ∨ R = B ∨ R = C := by
  rcases A with _ | ⟨xA, yA, hAn⟩
  · exact absurd rfl hA0
  rcases B with _ | ⟨xB, yB, hBn⟩
  · exact absurd rfl hB0
  rcases C with _ | ⟨xC, yC, hCn⟩
  · exact absurd rfl hC0
  rcases R with _ | ⟨x, y, hRn⟩
  · exact Or.inl rfl
  right
  by_cases hxA : x = xA
  · exact Or.inl (eq_of_neg_eq_of_X_eq hRn hAn hA hxA)
  by_cases hxB : x = xB
  · exact Or.inr (Or.inl (eq_of_neg_eq_of_X_eq hRn hBn hB hxB))
  by_cases hxC : x = xC
  · exact Or.inr (Or.inr (eq_of_neg_eq_of_X_eq hRn hCn hC hxC))
  exfalso
  have hAB' : xA ≠ xB := fun h => hAB (eq_of_neg_eq_of_X_eq hAn hBn hB h)
  have hAC' : xA ≠ xC := fun h => hAC (eq_of_neg_eq_of_X_eq hAn hCn hC h)
  have hBC' : xB ≠ xC := fun h => hBC (eq_of_neg_eq_of_X_eq hBn hCn hC h)
  have hne : W.Ψ₂Sq ≠ 0 := WeierstrassCurve.Ψ₂Sq_ne_zero W h4
  have hZcard : ({x, xA, xB, xC} : Finset F).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hBC'
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hAB', hAC'⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hxA, hxB, hxC⟩
  have hsub : ({x, xA, xB, xC} : Finset F).val ⊆ W.Ψ₂Sq.roots := by
    intro z hz
    rw [Finset.mem_val] at hz
    rw [Polynomial.mem_roots hne]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact isRoot_Ψ₂Sq_of_neg_eq hRn hR
    · exact isRoot_Ψ₂Sq_of_neg_eq hAn hA
    · exact isRoot_Ψ₂Sq_of_neg_eq hBn hB
    · exact isRoot_Ψ₂Sq_of_neg_eq hCn hC
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  have h3 := WeierstrassCurve.natDegree_Ψ₂Sq_le W
  omega

theorem klein_add_table {G : Type*} [AddCommGroup G] (f : ℕ → ℕ → G) (h00 : f 0 0 = 0)
    (hAA : f 1 0 + f 1 0 = 0) (hBB : f 0 1 + f 0 1 = 0) (hC : f 1 1 = f 1 0 + f 0 1) :
    ∀ i j i' j' : ℕ, i < 2 → j < 2 → i' < 2 → j' < 2 →
      f ((i + i') % 2) ((j + j') % 2) = f i j + f i' j' := by
  intro i j i' j' hi hj hi' hj'
  have hAAB : f 1 0 + (f 1 0 + f 0 1) = f 0 1 := by rw [← add_assoc, hAA, zero_add]
  have hBAB : f 0 1 + (f 1 0 + f 0 1) = f 1 0 := by
    rw [add_comm (f 1 0) (f 0 1), ← add_assoc, hBB, zero_add]
  have hCC : (f 1 0 + f 0 1) + (f 1 0 + f 0 1) = 0 := by
    rw [add_assoc, hBAB, hAA]
  interval_cases i <;> interval_cases j <;> interval_cases i' <;> interval_cases j'
  · show f 0 0 = f 0 0 + f 0 0; rw [h00, add_zero]
  · show f 0 1 = f 0 0 + f 0 1; rw [h00, zero_add]
  · show f 1 0 = f 0 0 + f 1 0; rw [h00, zero_add]
  · show f 1 1 = f 0 0 + f 1 1; rw [h00, zero_add]
  · show f 0 1 = f 0 1 + f 0 0; rw [h00, add_zero]
  · show f 0 0 = f 0 1 + f 0 1; rw [h00, hBB]
  · show f 1 1 = f 0 1 + f 1 0; rw [hC, add_comm]
  · show f 1 0 = f 0 1 + f 1 1; rw [hC, hBAB]
  · show f 1 0 = f 1 0 + f 0 0; rw [h00, add_zero]
  · show f 1 1 = f 1 0 + f 0 1; rw [hC]
  · show f 0 0 = f 1 0 + f 1 0; rw [h00, hAA]
  · show f 0 1 = f 1 0 + f 1 1; rw [hC, hAAB]
  · show f 1 1 = f 1 1 + f 0 0; rw [h00, add_zero]
  · show f 1 0 = f 1 1 + f 0 1; rw [hC, add_comm, hBAB]
  · show f 0 1 = f 1 1 + f 1 0; rw [hC, add_comm, hAAB]
  · show f 0 0 = f 1 1 + f 1 1; rw [hC, hCC, h00]

theorem klein_inj_table {G : Type*} (f : ℕ → ℕ → G)
    (hA0 : f 1 0 ≠ f 0 0) (hB0 : f 0 1 ≠ f 0 0) (hC0 : f 1 1 ≠ f 0 0)
    (hAB : f 1 0 ≠ f 0 1) (hAC : f 1 0 ≠ f 1 1) (hBC : f 0 1 ≠ f 1 1) :
    ∀ i j i' j' : ℕ, i < 2 → j < 2 → i' < 2 → j' < 2 →
      f i j = f i' j' → i = i' ∧ j = j' := by
  intro i j i' j' hi hj hi' hj' h
  interval_cases i <;> interval_cases j <;> interval_cases i' <;> interval_cases j'
  · exact ⟨rfl, rfl⟩
  · exact absurd h.symm hB0
  · exact absurd h.symm hA0
  · exact absurd h.symm hC0
  · exact absurd h hB0
  · exact ⟨rfl, rfl⟩
  · exact absurd h.symm hAB
  · exact absurd h hBC
  · exact absurd h hA0
  · exact absurd h hAB
  · exact ⟨rfl, rfl⟩
  · exact absurd h hAC
  · exact absurd h hC0
  · exact absurd h.symm hBC
  · exact absurd h.symm hAC
  · exact ⟨rfl, rfl⟩

end Generic

section Analytic

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q : K}

theorem neg_point_eq_of_sq (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {u : K} (hu0 : u ≠ 0)
    (hu : OffLattice q u) {j : ℤ} (hsq : u ^ 2 = q ^ j)
    (hns : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)) :
    -(Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point)
      = Point.some (pointX q u) (pointY q u) hns := by
  have hinv : u⁻¹ = q ^ (-j) * u := by
    rw [zpow_neg, ← hsq, sq, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  have hX : pointX q u⁻¹ = pointX q u := by rw [hinv, pointX_zpow_mul hq0]
  have hY : pointY q u⁻¹ = pointY q u := by rw [hinv, pointY_zpow_mul hq0]
  have h₁ : (curve q).toAffine.Nonsingular (pointX q u⁻¹) (pointY q u⁻¹) := by
    rw [hX, hY]; exact hns
  have hneg := point_inv_eq_neg hq0 hq hu0 hu h₁ hns
  rw [ps_congr hX hY h₁ hns] at hneg
  exact hneg.symm

variable {ζ t : K}

theorem norm_eq_one_of_isPrimitiveRoot_two (hζ : IsPrimitiveRoot ζ 2) : ‖ζ‖ = 1 := by
  have h : ‖ζ‖ ^ 2 = 1 := by rw [← norm_pow, hζ.pow_eq_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) two_ne_zero).mp h

theorem norm_lt_one_of_sq_eq (hq : ‖q‖₊ < 1) (ht : t ^ 2 = q) : ‖t‖ < 1 := by
  have h : ‖t‖ ^ 2 < 1 := by
    rw [← norm_pow, ht]
    exact_mod_cast hq
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg t) two_ne_zero).mp h

theorem norm_lt_norm_of_sq_eq (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (ht : t ^ 2 = q) : ‖q‖ < ‖t‖ := by
  have ht0 : t ≠ 0 := fun h => hq0 (by rw [← ht, h, zero_pow two_ne_zero])
  have hpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  calc ‖q‖ = ‖t‖ * ‖t‖ := by rw [← ht, norm_pow, sq]
    _ < ‖t‖ := mul_lt_of_lt_one_left hpos (norm_lt_one_of_sq_eq hq ht)

theorem pointX_zeta_ne_pointX_troot (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ 2) (ht : t ^ 2 = q) :
    pointX q (ζ ^ 1 * t ^ 0) ≠ pointX q (ζ ^ 0 * t ^ 1) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero two_ne_zero
  have ht0 : t ≠ 0 := fun h => hq0 (by rw [← ht, h, zero_pow two_ne_zero])
  have hζoff : OffLattice q ζ := by
    have h := tateParam_offLattice hq0 hq hζ ht (i := 1) (j := 0) one_lt_two two_pos (by omega)
    rwa [pow_one, pow_zero, mul_one] at h
  have htoff : OffLattice q t := by
    have h := tateParam_offLattice hq0 hq hζ ht (i := 0) (j := 1) two_pos one_lt_two (by omega)
    rwa [pow_one, pow_zero, one_mul] at h
  have hq1 : q ≠ 1 := by
    intro h
    rw [h, nnnorm_one] at hq
    exact lt_irrefl _ hq
  rw [pow_one, pow_zero, mul_one, pow_zero, pow_one, one_mul]
  intro hX
  have hζ1 : ‖ζ‖ ≤ 1 := (norm_eq_one_of_isPrimitiveRoot_two hζ).le
  have ht1 : ‖t‖ ≤ 1 := (norm_lt_one_of_sq_eq hq ht).le
  have hqt : ‖q‖ < ‖ζ * t‖ := by
    rw [norm_mul, norm_eq_one_of_isPrimitiveRoot_two hζ, one_mul]
    exact norm_lt_norm_of_sq_eq hq0 hq ht
  rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hζ0 ht0 hζoff htoff hζ1 ht1 hqt hX with h | h
  · exact hq1 (by rw [← ht, ← h, hζ.pow_eq_one])
  · apply hq1
    calc q = t ^ 2 := ht.symm
      _ = (ζ * t) ^ 2 := by rw [mul_pow, hζ.pow_eq_one, one_mul]
      _ = 1 := by rw [h, one_pow]

variable [IsAlgClosed K]

theorem neg_tateTorsionPoint_two (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ 2) (ht : t ^ 2 = q) (i j : ℕ) :
    -tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht i j
      = tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht i j := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero two_ne_zero
  have ht0 : t ≠ 0 := fun h => hq0 (by rw [← ht, h, zero_pow two_ne_zero])
  by_cases hij : i < 2 ∧ j < 2 ∧ ¬(i = 0 ∧ j = 0)
  · rw [tateTorsionPoint_spec hq0 hq Nat.prime_two hζ ht hij.1 hij.2.1 hij.2.2]
    exact neg_point_eq_of_sq hq0 hq (tateParam_ne_zero hζ0 ht0)
      (tateParam_offLattice hq0 hq hζ ht hij.1 hij.2.1 hij.2.2)
      (tateParam_pow hζ.pow_eq_one ht i j) _
  · rw [tateTorsionPoint, dif_neg hij, neg_zero]

theorem tateTorsionPoint_two_mem (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ 2) (ht : t ^ 2 = q) (i j : ℕ) :
    tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht i j
      ∈ Submodule.torsionBy ℤ (curve q).toAffine.Point (2 : ℕ) := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul, two_nsmul, add_eq_zero_iff_neg_eq]
  exact neg_tateTorsionPoint_two hq0 hq hζ ht i j

theorem tateTorsionPoint_two_one_one (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ 2) (ht : t ^ 2 = q) :
    tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht 1 1
      = tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht 1 0
        + tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht 0 1 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero two_ne_zero
  have ht0 : t ≠ 0 := fun h => hq0 (by rw [← ht, h, zero_pow two_ne_zero])
  have hyps : SymAddHyps q := symAddHyps_unconditional hq0 hq
  have hζinv : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hζ.pow_eq_one)
  have hvw : ζ ^ 1 * t ^ 0 * (ζ ^ 0 * t ^ 1) = ζ ^ 1 * t ^ 1 := by ring
  have hdiv : ζ ^ 1 * t ^ 0 * (ζ ^ 0 * t ^ 1)⁻¹ = (ζ ^ 1 * t ^ 1)⁻¹ := by
    simp only [pow_one, pow_zero, mul_one, one_mul, mul_inv, hζinv]
  have hoff10 : OffLattice q (ζ ^ 1 * t ^ 0) :=
    tateParam_offLattice hq0 hq hζ ht (i := 1) (j := 0) one_lt_two two_pos (by omega)
  have hoff01 : OffLattice q (ζ ^ 0 * t ^ 1) :=
    tateParam_offLattice hq0 hq hζ ht (i := 0) (j := 1) two_pos one_lt_two (by omega)
  have hoff11 : OffLattice q (ζ ^ 1 * t ^ 1) :=
    tateParam_offLattice hq0 hq hζ ht (i := 1) (j := 1) one_lt_two one_lt_two (by omega)
  have hap : AddParams q (ζ ^ 1 * t ^ 0) (ζ ^ 0 * t ^ 1) :=
    { q_ne_zero := hq0
      u_ne_zero := tateParam_ne_zero hζ0 ht0
      v_ne_zero := tateParam_ne_zero hζ0 ht0
      offLattice_u := hoff10
      offLattice_v := hoff01
      offLattice_mul := by rw [hvw]; exact hoff11
      offLattice_div := by rw [hdiv]; exact hoff11.inv hq0 }
  have hxne := pointX_zeta_ne_pointX_troot hq0 hq hζ ht
  have hns₁ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ 1 * t ^ 0 * (ζ ^ 0 * t ^ 1)))
      (pointY q (ζ ^ 1 * t ^ 0 * (ζ ^ 0 * t ^ 1))) := by
    rw [hvw]; exact nonsingular_point hq0 hq (tateParam_ne_zero hζ0 ht0) hoff11
  have hns10 := nonsingular_point hq0 hq (tateParam_ne_zero hζ0 ht0 (i := 1) (j := 0)) hoff10
  have hns01 := nonsingular_point hq0 hq (tateParam_ne_zero hζ0 ht0 (i := 0) (j := 1)) hoff01
  have hns11 := nonsingular_point hq0 hq (tateParam_ne_zero hζ0 ht0 (i := 1) (j := 1)) hoff11
  have key := point_mul_eq_add_or_sub_of_symAddHyps hyps hap hxne hns₁ hns10 hns01
  have hCeq : (Point.some _ _ hns₁ : (curve q).toAffine.Point)
      = Point.some (pointX q (ζ ^ 1 * t ^ 1)) (pointY q (ζ ^ 1 * t ^ 1)) hns11 :=
    ps_congr (congrArg (pointX q) hvw) (congrArg (pointY q) hvw) hns₁ hns11
  rw [hCeq] at key
  have hA := neg_point_eq_of_sq hq0 hq (tateParam_ne_zero hζ0 ht0) hoff10
    (tateParam_pow hζ.pow_eq_one ht 1 0) hns10
  have hB := neg_point_eq_of_sq hq0 hq (tateParam_ne_zero hζ0 ht0) hoff01
    (tateParam_pow hζ.pow_eq_one ht 0 1) hns01
  rw [tateTorsionPoint_spec hq0 hq Nat.prime_two hζ ht (i := 1) (j := 1) one_lt_two one_lt_two
      (by omega),
    tateTorsionPoint_spec hq0 hq Nat.prime_two hζ ht (i := 1) (j := 0) one_lt_two two_pos
      (by omega),
    tateTorsionPoint_spec hq0 hq Nat.prime_two hζ ht (i := 0) (j := 1) two_pos one_lt_two
      (by omega)]
  rcases key with h | h | h | h
  · exact h
  · exact h.trans (by rw [neg_add, hA, hB])
  · exact h.trans (by rw [sub_eq_add_neg, hB])
  · exact h.trans (by rw [neg_sub, sub_eq_add_neg, hA, add_comm])

theorem tateTorsionPoint_two_one_zero_ne_zero_one (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ 2) (ht : t ^ 2 = q) :
    tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht 1 0
      ≠ tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht 0 1 := by
  intro h
  rw [tateTorsionPoint_spec hq0 hq Nat.prime_two hζ ht (i := 1) (j := 0) one_lt_two two_pos
      (by omega),
    tateTorsionPoint_spec hq0 hq Nat.prime_two hζ ht (i := 0) (j := 1) two_pos one_lt_two
      (by omega), Point.some.injEq] at h
  exact pointX_zeta_ne_pointX_troot hq0 hq hζ ht h.1

variable (q ζ t) in

noncomputable def twoTorsionMap (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ 2) (ht : t ^ 2 = q) (ij : ZMod 2 × ZMod 2) :
    (curve q).n_torsionGen 2 :=
  ⟨tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht ij.1.val ij.2.val,
    tateTorsionPoint_two_mem hq0 hq hζ ht _ _⟩

theorem twoTorsionMap_val (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ 2) (ht : t ^ 2 = q) (i j : ZMod 2) :
    ((twoTorsionMap q ζ t hq0 hq hζ ht (i, j) : (curve q).n_torsionGen 2)
        : (curve q).toAffine.Point)
      = tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht i.val j.val := rfl

theorem twoTorsionMap_add (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ 2) (ht : t ^ 2 = q) (a b : ZMod 2 × ZMod 2) :
    ((twoTorsionMap q ζ t hq0 hq hζ ht (a + b) : (curve q).n_torsionGen 2)
        : (curve q).toAffine.Point)
      = (twoTorsionMap q ζ t hq0 hq hζ ht a : (curve q).toAffine.Point)
        + (twoTorsionMap q ζ t hq0 hq hζ ht b : (curve q).toAffine.Point) := by
  obtain ⟨i, j⟩ := a
  obtain ⟨i', j'⟩ := b
  show tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht (i + i').val (j + j').val = _
  rw [twoTorsionMap_val, twoTorsionMap_val, ZMod.val_add, ZMod.val_add]
  have hA := neg_tateTorsionPoint_two hq0 hq hζ ht 1 0
  have hB := neg_tateTorsionPoint_two hq0 hq hζ ht 0 1
  exact klein_add_table (fun i j => tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht i j)
    (tateTorsionPoint_zero_zero hq0 hq Nat.prime_two hζ ht)
    (add_eq_zero_iff_neg_eq.mpr hA) (add_eq_zero_iff_neg_eq.mpr hB)
    (tateTorsionPoint_two_one_one hq0 hq hζ ht) _ _ _ _
    (ZMod.val_lt i) (ZMod.val_lt j) (ZMod.val_lt i') (ZMod.val_lt j')

theorem twoTorsionMap_bijective (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ 2) (ht : t ^ 2 = q) :
    Function.Bijective (twoTorsionMap q ζ t hq0 hq hζ ht) := by
  have h00 := tateTorsionPoint_zero_zero hq0 hq Nat.prime_two hζ ht
  have hA0 := tateTorsionPoint_ne_zero hq0 hq Nat.prime_two hζ ht (i := 1) (j := 0)
    one_lt_two two_pos (by omega)
  have hB0 := tateTorsionPoint_ne_zero hq0 hq Nat.prime_two hζ ht (i := 0) (j := 1)
    two_pos one_lt_two (by omega)
  have hC0 := tateTorsionPoint_ne_zero hq0 hq Nat.prime_two hζ ht (i := 1) (j := 1)
    one_lt_two one_lt_two (by omega)
  have hAB := tateTorsionPoint_two_one_zero_ne_zero_one hq0 hq hζ ht
  have hC := tateTorsionPoint_two_one_one hq0 hq hζ ht
  have hA := neg_tateTorsionPoint_two hq0 hq hζ ht 1 0
  have hB := neg_tateTorsionPoint_two hq0 hq hζ ht 0 1
  have hCn := neg_tateTorsionPoint_two hq0 hq hζ ht 1 1
  have hAC : tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht 1 0
      ≠ tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht 1 1 := by
    intro h
    rw [hC, eq_comm, add_eq_left] at h
    exact hB0 h
  have hBC : tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht 0 1
      ≠ tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht 1 1 := by
    intro h
    rw [hC, eq_comm, add_eq_right] at h
    exact hA0 h
  constructor
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' := congrArg Subtype.val h
    rw [twoTorsionMap_val, twoTorsionMap_val] at h'
    obtain ⟨h1, h2⟩ := klein_inj_table
      (fun i j => tateTorsionPoint q ζ t hq0 hq Nat.prime_two hζ ht i j)
      (fun h => hA0 (h.trans h00)) (fun h => hB0 (h.trans h00)) (fun h => hC0 (h.trans h00))
      hAB hAC hBC
      _ _ _ _ (ZMod.val_lt i) (ZMod.val_lt j) (ZMod.val_lt i') (ZMod.val_lt j') h'
    rw [Prod.mk.injEq]
    exact ⟨ZMod.val_injective 2 h1, ZMod.val_injective 2 h2⟩
  · rintro ⟨R, hR⟩
    have hR' : -R = R := by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul, two_nsmul, add_eq_zero_iff_neg_eq] at hR
      exact hR
    have h4 : (4 : K) ≠ 0 := by norm_num
    rcases two_torsion_exhaust h4 hA0 hB0 hC0 hAB hAC hBC hA hB hCn hR' with h | h | h | h
    · exact ⟨(0, 0), Subtype.ext (h00.trans h.symm)⟩
    · exact ⟨(1, 0), Subtype.ext h.symm⟩
    · exact ⟨(0, 1), Subtype.ext h.symm⟩
    · exact ⟨(1, 1), Subtype.ext h.symm⟩

variable (q ζ t) in

noncomputable def twoTorsionEquiv (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ 2) (ht : t ^ 2 = q) :
    (ZMod 2 × ZMod 2) ≃ (curve q).n_torsionGen 2 :=
  Equiv.ofBijective _ (twoTorsionMap_bijective hq0 hq hζ ht)

end Analytic

section Bridge

variable {K₁ : Type*} [NontriviallyNormedField K₁] [IsUltrametricDist K₁]
variable {K₂ : Type*} [NontriviallyNormedField K₂] [IsUltrametricDist K₂]

theorem map_tsum_of_summable₂ {ι : Type*} (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {f : ι → K₁}
    (hf : Summable f) : σ (∑' i, f i) = ∑' i, σ (f i) := by
  have h := hf.hasSum.map σ hσ.continuous
  simpa [Function.comp] using h.tsum_eq.symm

theorem map_term₂ (σ : K₁ →+* K₂) (q : K₁) (c : ℕ → ℕ) (n : ℕ) :
    σ (term c q n) = term c (σ q) n := by
  simp only [term, map_mul, map_natCast, map_div₀, map_pow, map_sub, map_one]

variable [CompleteSpace K₁] [CompleteSpace K₂]

theorem map_coeffSum₂ (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {q : K₁} (hq : ‖q‖₊ < 1) (c : ℕ → ℕ) :
    σ (coeffSum c q) = coeffSum c (σ q) := by
  rw [coeffSum, coeffSum, map_tsum_of_summable₂ σ hσ (summable_term c hq)]
  exact tsum_congr fun n => map_term₂ σ q c n

theorem map_a₄₂ (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {q : K₁} (hq : ‖q‖₊ < 1) :
    σ (a₄ q) = a₄ (σ q) := by
  simp only [a₄, map_neg]
  exact congrArg Neg.neg (map_coeffSum₂ σ hσ hq _)

theorem map_a₆₂ (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {q : K₁} (hq : ‖q‖₊ < 1) :
    σ (a₆ q) = a₆ (σ q) := by
  simp only [a₆, map_neg]
  exact congrArg Neg.neg (map_coeffSum₂ σ hσ hq _)

theorem map_curve₂ (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {q : K₁} (hq : ‖q‖₊ < 1) :
    (curve q).map σ = curve (σ q) := by
  ext <;> simp [curve, WeierstrassCurve.map, map_a₄₂ σ hσ hq, map_a₆₂ σ hσ hq]

theorem torsionBy_baseChange_bijective (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0)
    (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [Algebra ℚ_[p] K]
    (hiso : ∀ x : ℚ_[p], ‖algebraMap ℚ_[p] K x‖ = ‖x‖)
    (ι : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] K) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    letI : DecidableEq K := Classical.decEq _
    ((TateCurve.curve qT).map (algebraMap ℚ_[p] K) = TateCurve.curve (algebraMap ℚ_[p] K qT)) ∧
    Function.Bijective
      (fun P : Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point n =>
        (⟨WeierstrassCurve.Affine.Point.map ι
            (P : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point),
          by
            rw [Submodule.mem_torsionBy_iff, ← AddMonoidHom.map_zsmul,
              (Submodule.mem_torsionBy_iff _ _).mp P.property, AddMonoidHom.map_zero]⟩ :
        Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄K).Point n)) := by
  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
  letI : DecidableEq K := Classical.decEq _
  have hf_isom : Isometry ⇑(algebraMap ℚ_[p] K) := AddMonoidHomClass.isometry_of_norm _ hiso
  have hιinj : Function.Injective ⇑ι := RingHom.injective ι.toRingHom
  refine ⟨map_curve₂ (algebraMap ℚ_[p] K) hf_isom hqT1, ?_, ?_⟩
  · intro P Q hPQ
    exact Subtype.ext (Affine.Point.map_injective ι (congrArg Subtype.val hPQ))
  · rintro ⟨Q, hQ⟩
    rcases Q with _ | ⟨x, y, hns⟩
    · exact ⟨0, Subtype.ext (_root_.map_zero _)⟩
    · haveI : (curve qT).IsElliptic := TateCurve.isElliptic hqT0 hqT1
      have hn_ne : ((n : ℤ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hn
      have hQ' : (n : ℤ) • (Affine.Point.some x y hns : ((curve qT)⁄K).Point) = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp hQ
      have hxy := WeierstrassCurve.Affine.Point.isIntegral_of_smul_eq_zero
        (F := ℚ_[p]) (L := K) (W := curve qT) (n := (n : ℤ)) hn_ne hns hQ'
      obtain ⟨x', hx'⟩ := hxy.1.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) ι
      obtain ⟨y', hy'⟩ := hxy.2.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) ι
      replace hx' : ι x' = x := hx'
      replace hy' : ι y' = y := hy'
      have hns' : ((curve qT)⁄(AlgebraicClosure ℚ_[p])).Nonsingular x' y' := by
        have hnsK : ((curve qT)⁄K).Nonsingular (ι x') (ι y') := hx' ▸ hy' ▸ hns
        exact (WeierstrassCurve.Affine.baseChange_nonsingular
          (W := (curve qT).toAffine) hιinj x' y').mp hnsK
      refine ⟨⟨Affine.Point.some x' y' hns', ?_⟩, ?_⟩
      · rw [Submodule.mem_torsionBy_iff]
        apply Affine.Point.map_injective ι
        rw [AddMonoidHom.map_zsmul, _root_.map_zero, Affine.Point.map_some,
          ps_congr hx' hy' _ hns]
        exact hQ'
      · exact Subtype.ext ((Affine.Point.map_some ι hns').trans (ps_congr hx' hy' _ hns))

end Bridge

section Transport

variable {K : Type} [Field K] [DecidableEq K]

noncomputable def torsionByAddEquivOfEq {W W' : WeierstrassCurve K} (h : W = W') (n : ℕ) :
    W.n_torsionGen n ≃+ W'.n_torsionGen n := by
  subst h; exact AddEquiv.refl _

theorem torsionByAddEquivOfEq_symm_apply_val {W W' : WeierstrassCurve K} (h : W = W')
    (n : ℕ) (P : W'.n_torsionGen n) :
    (((torsionByAddEquivOfEq h n).symm P : W.n_torsionGen n) : W.toAffine.Point)
      = h.symm ▸ (P : W'.toAffine.Point) := by
  subst h; rfl

theorem transport_point_some {W W' : WeierstrassCurve K} (h : W = W')
    {x y : K} (hns : W'.toAffine.Nonsingular x y) :
    (h.symm ▸ (Affine.Point.some x y hns : W'.toAffine.Point) : W.toAffine.Point)
      = Affine.Point.some x y (h.symm ▸ hns) := by
  subst h; rfl

theorem transport_point_zero {W W' : WeierstrassCurve K} (h : W = W') :
    (h.symm ▸ (0 : W'.toAffine.Point) : W.toAffine.Point) = 0 := by
  subst h; rfl

theorem transport_nonsingular {W W' : WeierstrassCurve K} (h : W = W')
    {x y : K} (hns : W'.toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular x y := by
  subst h; exact hns

end Transport

end TateCurve.TwoTorsionProlongation

open TateCurve.TwoTorsionProlongation

namespace TateCurve p2m_export "TateCurve" "isElliptic term summable_term coeffSum b a₄ a₆ curve tateParam_ne_zero tateParam_pow tateParam_offLattice point_inv_eq_neg point_mul_eq_add_or_sub_of_symAddHyps zeta_pow_mod tateTorsionPoint tateTorsionPoint_spec tateTorsionPoint_zero_zero tateTorsionPoint_ne_zero map_pointX_tateParam map_pointY_tateParam eq_or_mul_eq_one_of_pointX_eq SymAddHyps nonsingular_point OffLattice AddParams pointX pointY pointX_zpow_mul pointY_zpow_mul symAddHyps_unconditional" namespace TwoTorsionProlongation end TateCurve.TwoTorsionProlongation
p2m_open_scoped "TateCurve" in
set_option maxHeartbeats 6400000 in

theorem TateCurve.TwoTorsionProlongation.exists_primitiveRoot_equiv_torsion_of_eq_two
    (p : ℕ) [Fact p.Prime] (hp : p = 2) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (ζ t : AlgebraicClosure ℚ_[p]), IsPrimitiveRoot ζ p ∧
      t ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT ∧
    ∃ φ : (ZMod p × ZMod p) ≃
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
      (∀ a b, (φ (a + b) : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              = (φ a : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              + (φ b : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)) ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (e c : ℕ),
        σ ζ = ζ ^ e → σ t = ζ ^ c * t →
        ∀ i j : ZMod p, σ • (φ (i, j)) = φ (e • i + c • j, j) := by
  subst hp
  letI : DecidableEq (AlgebraicClosure ℚ_[2]) := Classical.decEq _
  have hp : (2 : ℕ).Prime := Nat.prime_two

  obtain ⟨K, instNF, instUM, instCS, instCZ, instAC, instAlg, hiso, ι, hext⟩ :=
    Padic.exists_complete_algClosed_isometry_algebraicClosure 2
  letI := instNF; letI := instUM; letI := instCS; letI := instCZ; letI := instAC; letI := instAlg
  letI : DecidableEq K := Classical.decEq _

  set qBar := algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) qT with hqBar_def
  have hqBar0 : qBar ≠ 0 :=
    fun h => hqT0 <| (algebraMap ℚ_[2] _).injective (h.trans (map_zero _).symm)
  haveI : NeZero ((2 : ℕ) : AlgebraicClosure ℚ_[2]) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζroot⟩ := IsAlgClosed.exists_root
    (Polynomial.cyclotomic 2 (AlgebraicClosure ℚ_[2]))
    (Polynomial.degree_cyclotomic_pos 2 _ hp.pos).ne'
  have hζ : IsPrimitiveRoot ζ 2 := Polynomial.isRoot_cyclotomic_iff.mp hζroot
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq qBar (n := 2) hp.pos
  refine ⟨ζ, t, hζ, ht, ?_⟩

  set q_K := algebraMap ℚ_[2] K qT with hq_K_def
  have hq_K0 : q_K ≠ 0 :=
    fun h => hqT0 <| (algebraMap ℚ_[2] K).injective (h.trans (map_zero _).symm)
  have hq_K1 : ‖q_K‖₊ < 1 := by
    have h : ‖q_K‖ < 1 := by rw [hq_K_def, hiso]; exact_mod_cast hqT1
    exact_mod_cast h
  have hιinj : Function.Injective ι := RingHom.injective ι.toRingHom
  set ζ_K := ι ζ with hζ_K_def
  set t_K := ι t with ht_K_def
  have hζ_K : IsPrimitiveRoot ζ_K 2 := hζ.map_of_injective hιinj
  have ht_K : t_K ^ 2 = q_K := by
    rw [ht_K_def, ← map_pow, ht, hqBar_def, hq_K_def]; exact ι.commutes qT
  have hζ_K0 : ζ_K ≠ 0 := hζ_K.ne_zero (by omega)
  have ht_K0 : t_K ≠ 0 := fun h0 => hq_K0 (by rw [← ht_K, h0, zero_pow hp.ne_zero])

  obtain ⟨hcurve_eq, hbij⟩ :=
    torsionBy_baseChange_bijective 2 (n := 2) two_ne_zero qT hqT0 hqT1 K hiso ι
  have hcurve_eq' : ((TateCurve.curve qT)⁄K : WeierstrassCurve K) = TateCurve.curve q_K :=
    hcurve_eq
  let br₁Fwd : Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point
                (2 : ℕ) →+
               Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄K).Point (2 : ℕ) :=
    { toFun := fun P =>
        ⟨Point.map ι (P : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point),
          by
            rw [Submodule.mem_torsionBy_iff, ← AddMonoidHom.map_zsmul,
              (Submodule.mem_torsionBy_iff _ _).mp P.property, AddMonoidHom.map_zero]⟩
      map_zero' := Subtype.ext (AddMonoidHom.map_zero _)
      map_add' := fun P Q => Subtype.ext (AddMonoidHom.map_add _ _ _) }
  let br₁ : Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point
              (2 : ℕ) ≃+
            Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄K).Point (2 : ℕ) :=
    AddEquiv.ofBijective br₁Fwd hbij
  have hbr₁_val : ∀ X,
      (↑(br₁ X) : ((TateCurve.curve qT)⁄K).Point)
        = Point.map ι (↑X : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point) :=
    fun _ => rfl
  let br₂ : ((TateCurve.curve qT)⁄K).n_torsionGen 2 ≃+ (TateCurve.curve q_K).n_torsionGen 2 :=
    torsionByAddEquivOfEq hcurve_eq' 2

  let tte_K := twoTorsionEquiv q_K ζ_K t_K hq_K0 hq_K1 hζ_K ht_K
  let tte_K_add : (ZMod 2 × ZMod 2) ≃+ (TateCurve.curve q_K).n_torsionGen 2 :=
    { tte_K with
      map_add' := fun a b => Subtype.ext <| twoTorsionMap_add hq_K0 hq_K1 hζ_K ht_K a b }

  let φAdd : (ZMod 2 × ZMod 2) ≃+
      Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point (2 : ℕ) :=
    tte_K_add.trans (br₂.symm.trans br₁.symm)

  have hφ_char : ∀ (a b : ZMod 2),
      (Point.map ι ↑(φAdd (a, b)) : ((TateCurve.curve qT)⁄K).Point)
        = hcurve_eq'.symm ▸
          (tateTorsionPoint q_K ζ_K t_K hq_K0 hq_K1 hp hζ_K ht_K a.val b.val
            : (TateCurve.curve q_K).toAffine.Point) := by
    intro a b
    have htte : (↑(tte_K_add (a, b)) : (TateCurve.curve q_K).toAffine.Point)
        = tateTorsionPoint q_K ζ_K t_K hq_K0 hq_K1 hp hζ_K ht_K a.val b.val := rfl
    have h0 : br₁ (φAdd (a, b)) = br₂.symm (tte_K_add (a, b)) := br₁.apply_symm_apply _
    have h1 : (↑(br₁ (φAdd (a, b))) : ((TateCurve.curve qT)⁄K).Point)
        = Point.map ι ↑(φAdd (a, b)) := hbr₁_val (φAdd (a, b))
    have h2 : (↑(br₂.symm (tte_K_add (a, b))) : ((TateCurve.curve qT)⁄K).toAffine.Point)
        = hcurve_eq'.symm ▸ (↑(tte_K_add (a, b)) : (TateCurve.curve q_K).toAffine.Point) :=
      torsionByAddEquivOfEq_symm_apply_val hcurve_eq' 2 _
    rw [← h1, h0, h2, htte]
  refine ⟨φAdd.toEquiv, ?_, ?_⟩
  ·
    intro a b
    rw [show φAdd.toEquiv (a + b) = φAdd (a + b) from rfl, φAdd.map_add]
    exact Submodule.coe_add _ _
  ·
    intro σ e c hσζ hσt i j
    obtain ⟨σK, hσKiso, hext_σ⟩ := hext σ
    have hσKinj : Function.Injective σK := hσKiso.injective
    have hσKq : σK q_K = q_K := by
      rw [hq_K_def, ← ι.commutes qT, hext_σ,
        show σ (algebraMap ℚ_[2] _ qT) = algebraMap ℚ_[2] _ qT from σ.commutes qT]
    have hσKζ : σK ζ_K = ζ_K ^ e := by rw [hζ_K_def, hext_σ, hσζ, map_pow]
    have hσKt : σK t_K = ζ_K ^ c * t_K := by
      rw [ht_K_def, hext_σ, hσt, map_mul, map_pow]
    let σK_alg : K →ₐ[ℚ_[2]] K :=
      { toRingHom := σK
        commutes' := fun r => by
          show σK (algebraMap ℚ_[2] K r) = algebraMap ℚ_[2] K r
          rw [← ι.commutes r, hext_σ, σ.commutes r] }
    have hcomp : (ι : AlgebraicClosure ℚ_[2] →ₐ[ℚ_[2]] K).comp σ.toAlgHom = σK_alg.comp ι :=
      AlgHom.ext fun x => (hext_σ x).symm
    have hfunc : ∀ (P : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point),
        Point.map ι (Point.map σ.toAlgHom P) = Point.map σK_alg (Point.map ι P) := by
      intro P
      calc Point.map ι (Point.map σ.toAlgHom P)
          = Point.map ((ι : AlgebraicClosure ℚ_[2] →ₐ[ℚ_[2]] K).comp σ.toAlgHom) P := by
            cases P <;> rfl
        _ = Point.map (σK_alg.comp ι) P := by rw [hcomp]
        _ = Point.map σK_alg (Point.map ι P) := by cases P <;> rfl
    apply hbij.1
    apply Subtype.ext
    show Point.map ι ((σ • φAdd (i, j) :
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point (2 : ℕ))
        : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point)
        = Point.map ι ((φAdd (e • i + c • j, j) :
            Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point (2 : ℕ))
          : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point)
    have hsmul_val : ((σ • φAdd (i, j) :
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point (2 : ℕ))
        : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point)
        = Point.map σ.toAlgHom
            (φAdd (i, j) : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[2])).Point) := rfl
    rw [hsmul_val, hfunc, hφ_char i j, hφ_char (e • i + c • j) j]
    have hnsmul_val : ∀ (n : ℕ) (x : ZMod 2), (n • x).val = (n * x.val) % 2 := by
      intro n x
      induction n with
      | zero => simp [Nat.zero_mod]
      | succ m ih =>
        rw [succ_nsmul, ZMod.val_add, ih, Nat.succ_mul, Nat.mod_add_mod]
    have hval : (e • i + c • j).val = (e * i.val + c * j.val) % 2 := by
      rw [ZMod.val_add, hnsmul_val e i, hnsmul_val c j, Nat.add_mod_mod, Nat.mod_add_mod]
    rw [hval]
    by_cases hij0 : i.val = 0 ∧ j.val = 0
    · obtain ⟨hi0, hj0⟩ := hij0
      simp only [hi0, hj0, mul_zero, add_zero, Nat.zero_mod, tateTorsionPoint_zero_zero,
        transport_point_zero hcurve_eq', AddMonoidHom.map_zero]
    · have hi_lt : i.val < 2 := i.val_lt
      have hj_lt : j.val < 2 := j.val_lt
      set i₂ := (e * i.val + c * j.val) % 2 with hi₂def
      have hi₂ : i₂ < 2 := Nat.mod_lt _ hp.pos
      have hpe : ¬ 2 ∣ e := by
        intro hdvd
        obtain ⟨k, rfl⟩ := hdvd
        have h1 : ζ_K ^ (2 * k) = 1 := by rw [pow_mul, hζ_K.pow_eq_one, one_pow]
        exact hζ_K.ne_one (by omega) (hσKinj ((hσKζ.trans h1).trans (map_one σK).symm))
      have hij₂ : ¬(i₂ = 0 ∧ j.val = 0) := by
        rintro ⟨h1, h2⟩
        refine hij0 ⟨?_, h2⟩
        rw [hi₂def, h2, mul_zero, add_zero] at h1
        rcases Nat.eq_zero_or_pos i.val with h0 | hpos
        · exact h0
        · exact absurd
            (Nat.le_of_dvd hpos
              ((Nat.Prime.dvd_mul hp).mp (Nat.dvd_of_mod_eq_zero h1) |>.resolve_left hpe))
            (by omega)
      rw [tateTorsionPoint_spec hq_K0 hq_K1 hp hζ_K ht_K hi_lt hj_lt hij0,
          transport_point_some hcurve_eq' _,
          tateTorsionPoint_spec hq_K0 hq_K1 hp hζ_K ht_K hi₂ hj_lt hij₂,
          transport_point_some hcurve_eq' _]
      have hX : σK (pointX q_K (ζ_K ^ i.val * t_K ^ j.val))
          = pointX q_K (ζ_K ^ i₂ * t_K ^ j.val) := by
        rw [map_pointX_tateParam hq_K0 hq_K1 hp hζ_K ht_K σK hσKiso hσKq hσKζ hσKt i.val j.val,
            hi₂def, zeta_pow_mod hζ_K.pow_eq_one (e * i.val + c * j.val)]
      have hY : σK (pointY q_K (ζ_K ^ i.val * t_K ^ j.val))
          = pointY q_K (ζ_K ^ i₂ * t_K ^ j.val) := by
        rw [map_pointY_tateParam hq_K0 hq_K1 hp hζ_K ht_K σK hσKiso hσKq hσKζ hσKt i.val j.val,
            hi₂def, zeta_pow_mod hζ_K.pow_eq_one (e * i.val + c * j.val)]
      have hns_target : ((TateCurve.curve qT)⁄K).toAffine.Nonsingular
          (σK (pointX q_K (ζ_K ^ i.val * t_K ^ j.val)))
          (σK (pointY q_K (ζ_K ^ i.val * t_K ^ j.val))) := by
        rw [hX, hY]
        exact transport_nonsingular hcurve_eq'
          (nonsingular_point hq_K0 hq_K1 (tateParam_ne_zero hζ_K0 ht_K0)
            (tateParam_offLattice hq_K0 hq_K1 hζ_K ht_K hi₂ hj_lt hij₂))
      calc (Point.map σK_alg (Affine.Point.some (pointX q_K (ζ_K ^ i.val * t_K ^ j.val))
              (pointY q_K (ζ_K ^ i.val * t_K ^ j.val)) _)
            : ((TateCurve.curve qT)⁄K).Point)
          = Affine.Point.some (σK (pointX q_K (ζ_K ^ i.val * t_K ^ j.val)))
              (σK (pointY q_K (ζ_K ^ i.val * t_K ^ j.val))) hns_target := rfl
        _ = Affine.Point.some (pointX q_K (ζ_K ^ i₂ * t_K ^ j.val))
              (pointY q_K (ζ_K ^ i₂ * t_K ^ j.val)) _ := ps_congr hX hY hns_target _

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hpr : (p : ℤ) ∣ Padic.valuation qT) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧
      Module.Flat ℤ_[p] H ∧
      Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by
  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
  have hpp := (Fact.out : p.Prime)
  have hpQ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  have hqT0' : (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) qT ≠ 0 :=
    fun h => hqT0 <| by
      have := (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective
      exact this (h.trans (_root_.map_zero _).symm)

  obtain ⟨ζ, t, hζ, ht, φ, hφadd, hφG⟩ :=
    TateCurve.TwoTorsionProlongation.exists_primitiveRoot_equiv_torsion_of_eq_two
      p hp qT hqT0 hqT1
  have ht0 : t ≠ 0 := fun h0 => hqT0' (by rw [← ht, h0, zero_pow hpp.ne_zero])

  obtain ⟨k, hk⟩ := hpr
  set u : ℚ_[p] := qT * (p : ℚ_[p]) ^ (-Padic.valuation qT) with hu_def
  have hpnn : (p : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  have hu : ‖u‖₊ = 1 := by
    have hqT_nn : ‖qT‖₊ = (p : ℝ≥0) ^ (-Padic.valuation qT) := by
      rw [← NNReal.coe_inj, NNReal.coe_zpow]; push_cast
      exact Padic.norm_eq_zpow_neg_valuation hqT0
    have hp_nn : ‖(p : ℚ_[p])‖₊ = (p : ℝ≥0)⁻¹ := by
      rw [← NNReal.coe_inj]; push_cast
      simp
    rw [hu_def, nnnorm_mul, nnnorm_zpow, hqT_nn, hp_nn, inv_zpow, ← zpow_neg,
        ← zpow_add₀ hpnn, neg_neg, neg_add_cancel, zpow_zero]
  set η : AlgebraicClosure ℚ_[p] := t * algebraMap ℚ_[p] _ ((p : ℚ_[p]) ^ (-k)) with hη_def
  have hη : η ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) u := by
    rw [hη_def, mul_pow, ht, ← map_pow, ← zpow_natCast, ← zpow_mul, ← map_mul, hu_def, hk]
    ring_nf

  obtain ⟨H, instCR, instHA, hFin, hFlat, hCocomm, ψ, hψmul, hψG⟩ :=
    PadicInt.exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one p u hu ζ η hζ hη

  refine ⟨H, instCR, instHA, hFin, hFlat, hCocomm, ψ.symm.trans φ, ?_, ?_⟩
  · intro f g
    have hsym : ψ.symm (f * g) = ψ.symm f + ψ.symm g := by
      apply ψ.injective
      rw [hψmul, ψ.apply_symm_apply, ψ.apply_symm_apply, ψ.apply_symm_apply]
    show φ (ψ.symm (f * g)) = φ (ψ.symm f) + φ (ψ.symm g)
    rw [hsym]
    exact Subtype.ext (by rw [Submodule.coe_add]; exact hφadd _ _)
  · intro σ f g hgσ
    have hσζp : (σ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨e, -, hσζ⟩ := hζ.eq_pow_of_pow_eq_one hσζp
    have hσtt : (σ t / t) ^ p = 1 := by
      rw [div_pow, ← map_pow, ht, AlgEquiv.commutes, div_self hqT0']
    obtain ⟨c, -, hσtc⟩ := hζ.eq_pow_of_pow_eq_one hσtt
    have hσt : σ t = ζ ^ c * t := ((eq_div_iff ht0).mp hσtc).symm
    have hση : σ η = ζ ^ c * η := by
      rw [hη_def, map_mul, hσt, AlgEquiv.commutes]; ring
    have hg_eq : g = ψ (e • (ψ.symm f).1 + c • (ψ.symm f).2, (ψ.symm f).2) := by
      have key : g.ofConv = (ψ (e • (ψ.symm f).1 + c • (ψ.symm f).2, (ψ.symm f).2)).ofConv := by
        ext h
        rw [hgσ h, hψG σ e c hσζ.symm hση (ψ.symm f).1 (ψ.symm f).2 h]
        simp only [Prod.mk.eta, ψ.apply_symm_apply]
      exact WithConv.ofConv_injective key
    show φ (ψ.symm g) = σ • (φ (ψ.symm f))
    rw [hg_eq, ψ.symm_apply_apply,
        ← hφG σ e c hσζ.symm hσt (ψ.symm f).1 (ψ.symm f).2]

end S_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_two
end P2MW
export P2MW.S_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_two (solution)
