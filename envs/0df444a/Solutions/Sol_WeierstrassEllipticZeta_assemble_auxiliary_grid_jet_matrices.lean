-- Prove2me | solution 1 for WeierstrassEllipticZeta.assemble_auxiliary_grid_jet_matrices
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T16:43:03.316263+00:00
-- url     : https://prove2.me/submissions/377c212b-8ad2-4c43-a1ed-b29ff786142d

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

private theorem grid_point_regular_and_period
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (A : Fin 3 → ℕ) (v : ℂ) (hv : v ∈ auxiliaryGrid u₁ u₂ ω A) :
    u₁ / 2 ∉ L.lattice ∧ u₁ / 2 + v ∉ L.lattice ∧ u₁ / 2 - v ∉ L.lattice ∧
      (v ∈ L.lattice → ∃ a : ℤ, a.natAbs ≤ A 2 ∧ v = a * ω) := by
  classical
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
  let m : Fin 3 → ℤ := fun i => (t i : ℕ)
  have hz : u₁ / 2 ∉ L.lattice := by
    simpa [integerGridPoint] using h_grid.shifted_regular (fun _ => 0)
  have hneg : integerGridPoint u₁ u₂ ω (fun i => -m i) =
      -integerGridPoint u₁ u₂ ω m := by
    simp only [integerGridPoint, Int.cast_neg]
    ring
  refine ⟨hz, ?_, ?_, ?_⟩
  · simpa only [add_comm] using h_grid.shifted_regular m
  · simpa only [hneg, sub_eq_add_neg, add_comm] using
      h_grid.shifted_regular (fun i => -m i)
  · intro hlattice
    have hm := (h_grid.lattice_iff m).mp hlattice
    refine ⟨m 2, ?_, ?_⟩
    · simp [m, Nat.le_of_lt (t 2).isLt]
    · change integerGridPoint u₁ u₂ ω m = _
      simp [integerGridPoint, hm.1, hm.2]

/-- Assemble the two arithmetic jet constructions over all points of the enlarged
grid, retaining the exact evaluations and a uniform vanishing-kernel equivalence. -/
theorem solution
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) (g : ℤ[X][X]) (d : ℤ[X])
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_coordinates : AuxiliaryNonlatticeCoordinateData L ω u₁ u₂ θ ν)
    (h_nonlattice_bounds : BoundedAuxiliaryNonlatticeJetData L θ ν g)
    (h_period_bounds : BoundedAuxiliaryPeriodJetData L ω (u₁ / 2) θ ν g d) :
    AuxiliaryGridJetMatrixData L ω u₁ u₂ θ ν g d := by
  classical
  obtain ⟨C, hC⟩ := h_coordinates
  refine ⟨C, ?_⟩
  intro K
  obtain ⟨Ap, hAp, hp⟩ := h_period_bounds K
  obtain ⟨An, hAn, hn⟩ := h_nonlattice_bounds K C
  let A := Ap + An
  have hpA : Ap ≤ A := le_add_of_nonneg_right hAn.le
  have hnA : An ≤ A := le_add_of_nonneg_left hAp.le
  refine ⟨A, add_pos hAp hAn, ?_⟩
  filter_upwards [hC, hp, hn, h_parameters 1 (by norm_num)] with N hCN hpN hnN hpar
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let s := auxiliaryS N
  let q := auxiliaryS3 N
  let Γ := auxiliaryGrid u₁ u₂ ω ![s, s, q]
  let Γ₃ := auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q]
  let I := Fin (m + 1) × Fin (l + 1) × Fin (l + 1)
  obtain ⟨Dp, hDp, hsizep, hpR⟩ := hpN
  obtain ⟨Dn, hDn, hsizen, hnR⟩ := hnN
  let D := max Dp Dn
  have hDpD : Dp ≤ D := le_max_left _ _
  have hDnD : Dn ≤ D := le_max_right _ _
  have hep : Real.exp (Ap * N) ≤ Real.exp (A * N) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hpA (Nat.cast_nonneg N))
  have hen : Real.exp (An * N) ≤ Real.exp (A * N) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnA (Nat.cast_nonneg N))
  have hD : (D : ℝ) ≤ A * m := by
    dsimp [D]
    rw [Nat.cast_max]
    exact max_le (hDp.trans (mul_le_mul_of_nonneg_right hpA (Nat.cast_nonneg m)))
      (hDn.trans (mul_le_mul_of_nonneg_right hnA (Nat.cast_nonneg m)))
  have hsize : (m + 1 : ℝ) * (l + 1 : ℝ) ^ 2 * (g.natDegree + 1) * (D + 1) ≤
      Real.exp (A * N) := by
    rcases le_total Dp Dn with h | h
    · simpa only [D, max_eq_right h] using hsizen.trans hen
    · simpa only [D, max_eq_left h] using hsizep.trans hep
  have hgap : 8 * ((m + 1) * Γ.card) ≤ (m + 1) * (l + 1) ^ 2 := by
    have h := hpar.2.2.2.2.2.1
    rw [h_grid.card_shifted_grid] at h
    simpa only [Γ, h_grid.card_grid] using h
  let Q (v : Γ₃) (hv : v.val ∉ L.lattice) :=
    Classical.choice (hCN v.val v.property hv)
  have hpoint : ∀ v : Γ₃, ∃ R : Fin (K * m + 1) → I → ℤ[X][X],
      (∀ n i, (R n i).natDegree < g.natDegree ∧
        (∀ j, ((R n i).coeff j).natDegree ≤ D) ∧
        ((∑ j ∈ (R n i).support, ∑ a ∈ ((R n i).coeff j).support,
          (((R n i).coeff j).coeff a).natAbs) : ℝ) ≤ Real.exp (A * N)) ∧
      (v.val ∈ L.lattice → ∀ n i,
        (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν =
          Polynomial.aeval θ d ^ (7 * (m + 2 * l + n)) *
            iteratedDeriv n (fun w => w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
              weierstrassZeta L w ^ i.2.2.val) (u₁ / 2 + v.val)) ∧
      (∀ (hv : v.val ∉ L.lattice) n i,
        (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν =
          (∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν]
            ((Q v hv).denominator a) ^ nonlatticeJetWeight m l n a) *
              iteratedDeriv n (clearedAdditionMonomial L v.val l i.1 i.2.1 i.2.2) (u₁ / 2)) ∧
      ∀ c : I → ℂ,
        ((∀ n, ∑ i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i = 0) ↔
          ∀ n ≤ K * m, iteratedDeriv n (fun w =>
            ∑ i, c i * w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
              weierstrassZeta L w ^ i.2.2.val) (u₁ / 2 + v.val) = 0) := by
    intro v
    obtain ⟨hz, hzv, hzv', hperiod⟩ := grid_point_regular_and_period L ω u₁ u₂ h_grid
      ![3 * s, 3 * s, 3 * q] v.val v.property
    by_cases hv : v.val ∈ L.lattice
    · obtain ⟨a, ha, hva⟩ := hperiod hv
      obtain ⟨R, hR, hReval, hRker⟩ := hpR a ha
      refine ⟨R, ?_, ?_, ?_, ?_⟩
      · intro n i
        exact ⟨(hR n i).1, fun j => ((hR n i).2.1 j).trans hDpD,
          (hR n i).2.2.trans hep⟩
      · intro _ n i
        simpa only [hva] using hReval n i
      · intro hnv
        exact (hnv hv).elim
      · intro c
        simpa only [hva] using hRker c
    · let P := Q v hv
      obtain ⟨R, hR, heval⟩ := hnR P.numerator P.denominator P.lengthBound
        P.numerator_degree P.denominator_degree P.numerator_length P.denominator_length P.length_le
      obtain ⟨hReval, hRker⟩ := heval v.val (u₁ / 2) hv hz hzv P.evaluation
      refine ⟨R, ?_, ?_, ?_, ?_⟩
      · intro n i
        exact ⟨(hR n i).1, fun j => ((hR n i).2.1 j).trans hDnD,
          (hR n i).2.2.trans hen⟩
      · intro hlattice
        exact (hv hlattice).elim
      · intro _ n i
        exact hReval n i
      · exact hRker hzv' P.denominator_ne_zero
  choose R hR hpEval hnEval hker using hpoint
  exact ⟨D, R, Q, hD, hsize, hgap, hR, hpEval, hnEval, hker⟩

