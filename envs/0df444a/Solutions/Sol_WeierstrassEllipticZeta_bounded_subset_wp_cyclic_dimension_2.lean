-- Prove2me | solution 2 for WeierstrassEllipticZeta.bounded_subset_wp_cyclic_dimension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T20:55:56.534849+00:00
-- url     : https://prove2.me/submissions/e8c0a625-cd85-4aac-a03b-e91437970acb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_wp_contact_dimension_bound
import Theorems.Thm_WeierstrassEllipticZeta_two_chart_analytic_inputs
import Theorems.Thm_WeierstrassEllipticZeta_frontier_projection_count_iff
import Theorems.Thm_WeierstrassEllipticZeta_linear_analytic_subgroup_degree_profile
import Theorems.Thm_WeierstrassEllipticZeta_linear_analytic_multiplicity_obstruction
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

open TranscendenceTheory

theorem solution (G : Frontier.Geometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, ∀ U : Fin ((G.B (m + 2 * n) - 2) / 3 + 1),
          1 ≤ m → 1 ≤ n → 1 ≤ (U : ℕ) → ∀ X : Finset ℂ,
          0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
            (∀ d ∈ Q.support, d 0 + d 1 = m ∧
              d 2 + d 3 + d 4 + d 5 + d 6 = n) →
            (∀ (c : Fin 2) (z : ℂ), G.S (extensionChartDenominator c) z ≠ 0 →
              let f := fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
                (extensionChartNormalize c Q)
              ∃! k : ℕ, k < G.B (m + 2 * n) ∧
                (z ∈ X + X + X → 3 * (U : ℕ) + 1 ≤ k) ∧
                (∀ j < k, iteratedDeriv j f z = 0) ∧ iteratedDeriv k f z ≠ 0 ∧
                ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
                  f =ᶠ[𝓝 z] (fun w => (w - z) ^ k * g w)) →
            (∀ (c : Fin 2) (k : ℕ),
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
                m + 2 * n + k) →
            Frontier.HasChartCertificates G m n (U : ℕ) X Q →
            ∀ Y : Finset ℂ, Y ⊆ X → 0 ∈ Y →
              Y.card = ⌊(C * (m : ℝ) * (n : ℝ) ^ 2) /
                (((U : ℕ) + 1 : ℕ) : ℝ)⌋₊ + 1 →
              let Z := Y.filter (fun z => z ∉ G.L.lattice)
              let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
                ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
                  (extensionChartCoordinates G.S 0 z.val) (3 * (U : ℕ) + 1)
              let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
              ((2 * Module.finrank ℂ (Algebra.adjoin ℂ ({x} : Set _)) +
                ((U : ℕ) + 1) : ℕ) : ℝ) ≤ C * (n : ℝ) ^ 2 := by
  classical
  let R : ℂ → ProjectiveExtensionChartLocus G.L.g₂ G.L.g₃ :=
    fun z => G.P ((extensionPeriodGraph G.L.lattice G.η).mkQ (z, 0))
  have hR (z : ℂ) : ∃ hv : (fun j : Fin 5 => G.S j z) ≠ 0,
      (R z).val.val = Projectivization.mk ℂ (fun j => G.S j z) hv := by
    have hvec : (fun j : Fin 5 => G.S j z) =
        ![G.S 0 z, G.S 1 z, G.S 2 z, G.S 3 z, G.S 4 z] := by
      funext j
      fin_cases j <;> rfl
    simpa only [zero_mul, add_zero, ← hvec] using G.hP z 0
  have hrep (z : ℂ) : ∃ a : ℂ, a ≠ 0 ∧
      (R z).val.val.rep = fun j => a * G.S j z := by
    obtain ⟨hv, h⟩ := hR z
    rw [h]
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (fun j => G.S j z) hv
    refine ⟨a, a.ne_zero, ?_⟩
    rw [← ha]
    rfl
  have hquad (z : ℂ) : G.S 0 z * G.S 4 z - G.S 2 z * G.S 3 z -
      2 * G.S 1 z ^ 2 = 0 := by
    obtain ⟨a, ha, h⟩ := hrep z
    have hq := (R z).val.property.1
    simp only [extensionQuadric, map_sub, map_mul, map_pow, MvPolynomial.eval_X,
      MvPolynomial.eval_C, h] at hq
    apply (mul_eq_zero.mp (show a ^ 2 *
      (G.S 0 z * G.S 4 z - G.S 2 z * G.S 3 z - 2 * G.S 1 z ^ 2) = 0 by
        linear_combination hq)).resolve_left (pow_ne_zero _ ha)
  have hcover (z : ℂ) : ∃ c : Fin 2,
      G.S (extensionChartDenominator c) z ≠ 0 := by
    obtain ⟨a, ha, h⟩ := hrep z
    rcases (R z).property with hz | hz
    · refine ⟨0, ?_⟩
      change G.S 0 z ≠ 0
      intro hzero
      apply hz
      rw [h]
      simp [hzero]
    · refine ⟨1, ?_⟩
      change G.S 2 z ≠ 0
      intro hzero
      apply hz
      rw [h]
      simp [hzero]
  obtain ⟨C₀, hC₀, hmult⟩ := linear_analytic_multiplicity_obstruction
    G.L G.D G.S G.hS G.hS_value G.hS_ne G.η G.hη
  refine ⟨7 * C₀, by positivity, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hlocal hdegree hcharts Y hYX hY0 hYcard
  have hfinite : ∃ (c : Fin 2) (z : ℂ), G.S (extensionChartDenominator c) z ≠ 0 ∧
      analyticOrderAt (fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
        (extensionChartNormalize c Q)) z ≠ ⊤ := by
    obtain ⟨c, hc⟩ := hcover 0
    obtain ⟨k, hk, _⟩ := hlocal c 0 hc
    refine ⟨c, 0, hc, ?_⟩
    intro htop
    have hj := ((G.hjets.2 c (extensionChartNormalize c Q) (k + 1)).2 0 hc).2.mp
      (show ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
        (fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
          (extensionChartNormalize c Q)) 0 by rw [htop]; exact le_top)
    apply hk.2.2.2.1
    rw [((G.hjets.2 c (extensionChartNormalize c Q) k).2 0 hc).1]
    exact hj k (by omega)
  have hhigh : ∀ z ∈ (X + X + X : Finset ℂ), ∃ c : Fin 2,
      G.S (extensionChartDenominator c) z ≠ 0 ∧
      ((3 * (U : ℕ) + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
        (fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
          (extensionChartNormalize c Q)) z := by
    intro z hz
    obtain ⟨c, hc⟩ := hcover z
    obtain ⟨k, hk, _⟩ := hlocal c z hc
    refine ⟨c, hc, ?_⟩
    apply ((G.hjets.2 c (extensionChartNormalize c Q) (3 * (U : ℕ) + 1)).2 z hc).2.mpr
    intro j hj
    rw [← ((G.hjets.2 c (extensionChartNormalize c Q) j).2 z hc).1]
    exact hk.2.2.1 j (lt_of_lt_of_le hj (hk.2.1 hz))
  obtain ⟨hne, horder⟩ := two_chart_analytic_inputs G.S G.hS hquad Q n
    (3 * (U : ℕ) + 1) (fun d hd => (hQ d hd).2)
    (X + X + X : Finset ℂ) hfinite hhigh
  obtain ⟨V, H, P₀, b, hH, hproper, hvanish, hb, hbound⟩ :=
    hmult m n U hm hn hU Y hY0 Q hQ hne
      (fun z hz => horder z (Finset.add_subset_add
        (Finset.add_subset_add hYX hYX) hYX hz))
  obtain ⟨a, ha, hprofile⟩ := linear_analytic_subgroup_degree_profile
    G.L G.η V H hH P₀ hproper hvanish
  have hsubgroup : Frontier.SubgroupBound G C₀ m n U Y := by
    refine ⟨H, a, b, hprofile, hb, ?_⟩
    rwa [ha (m : ℝ)]
  have hcounts := (frontier_projection_count_iff G C₀ hC₀.le m n U hn Y).mp hsubgroup
  let k : ℕ := (G.L.lattice.mkQ '' (Y : Set ℂ)).ncard
  have hk : 1 ≤ k := by
    dsimp [k]
    rw [← Finset.coe_image, Set.ncard_coe_finset]
    exact Finset.card_pos.mpr ⟨G.L.lattice.mkQ 0, Finset.mem_image.mpr ⟨0, hY0, rfl⟩⟩
  have hbigdiv : (7 * C₀ * (m : ℝ) * (n : ℝ) ^ 2) /
      (((U : ℕ) + 1 : ℕ) : ℝ) < (Y.card : ℝ) := by
    rw [hYcard]
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one
      ((7 * C₀ * (m : ℝ) * (n : ℝ) ^ 2) / (((U : ℕ) + 1 : ℕ) : ℝ))
  have hbig : 7 * C₀ * (m : ℝ) * (n : ℝ) ^ 2 <
      (((U : ℕ) + 1 : ℕ) : ℝ) * Y.card := by
    simpa [mul_comm] using (div_lt_iff₀ (show (0 : ℝ) <
      (((U : ℕ) + 1 : ℕ) : ℝ) by positivity)).mp hbigdiv
  have hperiod : (((U : ℕ) + 1 : ℕ) : ℝ) * k ≤ C₀ * (n : ℝ) ^ 2 := by
    rcases hcounts with hpoint | hperiod
    · have hnonneg : 0 ≤ C₀ * (m : ℝ) * (n : ℝ) ^ 2 := by positivity
      nlinarith
    · exact hperiod
  have hdim := (wp_contact_dimension_bound G Y (3 * (U : ℕ) + 1)).2
  dsimp only at hdim ⊢
  have hbound_nat := hdim.1.trans hdim.2
  have hnum : 2 * Module.finrank ℂ (Algebra.adjoin ℂ
      ({Ideal.Quotient.mk
        (⨅ z : Y.filter (fun z => z ∉ G.L.lattice),
          extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
            (extensionChartCoordinates G.S 0 z.val) (3 * (U : ℕ) + 1))
        (MvPolynomial.X (1 : Fin 4))} : Set _)) + ((U : ℕ) + 1) ≤
      7 * ((U : ℕ) + 1) * k := by
    have hweight : (U : ℕ) + 1 ≤ ((U : ℕ) + 1) * k := by
      simpa using Nat.mul_le_mul_left ((U : ℕ) + 1) hk
    change _ ≤ (3 * (U : ℕ) + 1) * k at hbound_nat
    nlinarith
  have hnum_real := Nat.cast_le (α := ℝ).mpr hnum
  push_cast at hnum_real
  push_cast at hperiod
  push_cast
  nlinarith

