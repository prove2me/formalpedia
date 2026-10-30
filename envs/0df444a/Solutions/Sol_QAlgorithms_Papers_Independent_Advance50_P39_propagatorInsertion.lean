-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P39.propagatorInsertion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:13:09.42048+00:00
-- url     : https://prove2.me/submissions/b9b5b5d2-30bc-44aa-a971-ddbf3fe6172f

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39
noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

theorem s109_pi_eq {n : ℕ} (G : Superoperator n) (u : ℝ) :
    semigroupEvolution G u =
      NormedSpace.exp ((u : ℂ) • LinearMap.toContinuousLinearMap G) := rfl

theorem s109_pi_hasDeriv {n : ℕ} (G : Superoperator n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => semigroupEvolution G u)
      (LinearMap.toContinuousLinearMap G * semigroupEvolution G t) t := by
  have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℂ) (LinearMap.toContinuousLinearMap G) (t : ℂ)
  have hh : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have h2 := HasDerivAt.scomp (F := SiteMatrix n →L[ℂ] SiteMatrix n) t h1 hh
  simp only [one_smul] at h2
  exact h2

theorem s109_pi_mul {n : ℕ} (G : Superoperator n) (a b : ℝ) :
    semigroupEvolution G a * semigroupEvolution G b = semigroupEvolution G (a + b) := by
  rw [s109_pi_eq, s109_pi_eq, s109_pi_eq]
  have hc : Commute ((a : ℂ) • LinearMap.toContinuousLinearMap G)
      ((b : ℂ) • LinearMap.toContinuousLinearMap G) := by
    show _ * _ = _ * _
    ext x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
      smul_smul, mul_comm]
  have hab : ((a + b : ℝ) : ℂ) • LinearMap.toContinuousLinearMap G =
      (a : ℂ) • LinearMap.toContinuousLinearMap G + (b : ℂ) • LinearMap.toContinuousLinearMap G := by
    ext x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, Complex.ofReal_add,
      add_smul]
  rw [hab]
  have hr := NormedSpace.expSeries_radius_eq_top ℂ (SiteMatrix n →L[ℂ] SiteMatrix n)
  exact (NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
    (𝔸 := SiteMatrix n →L[ℂ] SiteMatrix n) hc
    (hr.symm ▸ edist_lt_top _ _) (hr.symm ▸ edist_lt_top _ _)).symm

theorem s109_pi_comm {n : ℕ} (G : Superoperator n) (u : ℝ) :
    LinearMap.toContinuousLinearMap G * semigroupEvolution G u =
      semigroupEvolution G u * LinearMap.toContinuousLinearMap G := by
  rw [s109_pi_eq]
  have hc : Commute (LinearMap.toContinuousLinearMap G)
      ((u : ℂ) • LinearMap.toContinuousLinearMap G) := by
    show _ * _ = _ * _
    ext x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul]
  exact hc.exp_right.eq

theorem s109_pi_cont {n : ℕ} (G : Superoperator n) :
    Continuous (fun u : ℝ => semigroupEvolution G u) :=
  continuous_iff_continuousAt.2 fun t =>
    HasDerivAt.continuousAt (F := SiteMatrix n →L[ℂ] SiteMatrix n) (s109_pi_hasDeriv G t)

theorem s109_pi_deriv {n : ℕ} (G : Superoperator n) (rho0 : SiteMatrix n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => semigroupEvolution G u rho0)
      (G (semigroupEvolution G t rho0)) t := by
  have h2 := s109_pi_hasDeriv G t
  let ev : (SiteMatrix n →L[ℂ] SiteMatrix n) →L[ℝ] SiteMatrix n :=
    (ContinuousLinearMap.apply ℂ (SiteMatrix n) rho0).restrictScalars ℝ
  have h3 := HasFDerivAt.comp_hasDerivAt (F := SiteMatrix n →L[ℂ] SiteMatrix n)
    (E := SiteMatrix n) t ev.hasFDerivAt h2
  exact h3

theorem s109_propagatorInsertion {n r : ℕ} (D : TransportData n)
    (rho0 : SiteMatrix n) (hstate : QAlgorithms.IsDensityMatrix rho0)
    (parts : Fin r → Superoperator n) (hparts : ∑ k, parts k = transportGenerator D)
    (t : ℝ) (ht : 0 < t) :
    (∀ k, IntervalIntegrable
      (fun s => insertionIntegrand (transportGenerator D) (parts k) rho0 t s) volume 0 t) ∧
    HasDerivAt (transportState (transportGenerator D) rho0)
      (∑ k, averagedInsertion (transportGenerator D) (parts k) rho0 t) t ∧
    (∑ k, averagedInsertion (transportGenerator D) (parts k) rho0 t) =
      transportGenerator D (transportState (transportGenerator D) rho0 t) := by
  set G := transportGenerator D with hG
  have hcont : ∀ k, Continuous (fun s => insertionIntegrand G (parts k) rho0 t s) := by
    intro k
    unfold insertionIntegrand
    have hc1 : Continuous (fun s : ℝ => semigroupEvolution G (t - s)) :=
      (s109_pi_cont G).comp (continuous_const.sub continuous_id)
    have hc2 : Continuous (fun s : ℝ => parts k (semigroupEvolution G s rho0)) :=
      (LinearMap.continuous_of_finiteDimensional (parts k)).comp
        ((s109_pi_cont G).clm_apply continuous_const)
    exact hc1.clm_apply hc2
  have hsum : ∀ s, ∑ k, insertionIntegrand G (parts k) rho0 t s =
      G (semigroupEvolution G t rho0) := by
    intro s
    unfold insertionIntegrand
    rw [← map_sum]
    rw [← LinearMap.sum_apply, hparts]
    have e1 : G (semigroupEvolution G s rho0) =
        (LinearMap.toContinuousLinearMap G * semigroupEvolution G s) rho0 := rfl
    rw [e1, s109_pi_comm]
    have e2 : semigroupEvolution G (t - s) ((semigroupEvolution G s *
        LinearMap.toContinuousLinearMap G) rho0) =
        (semigroupEvolution G (t - s) * semigroupEvolution G s *
          LinearMap.toContinuousLinearMap G) rho0 := rfl
    rw [e2, s109_pi_mul, sub_add_cancel, ← s109_pi_comm]
    rfl
  have h3 : (∑ k, averagedInsertion G (parts k) rho0 t) =
      G (transportState G rho0 t) := by
    unfold averagedInsertion
    rw [← Finset.smul_sum, ← intervalIntegral.integral_finsetSum
      (fun k _ => (hcont k).intervalIntegrable 0 t)]
    simp only [hsum, intervalIntegral.integral_const, sub_zero]
    rw [← Complex.coe_smul, smul_smul]
    have : (t : ℂ)⁻¹ * (t : ℂ) = 1 := by
      have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      field_simp
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne']
    simp [transportState]
  refine ⟨fun k => (hcont k).intervalIntegrable 0 t, ?_, h3⟩
  rw [h3]
  exact s109_pi_deriv G rho0 t

end QAlgorithms.Papers.Independent.Advance50.P39

open QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {n r : ℕ} (D : TransportData n)
    (rho0 : SiteMatrix n) (hstate : QAlgorithms.IsDensityMatrix rho0)
    (parts : Fin r → Superoperator n) (hparts : ∑ k, parts k = transportGenerator D)
    (t : ℝ) (ht : 0 < t) :
    (∀ k, IntervalIntegrable
      (fun s => insertionIntegrand (transportGenerator D) (parts k) rho0 t s) volume 0 t) ∧
    HasDerivAt (transportState (transportGenerator D) rho0)
      (∑ k, averagedInsertion (transportGenerator D) (parts k) rho0 t) t ∧
    (∑ k, averagedInsertion (transportGenerator D) (parts k) rho0 t) =
      transportGenerator D (transportState (transportGenerator D) rho0 t) :=
  s109_propagatorInsertion D rho0 hstate parts hparts t ht

end
