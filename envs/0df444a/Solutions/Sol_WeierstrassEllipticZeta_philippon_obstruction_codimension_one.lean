-- Prove2me | solution 1 for WeierstrassEllipticZeta.philippon_obstruction_codimension_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T21:37:03.681222+00:00
-- url     : https://prove2.me/submissions/51f9e5a6-7311-4a24-be75-ee0cb5ac23f7

import Theorems.Thm_WeierstrassEllipticZeta_philippon_connected_subgroup_classification
import Theorems.Thm_WeierstrassEllipticZeta_sigma_projective_coordinates_entire
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_chart_flow
import Theorems.Thm_PhilipponMultiplicity_analyticCodimension_le_dimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped BigOperators Topology
open Filter MvPolynomial PhilipponMultiplicity
noncomputable section

namespace WeierstrassEllipticZeta
open PhilipponApplication

private theorem homogeneous_coordinate (j : Fin 7) :
    Bihomogeneous (X j : MvPolynomial (Fin 7) ℂ)
      (if j.val < 2 then 1 else 0) (if j.val < 2 then 0 else 1) := by
  intro d hd
  simp only [support_X, Finset.mem_singleton] at hd
  subst d
  fin_cases j <;> simp

private theorem tangent_top_of_codimension_zero {S : Fin 5 → ℂ → ℂ}
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hzero : analyticCodimension M.A H.carrier = 0) : M.A.tangentKernel H.carrier = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hp : Module.finrank ℂ M.A.ParameterSpace = M.A.parameterDimension := by
    simp [AnalyticSubgroup.ParameterSpace]
  have hle := (M.A.tangentKernel H.carrier).finrank_le
  rw [hp] at hle ⊢
  exact Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp hzero)

private theorem codimension_ne_zero_of_equation_derivative
    {S : Fin 5 → ℂ → ℂ} (M : Model S) (H : AlgebraicSubgroup M.group)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (hQ : Bihomogeneous Q m n)
    (hvan : ∀ g ∈ H.carrier,
      M.group.ambient.eval (M.polynomial Q) (M.group.embedding g) = 0)
    (c : ℂ) (hc : c ≠ 0)
    (hderiv : HasDerivAt (fun z => eval (rawCoordinates S z) Q) c 0) :
    analyticCodimension M.A H.carrier ≠ 0 := by
  intro hzero
  have htop := tangent_top_of_codimension_zero M H hzero
  have hPI : M.polynomial Q ∈ M.group.vanishingIdeal H.carrier := by
    apply Ideal.subset_span
    refine ⟨⟨![m, n], M.homogeneous Q m n hQ⟩, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact hvan g hg
  have hv : M.parameter.symm 1 ∈ M.A.tangentKernel H.carrier := by rw [htop]; trivial
  have hz := (Submodule.mem_iInf _).mp hv ⟨M.polynomial Q, hPI⟩
  change fderiv ℂ (M.A.pullback (M.polynomial Q) 0) 0 (M.parameter.symm 1) = 0 at hz
  have heq : M.A.pullback (M.polynomial Q) 0 =
      (fun z => eval (rawCoordinates S z) Q) ∘ M.parameter := by
    funext t
    simpa only [map_zero, zero_add, Function.comp_apply, Model.polynomial] using M.pullback Q 0 t
  have hdf : HasFDerivAt (fun z => eval (rawCoordinates S z) Q)
      (ContinuousLinearMap.toSpanSingleton ℂ c) (M.parameter (0 : M.A.ParameterSpace)) := by
    convert! hderiv.hasFDerivAt using 1 <;> simp only [map_zero]
  have hd := hdf.comp (0 : M.A.ParameterSpace) M.parameter.hasFDerivAt
  rw [heq, hd.fderiv] at hz
  apply hc
  simpa using hz

private theorem normalized_second_coordinate
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    S 2 0 = -2 := by
  obtain ⟨T, hT, hTv, _, hT0⟩ := sigma_projective_coordinates_entire L D
  have heq : S 2 = T 2 := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (hS 2) (hT 2) (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds L.ω₁_div_two_notMem_lattice]
      with z hz
    rw [hS_value z hz 2, hTv z hz 2]
  rw [heq, hT0]

/-- The connected proper subgroup cases needed in Senthil are transverse to
the actual curve. This avoids the general complex and p-adic Lie-subgroup input. -/
theorem philippon_obstruction_codimension_one
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hH : H.IsConnected) (hproper : H.carrier ≠ Set.univ) :
    analyticCodimension M.A H.carrier = 1 := by
  have hbound := analyticCodimension_le_dimension M.A H
  rw [M.analytic_dimension] at hbound
  have hX1 : Bihomogeneous (X (1 : Fin 7) : MvPolynomial (Fin 7) ℂ) 1 0 :=
    homogeneous_coordinate 1
  have hX2 : Bihomogeneous (X (2 : Fin 7) : MvPolynomial (Fin 7) ℂ) 0 1 :=
    homogeneous_coordinate 2
  have hX3 : Bihomogeneous (X (3 : Fin 7) : MvPolynomial (Fin 7) ℂ) 0 1 :=
    homogeneous_coordinate 3
  have first_case (hvan : ∀ g ∈ H.carrier,
      M.group.ambient.eval (M.polynomial (X 1)) (M.group.embedding g) = 0) :
      analyticCodimension M.A H.carrier ≠ 0 := by
    apply codimension_ne_zero_of_equation_derivative M H (X 1) 1 0 hX1 hvan 1 one_ne_zero
    convert! hasDerivAt_id (0 : ℂ) using 1
    funext z
    simp [rawCoordinates]
  have boundary_case
      (hvan0 : ∀ g ∈ H.carrier,
        M.group.ambient.eval (M.polynomial (X 2)) (M.group.embedding g) = 0)
      (hvan1 : ∀ g ∈ H.carrier,
        M.group.ambient.eval (M.polynomial (X 3)) (M.group.embedding g) = 0) :
      analyticCodimension M.A H.carrier ≠ 0 := by
    have h00 : S 0 0 = 0 := by
      have h := (M.zero_locus (X 2) 0 1 hX2 0).mp
        (hvan0 _ (by rw [map_zero]; exact H.toAddSubgroup.zero_mem))
      simpa [rawCoordinates] using h
    have h10 : S 1 0 = 0 := by
      have h := (M.zero_locus (X 3) 0 1 hX3 0).mp
        (hvan1 _ (by rw [map_zero]; exact H.toAddSubgroup.zero_mem))
      simpa [rawCoordinates] using h
    have h20 := normalized_second_coordinate L D S hS hS_value
    have h2ne : S 2 0 ≠ 0 := by rw [h20]; norm_num
    have hflow := (elliptic_extension_projective_chart_flow L D S hS hS_value).2 0 h2ne
    have hratio : HasDerivAt (fun w => S 1 w / S 2 w) (-(1 / 2 : ℂ)) 0 := by
      simpa [h00] using hflow.2.1
    have hmul := hratio.mul ((hS 2 0 trivial).differentiableAt.hasDerivAt)
    have hderiv : HasDerivAt (S 1) 1 0 := by
      have heq : (fun w => S 1 w / S 2 w * S 2 w) =ᶠ[𝓝 (0 : ℂ)] S 1 := by
        filter_upwards [(hS 2 0 trivial).continuousAt.eventually_ne h2ne] with w hw
        exact div_mul_cancel₀ _ hw
      simpa [h10, h20] using hmul.congr_of_eventuallyEq heq.symm
    apply codimension_ne_zero_of_equation_derivative M H (X 3) 0 1 hX3 hvan1 1 one_ne_zero
    simpa [rawCoordinates] using hderiv
  rcases philippon_connected_subgroup_classification L D S hS hS_value hS_ne M H hH hproper with
    hpoint | hfactor | ⟨ρ, hplane⟩ | ⟨a, b, ρ, hab, hline⟩
  · rw [hpoint]
    exact M.analytic_dimension
  · have hn := first_case ((hfactor (X 1) 1 0 hX1).mpr (by intro p; simp))
    omega
  · have hn := boundary_case
      ((hplane (X 2) 0 1 hX2).mpr (by intro p; simp))
      ((hplane (X 3) 0 1 hX3).mpr (by intro p; simp))
    omega
  · have hn := boundary_case
      ((hline (X 2) 0 1 hX2).mpr (by intro p; simp))
      ((hline (X 3) 0 1 hX3).mpr (by intro p; simp))
    omega

end WeierstrassEllipticZeta


end
set_option autoImplicit false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hH : H.IsConnected) (hproper : H.carrier ≠ Set.univ) :
    analyticCodimension M.A H.carrier = 1 := by
  exact WeierstrassEllipticZeta.philippon_obstruction_codimension_one L D S hS hS_value hS_ne M H hH hproper
#print axioms solution
