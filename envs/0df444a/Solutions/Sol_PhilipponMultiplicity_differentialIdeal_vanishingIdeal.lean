-- Prove2me | solution 1 for PhilipponMultiplicity.differentialIdeal_vanishingIdeal
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T17:48:32.034989+00:00
-- url     : https://prove2.me/submissions/77b8d80a-9be9-4a0f-8409-9615671c55f6

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter MvPolynomial
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

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_block_scale {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → K) (a : M.FactorIndex → K) :
    MvPolynomial.eval (fun j => a j.1 * v j) P = (∏ i, a i ^ D i) * MvPolynomial.eval v P := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i, j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring


end PhilipponMultiplicity

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_lift_eq_zero_of_mem_vanishingIdeal
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    {V : Set M.Point} {p : M.Point} (hp : p ∈ V)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal V) :
    MvPolynomial.eval v P = 0 := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hideal : M.vanishingIdeal V ≤ RingHom.ker (MvPolynomial.eval v) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨⟨D, hD⟩, hz⟩
    change MvPolynomial.eval v Q = 0
    rw [hv', M.eval_block_scale Q D hD (M.coordinate p) (fun i => (a i : K)),
      show MvPolynomial.eval (M.coordinate p) Q = 0
      from hz p hp, mul_zero]
  exact hideal hP


end PhilipponMultiplicity

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem chartDomain_isOpen (b : CoordinateChart G) :
    @IsOpen _ G.zariskiTopology (chartDomain G b) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have h (i : G.FactorIndex) : @IsOpen _ G.zariskiTopology
      {x | (G.embedding x i).rep (b i) ≠ 0} := by
    let v : G.ambient.Variable := ⟨i, b i⟩
    have hh : G.ambient.IsHomogeneous (X v) (Pi.single i 1) := by
      apply (G.ambient.degreePiece_iff _ _).mp
      exact isWeightedHomogeneous_X K _ v
    have ho := G.ambient.isOpen_basic (X v) (Pi.single i 1) hh
    have hp := ho.preimage (continuous_induced_dom :
      @Continuous _ _ G.zariskiTopology G.ambient.zariskiTopology G.embedding)
    simpa [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate, v] using hp
  have heq : chartDomain G b = ⋂ i, {x | (G.embedding x i).rep (b i) ≠ 0} := by
    ext x
    simp [chartDomain]
  rw [heq]
  exact isOpen_iInter_of_finite h

theorem exists_chartDomain (x : G.Point) : ∃ b : CoordinateChart G, x ∈ chartDomain G b := by
  have h (i : G.FactorIndex) : ∃ j, (G.embedding x i).rep j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using (G.embedding x i).rep_nonzero
  choose b hb using h
  exact ⟨b, hb⟩

theorem chartValue_homogeneous (b : CoordinateChart G) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) (x : G.Point) :
    chartValue G b P x =
      (∏ i, ((G.embedding x i).rep (b i))⁻¹ ^ D i) * G.ambient.eval P (G.embedding x) := by
  unfold chartValue
  calc
    _ = MvPolynomial.eval
        (fun v : G.ambient.Variable =>
          ((G.embedding x v.1).rep (b v.1))⁻¹ * (G.embedding x v.1).rep v.2) P := by
      apply congrArg (fun v : G.ambient.Variable → K => MvPolynomial.eval v P)
      funext v
      exact div_eq_inv_mul _ _
    _ = _ := G.ambient.eval_block_scale P D hP (G.ambient.coordinate (G.embedding x))
      (fun i : G.FactorIndex => ((G.embedding x i).rep (b i))⁻¹)

theorem locallyGeneratedIdeal_of_zero_sections (S : Set (LocalSection G))
    (hS : ∀ f ∈ S, ∀ x ∈ f.domain, f.value x = 0) :
    locallyGeneratedIdeal G S = G.vanishingIdeal Set.univ := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨⟨D, hD⟩, hP⟩
    apply Ideal.subset_span
    refine ⟨⟨D, hD⟩, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    obtain ⟨b, U, hU, hx, hsub, n, f, r, hfr, heq⟩ := hP x
    have hz : chartValue G b P x = 0 := by
      rw [heq x hx]
      apply Finset.sum_eq_zero
      intro i _
      rw [hS _ (f i).property x (hfr i x hx).1, mul_zero]
    rw [chartValue_homogeneous b P D hD x] at hz
    exact (mul_eq_zero.mp hz).resolve_left
      (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (inv_ne_zero (hsub hx i))))
  · apply Ideal.span_le.mpr
    rintro P ⟨⟨D, hD⟩, hP⟩
    apply Ideal.subset_span
    refine ⟨⟨D, hD⟩, ?_⟩
    intro x
    obtain ⟨b, hb⟩ := exists_chartDomain x
    refine ⟨b, chartDomain G b, chartDomain_isOpen b, hb, Set.Subset.rfl,
      0, Fin.elim0, Fin.elim0, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro y hy
      rw [chartValue_homogeneous b P D hD y, hP _ ⟨y, Set.mem_univ y, rfl⟩, mul_zero]
      simp

theorem normalizedJet_vanishingIdeal (A : AnalyticSubgroup G) (g : G.Point)
    (P : G.CoordinateRing) (hP : P ∈ G.vanishingIdeal Set.univ)
    (D : G.FactorIndex → ℕ) (hD : G.ambient.IsHomogeneous P D)
    (b : CoordinateChart G) {T : ℕ} (j : JetIndex A.parameterDimension T) (x : G.Point) :
    normalizedJet A g b P j x = 0 := by
  have hz : normalizedPullback A g b P x =ᶠ[𝓝 0] (fun _ => (0 : K)) := by
    filter_upwards [A.lift_represents (g + x)] with z hz
    obtain ⟨hz, hlift⟩ := hz
    have hzero : MvPolynomial.eval (A.lift (g + x) z) P = 0 :=
      G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding (Set.mem_univ _)) _ hlift hP
    unfold normalizedPullback
    calc
      _ = MvPolynomial.eval
          (fun v : G.ambient.Variable =>
            (A.lift (g + x) z ⟨v.1, b v.1⟩)⁻¹ * A.lift (g + x) z v) P := by
        apply congrArg (fun v : G.ambient.Variable → K => MvPolynomial.eval v P)
        funext v
        exact div_eq_inv_mul _ _
      _ = _ := (G.ambient.eval_block_scale P D hD (A.lift (g + x) z)
        (fun i => (A.lift (g + x) z ⟨i, b i⟩)⁻¹)).trans (by rw [hzero, mul_zero])
  unfold normalizedJet
  rw [(hz.iteratedFDeriv K j.order).eq_of_nhds]
  simp

/-- Every intrinsic differential ideal of the group's defining ideal is itself. -/
theorem differentialIdeal_vanishingIdeal (A : AnalyticSubgroup G) (g : G.Point) (T : ℕ) :
    differentialIdeal A g T (G.vanishingIdeal Set.univ) = G.vanishingIdeal Set.univ := by
  apply locallyGeneratedIdeal_of_zero_sections
  rintro f ⟨P, hP, ⟨D, hD⟩, b, j, rfl⟩ x hx
  exact normalizedJet_vanishingIdeal A g P hP D hD b j x

end PhilipponMultiplicity.OperatorSupport

end

theorem solution
    (K : Type*) [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point) (T : ℕ) :
    differentialIdeal A g T (G.vanishingIdeal Set.univ) = G.vanishingIdeal Set.univ := by
  exact OperatorSupport.differentialIdeal_vanishingIdeal A g T
