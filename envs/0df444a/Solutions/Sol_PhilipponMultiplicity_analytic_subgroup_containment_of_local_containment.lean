-- Prove2me | solution 1 for PhilipponMultiplicity.analytic_subgroup_containment_of_local_containment
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T21:37:03.717981+00:00
-- url     : https://prove2.me/submissions/f91ae86a-1bba-4f65-b5e3-e6ea6cef5758

import Definitions.Def_PhilipponMultiplicity_Analytic
set_option autoImplicit false
open scoped BigOperators Topology
open Filter PhilipponMultiplicity

-- Source: Solutions/PhilipponPowerSeriesBall.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology ENNReal NNReal
open Filter Set
noncomputable section

namespace PhilipponMultiplicity

private theorem norm_scalar_coeff {K : Type*} [NontriviallyNormedField K]
    (p : FormalMultilinearSeries K K K) (n : ℕ) : ‖p.coeff n‖ = ‖p n‖ := by
  change ‖p n (fun _ => 1)‖ = ‖p n‖
  rw [← ContinuousMultilinearMap.norm_mkPiRing (𝕜 := K) (ι := Fin n),
    ContinuousMultilinearMap.mkPiRing_apply_one_eq_self]

/-- The Cauchy product retains the whole common scalar convergence ball. -/
theorem scalar_powerSeries_mul_onBall
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    {f g : K → K} {p q : FormalMultilinearSeries K K K} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 r) (hg : HasFPowerSeriesOnBall g q 0 r) :
    ∃ s : FormalMultilinearSeries K K K,
      HasFPowerSeriesOnBall (fun z => f z * g z) s 0 r := by
  classical
  let c (n : ℕ) := ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, p.coeff kl.1 * q.coeff kl.2
  let s : FormalMultilinearSeries K K K :=
    fun n => ContinuousMultilinearMap.mkPiRing K (Fin n) (c n)
  have hs_norm (n : ℕ) : ‖s n‖ = ‖c n‖ := ContinuousMultilinearMap.norm_mkPiRing _
  have hs_apply (z : K) (n : ℕ) :
      s n (fun _ => z) = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (p kl.1 (fun _ => z)) * (q kl.2 (fun _ => z)) := by
    simp only [s, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const,
      Finset.card_fin, smul_eq_mul, c, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro kl hkl
    have hkl' := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_fin, smul_eq_mul]
    rw [← hkl', pow_add]
    ring
  refine ⟨s, ?_, hf.r_pos, ?_⟩
  · apply ENNReal.le_of_forall_nnreal_lt
    intro t ht
    have hp := p.summable_norm_mul_pow (ht.trans_le hf.r_le)
    have hq := q.summable_norm_mul_pow (ht.trans_le hg.r_le)
    have hb : Summable (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (‖p kl.1‖ * (t : ℝ) ^ kl.1) * (‖q kl.2‖ * (t : ℝ) ^ kl.2)) :=
      summable_sum_mul_antidiagonal_of_summable_mul (A := ℕ) (α := ℝ)
        (f := fun n : ℕ => ‖p n‖ * (t : ℝ) ^ n)
        (g := fun n : ℕ => ‖q n‖ * (t : ℝ) ^ n)
        (hp.mul_of_nonneg hq
          (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg t.coe_nonneg n))
          (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg t.coe_nonneg n)))
    apply s.le_radius_of_summable_norm
    apply hb.of_nonneg_of_le (fun _ => by positivity)
    intro n
    rw [hs_norm]
    calc
      ‖c n‖ * (t : ℝ) ^ n ≤
          (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, ‖p.coeff kl.1 * q.coeff kl.2‖) * (t : ℝ) ^ n := by
        gcongr
        exact norm_sum_le _ _
      _ = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          (‖p kl.1‖ * (t : ℝ) ^ kl.1) * (‖q kl.2‖ * (t : ℝ) ^ kl.2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro kl hkl
        rw [norm_mul, norm_scalar_coeff, norm_scalar_coeff,
          ← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]
        ring
  · intro z hz
    have hp := p.summable_norm_apply (Metric.eball_subset_eball hf.r_le hz)
    have hq := q.summable_norm_apply (Metric.eball_subset_eball hg.r_le hz)
    have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hp hq).of_norm.hasSum
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hp hq,
      (hf.hasSum hz).tsum_eq, (hg.hasSum hz).tsum_eq] at hs
    simpa only [hs_apply] using hs

/-- Polynomial operations on scalar power series do not shrink their common ball. -/
theorem scalar_powerSeries_polynomial_onBall
    {K σ : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    (f : K → σ → K) {r : ℝ≥0∞} (hr : 0 < r)
    (hf : ∀ i, ∃ p : FormalMultilinearSeries K K K,
      HasFPowerSeriesOnBall (fun z => f z i) p 0 r)
    (P : MvPolynomial σ K) :
    ∃ p : FormalMultilinearSeries K K K,
      HasFPowerSeriesOnBall (fun z => MvPolynomial.eval (f z) P) p 0 r := by
  apply P.induction_on
  · intro a
    simp only [MvPolynomial.eval_C]
    exact ⟨_, hasFPowerSeriesOnBall_const.mono hr le_top⟩
  · intro P Q hP hQ
    obtain ⟨p, hp⟩ := hP
    obtain ⟨q, hq⟩ := hQ
    refine ⟨p + q, ?_⟩
    convert hp.add hq using 1
    funext z
    exact map_add (MvPolynomial.eval (f z)) P Q
  · intro P i hP
    obtain ⟨p, hp⟩ := hP
    obtain ⟨q, hq⟩ := hf i
    simpa only [map_mul, MvPolynomial.eval_X] using scalar_powerSeries_mul_onBall hp hq

/-- A polynomial in coordinate series on a ball is determined there by its germ.
The proof restricts to scalar lines, so it also applies over nonarchimedean fields. -/
theorem polynomial_zero_onBall_of_zero_germ
    {K E σ : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E]
    (f : E → σ → K) {r : ℝ≥0∞} (hr : 0 < r)
    (hf : ∀ i, ∃ p : FormalMultilinearSeries K E K,
      HasFPowerSeriesOnBall (fun z => f z i) p 0 r)
    (P : MvPolynomial σ K)
    (hzero : (fun z => MvPolynomial.eval (f z) P) =ᶠ[𝓝 0] 0) :
    ∀ z ∈ Metric.eball (0 : E) r, MvPolynomial.eval (f z) P = 0 := by
  intro z hz
  let u : K →L[K] E := (ContinuousLinearMap.id K K).smulRight z
  have hr' : 0 < r / ‖u‖ₑ := by
    simp only [ENNReal.div_pos_iff, ne_eq, enorm_ne_top, not_false_eq_true, and_true]
    exact ne_of_gt hr
  have hf' (i : σ) : ∃ p : FormalMultilinearSeries K K K,
      HasFPowerSeriesOnBall (fun t => f (u t) i) p 0 (r / ‖u‖ₑ) := by
    obtain ⟨p, hp⟩ := hf i
    have hp' : HasFPowerSeriesOnBall (fun z => f z i) p (u 0) r := by
      simpa only [map_zero] using hp
    exact ⟨p.compContinuousLinearMap u, hp'.compContinuousLinearMap⟩
  obtain ⟨p, hp⟩ := scalar_powerSeries_polynomial_onBall (fun t => f (u t)) hr' hf' P
  have hnear : (fun t => MvPolynomial.eval (f (u t)) P) =ᶠ[𝓝 (0 : K)] 0 := by
    exact hzero.comp_tendsto (by simpa only [map_zero] using u.continuous.tendsto 0)
  have hpzero : p = 0 := hp.hasFPowerSeriesAt.eq_zero_of_eventually hnear
  have h1 : (1 : K) ∈ Metric.eball 0 (r / ‖u‖ₑ) := by
    rw [mem_eball_zero_iff, enorm_one]
    apply (ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.one_ne_top) (Or.inl enorm_ne_top)).mpr
    simpa only [one_mul, u, enorm_eq_nnnorm, ContinuousLinearMap.nnnorm_smulRight_apply,
      ContinuousLinearMap.nnnorm_id, one_mul] using (mem_eball_zero_iff.mp hz)
  have hs := hp.hasSum h1
  rw [hpzero] at hs
  have heq := hs.unique hasSum_zero
  simpa only [zero_add, u, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, one_smul] using heq

end PhilipponMultiplicity

end

-- Source: Solutions/PhilipponProjectiveGeometry.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem vanishingIdeal_antitone {S T : Set M.Point} (h : S ⊆ T) :
    M.vanishingIdeal T ≤ M.vanishingIdeal S := by
  apply Ideal.span_mono
  rintro P ⟨hP, hz⟩
  exact ⟨hP, fun x hx => hz x (h hx)⟩

theorem isClosed_zeroLocus_vanishingIdeal (S : Set M.Point) :
    @IsClosed _ M.zariskiTopology (M.zeroLocus (M.vanishingIdeal S)) := by
  letI := M.zariskiTopology
  have hset : M.zeroLocus (M.vanishingIdeal S) =
      ⋂ P : {P : M.CoordinateRing // (∃ D, M.IsHomogeneous P D) ∧
        ∀ x ∈ S, M.eval P x = 0}, {x | M.eval P.val x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, zeroLocus]
    constructor
    · intro hx P
      exact hx P (Ideal.subset_span P.property)
    · intro hx P hP
      have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
        apply Ideal.span_le.mpr
        intro Q hQ
        exact hx ⟨Q, hQ⟩
      exact hle hP
  rw [hset]
  apply isClosed_iInter
  intro P
  obtain ⟨D, hD⟩ := P.property.1
  exact M.isClosed_zero P.val D hD

/-- The chosen-representative ideal agrees with Zariski closure. -/
theorem zeroLocus_vanishingIdeal_eq_closure (S : Set M.Point) :
    M.zeroLocus (M.vanishingIdeal S) = @closure _ M.zariskiTopology S := by
  letI := M.zariskiTopology
  apply Set.Subset.antisymm
  · intro x hx
    apply M.isTopologicalBasis_basic.mem_closure_iff.mpr
    rintro U ⟨P, D, hP, rfl⟩ hxU
    by_contra hn
    have hPS : ∀ y ∈ S, M.eval P y = 0 := by
      intro y hy
      by_contra hp
      exact hn ⟨y, hp, hy⟩
    exact hxU (hx P (Ideal.subset_span ⟨⟨D, hP⟩, hPS⟩))
  · apply closure_minimal
    · intro x hx P hP
      exact M.eval_eq_zero_of_mem_vanishingIdeal hP hx
    · exact M.isClosed_zeroLocus_vanishingIdeal S

end MultiProjectiveSpace

end PhilipponMultiplicity
end

-- Source: Solutions/PhilipponProjectiveContact.lean

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

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
end

-- Source: Solutions/PhilipponAnalyticContainment.lean

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

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
end

-- Source: Solutions/PhilipponAdditiveSubgroups.lean

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_eq_zero_iff_of_lift
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (p : M.Point)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    MvPolynomial.eval v P = 0 ↔ M.eval P p = 0 := by
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
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K))]
  exact mul_eq_zero.trans (or_iff_right hne)

theorem AlgebraicSubgroup.mem_of_homogeneous_equations
    {K : Type*} [Field K] {G : EmbeddedGroupProduct K}
    (H : AlgebraicSubgroup G) (x : G.Point)
    (hx : ∀ (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
      G.ambient.IsHomogeneous P D →
      (∀ y ∈ H.carrier, G.ambient.eval P (G.embedding y) = 0) →
      G.ambient.eval P (G.embedding x) = 0) : x ∈ H.carrier := by
  letI := G.ambient.zariskiTopology
  letI := G.zariskiTopology
  have hcl : @closure _ G.zariskiTopology H.carrier =
      G.embedding ⁻¹' G.ambient.zeroLocus (G.vanishingIdeal H.carrier) := by
    ext y
    rw [EmbeddedGroupProduct.zariskiTopology, closure_induced,
      ← G.ambient.zeroLocus_vanishingIdeal_eq_closure]
    rfl
  have hclosed : closure H.carrier = H.carrier := H.isClosed.closure_eq
  rw [← hclosed, hcl]
  intro P hP
  have hideal : G.vanishingIdeal H.carrier ≤
      RingHom.ker (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨⟨D, hD⟩, hQ⟩
    exact hx Q D hD (fun y hy => hQ _ ⟨y, hy, rfl⟩)
  exact hideal hP

end PhilipponMultiplicity
end

-- Source: Solutions/PhilipponAnalyticGlobalContainment.lean

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

/-- Vanishing germs of homogeneous equations determine containment of the full
generated subgroup, because the base coordinate series converge on the full ball. -/
theorem AnalyticSubgroup.carrier_subset_of_homogeneous_zero_germs
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hgerm : ∀ (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
      G.ambient.IsHomogeneous P D →
      (∀ x ∈ H.carrier, G.ambient.eval P (G.embedding x) = 0) →
      A.pullback P 0 =ᶠ[𝓝 0] 0) : A.carrier ⊆ H.carrier := by
  change AddSubgroup.closure (Set.range A.map) ≤ H.toAddSubgroup
  apply (AddSubgroup.closure_le H.toAddSubgroup).mpr
  rintro _ ⟨z, rfl⟩
  apply H.mem_of_homogeneous_equations
  intro P D hP hPH
  have hz : z.val ∈ Metric.eball (0 : A.ParameterSpace) (ENNReal.ofReal A.radius) := by
    rw [Metric.eball_ofReal, ← A.domain_eq_ball]
    exact z.property
  have hp := polynomial_zero_onBall_of_zero_germ (A.lift 0)
    (ENNReal.ofReal_pos.mpr A.radius_pos) A.base_series P (hgerm P D hP hPH) z.val hz
  exact (G.ambient.eval_eq_zero_iff_of_lift (G.embedding (A.map z))
    (A.lift 0 z.val) (A.base_represents z) P D hP).mp hp

/-- Local containment of the analytic parametrization extends to its entire
specified convergence ball and then to the subgroup generated by its image. -/
theorem analytic_subgroup_containment_of_local_containment
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hlocal : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ hz : z ∈ A.domain, A.map ⟨z, hz⟩ ∈ H.carrier) :
    A.carrier ⊆ H.carrier := by
  apply A.carrier_subset_of_homogeneous_zero_germs H
  intro P D hP hPH
  have hPI : P ∈ G.vanishingIdeal H.carrier := by
    apply Ideal.subset_span
    refine ⟨⟨D, hP⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hPH x hx
  filter_upwards [hlocal, A.domain_open.mem_nhds A.zero_mem] with z hz hzd
  exact G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
    (Set.mem_image_of_mem G.embedding (hz hzd)) (A.lift 0 z)
    (A.base_represents ⟨z, hzd⟩) hPI

/-- In finite-dimensional parameter space, codimension zero means that every
parameter direction lies in the actual tangent kernel. -/
theorem AnalyticSubgroup.tangentKernel_eq_top_of_codimension_zero
    {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (V : Set G.Point)
    (hzero : analyticCodimension A V = 0) : A.tangentKernel V = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hp : Module.finrank K A.ParameterSpace = A.parameterDimension := by
    simp [AnalyticSubgroup.ParameterSpace]
  have hle := (A.tangentKernel V).finrank_le
  rw [hp] at hle ⊢
  exact Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp hzero)

end PhilipponMultiplicity

end

theorem solution
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hlocal : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ hz : z ∈ A.domain, A.map ⟨z, hz⟩ ∈ H.carrier) :
    A.carrier ⊆ H.carrier := by
  exact PhilipponMultiplicity.analytic_subgroup_containment_of_local_containment K G A H hlocal
#print axioms solution
