-- Prove2me | solution 1 for PhilipponMultiplicity.translation_geometry_remarks
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T15:36:48.069586+00:00
-- url     : https://prove2.me/submissions/dfa97d31-2645-43cd-8b9f-fccbc132442f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PhilipponMultiplicity_Support
import Theorems.Thm_PhilipponMultiplicity_differentialIdeal_eq_iterated_jet_sections
import Theorems.Thm_PhilipponMultiplicity_iterated_jet_sections_eq_differentialIdeal
import Theorems.Thm_PhilipponMultiplicity_hilbertDegreeForm_eq_of_extendable_translations
import Theorems.Thm_PhilipponMultiplicity_exists_quadratic_translation_reembedding


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

end MultiProjectiveSpace
end PhilipponMultiplicity
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
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
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [Field K]

theorem homogeneous_span (M : MultiProjectiveSpace K) (S : Set M.CoordinateRing)
    (hS : ∀ P ∈ S, ∃ D, M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (Ideal.span S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hh : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D,hD⟩ := hS P hP
    exact ⟨D,(M.degreePiece_iff P D).mpr hD⟩
  intro P hP D
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP D

end PhilipponMultiplicity.OperatorSupport
end

namespace PhilipponMultiplicity
theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) :=
  OperatorSupport.homogeneous_span M _ (fun _ h => h.1)
end PhilipponMultiplicity



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

namespace PhilipponMultiplicity
private theorem completeSpace_of_isometric_ringEquiv
    {K F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField F]
    [CompleteSpace F] (e : K ≃+* F) (he : Isometry e) : CompleteSpace K :=
  (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem IsPhilipponBaseField.completeSpace {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact completeSpace_of_isometric_ringEquiv e he
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact completeSpace_of_isometric_ringEquiv e he

end PhilipponMultiplicity


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

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

end PhilipponMultiplicity.OperatorSupport
end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K]

/-- The constant parametrization supplies analytic charts without imposing
any extra hypothesis on the algebraic group. -/
def AnalyticSubgroup.trivial (G : EmbeddedGroupProduct K) : AnalyticSubgroup G where
  parameterDimension := 1
  parameterDimension_pos := by decide
  radius := 1
  radius_pos := by norm_num
  domain := Metric.ball 0 1
  domain_eq_ball := rfl
  domain_open := Metric.isOpen_ball
  zero_mem := by simp
  map := fun _ => 0
  map_zero := rfl
  map_add := by intros; exact (zero_add 0).symm
  lift := fun g _ => G.ambient.coordinate (G.embedding g)
  lift_analytic := fun _ _ => analyticAt_const
  base_series := fun _ => ⟨_, hasFPowerSeriesOnBall_const.mono (by simp) le_top⟩
  base_represents := fun _ i => ⟨Projectivization.rep_nonzero (G.embedding 0 i),
    Projectivization.mk_rep (G.embedding 0 i)⟩
  lift_represents := by
    intro g
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (0 : Fin 1 → K) ∈ Metric.ball 0 1 by simp)]
      with z hz
    refine ⟨hz, fun i => ⟨Projectivization.rep_nonzero (G.embedding g i), ?_⟩⟩
    simpa only [add_zero, MultiProjectiveSpace.coordinate] using
      Projectivization.mk_rep (G.embedding g i)

end PhilipponMultiplicity
end

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K]

theorem projective_ratios_eq {ι : Type*} (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk K v hv = Projectivization.mk K w hw) (i j : ι) :
    v i / v j = w i / w j := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp h
  have he (k : ι) : v k = (a : K) * w k := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha k).symm
  rw [he i,he j,mul_div_mul_left _ _ a.ne_zero]

end PhilipponMultiplicity.OperatorSupport


set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem normalizedPullback_zero (g x : G.Point) (b : CoordinateChart G)
    (P : G.CoordinateRing) :
    normalizedPullback A g b P x 0 = chartValue G b P (g+x) := by
  obtain ⟨hz,hrep⟩ := (A.lift_represents (g+x)).self_of_nhds
  unfold normalizedPullback chartValue
  apply congrArg (fun f : G.ambient.Variable → K => MvPolynomial.eval f P)
  funext v
  obtain ⟨hv,he⟩ := hrep v.1
  have he' : Projectivization.mk K (fun j => A.lift (g+x) 0 ⟨v.1,j⟩) hv =
      G.embedding (g+x) v.1 := by simpa only [A.map_zero,add_zero] using he
  exact projective_ratios_eq _ _ hv (G.embedding (g+x) v.1).rep_nonzero
    (he'.trans (G.embedding (g+x) v.1).mk_rep.symm) v.2 (b v.1)

/-- At order zero the intrinsic differential ideal is the actual translated
local ideal, with arbitrary projective representatives normalized away. -/
theorem differentialIdeal_zero_eq_translatedIdeal (g : G.Point)
    (I : Ideal G.CoordinateRing) : differentialIdeal A g 0 I = translatedIdeal G g I := by
  have heq : differentialSections A g 0 I = translationSections G g I := by
    ext f
    constructor
    · rintro ⟨P,hP,hD,b,j,rfl⟩
      rcases j with ⟨k,hk,directions⟩
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      refine ⟨P,hP,hD,b,?_⟩
      congr 1
      funext x
      simp only [normalizedJet,iteratedFDeriv_zero_apply]
      exact normalizedPullback_zero g x b P
    · rintro ⟨P,hP,hD,b,rfl⟩
      refine ⟨P,hP,hD,b,⟨0,le_rfl,Fin.elim0⟩,?_⟩
      congr 1
      funext x
      simp only [normalizedJet,iteratedFDeriv_zero_apply]
      exact (normalizedPullback_zero g x b P).symm
  exact congrArg (locallyGeneratedIdeal G) heq

end PhilipponMultiplicity
end

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
theorem translate_translate (g h : G.Point) (V : Set G.Point) :
    translate g (translate h V) = translate (g+h) V := by
  simp only [translate,Set.image_image,Function.comp_def,add_assoc]

theorem translate_zero (V : Set G.Point) : translate (0 : G.Point) V = V := by
  simp only [translate,zero_add,Set.image_id']

end PhilipponMultiplicity


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.TranslationGeometry
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem locallyGenerated_mono {S T : Set (LocalSection G)} (hST : S ⊆ T)
    {P : G.CoordinateRing} (hP : LocallyGenerated G S P) : LocallyGenerated G T P := by
  intro x
  obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := hP x
  exact ⟨b,U,hU,hx,hUb,n,fun i => ⟨(f i).val,hST (f i).property⟩,r,hfr,heq⟩

theorem translatedIdeal_mono (g : G.Point) {I J : Ideal G.CoordinateRing} (hIJ : I ≤ J) :
    translatedIdeal G g I ≤ translatedIdeal G g J := by
  apply Ideal.span_mono
  rintro P ⟨hP,hlocal⟩
  refine ⟨hP,locallyGenerated_mono ?_ hlocal⟩
  rintro f ⟨Q,hQ,hD,b,rfl⟩
  exact ⟨Q,hIJ hQ,hD,b,rfl⟩

/-- Every locally generated translated equation vanishes at the translated set. -/
theorem translatedIdeal_le_vanishingIdeal (V : Set G.Point) (g : G.Point) :
    translatedIdeal G g (G.vanishingIdeal V) ≤ G.vanishingIdeal (translate (-g) V) := by
  classical
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  apply Ideal.subset_span
  refine ⟨⟨D,hD⟩,?_⟩
  rintro _ ⟨x,⟨y,hy,hxy⟩,rfl⟩
  have htrans : g+x = y := by rw [← hxy]; exact add_neg_cancel_left g y
  obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := hP x
  have hz : chartValue G b P x = 0 := by
    rw [heq x hx]
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨Q,hQ,⟨E,hE⟩,b',hf⟩ := (f i).property
    have hval : (f i).val.value x = 0 := by
      rw [hf]
      change chartValue G b' Q (g+x) = 0
      rw [chartValue_homogeneous b' Q E hE (g+x),htrans]
      rw [G.ambient.eval_eq_zero_of_mem_vanishingIdeal hQ ⟨y,hy,rfl⟩,mul_zero]
    rw [hval,mul_zero]
  rw [chartValue_homogeneous b P D hD x] at hz
  exact (mul_eq_zero.mp hz).resolve_left
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (inv_ne_zero (hUb hx i))))

/-- Translation by zero contains the original homogeneous equations. -/
theorem vanishingIdeal_le_translatedIdeal_zero (V : Set G.Point) :
    G.vanishingIdeal V ≤ translatedIdeal G 0 (G.vanishingIdeal V) := by
  classical
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hz⟩
  have hPI : P ∈ G.vanishingIdeal V := Ideal.subset_span ⟨⟨D,hD⟩,hz⟩
  apply Ideal.subset_span
  refine ⟨⟨D,hD⟩,?_⟩
  intro x
  obtain ⟨b,hb⟩ := exists_chartDomain x
  let f : translationSections G 0 (G.vanishingIdeal V) :=
    ⟨⟨chartDomain G b,chartValue G b P⟩,P,hPI,⟨D,hD⟩,b,by simp⟩
  let r : RationalCoefficient G :=
    ⟨1,1,0,G.ambient.isHomogeneous_one,G.ambient.isHomogeneous_one⟩
  refine ⟨b,chartDomain G b,chartDomain_isOpen b,hb,Set.Subset.rfl,1,
    fun _ => f,fun _ => r,?_,?_⟩
  · intro i y hy
    exact ⟨hy,by simp [r,MultiProjectiveSpace.eval]⟩
  · intro y hy
    simp [r,f,RationalCoefficient.value,MultiProjectiveSpace.eval]

theorem translatedIdeal_zero_vanishingIdeal (V : Set G.Point) :
    translatedIdeal G 0 (G.vanishingIdeal V) = G.vanishingIdeal V := by
  apply le_antisymm ?_ (vanishingIdeal_le_translatedIdeal_zero V)
  simpa [translate] using translatedIdeal_le_vanishingIdeal V (0 : G.Point)

/-- The inverse translation upgrades pointwise containment to exact equality
of defining ideals, for arbitrary subsets of the group. -/
theorem ideal_transport_of_composition
    (hcomp : ∀ (g h : G.Point) (I : Ideal G.CoordinateRing),
      IsMultihomogeneousIdeal G.ambient I →
      translatedIdeal G g (translatedIdeal G h I) = translatedIdeal G (g+h) I)
    (V : Set G.Point) (g : G.Point) :
    translatedIdeal G g (G.vanishingIdeal V) = G.vanishingIdeal (translate (-g) V) := by
  apply le_antisymm (translatedIdeal_le_vanishingIdeal V g)
  have hinv : translatedIdeal G (-g) (G.vanishingIdeal (translate (-g) V)) ≤
      G.vanishingIdeal V := by
    have h := translatedIdeal_le_vanishingIdeal (translate (-g) V) (-g)
    simpa only [neg_neg,translate_translate,add_neg_cancel,translate_zero] using h
  have h := translatedIdeal_mono g hinv
  rw [hcomp g (-g) (G.vanishingIdeal (translate (-g) V))
    (vanishingIdeal_multihomogeneous K G.ambient (G.embedding '' translate (-g) V)),add_neg_cancel,
    translatedIdeal_zero_vanishingIdeal] at h
  exact h

theorem ideal_transport
    (hK : IsPhilipponBaseField K) (V : Set G.Point) (g : G.Point) :
    translatedIdeal G g (G.vanishingIdeal V) = G.vanishingIdeal (translate (-g) V) := by
  letI : CompleteSpace K := hK.completeSpace
  apply ideal_transport_of_composition ?_ V g
  intro a b I hI
  let A := AnalyticSubgroup.trivial G
  rw [← differentialIdeal_zero_eq_translatedIdeal (A := A) b,
    ← differentialIdeal_zero_eq_translatedIdeal (A := A) a,
    PhilipponMultiplicity.differentialIdeal_eq_iterated_jet_sections K hK G A a b 0 0 I hI,
    PhilipponMultiplicity.iterated_jet_sections_eq_differentialIdeal K G A a b 0 0 I,
    Nat.zero_add, differentialIdeal_zero_eq_translatedIdeal]
end PhilipponMultiplicity.TranslationGeometry
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    (∀ (G : EmbeddedGroupProduct K) (V : GroupSubvariety G) (g : G.Point),
      translatedIdeal G g (G.vanishingIdeal V.carrier) =
        G.vanishingIdeal (PhilipponMultiplicity.translate (-g) V.carrier)) ∧
    (∀ (G : EmbeddedGroupProduct K), @_root_.IsConnected _ G.zariskiTopology Set.univ →
      TranslationsExtendToClosure G →
      ∀ (V : GroupSubvariety G) (g : G.Point) (D : G.FactorIndex → ℕ),
        (∀ i, 1 ≤ D i) →
        hilbertDegreeForm G V.carrier D = hilbertDegreeForm G (PhilipponMultiplicity.translate g V.carrier) D) ∧
    (∀ E : EmbeddedCommutativeGroup K,
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ (A : AnalyticSubgroup (singleGroupProduct F)) (g : (singleGroupProduct F).Point),
          ∃ atlas : TranslationAtlas A g, atlas.IsBoundedBy (fun _ => 2)) := by
  exact ⟨fun G V g => TranslationGeometry.ideal_transport hK V.carrier g,
    hilbertDegreeForm_eq_of_extendable_translations K hK,
    exists_quadratic_translation_reembedding K hK⟩
