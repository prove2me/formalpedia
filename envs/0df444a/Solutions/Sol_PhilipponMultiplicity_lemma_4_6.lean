-- Prove2me | solution 1 for PhilipponMultiplicity.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T14:03:11.358358+00:00
-- url     : https://prove2.me/submissions/6d93c7df-44ec-43af-bdac-2fe3f4df30a4

import Definitions.Def_PhilipponMultiplicity_SectionFour

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set MvPolynomial TopologicalSpace Filter
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

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

end PhilipponMultiplicity.MultiProjectiveSpace

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

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.nat_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : ℕ) : M.IsHomogeneous (c * P) D := by
  simpa only [map_natCast] using hP.C_mul M (c : K)

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

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
universe u
variable {K : Type u} [Field K]

theorem isHomogeneous_zero (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) :
    M.IsHomogeneous 0 D := by simp [IsHomogeneous]

theorem isHomogeneous_sum (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) D) :
    M.IsHomogeneous (∑ i ∈ s, P i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_zero D
  | @insert i s hi ih =>
    simp only [Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).add M (ih (fun j hj => hP j (by simp [hj])))

theorem isHomogeneous_prod (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : ι → M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) (D i)) :
    M.IsHomogeneous (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_one
  | @insert i s hi ih =>
    simp only [Finset.prod_insert, Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).mul M (ih (fun j hj => hP j (by simp [hj])))

/-- Substituting tuples homogeneous in each source block preserves
multihomogeneity, with the expected linear transformation of degrees. -/
theorem IsHomogeneous.eval₂_blocks (M N : MultiProjectiveSpace K)
    {Q : N.CoordinateRing} {D : N.FactorIndex → ℕ} (hQ : N.IsHomogeneous Q D)
    (P : N.Variable → M.CoordinateRing) (E : N.FactorIndex → M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) (E j.1)) :
    M.IsHomogeneous (eval₂ C P Q) (fun i => ∑ b, D b * E b i) := by
  classical
  rw [eval₂_eq']
  apply M.isHomogeneous_sum
  intro d hd
  have hh := M.isHomogeneous_prod Finset.univ (fun j => P j ^ d j)
    (fun j i => d j * E j.1 i) (fun j _ => (hP j).pow M (d j))
  have he : (∑ j : N.Variable, fun i => d j * E j.1 i) =
      (fun i => ∑ b, D b * E b i) := by
    funext i
    simp only [Finset.sum_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ y, d ⟨b, y⟩ * E b i) = D b * E b i
    rw [← Finset.sum_mul, hQ d hd b]
  rw [he] at hh
  exact hh.C_mul M _

/-- Two projective lifts represent the same point precisely when all their
two-by-two cross products vanish. -/
theorem projectivization_mk_eq_iff_cross {ι : Type*}
    (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw ↔
      ∀ j k, v j * w k = v k * w j := by
  classical
  constructor
  · intro heq
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K v w hv hw).mp heq
    intro j k
    rw [← ha]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
    change w k ≠ 0 at hk
    apply (Projectivization.mk_eq_mk_iff' K v w hv hw).mpr
    refine ⟨v k / w k, ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    exact h k j

/-- Regular maps into a multiprojective space have a closed equalizer, even
though the Zariski topology on the target is not Hausdorff. -/
theorem IsRegularAlong.isClosed_equalizer
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g) :
    @IsClosed X (TopologicalSpace.induced e M.zariskiTopology) {x | f x = g x} := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hx
  obtain ⟨U, hU, hxU, D, P, hP, hflift⟩ := hf x b
  obtain ⟨V, hV, hxV, E, Q, hQ, hglift⟩ := hg x b
  obtain ⟨hp, hpx⟩ := hflift x hxU
  obtain ⟨hq, hqx⟩ := hglift x hxV
  have hcross : ∃ j k, M.eval (P j * Q k - P k * Q j) (e x) ≠ 0 := by
    by_contra! hn
    apply hb
    rw [← hpx, ← hqx, projectivization_mk_eq_iff_cross]
    intro j k
    simpa only [eval, map_sub, map_mul, sub_eq_zero] using hn j k
  obtain ⟨j, k, hjk⟩ := hcross
  have hhom := ((hP j).mul M (hQ k)).sub M ((hP k).mul M (hQ j))
  let W := U ∩ V ∩ {p | M.eval (P j * Q k - P k * Q j) p ≠ 0}
  have hopen : IsOpen (e ⁻¹' W) :=
    ((hU.inter hV).inter (M.isOpen_basic _ _ hhom)).preimage continuous_induced_dom
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨hxU, hxV⟩, hjk⟩) ?_
  intro y hy heq
  obtain ⟨hpy, hpy'⟩ := hflift y hy.1.1
  obtain ⟨hqy, hqy'⟩ := hglift y hy.1.2
  have hmk := hpy'.trans ((congrFun heq b).trans hqy'.symm)
  have hz := (projectivization_mk_eq_iff_cross _ _ hpy hqy).mp hmk j k
  exact hy.2 (by simpa only [eval, map_sub, map_mul, sub_eq_zero] using hz)

theorem IsRegularAlong.eq_of_dense
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g)
    (A : Set X) (hA : @Dense X (TopologicalSpace.induced e M.zariskiTopology) A)
    (hfg : Set.EqOn f g A) : f = g := by
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  have hh : closure A ⊆ {x | f x = g x} :=
    closure_minimal hfg (hf.isClosed_equalizer M N hg)
  funext x
  exact hh (hA x)

/-- Regular maps are continuous for the actual polynomial Zariski topologies. -/
theorem IsRegularAlong.continuous
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) :
    @Continuous X N.Point (TopologicalSpace.induced e M.zariskiTopology)
      N.zariskiTopology f := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨R, D, hR, rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  choose U hU hxU E P hP hlift using hf x
  let pull := eval₂ C (fun j : N.Variable => P j.1 j.2) R
  have hpull : M.IsHomogeneous pull (fun i => ∑ b, D b * E b i) :=
    hR.eval₂_blocks M N _ E (fun j => hP j.1 j.2)
  have heval (y : X) : M.eval pull (e y) =
      MvPolynomial.eval (fun j : N.Variable => M.eval (P j.1 j.2) (e y)) R := by
    dsimp only [eval, pull]
    rw [← eval_assoc]
    rfl
  have hiff (y : X) (hy : ∀ b, e y ∈ U b) :
      M.eval pull (e y) = 0 ↔ N.eval R (f y) = 0 := by
    rw [heval]
    exact N.eval_eq_zero_iff_of_lift (f y) _ (fun b => hlift b y (hy b)) R D hR
  let W : Set M.Point := (⋂ b, U b) ∩ {p | M.eval pull p ≠ 0}
  have hW : IsOpen (e ⁻¹' W) :=
    ((isOpen_iInter_of_finite hU).inter (M.isOpen_basic _ _ hpull)).preimage
      continuous_induced_dom
  have hxW : x ∈ e ⁻¹' W := ⟨Set.mem_iInter.mpr hxU, (hiff x hxU).not.mpr hx⟩
  refine Filter.mem_of_superset (hW.mem_nhds hxW) ?_
  intro y hy
  exact (hiff y (Set.mem_iInter.mp hy.1)).not.mp hy.2

theorem IsRegularAlong.comp_domain
    {X Y : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) (g : Y → X) :
    M.IsRegularAlong N (e ∘ g) (f ∘ g) := by
  intro y b
  obtain ⟨U, hU, hy, D, P, hP, hl⟩ := hf (g y) b
  exact ⟨U, hU, hy, D, P, hP, fun z hz => hl (g z) hz⟩

end PhilipponMultiplicity.MultiProjectiveSpace
namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K] {n : ℕ}

def projectiveLeftSlice (a : Projectivization K (Fin (n + 1) → K))
    (p : (projectiveSpace K n).Point) : (projectiveSquare K n).Point :=
  fun b => if b.val = 0 then p (0 : Fin 1) else a

def projectiveLeftSlicePolynomial (a : Projectivization K (Fin (n + 1) → K))
    (v : (projectiveSquare K n).Variable) : (projectiveSpace K n).CoordinateRing :=
  if v.1.val = 0 then X ⟨(0 : Fin 1), v.2⟩ else C (a.rep v.2)

theorem projectiveLeftSlicePolynomial_homogeneous
    (a : Projectivization K (Fin (n + 1) → K)) (v : (projectiveSquare K n).Variable) :
    (projectiveSpace K n).IsHomogeneous (projectiveLeftSlicePolynomial a v)
      (fun _ => if v.1.val = 0 then 1 else 0) := by
  classical
  by_cases hv : v.1.val = 0
  · simp only [projectiveLeftSlicePolynomial, if_pos hv]
    convert (projectiveSpace K n).isHomogeneous_X ⟨(0 : Fin 1), v.2⟩ using 1
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    simp [hi]
  · simpa only [projectiveLeftSlicePolynomial, if_neg hv] using!
      (projectiveSpace K n).isHomogeneous_C (a.rep v.2)

theorem projectiveLeftSlice_eval (a : Projectivization K (Fin (n + 1) → K))
    (P : (projectiveSquare K n).CoordinateRing) (p : (projectiveSpace K n).Point) :
    (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p =
      (projectiveSquare K n).eval P (projectiveLeftSlice a p) := by
  dsimp only [MultiProjectiveSpace.eval]
  rw [← eval_assoc]
  apply congrArg (fun v => MvPolynomial.eval v P)
  funext v
  by_cases hv : v.1.val = 0 <;>
    simp [projectiveLeftSlicePolynomial, projectiveLeftSlice,
      MultiProjectiveSpace.coordinate, hv]

theorem projectiveLeftSlice_continuous (a : Projectivization K (Fin (n + 1) → K)) :
    @Continuous _ _ (projectiveSpace K n).zariskiTopology
      (projectiveSquare K n).zariskiTopology (projectiveLeftSlice a) := by
  classical
  let := (projectiveSpace K n).zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have heq : projectiveLeftSlice a ⁻¹' {p | (projectiveSquare K n).eval P p ≠ 0} =
      {p | (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p ≠ 0} := by
    ext p
    change (projectiveSquare K n).eval P (projectiveLeftSlice a p) ≠ 0 ↔
      (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p ≠ 0
    rw [projectiveLeftSlice_eval]
  rw [heq]
  apply (projectiveSpace K n).isOpen_basic
  exact hP.eval₂_blocks _ _ _ (fun b _ => if b.val = 0 then 1 else 0)
    (projectiveLeftSlicePolynomial_homogeneous a)

/-- Fixing one projective argument of a regular map gives a regular map. -/
theorem MultiProjectiveSpace.IsRegularAlong.of_left_slice
    {X : Type u} (N : MultiProjectiveSpace K)
    (a : Projectivization K (Fin (n + 1) → K))
    {e : X → (projectiveSpace K n).Point} {f : X → N.Point}
    (hf : (projectiveSquare K n).IsRegularAlong N (projectiveLeftSlice a ∘ e) f) :
    (projectiveSpace K n).IsRegularAlong N e f := by
  classical
  let := (projectiveSpace K n).zariskiTopology
  let := (projectiveSquare K n).zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hlift⟩ := hf x b
  refine ⟨projectiveLeftSlice a ⁻¹' U, hU.preimage (projectiveLeftSlice_continuous a),
    hxU, (fun i => ∑ c, D c * (if c.val = 0 then 1 else 0)),
    (fun j => eval₂ C (projectiveLeftSlicePolynomial a) (P j)), ?_, ?_⟩
  · intro j
    exact (hP j).eval₂_blocks _ _ _ (fun c _ => if c.val = 0 then 1 else 0)
      (projectiveLeftSlicePolynomial_homogeneous a)
  · intro y hy
    obtain ⟨hn, heq⟩ := hlift y hy
    simpa only [projectiveLeftSlice_eval, Function.comp_apply] using ⟨hn, heq⟩

/-- The regular group law supplies regular translations. -/
theorem EmbeddedCommutativeGroup.translation_regular
    (G : EmbeddedCommutativeGroup K) (a : G.Point) :
    (projectiveSpace K G.ambientDimension).IsRegularAlong
      (projectiveSpace K G.ambientDimension)
      (fun x : G.Point => fun _ => x.val)
      (fun x => fun _ => (x + a).val) := by
  apply MultiProjectiveSpace.IsRegularAlong.of_left_slice _ a.val
  exact G.addition_regular.comp_domain (fun x : G.Point => (x, a))

end PhilipponMultiplicity
namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem homogeneous_tuple_lift {ι : Type*} (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) D)
    (hn : (fun j => M.eval (P j) p) ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (P j)) h =
        Projectivization.mk K (fun j => M.eval (P j) p) hn := by
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
  let b : K := ∏ i, (a i : K) ^ D i
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (a i).ne_zero)
  have heval : (fun j => MvPolynomial.eval v (P j)) = b • (fun j => M.eval (P j) p) := by
    funext j
    rw [hv', M.eval_block_scale (P j) D (hP j) (M.coordinate p) (fun i => (a i : K))]
    rfl
  have hn' : (fun j => MvPolynomial.eval v (P j)) ≠ 0 := by
    rw [heval]
    exact smul_ne_zero hb hn
  exact ⟨hn', (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨b, heval.symm⟩⟩

/-- Composition of regular maps, including maps given along arbitrary embedded domains. -/
theorem IsRegularAlong.comp {X : Type u} {M N Q : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} {g : X → Q.Point}
    (hf : M.IsRegularAlong N e f) (hg : N.IsRegularAlong Q f g) :
    M.IsRegularAlong Q e g := by
  classical
  let := M.zariskiTopology
  let := N.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hPlift⟩ := hg x b
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp (hU.preimage hf.continuous)
  choose W hW hxW E R hR hRlift using hf x
  let pull (j : Fin (Q.ambientDimension b + 1)) :=
    eval₂ C (fun t : N.Variable => R t.1 t.2) (P j)
  refine ⟨V ∩ ⋂ a, W a, hV.inter (isOpen_iInter_of_finite hW),
    ⟨?_, mem_iInter.mpr hxW⟩, (fun i => ∑ a, D a * E a i), pull, ?_, ?_⟩
  · have hx : x ∈ f ⁻¹' U := hxU
    rwa [← hVeq] at hx
  · intro j
    exact (hP j).eval₂_blocks M N _ E (fun t => hR t.1 t.2)
  · intro y hy
    have hyU : f y ∈ U := by
      change y ∈ f ⁻¹' U
      rw [← hVeq]
      exact hy.1
    obtain ⟨hn, heq⟩ := hPlift y hyU
    have hlift (a : N.FactorIndex) := hRlift a y (mem_iInter.mp hy.2 a)
    obtain ⟨hn', heq'⟩ := N.homogeneous_tuple_lift (f y)
      (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) hlift P D hP hn
    have heval (j) : M.eval (pull j) (e y) =
        MvPolynomial.eval (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) (P j) := by
      dsimp only [eval, pull]
      rw [← eval_assoc]
      rfl
    simpa only [heval] using ⟨hn', heq'.trans heq⟩

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

theorem MultiProjectiveSpace.projection_regular (M : MultiProjectiveSpace K)
    (i : M.FactorIndex) :
    M.IsRegularAlong (projectiveSpace K (M.ambientDimension i)) id (fun p _ => p i) := by
  let := M.zariskiTopology
  intro x b
  refine ⟨univ, isOpen_univ, mem_univ _, (fun a => if a = i then 1 else 0),
    (fun j => X ⟨i, j⟩), (fun j => M.isHomogeneous_X ⟨i, j⟩), ?_⟩
  intro y _
  simp only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate, id_eq]
  exact ⟨Projectivization.rep_nonzero (y i), Projectivization.mk_rep (y i)⟩

theorem EmbeddedGroupProduct.translation_regular (G : EmbeddedGroupProduct K) (a : G.Point) :
    G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (x + a)) := by
  intro x b
  have hp := (G.ambient.projection_regular b).comp_domain G.embedding
  have ht := ((G.factor b).translation_regular (a b)).comp_domain (fun y : G.Point => y b)
  obtain ⟨U, hU, hx, D, P, hP, hl⟩ := (hp.comp ht) x (0 : Fin 1)
  exact ⟨U, hU, hx, D, P, hP, hl⟩


end PhilipponMultiplicity
namespace PhilipponMultiplicity
variable {K : Type*} [Field K] (G : EmbeddedGroupProduct K)

theorem EmbeddedGroupProduct.continuous_translation (g : G.Point) :
    @Continuous _ _ G.zariskiTopology G.zariskiTopology (fun x : G.Point => g+x) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have hh : Continuous (fun x : G.Point => x+g) :=
    continuous_induced_rng.mpr (G.translation_regular g).continuous
  simpa only [add_comm] using hh

/-- Translation is a homeomorphism for the specified polynomial Zariski
topology. No topological-group instance is assumed. -/
def EmbeddedGroupProduct.translationHomeomorph (g : G.Point) :
    @Homeomorph G.Point G.Point G.zariskiTopology G.zariskiTopology := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact {
    toEquiv :=
      { toFun := fun x => g+x
        invFun := fun x => -g+x
        left_inv := fun x => by simp only [← add_assoc,neg_add_cancel,zero_add]
        right_inv := fun x => by simp only [← add_assoc,add_neg_cancel,zero_add] }
    continuous_toFun := G.continuous_translation g
    continuous_invFun := G.continuous_translation (-g) }

theorem isLocallyClosed_translate (g : G.Point) (V : Set G.Point)
    (hV : @IsLocallyClosed _ G.zariskiTopology V) :
    @IsLocallyClosed _ G.zariskiTopology (translate g V) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  have heq : translate g V = (fun x : G.Point => -g+x) ⁻¹' V := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [Set.mem_preimage,← add_assoc,neg_add_cancel,zero_add] using hy
    · intro hx
      exact ⟨-g+x,hx,by simp only [← add_assoc,add_neg_cancel,zero_add]⟩
  rw [heq]
  exact hV.preimage (G.continuous_translation (-g))

/-- Translation preserves the actual topological Krull dimension of every
subspace. Identifying it with the mission's Hilbert dimension is a separate
algebraic-geometric step in Lemma 4.5. -/
theorem topologicalKrullDim_translate (g : G.Point) (V : Set G.Point) :
    @topologicalKrullDim V (@TopologicalSpace.induced V G.Point Subtype.val G.zariskiTopology) =
      @topologicalKrullDim (translate g V)
        (@TopologicalSpace.induced (translate g V) G.Point Subtype.val G.zariskiTopology) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  let e := (G.translationHomeomorph g).image V
  exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph

theorem PolynomialTranslationChart.pullback_homogeneous {g : G.Point}
    (chart : PolynomialTranslationChart G g) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P)
      (fun i => chart.degree i * D i) := by
  classical
  have hh := hP.eval₂_blocks G.ambient G.ambient chart.coordinates
    (fun j i => if i=j then chart.degree i else 0) chart.homogeneous
  simpa [mul_ite,mul_comm] using hh

theorem PolynomialTranslationChart.pullback_eval_zero_iff {g : G.Point}
    (chart : PolynomialTranslationChart G g) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : G.Point) (hx : x ∈ chart.domain) :
    G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P) (G.embedding x) = 0 ↔
      G.ambient.eval P (G.embedding (g+x)) = 0 := by
  have heval : G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P) (G.embedding x) =
      MvPolynomial.eval (fun v => G.ambient.eval (chart.coordinates v) (G.embedding x)) P := by
    dsimp only [MultiProjectiveSpace.eval]
    rw [← MvPolynomial.eval_assoc]
    rfl
  rw [heval]
  exact G.ambient.eval_eq_zero_iff_of_lift (G.embedding (g+x))
    (fun v => G.ambient.eval (chart.coordinates v) (G.embedding x))
    (chart.represents x hx) P D hP

end PhilipponMultiplicity

namespace PhilipponMultiplicity

/-- A nonvanishing cover by finite-variable polynomials has a finite subcover,
even on an arbitrary subset of affine coordinate tuples. -/
theorem finite_polynomial_nonzero_cover {K σ X ι : Type*} [Field K] [Finite σ]
    (P : ι → MvPolynomial σ K) (v : X → σ → K)
    (hcover : ∀ x, ∃ i, MvPolynomial.eval (v x) (P i) ≠ 0) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, MvPolynomial.eval (v x) (P i) ≠ 0 := by
  classical
  obtain ⟨s,hs,hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := MvPolynomial σ K) (Set.range P)).mp
      (IsNoetherian.noetherian (Ideal.span (Set.range P)))
  choose ind hind using (fun q : s => hs q.property)
  let t : Finset ι := Finset.univ.image ind
  refine ⟨t,?_⟩
  intro x
  by_contra hx
  push Not at hx
  have hle : Ideal.span (Set.range P) ≤ RingHom.ker (MvPolynomial.eval (v x)) := by
    change Ideal.span (Set.range P) = Ideal.span (s : Set (MvPolynomial σ K)) at hspan
    rw [hspan]
    apply Ideal.span_le.mpr
    intro q hq
    change MvPolynomial.eval (v x) q = 0
    have hi : P (ind ⟨q,hq⟩) = q := hind ⟨q,hq⟩
    rw [← hi]
    exact hx (ind ⟨q,hq⟩) (Finset.mem_image.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,rfl⟩)
  obtain ⟨i,hi⟩ := hcover x
  exact hi (hle (Ideal.subset_span (Set.mem_range_self i)))

namespace MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Every open cover of an arbitrary multiprojective locus admits a finite
subcover. This supplies the finite family needed for uniform chart degrees. -/
theorem finite_open_subcover {X ι : Type*} (e : X → M.Point)
    (U : ι → Set M.Point) (hU : ∀ i, @IsOpen _ M.zariskiTopology (U i))
    (hcover : ∀ x, ∃ i, e x ∈ U i) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, e x ∈ U i := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  choose ind hind using hcover
  have hbasic (x : X) : ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
      M.eval P (e x) ≠ 0 ∧ {p : M.Point | M.eval P p ≠ 0} ⊆ U (ind x) := by
    obtain ⟨V,⟨P,D,hP,rfl⟩,hx,hV⟩ :=
      M.isTopologicalBasis_basic.exists_subset_of_mem_open (hind x) (hU (ind x))
    exact ⟨P,D,hP,hx,hV⟩
  choose P D hP hx hPU using hbasic
  obtain ⟨s,hs⟩ := finite_polynomial_nonzero_cover P (fun x => M.coordinate (e x))
    (fun x => ⟨x,hx x⟩)
  refine ⟨s.image ind,?_⟩
  intro x
  obtain ⟨y,hy,hyx⟩ := hs x
  exact ⟨ind y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,hPU y hyx⟩

end MultiProjectiveSpace
end PhilipponMultiplicity

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K] {X : Type u}
  {M N : MultiProjectiveSpace K} {e : X → M.Point} {f : X → N.Point}

/-- Polynomial formulas for one target block, with a homogeneous basic domain.
The entire tuple vanishes off that domain, giving global compatibility. -/
structure PolynomialMapChart (M N : MultiProjectiveSpace K)
    {X : Type u} (e : X → M.Point) (f : X → N.Point) (b : N.FactorIndex) where
  cut : M.CoordinateRing
  cutDegree : M.FactorIndex → ℕ
  cut_homogeneous : M.IsHomogeneous cut cutDegree
  degree : M.FactorIndex → ℕ
  coordinates : Fin (N.ambientDimension b + 1) → M.CoordinateRing
  homogeneous : ∀ j, M.IsHomogeneous (coordinates j) degree
  zero_off : ∀ x, M.eval cut (e x) = 0 → ∀ j, M.eval (coordinates j) (e x) = 0
  represents : ∀ x, M.eval cut (e x) ≠ 0 →
    ∃ h : (fun j => M.eval (coordinates j) (e x)) ≠ 0,
      Projectivization.mk K (fun j => M.eval (coordinates j) (e x)) h = f x b

theorem PolynomialMapChart.compatible {b : N.FactorIndex}
    (chart : PolynomialMapChart M N e f b) (x : X)
    (j k : Fin (N.ambientDimension b + 1)) :
    M.eval (chart.coordinates j) (e x) * (f x b).rep k =
      M.eval (chart.coordinates k) (e x) * (f x b).rep j := by
  by_cases hx : M.eval chart.cut (e x) = 0
  · rw [chart.zero_off x hx j,chart.zero_off x hx k,zero_mul,zero_mul]
  · obtain ⟨hn,heq⟩ := chart.represents x hx
    exact (projectivization_mk_eq_iff_cross _ _ hn (f x b).rep_nonzero).mp
      (heq.trans (f x b).mk_rep.symm) j k

theorem IsRegularAlong.exists_polynomialMapChart (hf : M.IsRegularAlong N e f)
    (x : X) (b : N.FactorIndex) :
    ∃ chart : PolynomialMapChart M N e f b, M.eval chart.cut (e x) ≠ 0 := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  obtain ⟨U,hU,hx,D,P,hP,hrep⟩ := hf x b
  obtain ⟨V,⟨q,E,hq,rfl⟩,hxq,hqU⟩ :=
    M.isTopologicalBasis_basic.exists_subset_of_mem_open hx hU
  let chart : PolynomialMapChart M N e f b :=
    { cut := q
      cutDegree := E
      cut_homogeneous := hq
      degree := E+D
      coordinates := fun j => q * P j
      homogeneous := fun j => hq.mul M (hP j)
      zero_off := by
        intro y hy j
        simp only [eval,map_mul] at hy ⊢
        rw [hy,zero_mul]
      represents := by
        intro y hy
        obtain ⟨hn,heq⟩ := hrep y (hqU hy)
        have hval : (fun j => M.eval (q * P j) (e y)) =
            M.eval q (e y) • (fun j => M.eval (P j) (e y)) := by
          funext j
          simp only [eval,map_mul,Pi.smul_apply,smul_eq_mul]
        have hn' : (fun j => M.eval (q * P j) (e y)) ≠ 0 := by
          rw [hval]
          exact smul_ne_zero hy hn
        exact ⟨hn',((Projectivization.mk_eq_mk_iff' K _ _ hn' hn).mpr
          ⟨M.eval q (e y),hval.symm⟩).trans heq⟩ }
  exact ⟨chart,hxq⟩

/-- A finite family of globally compatible polynomial formulas covers an
arbitrary regular map into a chosen target projective block. -/
theorem IsRegularAlong.exists_finite_polynomialMapCharts (hf : M.IsRegularAlong N e f)
    (b : N.FactorIndex) :
    ∃ charts : Finset (PolynomialMapChart M N e f b),
      ∀ x, ∃ chart ∈ charts, M.eval chart.cut (e x) ≠ 0 := by
  classical
  exact finite_polynomial_nonzero_cover (fun chart : PolynomialMapChart M N e f b => chart.cut)
    (fun x => M.coordinate (e x)) (fun x => hf.exists_polynomialMapChart x b)

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K] {X : Type u}
  {M N : MultiProjectiveSpace K} {e : X → M.Point} {f : X → N.Point}
  {b : N.FactorIndex}

theorem PolynomialMapChart.represents_lift (chart : PolynomialMapChart M N e f b)
    (x : X) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = e x i)
    (hcut : MvPolynomial.eval v chart.cut ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (chart.coordinates j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (chart.coordinates j)) h = f x b := by
  have hc : M.eval chart.cut (e x) ≠ 0 :=
    (M.eval_eq_zero_iff_of_lift (e x) v hv chart.cut chart.cutDegree chart.cut_homogeneous).not.mp hcut
  obtain ⟨hn,heq⟩ := chart.represents x hc
  obtain ⟨hn',heq'⟩ := M.homogeneous_tuple_lift (e x) v hv chart.coordinates chart.degree chart.homogeneous hn
  exact ⟨hn',heq'.trans heq⟩

/-- The chart cross-product identity survives arbitrary genuine homogeneous
lifts of both source and target, including outside the chart domain. -/
theorem PolynomialMapChart.compatible_lifts (chart : PolynomialMapChart M N e f b)
    (x : X) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = e x i)
    (w : Fin (N.ambientDimension b + 1) → K) (hw : w ≠ 0)
    (hwrep : Projectivization.mk K w hw = f x b) :
    ∀ j k, MvPolynomial.eval v (chart.coordinates j) * w k =
      MvPolynomial.eval v (chart.coordinates k) * w j := by
  by_cases hcut : MvPolynomial.eval v chart.cut = 0
  · have hc := (M.eval_eq_zero_iff_of_lift (e x) v hv chart.cut chart.cutDegree
      chart.cut_homogeneous).mp hcut
    have hz (j) : MvPolynomial.eval v (chart.coordinates j) = 0 :=
      (M.eval_eq_zero_iff_of_lift (e x) v hv (chart.coordinates j) chart.degree
        (chart.homogeneous j)).mpr (chart.zero_off x hc j)
    intro j k
    rw [hz j,hz k,zero_mul,zero_mul]
  · obtain ⟨hn,heq⟩ := chart.represents_lift x v hv hcut
    exact (projectivization_mk_eq_iff_cross _ _ hn hw).mp (heq.trans hwrep.symm)

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem noetherian_induced {X : Type*} (e : X → M.Point) :
    @NoetherianSpace X (TopologicalSpace.induced e M.zariskiTopology) := by
  letI : TopologicalSpace M.Point := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  apply noetherianSpace_iff_isCompact.mpr
  intro S
  apply isCompact_iff_finite_subcover.mpr
  intro ι U hU hcover
  choose W hW heq using fun i => isOpen_induced_iff.mp (hU i)
  obtain ⟨t,ht⟩ := M.finite_open_subcover (fun x : S => e x.val) W hW (by
    intro x
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover x.property)
    exact ⟨i,by change x.val ∈ e ⁻¹' W i; rwa [heq i]⟩)
  refine ⟨t,?_⟩
  intro x hx
  obtain ⟨i,hi,hxi⟩ := ht ⟨x,hx⟩
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,by rw [← heq i]; exact hxi⟩⟩

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity

/-- A connected Noetherian space on which homeomorphisms act transitively
is irreducible. This uses only individual homeomorphisms, not a topological
group structure on the Zariski topology. -/
theorem irreducible_of_transitive_homeomorphisms {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [ConnectedSpace X]
    (htrans : ∀ x y : X, ∃ e : X ≃ₜ X, e x = y) : IrreducibleSpace X := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨U,hU,⟨p,hp⟩,hUC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have hCopen : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨e,he⟩ := htrans p y
    have hopen : IsOpen (e '' U) := e.isOpenMap _ hU
    have hclosed : IsClosed (e '' C) := e.isClosedMap _
      (isClosed_of_mem_irreducibleComponents C hC)
    have hydense : C ⊆ closure (C ∩ e '' U) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 hopen
        ⟨y,hy,p,hp,he⟩
    have hCeC : C ⊆ e '' C := hydense.trans (closure_minimal
      (fun z hz => Set.image_mono hUC hz.2) hclosed)
    have heCC : e '' C ⊆ C := hC.2 (hC.1.image e e.continuous.continuousOn) hCeC
    exact Filter.mem_of_superset (hopen.mem_nhds ⟨p,hp,he⟩)
      ((Set.image_mono hUC).trans heCC)
  have hfull : C = univ := (show IsClopen C from
    ⟨isClosed_of_mem_irreducibleComponents C hC,hCopen⟩).eq_univ hC.1.nonempty
  exact { isPreirreducible_univ := by simpa only [hfull] using hC.1.2
          toNonempty := inferInstance }

variable {K : Type*} [Field K] {G : EmbeddedGroupProduct K}

def AlgebraicSubgroup.translationHomeomorph (H : AlgebraicSubgroup G)
    (a : H.toAddSubgroup) :
    @Homeomorph H.carrier H.carrier
      (TopologicalSpace.induced Subtype.val G.zariskiTopology)
      (TopologicalSpace.induced Subtype.val G.zariskiTopology) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact (G.translationHomeomorph a.val).subtype (by
    intro x
    change x ∈ H.toAddSubgroup ↔ a.val+x ∈ H.toAddSubgroup
    exact ⟨fun hx => H.toAddSubgroup.add_mem a.property hx,fun hx => by
      have h := H.toAddSubgroup.add_mem (H.toAddSubgroup.neg_mem a.property) hx
      simpa only [← add_assoc,neg_add_cancel,zero_add] using h⟩)

/-- The actual connected algebraic subgroup is irreducible for the specified
polynomial Zariski topology, as used before Philippon's Lemma 4.6. -/
theorem AlgebraicSubgroup.isIrreducible_of_isConnected (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) : @IsIrreducible _ G.zariskiTopology H.carrier := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : NoetherianSpace G.Point := G.ambient.noetherian_induced G.embedding
  letI : ConnectedSpace H.carrier := isConnected_iff_connectedSpace.mp hH
  apply isIrreducible_iff_irreducibleSpace.mpr
  apply irreducible_of_transitive_homeomorphisms
  intro x y
  let a : H.toAddSubgroup := ⟨y.val-x.val,H.toAddSubgroup.sub_mem y.property x.property⟩
  refine ⟨H.translationHomeomorph a,?_⟩
  apply Subtype.ext
  change y.val-x.val+x.val = y.val
  exact sub_add_cancel _ _

theorem AlgebraicSubgroup.isIrreducible_translate (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) (g : G.Point) :
    @IsIrreducible _ G.zariskiTopology (translate g H.carrier) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact (H.isIrreducible_of_isConnected hH).image _ (G.continuous_translation g).continuousOn


end PhilipponMultiplicity

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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


end PhilipponMultiplicity.Hilbert

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


end PhilipponMultiplicity.OperatorSupport

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

def pivotPolynomial (b : CoordinateChart G) (D : G.FactorIndex → ℕ) : G.CoordinateRing :=
  ∏ i, X ⟨i, b i⟩ ^ D i

theorem pivotPolynomial_homogeneous (b : CoordinateChart G) (D : G.FactorIndex → ℕ) :
    G.ambient.IsHomogeneous (pivotPolynomial b D) D :=
  Hilbert.variable_product_homogeneous G.ambient b D

theorem pivotPolynomial_eval_ne_zero (b : CoordinateChart G) (D : G.FactorIndex → ℕ)
    (x : G.Point) (hx : x ∈ chartDomain G b) :
    G.ambient.eval (pivotPolynomial b D) (G.embedding x) ≠ 0 := by
  classical
  simp only [pivotPolynomial, MultiProjectiveSpace.eval, map_prod, map_pow, eval_X]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hx i))


end PhilipponMultiplicity.OperatorSupport

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem polynomialPullback_analytic (A : AnalyticSubgroup G)
    (g : G.Point) (P : G.CoordinateRing) :
    AnalyticAt K (A.pullback P g) 0 :=
  AnalyticAt.aeval_mvPolynomial (fun v => A.lift_analytic g v) P

theorem lift_zero_represents (A : AnalyticSubgroup G) (g : G.Point) :
    ∀ i : G.FactorIndex, ∃ h : (fun j => A.lift g 0 ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => A.lift g 0 ⟨i,j⟩) h = G.embedding g i := by
  obtain ⟨hz,hrep⟩ := (A.lift_represents g).self_of_nhds
  have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  simpa only [hz',A.map_zero,add_zero] using hrep


end PhilipponMultiplicity.OperatorSupport
namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem coordinate_coeff_analytic (chart : TranslationChart A g)
    (v : G.ambient.Variable) (e : G.ambient.Variable →₀ ℕ) :
    AnalyticAt K ((chart.coordinates v).coeff e) 0 := by
  by_cases he : e ∈ (chart.coordinates v).support
  · exact chart.coefficient_analytic v e he
  · have he0 : (chart.coordinates v).coeff e = 0 := by
      simpa only [mem_support_iff, not_not] using he
    rw [he0]
    exact analyticAt_const

theorem substituted_coeff_analytic (chart : TranslationChart A g)
    (P : G.CoordinateRing) (e : G.ambient.Variable →₀ ℕ) :
    AnalyticAt K ((substitutedPolynomial chart P).coeff e) 0 := by
  classical
  induction P using MvPolynomial.induction_on generalizing e with
  | C a =>
    simp only [substitutedPolynomial, eval₂Hom_C, RingHom.comp_apply, coeff_C]
    split_ifs <;> exact analyticAt_const
  | add P Q hP hQ =>
    simp only [substitutedPolynomial, map_add, coeff_add]
    exact (hP e).add (hQ e)
  | mul_X P v hP =>
    simp only [substitutedPolynomial, map_mul, eval₂Hom_X']
    change AnalyticAt K ((substitutedPolynomial chart P * chart.coordinates v).coeff e) 0
    rw [coeff_mul]
    exact Finset.analyticAt_sum _ fun p _ => (hP p.1).mul (coordinate_coeff_analytic chart v p.2)

theorem evaluated_coefficients_analytic
    (F : MvPolynomial G.ambient.Variable (AnalyticCoefficientRing A))
    (hF : ∀ e, AnalyticAt K (F.coeff e) 0) (x : G.Point) :
    AnalyticAt K (evaluateCoefficientPolynomial A F x) 0 := by
  classical
  change AnalyticAt K (fun z => eval₂ (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z)
    (G.ambient.coordinate (G.embedding x)) F) 0
  simp only [eval₂_eq, Pi.evalRingHom_apply]
  exact Finset.analyticAt_fun_sum _ fun e _ => (hF e).mul analyticAt_const

theorem chart_evaluation_analytic (chart : TranslationChart A g)
    (x : G.Point) (v : G.ambient.Variable) :
    AnalyticAt K (evaluateCoefficientPolynomial A (chart.coordinates v) x) 0 :=
  evaluated_coefficients_analytic _ (coordinate_coeff_analytic chart v) x

theorem evaluate_substituted (chart : TranslationChart A g) (P : G.CoordinateRing)
    (x : G.Point) (z : A.ParameterSpace) :
    evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x z =
      MvPolynomial.eval (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) P := by
  unfold evaluateCoefficientPolynomial substitutedPolynomial
  rw [MvPolynomial.map_eval₂Hom]
  change eval₂Hom _ _ P = eval₂Hom (RingHom.id K) _ P
  congr 2
  ext a
  simp

/-- Evaluation of the actual coefficientwise polynomial operator is the
corresponding mixed derivative of the actual evaluated chart polynomial. -/
theorem polynomialOperator_eval (chart : TranslationChart A g) (P : G.CoordinateRing)
    (x : G.Point) (n : ℕ) (directions : Fin n → Fin A.parameterDimension) :
    G.ambient.eval (polynomialOperator chart n directions P) (G.embedding x) =
      iteratedFDeriv K n
        (fun z => MvPolynomial.eval
          (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) P) 0
        (fun i => Pi.single (directions i) 1) := by
  classical
  let F := substitutedPolynomial chart P
  let v := G.ambient.coordinate (G.embedding x)
  have heval : (fun z => MvPolynomial.eval
      (fun w => evaluateCoefficientPolynomial A (chart.coordinates w) x z) P) =
      fun z => ∑ e ∈ F.support, (∏ i ∈ e.support, v i ^ e i) * F.coeff e z := by
    funext z
    rw [← evaluate_substituted]
    change eval₂ _ v F = _
    simp only [eval₂_eq, Pi.evalRingHom_apply, mul_comm]
  rw [heval, iteratedFDeriv_fun_sum_apply
    (f := fun e z => (∏ i ∈ e.support, v i ^ e i) * F.coeff e z)
    (fun e _ => (analyticAt_const.mul (substituted_coeff_analytic chart P e)).contDiffAt)]
  simp only [ContinuousMultilinearMap.sum_apply]
  unfold polynomialOperator MultiProjectiveSpace.eval
  change MvPolynomial.eval v ((AddMonoidAlgebra.coeff F).sum _) = _
  rw [Finsupp.sum]
  simp only [map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro e _
  rw [show (fun z => (∏ i ∈ e.support, v i ^ e i) * F.coeff e z) =
    (fun z => (∏ i ∈ e.support, v i ^ e i) • F.coeff e z) from rfl,
    iteratedFDeriv_const_smul_apply' (substituted_coeff_analytic chart P e).contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, Finsupp.prod]
  exact mul_comm _ _

end PhilipponMultiplicity.OperatorSupport
namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperator_coeff (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (P : G.CoordinateRing)
    (e : G.ambient.Variable →₀ ℕ) :
    (polynomialOperator chart n directions P).coeff e =
      iteratedFDeriv K n ((substitutedPolynomial chart P).coeff e) 0
        (fun i => Pi.single (directions i) 1) := by
  classical
  unfold polynomialOperator
  rw [Finsupp.sum]
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with he
  · rfl
  · have hz : (substitutedPolynomial chart P).coeff e = 0 := by
      exact Finsupp.notMem_support_iff.mp he
    simp [hz]

theorem polynomialOperator_add (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (P Q : G.CoordinateRing) :
    polynomialOperator chart n directions (P + Q) =
      polynomialOperator chart n directions P + polynomialOperator chart n directions Q := by
  ext e
  simp only [coeff_add, polynomialOperator_coeff]
  have heq : (substitutedPolynomial chart (P + Q)).coeff e =
      fun z => (substitutedPolynomial chart P).coeff e z +
        (substitutedPolynomial chart Q).coeff e z := by
    simp [substitutedPolynomial]
    rfl
  rw [heq, fun_iteratedFDeriv_add_apply (substituted_coeff_analytic chart P e).contDiffAt
    (substituted_coeff_analytic chart Q e).contDiffAt]
  rfl

theorem polynomialOperator_C_mul (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (a : K) (P : G.CoordinateRing) :
    polynomialOperator chart n directions (C a * P) =
      C a * polynomialOperator chart n directions P := by
  ext e
  simp only [coeff_C_mul, polynomialOperator_coeff]
  have heq : (substitutedPolynomial chart (C a * P)).coeff e =
      fun z => a • (substitutedPolynomial chart P).coeff e z := by
    simp [substitutedPolynomial, coeff_C_mul, smul_eq_mul]
    rfl
  rw [heq, iteratedFDeriv_const_smul_apply' (substituted_coeff_analytic chart P e).contDiffAt]
  rfl

theorem polynomialOperator_zero_order (chart : TranslationChart A g)
    (directions : Fin 0 → Fin A.parameterDimension) (P : G.CoordinateRing) :
    polynomialOperator chart 0 directions P =
      MvPolynomial.map (Pi.evalRingHom (fun _ : A.ParameterSpace => K) 0)
        (substitutedPolynomial chart P) := by
  ext e
  simp [polynomialOperator_coeff, coeff_map]

theorem polynomialOperator_zero_algHom (chart : TranslationChart A g)
    (directions : Fin 0 → Fin A.parameterDimension) :
    ∃ f : G.CoordinateRing →ₐ[K] G.CoordinateRing,
      ∀ P, f P = polynomialOperator chart 0 directions P := by
  let f : G.CoordinateRing →+* G.CoordinateRing :=
    (MvPolynomial.map (Pi.evalRingHom (fun _ : A.ParameterSpace => K) 0)).comp
      (MvPolynomial.eval₂Hom
        (MvPolynomial.C.comp (Pi.constRingHom A.ParameterSpace K)) chart.coordinates)
  have hf (a : K) : f (algebraMap K G.CoordinateRing a) = algebraMap K G.CoordinateRing a := by
    simp [f, MvPolynomial.algebraMap_eq]
  refine ⟨{ f with commutes' := hf }, fun P => ?_⟩
  exact (polynomialOperator_zero_order chart directions P).symm

theorem substitutedPolynomial_homogeneous (chart : TranslationChart A g)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    (substitutedPolynomial chart P).IsWeightedHomogeneous
      (Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension)
      (fun i => chart.degree i * D i) := by
  classical
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  let c : G.ambient.Variable → G.FactorIndex → ℕ := fun v i =>
    chart.degree i * w v i
  have hc (v : G.ambient.Variable) : (chart.coordinates v).IsWeightedHomogeneous w (c v) := by
    intro e he
    funext i
    rw [G.ambient.blockWeight_apply]
    obtain ⟨h₁, h₂⟩ := chart.coordinate_homogeneous v e (mem_support_iff.mpr he)
    by_cases hi : i = v.1
    · subst i
      simpa [c, w, Hilbert.blockWeight] using h₁
    · simpa [c, w, Hilbert.blockWeight, Ne.symm hi] using h₂ i hi
  have hwP : P.IsWeightedHomogeneous w D := (G.ambient.degreePiece_iff P D).mpr hP
  apply IsWeightedHomogeneous.induction_on (motive := fun Q _ =>
    (substitutedPolynomial chart Q).IsWeightedHomogeneous w
      (fun i => chart.degree i * D i)) ?_ ?_ ?_ hwP
  · simpa [substitutedPolynomial] using
      isWeightedHomogeneous_zero (AnalyticCoefficientRing A) w (fun i => chart.degree i * D i)
  · intro P Q hP hQ ihP ihQ
    simpa only [substitutedPolynomial, map_add] using ihP.add ihQ
  · intro e a he
    have hweight : (∑ v ∈ e.support, e v • c v) = fun i => chart.degree i * D i := by
      funext i
      have hwi := congrFun he i
      rw [Finsupp.weight_eq_sum] at hwi
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hwi ⊢
      calc
        ∑ v ∈ e.support, e v * c v i =
            chart.degree i * ∑ v ∈ e.support, e v * w v i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          dsimp [c]
          ring
        _ = chart.degree i * D i := by
          congr 1
          rw [← hwi]
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ hv
          rw [Finsupp.notMem_support_iff.mp hv, zero_mul]
    unfold substitutedPolynomial
    rw [eval₂Hom_monomial, Finsupp.prod]
    change IsWeightedHomogeneous w (C _ * _) _
    have hprod := (IsWeightedHomogeneous.prod e.support
      (fun v => chart.coordinates v ^ e v) (fun v => e v • c v)
        (fun v _ => (hc v).pow (e v))).C_mul ((Pi.constRingHom A.ParameterSpace K) a)
    exact hweight ▸ hprod

theorem polynomialOperator_homogeneous (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (polynomialOperator chart n directions P)
      (fun i => chart.degree i * D i) := by
  intro e he i
  have hc : (substitutedPolynomial chart P).coeff e ≠ 0 := by
    intro hz
    have := mem_support_iff.mp he
    rw [polynomialOperator_coeff, hz] at this
    simpa using this
  have hw := substitutedPolynomial_homogeneous chart P D hP hc
  exact (G.ambient.blockWeight_apply e i).symm.trans (congrFun hw i)

end PhilipponMultiplicity.OperatorSupport
namespace PhilipponMultiplicity
open OperatorSupport

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- At a zero of the polynomial, changing an analytic projective lift
multiplies every directional derivative by one nonzero scalar. -/
theorem MultiProjectiveSpace.fderiv_eval_zero_iff_of_projective_lifts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (f g : E → M.Variable → K) (x v : E)
    (hf : ∀ j, AnalyticAt K (fun z => f z j) x)
    (hg : ∀ j, AnalyticAt K (fun z => g z j) x)
    (hrep : ∀ᶠ z in 𝓝 x, ∀ i : M.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i,j⟩) ≠ 0,
      ∃ hgi : (fun j => g z ⟨i,j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i,j⟩) hfi =
          Projectivization.mk K (fun j => g z ⟨i,j⟩) hgi)
    (hzero : MvPolynomial.eval (g x) P = 0) :
    fderiv K (fun z => MvPolynomial.eval (f z) P) x v = 0 ↔
      fderiv K (fun z => MvPolynomial.eval (g z) P) x v = 0 := by
  classical
  have hpivot (i : M.FactorIndex) : ∃ j, g x ⟨i,j⟩ ≠ 0 := by
    obtain ⟨_,hgi,_⟩ := hrep.self_of_nhds i
    simpa only [ne_eq,funext_iff,Pi.zero_apply,not_forall] using hgi
  choose j hj using hpivot
  let a (z : E) (i : M.FactorIndex) := f z ⟨i,j i⟩ / g z ⟨i,j i⟩
  let u (z : E) := ∏ i, a z i ^ D i
  have ha (i : M.FactorIndex) : AnalyticAt K (fun z => a z i) x :=
    (hf _).div (hg _) (hj i)
  have hu : AnalyticAt K u x :=
    Finset.analyticAt_fun_prod _ (fun i _ => (ha i).pow _)
  have hscale (z : E) (hz : ∀ i : M.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i,j⟩) ≠ 0,
      ∃ hgi : (fun j => g z ⟨i,j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i,j⟩) hfi =
          Projectivization.mk K (fun j => g z ⟨i,j⟩) hgi)
      (hjz : ∀ i, g z ⟨i,j i⟩ ≠ 0) :
      (∀ i, a z i ≠ 0) ∧ f z = fun q => a z q.1 * g z q := by
    have hh (i : M.FactorIndex) :
        a z i ≠ 0 ∧ ∀ k, f z ⟨i,k⟩ = a z i * g z ⟨i,k⟩ := by
      obtain ⟨hfi,hgi,heq⟩ := hz i
      obtain ⟨b,hb⟩ := (Projectivization.mk_eq_mk_iff K _ _ hfi hgi).mp heq
      have he (k) : f z ⟨i,k⟩ = (b : K) * g z ⟨i,k⟩ := by
        simpa only [Pi.smul_apply,Units.smul_def,smul_eq_mul] using (congrFun hb k).symm
      have hab : a z i = (b : K) := by
        dsimp [a]
        rw [he, mul_div_cancel_right₀ _ (hjz i)]
      exact ⟨hab ▸ b.ne_zero, fun k => by rw [hab]; exact he k⟩
    exact ⟨fun i => (hh i).1, funext fun q => (hh q.1).2 q.2⟩
  have hux : u x ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ ((hscale x hrep.self_of_nhds hj).1 i))
  have hnear : ∀ᶠ z in 𝓝 x, ∀ i, g z ⟨i,j i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    exact fun i => (hg _).continuousAt.eventually_ne (hj i)
  have heq : (fun z => MvPolynomial.eval (f z) P) =ᶠ[𝓝 x]
      (fun z => u z * MvPolynomial.eval (g z) P) := by
    filter_upwards [hrep,hnear] with z hz hjz
    rw [(hscale z hz hjz).2, M.eval_block_scale P D hP]
  have hgP : AnalyticAt K (fun z => MvPolynomial.eval (g z) P) x :=
    AnalyticAt.aeval_mvPolynomial hg P
  rw [heq.fderiv_eq, fderiv_fun_mul hu.differentiableAt hgP.differentiableAt]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    hzero,smul_eq_mul,zero_mul,add_zero]
  exact mul_eq_zero_iff_left hux

variable {G : EmbeddedGroupProduct K}

/-- Homogeneous equations suffice to test the actual ideal-defined tangent
kernel. The product rule handles their arbitrary polynomial multiples. -/
theorem AnalyticSubgroup.fderiv_zero_of_homogeneous_equations
    (A : AnalyticSubgroup G) (V : Set G.Point) (x : G.Point) (hx : x ∈ V)
    (v : A.ParameterSpace)
    (h : ∀ P : G.CoordinateRing, (∃ D, G.ambient.IsHomogeneous P D) →
      (∀ y ∈ V, G.ambient.eval P (G.embedding y) = 0) →
      fderiv K (A.pullback P x) 0 v = 0)
    (P : G.CoordinateRing) (hP : P ∈ G.vanishingIdeal V) :
    fderiv K (A.pullback P x) 0 v = 0 := by
  have hzero (Q : G.CoordinateRing) (hQ : Q ∈ G.vanishingIdeal V) :
      A.pullback Q x 0 = 0 := G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding hx) _ (lift_zero_represents A x) hQ
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    exact h Q hQ.1 (fun y hy => hQ.2 _ ⟨y,hy,rfl⟩)
  | zero =>
    change fderiv K (fun z : A.ParameterSpace => MvPolynomial.eval (A.lift x z) 0) 0 v = 0
    simp only [_root_.map_zero, fderiv_const_apply, ContinuousLinearMap.zero_apply]
  | add Q R hQ hR ihQ ihR =>
    have heq : A.pullback (Q+R) x = fun z => A.pullback Q x z + A.pullback R x z := by
      funext z; exact _root_.map_add _ _ _
    rw [heq, fderiv_fun_add (polynomialPullback_analytic A x Q).differentiableAt
      (polynomialPullback_analytic A x R).differentiableAt]
    simp only [ContinuousLinearMap.add_apply,ihQ,ihR,add_zero]
  | smul a Q hQ ih =>
    have heq : A.pullback (a • Q) x = fun z => A.pullback a x z * A.pullback Q x z := by
      funext z; exact map_mul _ _ _
    rw [heq, fderiv_fun_mul (polynomialPullback_analytic A x a).differentiableAt
      (polynomialPullback_analytic A x Q).differentiableAt]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ih,hzero Q hQ,smul_zero,zero_smul,add_zero]

/-- Pulling an equation back by the regular translation by `-x`, then
multiplying by the chart cuts, gives a global equation of `x + V`. Near
`x` the cuts are units, so its derivative detects the original direction. -/
theorem AnalyticSubgroup.mem_tangentKernel_of_translated_equations
    (A : AnalyticSubgroup G) (V : Set G.Point) (hV : (0 : G.Point) ∈ V)
    (x : G.Point) (v : A.ParameterSpace)
    (hd : ∀ Q ∈ G.vanishingIdeal (translate x V),
      fderiv K (A.pullback Q x) 0 v = 0) :
    v ∈ A.tangentKernel V := by
  classical
  apply (Submodule.mem_iInf _).mpr
  intro P
  change fderiv K (A.pullback P.val 0) 0 v = 0
  apply A.fderiv_zero_of_homogeneous_equations V 0 hV v _ P.val P.property
  rintro P ⟨D,hP⟩ hPV
  have hPI : P ∈ G.vanishingIdeal V :=
    Ideal.subset_span ⟨⟨D,hP⟩,by rintro _ ⟨y,hy,rfl⟩; exact hPV y hy⟩
  have hP0 : A.pullback P 0 0 = 0 :=
    G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
      (Set.mem_image_of_mem G.embedding hV) _ (lift_zero_represents A 0) hPI
  choose chart hchart using
    (fun i => (G.translation_regular (-x)).exists_polynomialMapChart x i)
  let coords (q : G.ambient.Variable) := (chart q.1).coordinates q.2
  let s : G.CoordinateRing := ∏ i, (chart i).cut
  let E : G.FactorIndex → ℕ := ∑ i, (chart i).cutDegree
  let R : G.CoordinateRing := eval₂ C coords P
  let F : G.FactorIndex → ℕ := fun i => ∑ b, D b * (chart b).degree i
  have hs : G.ambient.IsHomogeneous s E :=
    G.ambient.isHomogeneous_prod _ _ _ (fun i _ => (chart i).cut_homogeneous)
  have hR : G.ambient.IsHomogeneous R F :=
    hP.eval₂_blocks G.ambient G.ambient coords (fun i => (chart i).degree)
      (fun q => (chart q.1).homogeneous q.2)
  have hseval (y : G.Point) :
      G.ambient.eval s (G.embedding y) = ∏ i, G.ambient.eval (chart i).cut (G.embedding y) :=
    map_prod _ _ _
  have hReval (y : G.Point) : G.ambient.eval R (G.embedding y) =
      MvPolynomial.eval (fun q => G.ambient.eval (coords q) (G.embedding y)) P := by
    dsimp only [R,MultiProjectiveSpace.eval]
    rw [← eval_assoc]
    rfl
  have hsR : s*R ∈ G.vanishingIdeal (translate x V) := by
    apply Ideal.subset_span
    refine ⟨⟨E+F,hs.mul G.ambient hR⟩,?_⟩
    rintro _ ⟨y,hy,rfl⟩
    change G.ambient.eval (s*R) (G.embedding y) = 0
    rw [show G.ambient.eval (s*R) (G.embedding y) =
      G.ambient.eval s (G.embedding y) * G.ambient.eval R (G.embedding y) from map_mul _ _ _]
    by_cases hsy : G.ambient.eval s (G.embedding y) = 0
    · rw [hsy,zero_mul]
    · have hcuts : ∀ i, G.ambient.eval (chart i).cut (G.embedding y) ≠ 0 := by
        have hp : (∏ i, G.ambient.eval (chart i).cut (G.embedding y)) ≠ 0 :=
          (hseval y) ▸ hsy
        exact fun i => (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
      have hyV : y+(-x) ∈ V := by
        obtain ⟨z,hz,rfl⟩ := hy
        simpa only [add_comm x z,add_neg_cancel_right] using hz
      have hz : G.ambient.eval R (G.embedding y) = 0 := by
        rw [hReval]
        apply G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
          (Set.mem_image_of_mem G.embedding hyV) _ _ hPI
        exact fun i => (chart i).represents y (hcuts i)
      rw [hz,mul_zero]
  let f (z : A.ParameterSpace) (q : G.ambient.Variable) :=
    MvPolynomial.eval (A.lift x z) (coords q)
  have hf (q) : AnalyticAt K (fun z => f z q) 0 :=
    polynomialPullback_analytic A x (coords q)
  have hcut0 (i : G.FactorIndex) : A.pullback (chart i).cut x 0 ≠ 0 :=
    (G.ambient.eval_eq_zero_iff_of_lift (G.embedding x) (A.lift x 0)
      (lift_zero_represents A x) _ _ (chart i).cut_homogeneous).not.mpr (hchart i)
  have hnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ i,
      A.pullback (chart i).cut x z ≠ 0 := by
    rw [Filter.eventually_all]
    exact fun i => (polynomialPullback_analytic A x _).continuousAt.eventually_ne (hcut0 i)
  have hrep : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ i : G.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i,j⟩) ≠ 0,
      ∃ hgi : (fun j => A.lift 0 z ⟨i,j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i,j⟩) hfi =
          Projectivization.mk K (fun j => A.lift 0 z ⟨i,j⟩) hgi := by
    filter_upwards [hnear,A.lift_represents x,A.lift_represents 0] with z hz hzx hz0
    obtain ⟨hzx,hxlift⟩ := hzx
    obtain ⟨hz0,h0lift⟩ := hz0
    have hsame : (⟨z,hzx⟩ : A.domain) = ⟨z,hz0⟩ := Subtype.ext rfl
    intro i
    obtain ⟨hn,heq⟩ := (chart i).represents_lift (x+A.map ⟨z,hzx⟩)
      (A.lift x z) hxlift (hz i)
    obtain ⟨hn0,heq0⟩ := h0lift i
    refine ⟨hn,hn0,heq.trans ?_⟩
    rw [heq0,hsame]
    exact congrArg (fun y => G.embedding y i) (by abel)
  have hRpull : A.pullback R x = fun z => MvPolynomial.eval (f z) P := by
    funext z
    dsimp only [AnalyticSubgroup.pullback,R,f]
    rw [← eval_assoc]
    rfl
  have hR0 : A.pullback R x 0 = 0 := by
    rw [hRpull]
    apply G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
      (Set.mem_image_of_mem G.embedding hV) _ _ hPI
    intro i
    obtain ⟨hn,hn0,heq⟩ := hrep.self_of_nhds i
    obtain ⟨hn',heq'⟩ := lift_zero_represents A 0 i
    exact ⟨hn,heq.trans heq'⟩
  have hs0 : A.pullback s x 0 ≠ 0 := by
    change MvPolynomial.eval (A.lift x 0) (∏ i, (chart i).cut) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hcut0 i)
  have hsd := hd (s*R) hsR
  have hmul : A.pullback (s*R) x = fun z => A.pullback s x z * A.pullback R x z := by
    funext z; exact map_mul _ _ _
  rw [hmul,fderiv_fun_mul (polynomialPullback_analytic A x s).differentiableAt
    (polynomialPullback_analytic A x R).differentiableAt] at hsd
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    hR0,smul_eq_mul,zero_mul,add_zero] at hsd
  have hRd : fderiv K (A.pullback R x) 0 v = 0 := (mul_eq_zero.mp hsd).resolve_left hs0
  rw [hRpull] at hRd
  exact (G.ambient.fderiv_eval_zero_iff_of_projective_lifts P D hP f (A.lift 0)
    0 v hf (A.lift_analytic 0) hrep hP0).mp hRd

end PhilipponMultiplicity

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem AlgebraicSubgroup.translate_eq_of_mem (H : AlgebraicSubgroup G)
    (g x : G.Point) (hx : x ∈ translate g H.carrier) :
    translate x H.carrier = translate g H.carrier := by
  obtain ⟨h,hh,rfl⟩ := hx
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨h+z,H.toAddSubgroup.add_mem hh hz,by ext i; simp [add_assoc]⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨-h+z,H.toAddSubgroup.add_mem (H.toAddSubgroup.neg_mem hh) hz,
      by ext i; simp [add_assoc]⟩

/-- The geometric implication in Philippon's rank argument: if all coset
equations annihilate a direction at `x`, it is in the identity tangent kernel. -/
theorem AnalyticSubgroup.mem_tangentKernel_of_coset_equations
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g x : G.Point)
    (hx : x ∈ translate g H.carrier) (v : A.ParameterSpace)
    (hd : ∀ Q ∈ G.vanishingIdeal (translate g H.carrier),
      fderiv K (A.pullback Q x) 0 v = 0) :
    v ∈ A.tangentKernel H.carrier := by
  apply A.mem_tangentKernel_of_translated_equations H.carrier H.toAddSubgroup.zero_mem x v
  simpa only [H.translate_eq_of_mem g x hx] using hd

/-- Actual homogeneous equations of the coset have independent directional
derivatives on the specified transverse axes. No rank assumption is added. -/
theorem transverse_equation_derivatives_linearIndependent
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g x : G.Point)
    (hx : x ∈ translate g H.carrier)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions) :
    LinearIndependent K (fun i => fun Q :
      {Q : G.CoordinateRing // Q ∈ G.vanishingIdeal (translate g H.carrier) ∧
        ∃ D, G.ambient.IsHomogeneous Q D} =>
      fderiv K (A.pullback Q.val x) 0 (Pi.single (directions i) 1)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let v : A.ParameterSpace := ∑ i, c i • Pi.single (directions i) 1
  have hd : ∀ Q ∈ G.vanishingIdeal (translate g H.carrier),
      fderiv K (A.pullback Q x) 0 v = 0 := by
    intro Q hQ
    apply A.fderiv_zero_of_homogeneous_equations _ x hx v _ Q hQ
    intro P hP hzero
    have hPI : P ∈ G.vanishingIdeal (translate g H.carrier) :=
      Ideal.subset_span ⟨hP,by rintro _ ⟨y,hy,rfl⟩; exact hzero y hy⟩
    have he := congrFun hc ⟨P,hPI,hP⟩
    simpa only [v,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,Pi.zero_apply] using he
  have hv := A.mem_tangentKernel_of_coset_equations H g x hx v hd
  have hquot : ∑ i, c i • (A.tangentKernel H.carrier).mkQ (Pi.single (directions i) 1) = 0 := by
    simp_rw [← map_smul]
    rw [← map_sum]
    change (A.tangentKernel H.carrier).mkQ v = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hv
  exact Fintype.linearIndependent_iff.mp htransverse.1 c hquot

/-- A finite square minor witnessing full rank at a specified coset point,
chosen from genuine homogeneous equations. -/
theorem exists_transverse_derivative_minor
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g x : G.Point)
    (hx : x ∈ translate g H.carrier)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions) :
    ∃ Q : Fin (analyticCodimension A H.carrier) → G.CoordinateRing,
      (∀ j, Q j ∈ G.vanishingIdeal (translate g H.carrier)) ∧
      (∀ j, ∃ D, G.ambient.IsHomogeneous (Q j) D) ∧
      (Matrix.of (fun i j => fderiv K (A.pullback (Q j) x) 0
        (Pi.single (directions i) 1))).det ≠ 0 := by
  classical
  let T := {Q : G.CoordinateRing // Q ∈ G.vanishingIdeal (translate g H.carrier) ∧
    ∃ D, G.ambient.IsHomogeneous Q D}
  let col (Q : T) (i : Fin (analyticCodimension A H.carrier)) :=
    fderiv K (A.pullback Q.val x) 0 (Pi.single (directions i) 1)
  have hspan : Submodule.span K (Set.range col) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr
      (transverse_equation_derivatives_linearIndependent A H g x hx directions htransverse)
  obtain ⟨κ,a,ha,hsp,hli⟩ := exists_linearIndependent' K col
  rw [hspan] at hsp
  let b : Module.Basis κ K (Fin (analyticCodimension A H.carrier) → K) :=
    Module.Basis.mk hli hsp.ge
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : Fintype.card κ = analyticCodimension A H.carrier := by
    simpa using (Module.finrank_eq_card_basis b).symm
  let e : κ ≃ Fin (analyticCodimension A H.carrier) :=
    (Fintype.equivFin κ).trans (finCongr hc)
  refine ⟨fun j => (a (e.symm j)).val,fun j => (a (e.symm j)).property.1,
    fun j => (a (e.symm j)).property.2,?_⟩
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  exact hli.comp e.symm e.symm.injective

/-- Equalize the equation degrees with pivot monomials nonzero at `x`.
This preserves the nonzero derivative minor. -/
theorem exists_uniform_transverse_derivative_minor
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g x : G.Point)
    (hx : x ∈ translate g H.carrier)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions) :
    ∃ D : G.FactorIndex → ℕ,
    ∃ Q : Fin (analyticCodimension A H.carrier) → G.CoordinateRing,
      (∀ j, Q j ∈ G.vanishingIdeal (translate g H.carrier)) ∧
      (∀ j, G.ambient.IsHomogeneous (Q j) D) ∧
      (Matrix.of (fun i j => fderiv K (A.pullback (Q j) x) 0
        (Pi.single (directions i) 1))).det ≠ 0 := by
  classical
  obtain ⟨Q,hQI,hQ,hdet⟩ := exists_transverse_derivative_minor A H g x hx directions htransverse
  choose d hd using hQ
  obtain ⟨b,hb⟩ := exists_chartDomain x
  let D : G.ambient.FactorIndex → ℕ := ∑ j, d j
  let B (j : Fin (analyticCodimension A H.carrier)) := pivotPolynomial b (D-d j)
  have hdD (j : Fin (analyticCodimension A H.carrier)) : d j ≤ D := by
    intro i
    simpa only [D,Finset.sum_apply] using
      Finset.single_le_sum (fun k _ => Nat.zero_le (d k i)) (Finset.mem_univ j)
  have hB (j) : G.ambient.IsHomogeneous (B j) (D-d j) := pivotPolynomial_homogeneous _ _
  have hB0 (j) : A.pullback (B j) x 0 ≠ 0 :=
    (G.ambient.eval_eq_zero_iff_of_lift (G.embedding x) (A.lift x 0)
      (lift_zero_represents A x) _ _ (hB j)).not.mpr (pivotPolynomial_eval_ne_zero b _ x hb)
  have hQ0 (j) : A.pullback (Q j) x 0 = 0 :=
    G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal (Set.mem_image_of_mem G.embedding hx)
      _ (lift_zero_represents A x) (hQI j)
  refine ⟨D,fun j => B j * Q j,
    fun j => (G.vanishingIdeal _).mul_mem_left _ (hQI j),?_,?_⟩
  · intro j
    have hh := (hB j).mul G.ambient (hd j)
    have hdeg : (D-d j)+d j = D := by
      funext i
      exact Nat.sub_add_cancel (hdD j i)
    exact hdeg ▸ hh
  · have he (i j) : fderiv K (A.pullback (B j * Q j) x) 0 (Pi.single (directions i) 1) =
        A.pullback (B j) x 0 * fderiv K (A.pullback (Q j) x) 0 (Pi.single (directions i) 1) := by
      have hmul : A.pullback (B j * Q j) x =
          fun z => A.pullback (B j) x z * A.pullback (Q j) x z := by
        funext z; exact map_mul _ _ _
      rw [hmul,fderiv_fun_mul (polynomialPullback_analytic A x _).differentiableAt
        (polynomialPullback_analytic A x _).differentiableAt]
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
        hQ0 j,smul_eq_mul,zero_mul,add_zero]
    simp_rw [he]
    rw [Matrix.det_mul_row]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => hB0 j)) hdet

end PhilipponMultiplicity

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

def chartPullback (chart : TranslationChart A 0) (P : G.CoordinateRing) (x : G.Point) :=
  evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x

theorem chartPullback_analytic (chart : TranslationChart A 0)
    (P : G.CoordinateRing) (x : G.Point) : AnalyticAt K (chartPullback chart P x) 0 :=
  evaluated_coefficients_analytic _ (substituted_coeff_analytic chart P) x

theorem chartPullback_mul (chart : TranslationChart A 0)
    (P Q : G.CoordinateRing) (x : G.Point) :
    chartPullback chart (P*Q) x = fun z => chartPullback chart P x z * chartPullback chart Q x z := by
  funext z
  simp only [chartPullback,evaluate_substituted,map_mul]

theorem first_operator_eval (chart : TranslationChart A 0)
    (P : G.CoordinateRing) (x : G.Point) (i : Fin A.parameterDimension) :
    G.ambient.eval (polynomialOperator chart 1 (fun _ => i) P) (G.embedding x) =
      fderiv K (chartPullback chart P x) 0 (Pi.single i 1) := by
  rw [polynomialOperator_eval,iteratedFDeriv_one_apply]
  congr 2
  funext z
  exact (evaluate_substituted chart P x z).symm

theorem chart_zero_represents (chart : TranslationChart A 0)
    (x : G.Point) (hx : x ∈ chart.domain) :
    ∀ i : G.FactorIndex,
      ∃ hn : (fun j => evaluateCoefficientPolynomial A (chart.coordinates ⟨i,j⟩) x 0) ≠ 0,
        Projectivization.mk K (fun j => evaluateCoefficientPolynomial A
          (chart.coordinates ⟨i,j⟩) x 0) hn = G.embedding x i := by
  obtain ⟨hz,hrep⟩ := (chart.represents x hx).self_of_nhds
  have he : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  simpa only [he,A.map_zero,add_zero] using hrep

theorem chartPullback_zero_of_mem (chart : TranslationChart A 0)
    (V : Set G.Point) (P : G.CoordinateRing) (hP : P ∈ G.vanishingIdeal V)
    (x : G.Point) (hx : x ∈ chart.domain) (hxV : x ∈ V) :
    chartPullback chart P x 0 = 0 := by
  rw [chartPullback,evaluate_substituted]
  exact G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
    (Set.mem_image_of_mem G.embedding hxV)
    (fun q => evaluateCoefficientPolynomial A (chart.coordinates q) x 0)
    (chart_zero_represents chart x hx) hP

/-- At a chart point the degree-dependent scale is shared by every
homogeneous polynomial of that degree. -/
theorem chartPullback_zero_scales (chart : TranslationChart A 0)
    (x : G.Point) (hx : x ∈ chart.domain) :
    ∃ a : G.ambient.FactorIndex → Kˣ, ∀ P : G.CoordinateRing, ∀ D : G.ambient.FactorIndex → ℕ,
      G.ambient.IsHomogeneous P D →
      chartPullback chart P x 0 = (∏ i, (a i : K) ^ D i) * G.ambient.eval P (G.embedding x) := by
  classical
  have hh (i : G.ambient.FactorIndex) : ∃ a : Kˣ, ∀ j,
      evaluateCoefficientPolynomial A (chart.coordinates ⟨i,j⟩) x 0 =
        (a : K) * (G.embedding x i).rep j := by
    obtain ⟨hn,heq⟩ := chart_zero_represents chart x hx i
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ hn (G.embedding x i).rep_nonzero).mp
      (heq.trans (G.embedding x i).mk_rep.symm)
    exact ⟨a,fun j => by
      simpa only [Pi.smul_apply,Units.smul_def,smul_eq_mul] using (congrFun ha j).symm⟩
  choose a ha using hh
  refine ⟨a,?_⟩
  intro P D hP
  rw [chartPullback,evaluate_substituted]
  have he : (fun q => evaluateCoefficientPolynomial A (chart.coordinates q) x 0) =
      fun q => (a q.1 : K) * G.ambient.coordinate (G.embedding x) q := by
    funext q; exact ha q.1 q.2
  rw [he]
  exact G.ambient.eval_block_scale P D hP
    (G.ambient.coordinate (G.embedding x)) (fun i => (a i : K))

theorem first_operator_mul_eval (chart : TranslationChart A 0)
    (P Q : G.CoordinateRing) (x : G.Point) (i : Fin A.parameterDimension)
    (hQ : chartPullback chart Q x 0 = 0) :
    G.ambient.eval (polynomialOperator chart 1 (fun _ => i) (P*Q)) (G.embedding x) =
      chartPullback chart P x 0 *
        G.ambient.eval (polynomialOperator chart 1 (fun _ => i) Q) (G.embedding x) := by
  rw [first_operator_eval,first_operator_eval,chartPullback_mul,
    fderiv_fun_mul (chartPullback_analytic chart P x).differentiableAt
      (chartPullback_analytic chart Q x).differentiableAt]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    hQ,smul_eq_mul,zero_mul,add_zero]

theorem polynomialOperator_sum (chart : TranslationChart A 0)
    (n : ℕ) (directions : Fin n → Fin A.parameterDimension) {ι : Type*}
    (t : Finset ι) (P : ι → G.CoordinateRing) :
    polynomialOperator chart n directions (∑ i ∈ t, P i) =
      ∑ i ∈ t, polynomialOperator chart n directions (P i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    ext e
    simp [polynomialOperator_coeff,substitutedPolynomial]
  | @insert i t hi ih =>
    simp only [Finset.sum_insert,hi,not_false_eq_true,polynomialOperator_add,ih]

/-- The nonzero intrinsic derivative minor remains nonzero for every
polynomial translation chart that contains the chosen point. -/
theorem operator_derivative_minor_ne_zero
    (chart : TranslationChart A 0) {n : ℕ} (directions : Fin n → Fin A.parameterDimension)
    (V : Set G.Point) (x : G.Point) (hx : x ∈ V) (hchart : x ∈ chart.domain)
    (Q : Fin n → G.CoordinateRing)
    (hQI : ∀ j, Q j ∈ G.vanishingIdeal V)
    (hQ : ∀ j, ∃ D, G.ambient.IsHomogeneous (Q j) D)
    (hdet : (Matrix.of (fun i j => fderiv K (A.pullback (Q j) x) 0
      (Pi.single (directions i) 1))).det ≠ 0) :
    (Matrix.of (fun i j => G.ambient.eval
      (polynomialOperator chart 1 (fun _ => directions i) (Q j)) (G.embedding x))).det ≠ 0 := by
  classical
  intro hz
  obtain ⟨c,hc,hcB⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz
  let v : A.ParameterSpace := ∑ i, c i • Pi.single (directions i) 1
  have hzero (j) : A.pullback (Q j) x 0 = 0 :=
    G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal (Set.mem_image_of_mem G.embedding hx)
      _ (lift_zero_represents A x) (hQI j)
  have hder (j) : fderiv K (A.pullback (Q j) x) 0 v = 0 := by
    obtain ⟨D,hD⟩ := hQ j
    have hsum := congrFun hcB j
    simp only [Matrix.vecMul,Matrix.of_apply,dotProduct,Pi.zero_apply,first_operator_eval] at hsum
    have hchartd : fderiv K (chartPullback chart (Q j) x) 0 v = 0 := by
      simpa only [v,map_sum,map_smul,smul_eq_mul] using hsum
    have hlift : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ b : G.FactorIndex,
        ∃ hf : (fun k => evaluateCoefficientPolynomial A (chart.coordinates ⟨b,k⟩) x z) ≠ 0,
        ∃ hg : (fun k => A.lift x z ⟨b,k⟩) ≠ 0,
          Projectivization.mk K (fun k => evaluateCoefficientPolynomial A
            (chart.coordinates ⟨b,k⟩) x z) hf =
          Projectivization.mk K (fun k => A.lift x z ⟨b,k⟩) hg := by
      filter_upwards [chart.represents x hchart,A.lift_represents x] with z hz hz'
      obtain ⟨hd,hr⟩ := hz
      obtain ⟨hd',hr'⟩ := hz'
      intro b
      obtain ⟨hf,hfr⟩ := hr b
      obtain ⟨hg,hgr⟩ := hr' b
      exact ⟨hf,hg,hfr.trans (by simpa only [add_zero] using hgr.symm)⟩
    apply (G.ambient.fderiv_eval_zero_iff_of_projective_lifts (Q j) D hD
      (fun z q => evaluateCoefficientPolynomial A (chart.coordinates q) x z)
      (A.lift x) 0 v (chart_evaluation_analytic chart x) (A.lift_analytic x) hlift (hzero j)).mp
    have heval : chartPullback chart (Q j) x = fun z =>
        MvPolynomial.eval (fun q => evaluateCoefficientPolynomial A (chart.coordinates q) x z) (Q j) :=
      funext fun z => evaluate_substituted chart (Q j) x z
    rw [← heval]
    exact hchartd
  apply hdet
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨c,hc,?_⟩
  funext j
  simpa only [v,map_sum,map_smul,smul_eq_mul,Matrix.vecMul,Matrix.of_apply,
    dotProduct,Pi.zero_apply] using hder j

end PhilipponMultiplicity.OperatorSupport

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isHomogeneous_det {n : ℕ} (B : Matrix (Fin n) (Fin n) M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hB : ∀ i j, M.IsHomogeneous (B i j) D) :
    M.IsHomogeneous B.det (n • D) := by
  classical
  rw [Matrix.det_apply]
  apply M.isHomogeneous_sum
  intro σ _
  have hp : M.IsHomogeneous (∏ i, B (σ i) i) (n • D) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin] using
      M.isHomogeneous_prod Finset.univ (fun i => B (σ i) i) (fun _ => D)
        (fun i _ => hB (σ i) i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa only [h,one_smul] using hp
  · simpa only [h,Units.neg_smul,one_smul] using hp.neg M

theorem isHomogeneous_adjugate {n : ℕ} (B : Matrix (Fin n) (Fin n) M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hB : ∀ i j, M.IsHomogeneous (B i j) D)
    (i j : Fin n) : M.IsHomogeneous (B.adjugate i j) ((n-1) • D) := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hd := M.isHomogeneous_det (B.submatrix j.succAbove i.succAbove) D
      (fun a b => hB (j.succAbove a) (i.succAbove b))
    simpa only [Nat.add_sub_cancel,map_pow,map_neg,map_one] using
      hd.C_mul M ((-1 : K) ^ (j.val+i.val))

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem homogeneous_mem_vanishingIdeal_of_open
    (V U : Set G.Point) (hV : @IsIrreducible _ G.zariskiTopology V)
    (hU : @IsOpen _ G.zariskiTopology U) (hmeets : (V ∩ U).Nonempty)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (hz : ∀ x ∈ V ∩ U, G.ambient.eval P (G.embedding x) = 0) :
    P ∈ G.vanishingIdeal V := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have hclosed : IsClosed {x : G.Point | G.ambient.eval P (G.embedding x) = 0} :=
    (G.ambient.isClosed_zero P D hP).preimage continuous_induced_dom
  have hsub : V ⊆ {x : G.Point | G.ambient.eval P (G.embedding x) = 0} :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hV.2 hU hmeets).trans
      (closure_minimal hz hclosed)
  exact Ideal.subset_span ⟨⟨D,hP⟩,by rintro _ ⟨x,hx,rfl⟩; exact hsub hx⟩

/-- The adjugate identity, with all degree and chart factors retained.
Its input equations and its output equations lie in the same actual ideal. -/
theorem first_operator_adjugate_eval
    (chart : TranslationChart A 0) {n : ℕ}
    (directions : Fin n → Fin A.parameterDimension)
    (V : Set G.Point) (D : G.FactorIndex → ℕ)
    (Q : Fin n → G.CoordinateRing)
    (hQI : ∀ j, Q j ∈ G.vanishingIdeal V)
    (hQ : ∀ j, G.ambient.IsHomogeneous (Q j) D)
    (x : G.Point) (hx : x ∈ V) (hxchart : x ∈ chart.domain) :
    let B : Matrix (Fin n) (Fin n) G.CoordinateRing :=
      fun i j => polynomialOperator chart 1 (fun _ => directions i) (Q j)
    let E : G.FactorIndex → ℕ := (n-1) • (fun i => chart.degree i * D i)
    ∃ a : G.FactorIndex → Kˣ, ∀ i j,
      G.ambient.eval (polynomialOperator chart 1 (fun _ => directions i)
        (∑ k, B.adjugate k j * Q k)) (G.embedding x) =
      (∏ b, (a b : K) ^ E b) *
        (if i=j then G.ambient.eval B.det (G.embedding x) else 0) := by
  classical
  dsimp only
  let B : Matrix (Fin n) (Fin n) G.CoordinateRing :=
    fun i j => polynomialOperator chart 1 (fun _ => directions i) (Q j)
  let F : G.FactorIndex → ℕ := fun i => chart.degree i * D i
  have hB (i j) : G.ambient.IsHomogeneous (B i j) F :=
    polynomialOperator_homogeneous chart _ _ _ D (hQ j)
  have hC (k j) : G.ambient.IsHomogeneous (B.adjugate k j) ((n-1) • F) :=
    G.ambient.isHomogeneous_adjugate B F hB k j
  obtain ⟨a,ha⟩ := chartPullback_zero_scales chart x hxchart
  refine ⟨a,?_⟩
  intro i j
  have hprod (k) : G.ambient.eval
      (polynomialOperator chart 1 (fun _ => directions i) (B.adjugate k j * Q k)) (G.embedding x) =
      (∏ b, (a b : K) ^ ((n-1) • F) b) *
        (G.ambient.eval (B.adjugate k j) (G.embedding x) *
          G.ambient.eval (B i k) (G.embedding x)) := by
    rw [first_operator_mul_eval chart _ _ x _
      (chartPullback_zero_of_mem chart V (Q k) (hQI k) x hxchart hx),ha _ _ (hC k j)]
    exact mul_assoc _ _ _
  have hsum : ∑ k, G.ambient.eval (B.adjugate k j) (G.embedding x) *
      G.ambient.eval (B i k) (G.embedding x) =
      if i=j then G.ambient.eval B.det (G.embedding x) else 0 := by
    have hh := congrArg (fun P : G.CoordinateRing => G.ambient.eval P (G.embedding x))
      (congrFun (congrFun (Matrix.mul_adjugate B) i) j)
    simpa only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
      MultiProjectiveSpace.eval,map_sum,map_mul,apply_ite,map_one,map_zero,mul_one,mul_zero,
      mul_comm,one_mul,zero_mul] using hh
  change G.ambient.eval (polynomialOperator chart 1 (fun _ => directions i)
    (∑ k, B.adjugate k j * Q k)) (G.embedding x) = _
  rw [polynomialOperator_sum]
  change MvPolynomial.eval _ (∑ k, _) = _
  rw [map_sum]
  change (∑ k, G.ambient.eval
    (polynomialOperator chart 1 (fun _ => directions i) (B.adjugate k j * Q k))
      (G.embedding x)) = _
  simp_rw [hprod]
  rw [← Finset.mul_sum,hsum]
  rfl

/-- Philippon, Lemma 4.6, using a nonzero homogeneous derivative minor and
its adjugate. Irreducibility extends the off-diagonal identities from the
chosen chart to the full coset. -/
theorem transverse_equations_completed
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions)
    (chart : TranslationChart A (0 : G.Point))
    (hmeets : (translate g H.carrier ∩ chart.domain).Nonempty) :
    ∃ Q : Fin (analyticCodimension A H.carrier) → G.CoordinateRing,
      (∀ j, Q j ∈ G.vanishingIdeal (translate g H.carrier)) ∧
      (∀ i j,
        polynomialOperator chart 1 (fun _ => directions i) (Q j) ∉
          G.vanishingIdeal (translate g H.carrier) ↔ i = j) := by
  classical
  letI : CompleteSpace K := hK.completeSpace
  obtain ⟨x,hx,hxchart⟩ := hmeets
  obtain ⟨D,Q,hQI,hQ,hdet⟩ :=
    exists_uniform_transverse_derivative_minor A H g x hx directions htransverse
  let n := analyticCodimension A H.carrier
  let B : Matrix (Fin n) (Fin n) G.CoordinateRing :=
    fun i j => polynomialOperator chart 1 (fun _ => directions i) (Q j)
  let F : G.FactorIndex → ℕ := fun i => chart.degree i * D i
  let E : G.FactorIndex → ℕ := (n-1) • F
  let R : Fin n → G.CoordinateRing := fun j => ∑ k, B.adjugate k j * Q k
  have hB (i j) : G.ambient.IsHomogeneous (B i j) F :=
    polynomialOperator_homogeneous chart _ _ _ D (hQ j)
  have hC (k j) : G.ambient.IsHomogeneous (B.adjugate k j) E :=
    G.ambient.isHomogeneous_adjugate B F hB k j
  have hR (j) : G.ambient.IsHomogeneous (R j) (E+D) :=
    G.ambient.isHomogeneous_sum Finset.univ _ _ (fun k _ => (hC k j).mul G.ambient (hQ k))
  have hdetx : G.ambient.eval B.det (G.embedding x) ≠ 0 := by
    have hh := operator_derivative_minor_ne_zero chart directions _ x hx hxchart Q hQI
      (fun j => ⟨D,hQ j⟩) hdet
    rw [MultiProjectiveSpace.eval,RingHom.map_det]
    exact hh
  refine ⟨R,?_,?_⟩
  · intro j
    exact (G.vanishingIdeal _).sum_mem (fun k _ =>
      (G.vanishingIdeal _).mul_mem_left _ (hQI k))
  · intro i j
    constructor
    · intro hnot
      by_contra hij
      apply hnot
      apply homogeneous_mem_vanishingIdeal_of_open _ chart.domain
        (H.isIrreducible_translate hH g) chart.domain_isOpen ⟨x,hx,hxchart⟩
        _ _ (polynomialOperator_homogeneous chart _ _ (R j) (E+D) (hR j))
      rintro y ⟨hy,hyc⟩
      obtain ⟨a,ha⟩ := first_operator_adjugate_eval chart directions _ D Q hQI hQ y hy hyc
      have hh := ha i j
      simpa only [if_neg hij,mul_zero] using hh
    · rintro rfl hmem
      have hz := G.ambient.eval_eq_zero_of_mem_vanishingIdeal hmem
        (Set.mem_image_of_mem G.embedding hx)
      obtain ⟨a,ha⟩ := first_operator_adjugate_eval chart directions _ D Q hQI hQ x hx hxchart
      have he := ha i i
      simp only [ite_true] at he
      rw [he] at hz
      exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun b _ => pow_ne_zero _ (a b).ne_zero))
        hdetx) hz

end PhilipponMultiplicity


end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions)
    (chart : TranslationChart A (0 : G.Point))
    (hmeets : (PhilipponMultiplicity.translate g H.carrier ∩ chart.domain).Nonempty) :
    ∃ Q : Fin (analyticCodimension A H.carrier) → G.CoordinateRing,
      (∀ j, Q j ∈ G.vanishingIdeal (PhilipponMultiplicity.translate g H.carrier)) ∧
      (∀ i j,
        polynomialOperator chart 1 (fun _ => directions i) (Q j) ∉
          G.vanishingIdeal (PhilipponMultiplicity.translate g H.carrier) ↔ i = j) := by
  exact transverse_equations_completed K hK G A H hH g directions htransverse chart hmeets
