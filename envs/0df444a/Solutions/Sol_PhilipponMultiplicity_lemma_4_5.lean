-- Prove2me | solution 1 for PhilipponMultiplicity.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T13:14:14.136322+00:00
-- url     : https://prove2.me/submissions/3e03a724-6bfb-4aaa-99bc-ed6d818a0b4e

import Definitions.Def_PhilipponMultiplicity_SectionFour
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients

set_option autoImplicit false
set_option maxHeartbeats 1000000
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

theorem exists_form_nonzero_at (p : M.Point) (D : M.FactorIndex → ℕ) :
    ∃ Q : M.CoordinateRing, M.IsHomogeneous Q D ∧ M.eval Q p ≠ 0 := by
  classical
  have hj (i : M.FactorIndex) : ∃ j, (p i).rep j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using
      (Projectivization.rep_nonzero (p i))
  choose j hj using hj
  let d : M.Variable →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun v => if v.2 = j v.1 then D v.1 else 0)
  refine ⟨monomial d 1, ?_, ?_⟩
  · intro m hm i
    have hm' : m = d := Finset.mem_singleton.mp (support_monomial_subset hm)
    subst m
    simp [d]
  · change MvPolynomial.eval (M.coordinate p) (monomial d 1) ≠ 0
    rw [eval_monomial]
    simp only [one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    dsimp [d]
    split_ifs with h
    · apply pow_ne_zero
      change (p v.1).rep v.2 ≠ 0
      rw [h]
      exact hj v.1
    · simp


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

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Compute a genuine quotient Hilbert function through a parametrization whose
polynomial kernel agrees with the homogeneous equations of the image. -/
theorem hilbertFunction_eq_finrank_image
    {T A : Type*} [CommRing A] [Algebra K A]
    (p : T → M.Point) (φ : M.CoordinateRing →ₐ[K] A) (D : M.FactorIndex → ℕ)
    (hker : ∀ P : M.CoordinateRing, M.IsHomogeneous P D →
      (φ P = 0 ↔ ∀ t, M.eval P (p t) = 0)) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D =
      Module.finrank K ((Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        φ.toLinearMap) := by
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let I := M.vanishingIdeal (Set.range p)
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := φ.toLinearMap.domRestrict V
  have hfg : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ φ P.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hker P.val ((M.degreePiece_iff _ _).mp P.property)]
    constructor
    · intro h t
      exact M.eval_eq_zero_of_mem_vanishingIdeal h (Set.mem_range_self t)
    · intro h
      exact Ideal.subset_span ⟨⟨D, (M.degreePiece_iff _ _).mp P.property⟩,
        by rintro x ⟨t, rfl⟩; exact h t⟩
  have hf : LinearMap.range f = V.map (Ideal.Quotient.mkₐ K I).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have hg : LinearMap.range g = V.map φ.toLinearMap := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hfg).trans g.quotKerEquivRange)).finrank_eq
  rw [hf, hg] at he
  exact he


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

def evaluationMap {X : Type*} (p : X → M.Point) : M.CoordinateRing →ₐ[K] (X → K) :=
  AlgHom.pi (fun x => MvPolynomial.aeval (M.coordinate (p x)))

@[simp] theorem evaluationMap_apply {X : Type*} (p : X → M.Point)
    (P : M.CoordinateRing) (x : X) : M.evaluationMap p P x = M.eval P (p x) := rfl

def sectionSpace {X : Type*} (p : X → M.Point) (D : M.FactorIndex → ℕ) :
    Submodule K (X → K) :=
  (Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
    (M.evaluationMap p).toLinearMap

instance sectionSpace_finite {X : Type*} (p : X → M.Point) (D : M.FactorIndex → ℕ) :
    Module.Finite K (M.sectionSpace p D) := by
  unfold sectionSpace
  infer_instance

theorem hilbertFunction_eq_sectionSpace {X : Type*} (p : X → M.Point)
    (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D = Module.finrank K (M.sectionSpace p D) := by
  apply M.hilbertFunction_eq_finrank_image p (M.evaluationMap p) D
  intro P _
  exact funext_iff


end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_empty (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal ∅) D = 0 := by
  have h := M.hilbertFunction_eq_sectionSpace (fun x : Empty => isEmptyElim x) D
  have hr : Set.range (fun x : Empty => (isEmptyElim x : M.Point)) = ∅ := by
    ext x
    simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
    rintro ⟨e, _⟩
    exact isEmptyElim e
  have hf : Module.finrank K (M.sectionSpace (fun x : Empty => isEmptyElim x) D) = 0 :=
    Module.finrank_eq_zero_of_subsingleton K _
  rw [hr, hf] at h
  exact h

theorem hilbertPolynomial_empty :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
      (M.vanishingIdeal ∅) = 0 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, fun D _ => ?_⟩
  rw [M.hilbertFunction_empty]
  simp

theorem hilbertFunction_pos {S : Set M.Point} (hS : S.Nonempty)
    (D : M.FactorIndex → ℕ) :
    0 < Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal S) D := by
  classical
  obtain ⟨x, hx⟩ := hS
  obtain ⟨Q, hQ, hQx⟩ := M.exists_form_nonzero_at x D
  let I := M.vanishingIdeal S
  let W := Hilbert.quotientPiece K M.factorCount M.ambientDimension I D
  let q : W := ⟨Ideal.Quotient.mk I Q,
    ⟨Q, (M.degreePiece_iff Q D).mpr hQ, rfl⟩⟩
  have hq : q ≠ 0 := by
    intro h
    have hz : Ideal.Quotient.mk I Q = 0 := congrArg Subtype.val h
    have hm : Q ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    exact hQx (M.eval_eq_zero_of_mem_vanishingIdeal hm hx)
  letI : Nontrivial W := nontrivial_of_ne q 0 hq
  letI : Module.Finite K W := by
    dsimp [W, Hilbert.quotientPiece]
    infer_instance
  exact Module.finrank_pos

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
open SectionThree

theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [M.blockWeight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d


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
theorem exists_basic_subset (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U)
    (x : G.Point) (hx : x ∈ U) :
    ∃ s : G.CoordinateRing, ∃ E : G.FactorIndex → ℕ, G.ambient.IsHomogeneous s E ∧
      G.ambient.eval s (G.embedding x) ≠ 0 ∧
      {y : G.Point | G.ambient.eval s (G.embedding y) ≠ 0} ⊆ U := by
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨W, ⟨s,E,hs,rfl⟩, hxW, hWV⟩ :=
    G.ambient.isTopologicalBasis_basic.exists_subset_of_mem_open hx hV
  exact ⟨s,E,hs,hxW,fun y hy => hWV hy⟩


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

namespace PhilipponMultiplicity.TranslationSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
local instance : TopologicalSpace G.Point := G.zariskiTopology
local instance : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology

/-- One polynomial weight supported in an exclusive open piece of each
irreducible component, together with a valid polynomial translation chart. -/
structure SeparatingCharts (V : Set G.Point) {g : G.Point}
    (atlas : PolynomialTranslationAtlas G g) where
  Index : Type u
  finite : Fintype Index
  component : Index → Set V
  irreducible : ∀ i, IsIrreducible (component i)
  covers : ∀ x : V, ∃ i, x ∈ component i
  chart : Index → atlas.Index
  weight : Index → G.CoordinateRing
  degree : Index → G.FactorIndex → ℕ
  homogeneous : ∀ i, G.ambient.IsHomogeneous (weight i) (degree i)
  point : Index → V
  point_mem : ∀ i, point i ∈ component i
  nonzero : ∀ i, G.ambient.eval (weight i) (G.embedding (point i).val) ≠ 0
  support_chart : ∀ i (x : V), G.ambient.eval (weight i) (G.embedding x.val) ≠ 0 →
    x.val ∈ (atlas.chart (chart i)).domain
  zero_other : ∀ i j, i ≠ j → ∀ x : V, x ∈ component i →
    G.ambient.eval (weight j) (G.embedding x.val) = 0
  pivot : Index → CoordinateChart G
  point_pivot : ∀ i, (point i).val ∈ chartDomain G (pivot i)

attribute [instance] SeparatingCharts.finite

theorem exists_separating_charts (V : Set G.Point) {g : G.Point}
    (atlas : PolynomialTranslationAtlas G g) : Nonempty (SeparatingCharts V atlas) := by
  classical
  letI : NoetherianSpace G.Point := G.ambient.noetherian_induced G.embedding
  let C := irreducibleComponents V
  have hC : C.Finite := NoetherianSpace.finite_irreducibleComponents
  letI : Fintype C := hC.fintype
  have hdata (i : C) : ∃ x : V, x ∈ i.val ∧ ∃ a : atlas.Index,
      ∃ P : G.CoordinateRing, ∃ D : G.FactorIndex → ℕ,
        G.ambient.IsHomogeneous P D ∧ G.ambient.eval P (G.embedding x.val) ≠ 0 ∧
          (∀ y : V, G.ambient.eval P (G.embedding y.val) ≠ 0 →
            y.val ∈ (atlas.chart a).domain ∧ ∀ j : C, j ≠ i → y ∉ j.val) := by
    let O : Set V := (⋃₀ (C \ {i.val}))ᶜ
    have hO : IsOpen O := by
      dsimp only [O]
      rw [Set.sUnion_eq_biUnion,isOpen_compl_iff]
      exact hC.sdiff.isClosed_biUnion (fun W hW => isClosed_of_mem_irreducibleComponents W hW.1)
    have hclosure : closure O = i.val := closure_sUnion_irreducibleComponents_sdiff_singleton hC i.val i.property
    have hOne : O.Nonempty := by
      rw [← closure_nonempty_iff,hclosure]
      exact i.property.1.nonempty
    obtain ⟨x,hx⟩ := hOne
    obtain ⟨a,ha⟩ := atlas.covers x.val
    obtain ⟨W,hW,heq⟩ := isOpen_induced_iff.mp (hO.inter
      ((atlas.chart a).domain_open.preimage continuous_subtype_val))
    have hxW : x.val ∈ W := by
      change x ∈ Subtype.val ⁻¹' W
      rw [heq]
      exact ⟨hx,ha⟩
    obtain ⟨P,D,hP,hPx,hPW⟩ := OperatorSupport.exists_basic_subset W hW x.val hxW
    refine ⟨x,?_,a,P,D,hP,hPx,?_⟩
    · rw [← hclosure]
      exact subset_closure hx
    · intro y hy
      have hyO : y ∈ O ∩ {q : V | q.val ∈ (atlas.chart a).domain} := by
        change y ∈ O ∩ Subtype.val ⁻¹' (atlas.chart a).domain
        rw [← heq]
        exact hPW hy
      refine ⟨hyO.2,?_⟩
      intro j hji hj
      apply hyO.1
      exact Set.mem_sUnion.mpr ⟨j.val,⟨j.property,by
        simp only [Set.mem_singleton_iff]
        exact fun h => hji (Subtype.ext h)⟩,hj⟩
  choose x hx a P D hP hn hs using hdata
  choose b hb using fun i => OperatorSupport.exists_chartDomain (x i).val
  refine ⟨⟨C,inferInstance,(fun i => i.val),(fun i => i.property.1),?_,a,P,D,hP,x,hx,hn,
    (fun i y hy => (hs i y hy).1),?_,b,hb⟩⟩
  · intro y
    exact ⟨⟨irreducibleComponent y,irreducibleComponent_mem_irreducibleComponents y⟩,mem_irreducibleComponent⟩
  · intro i j hij y hy
    by_contra hn
    exact (hs j y hn).2 i hij hy

end PhilipponMultiplicity.TranslationSupport
namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A linear map of homogeneous equations with the same vanishing kernel
compares the actual quotient Hilbert functions. -/
theorem hilbertFunction_le_of_linear_pullback (S T : Set M.Point)
    (D E : M.FactorIndex → ℕ) (L : M.CoordinateRing →ₗ[K] M.CoordinateRing)
    (hhom : ∀ P, M.IsHomogeneous P D → M.IsHomogeneous (L P) E)
    (hker : ∀ P, M.IsHomogeneous P D →
      ((∀ x ∈ S, M.eval P x = 0) ↔ ∀ x ∈ T, M.eval (L P) x = 0)) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal T) E := by
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let W := Hilbert.degreePiece K M.factorCount M.ambientDimension E
  let I := M.vanishingIdeal S
  let J := M.vanishingIdeal T
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let q := (Ideal.Quotient.mkₐ K J).toLinearMap
  let g := (q.comp L).domRestrict V
  have hmem (U : Set M.Point) (P : M.CoordinateRing) (d : M.FactorIndex → ℕ)
      (hP : M.IsHomogeneous P d) :
      P ∈ M.vanishingIdeal U ↔ ∀ x ∈ U, M.eval P x = 0 := by
    constructor
    · intro h x hx
      exact M.eval_eq_zero_of_mem_vanishingIdeal h hx
    · intro h
      exact Ideal.subset_span ⟨⟨d,hP⟩,h⟩
  have hfg : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ Ideal.Quotient.mk J (L P.val) = 0
    have hP := (M.degreePiece_iff _ _).mp P.property
    rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.Quotient.eq_zero_iff_mem,
      hmem S P.val D hP,hmem T (L P.val) E (hhom _ hP)]
    exact hker _ hP
  have hf : LinearMap.range f = V.map (Ideal.Quotient.mkₐ K I).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P,rfl⟩
      exact ⟨P.val,P.property,rfl⟩
    · rintro ⟨P,hP,rfl⟩
      exact ⟨⟨P,hP⟩,rfl⟩
  have hg : LinearMap.range g ≤ W.map q := by
    rintro _ ⟨P,rfl⟩
    exact ⟨L P.val,(M.degreePiece_iff _ _).mpr
      (hhom _ ((M.degreePiece_iff _ _).mp P.property)),rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hfg).trans g.quotKerEquivRange)).finrank_eq
  rw [hf] at he
  letI : Module.Finite K (Hilbert.quotientPiece K M.factorCount M.ambientDimension J E) := by
    dsimp [Hilbert.quotientPiece]
    infer_instance
  exact he.trans_le (Submodule.finrank_mono hg)

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.TranslationSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
local instance : TopologicalSpace G.Point := G.zariskiTopology
local instance : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
open OperatorSupport

variable {V : Set G.Point} {g : G.Point} {atlas : PolynomialTranslationAtlas G g}

def SeparatingCharts.shift (s : SeparatingCharts V atlas) (k : G.FactorIndex) : ℕ :=
  ∑ i, s.degree i k

theorem SeparatingCharts.degree_le_shift (s : SeparatingCharts V atlas)
    (i : s.Index) (k : G.FactorIndex) : s.degree i k ≤ s.shift k := by
  classical
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (s.degree j k)) (Finset.mem_univ i)

def SeparatingCharts.padding (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (i : s.Index) (k : G.FactorIndex) : ℕ :=
  s.shift k - s.degree i k + (c k - (atlas.chart (s.chart i)).degree k) * D k

def SeparatingCharts.pullback (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) : G.CoordinateRing →ₗ[K] G.CoordinateRing :=
  ∑ i, (LinearMap.mulLeft K (s.weight i * pivotPolynomial (s.pivot i) (s.padding c D i))).comp
    (MvPolynomial.aeval (atlas.chart (s.chart i)).coordinates).toLinearMap

theorem SeparatingCharts.pullback_apply (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (P : G.CoordinateRing) :
    s.pullback c D P = ∑ i, s.weight i * pivotPolynomial (s.pivot i) (s.padding c D i) *
      MvPolynomial.eval₂ MvPolynomial.C (atlas.chart (s.chart i)).coordinates P := by
  simp only [SeparatingCharts.pullback,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem SeparatingCharts.pullback_homogeneous (s : SeparatingCharts V atlas)
    (c : G.FactorIndex → ℕ) (hc : ∀ a k, (atlas.chart a).degree k ≤ c k)
    (D : G.FactorIndex → ℕ) (P : G.CoordinateRing) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (s.pullback c D P) (fun k => c k * D k + s.shift k) := by
  classical
  rw [s.pullback_apply]
  apply (G.ambient.degreePiece_iff _ _).mp
  apply Submodule.sum_mem
  intro i _
  apply (G.ambient.degreePiece_iff _ _).mpr
  have ht := ((s.homogeneous i).mul G.ambient
    (pivotPolynomial_homogeneous (s.pivot i) (s.padding c D i))).mul G.ambient
    ((atlas.chart (s.chart i)).pullback_homogeneous G P D hP)
  convert ht using 1
  funext k
  have h₁ := s.degree_le_shift i k
  have h₂ := Nat.mul_le_mul_right (D k) (hc (s.chart i) k)
  simp only [Pi.add_apply,SeparatingCharts.padding,Nat.sub_mul]
  omega

theorem SeparatingCharts.eval_pullback (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (P : G.CoordinateRing) (x : G.Point) :
    G.ambient.eval (s.pullback c D P) (G.embedding x) =
      ∑ i, G.ambient.eval (s.weight i) (G.embedding x) *
        G.ambient.eval (pivotPolynomial (s.pivot i) (s.padding c D i)) (G.embedding x) *
        G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C
          (atlas.chart (s.chart i)).coordinates P) (G.embedding x) := by
  rw [s.pullback_apply]
  simp only [MultiProjectiveSpace.eval,map_sum,map_mul]

/-- The component weights remove invalid charts, while an exclusive dense
open subset of each component prevents cancellation in the reverse direction. -/
theorem SeparatingCharts.pullback_vanishing_iff (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (P : G.CoordinateRing) (hP : G.ambient.IsHomogeneous P D) :
    (∀ x ∈ translate g V, G.ambient.eval P (G.embedding x) = 0) ↔
      ∀ x ∈ V, G.ambient.eval (s.pullback c D P) (G.embedding x) = 0 := by
  classical
  constructor
  · intro h x hx
    rw [s.eval_pullback]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : G.ambient.eval (s.weight i) (G.embedding x) = 0
    · rw [hi,zero_mul,zero_mul]
    · have hz := ((atlas.chart (s.chart i)).pullback_eval_zero_iff G P D hP x
        (s.support_chart i ⟨x,hx⟩ hi)).mpr (h (g+x) ⟨x,hx,rfl⟩)
      rw [hz,mul_zero]
  · intro h y hy
    obtain ⟨x,hx,rfl⟩ := hy
    let Z : Set V := {x | G.ambient.eval P (G.embedding (g+x.val)) = 0}
    have he : Continuous (G.embedding : G.Point → G.ambient.Point) := continuous_induced_dom
    have hv : Continuous (Subtype.val : V → G.Point) := continuous_subtype_val
    have hZ : IsClosed Z := (G.ambient.isClosed_zero P D hP).preimage
      (he.comp ((G.continuous_translation g).comp hv))
    obtain ⟨i,hi⟩ := s.covers ⟨x,hx⟩
    suffices hs : s.component i ⊆ Z by
      exact hs (a := (⟨x,hx⟩ : V)) hi
    let U : Set V := {x | G.ambient.eval (s.weight i) (G.embedding x.val) ≠ 0} ∩
      Subtype.val ⁻¹' chartDomain G (s.pivot i)
    have hU : IsOpen U := ((G.ambient.isOpen_basic (s.weight i) (s.degree i)
      (s.homogeneous i)).preimage (he.comp hv)).inter
      ((chartDomain_isOpen (s.pivot i)).preimage hv)
    have hdense : s.component i ⊆ closure (s.component i ∩ U) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen (s.irreducible i).2 hU
        ⟨s.point i,s.point_mem i,s.nonzero i,s.point_pivot i⟩
    apply hdense.trans
    apply closure_minimal _ hZ
    intro z hz
    have heval := h z.val z.property
    rw [s.eval_pullback,Finset.sum_eq_single i] at heval
    · have hzpull : G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C
          (atlas.chart (s.chart i)).coordinates P) (G.embedding z.val) = 0 :=
        (mul_eq_zero.mp heval).resolve_left (mul_ne_zero hz.2.1
          (pivotPolynomial_eval_ne_zero (s.pivot i) (s.padding c D i) z.val hz.2.2))
      exact ((atlas.chart (s.chart i)).pullback_eval_zero_iff G P D hP z.val
        (s.support_chart i z hz.2.1)).mp hzpull
    · intro j _ hji
      rw [s.zero_other i j hji.symm z hz.1,zero_mul,zero_mul]
    · simp

/-- A bounded translation atlas induces a uniform shifted comparison of
homogeneous quotient dimensions. The shift is independent of the input degree. -/
theorem translated_hilbertFunction_le (V : Set G.Point) (g : G.Point)
    (c : G.FactorIndex → ℕ) (atlas : PolynomialTranslationAtlas G g)
    (hc : ∀ a k, (atlas.chart a).degree k ≤ c k) :
    ∃ E : G.FactorIndex → ℕ, ∀ D : G.FactorIndex → ℕ,
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal (translate g V)) D ≤
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal V) (fun k => c k * D k + E k) := by
  obtain ⟨s⟩ := exists_separating_charts V atlas
  refine ⟨s.shift,fun D => ?_⟩
  apply G.ambient.hilbertFunction_le_of_linear_pullback
    (G.embedding '' translate g V) (G.embedding '' V) D _ (s.pullback c D)
    (fun P hP => s.pullback_homogeneous c hc D P hP)
  intro P hP
  simpa only [Set.forall_mem_image] using s.pullback_vanishing_iff c D P hP

end PhilipponMultiplicity.TranslationSupport


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


end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.Hilbert

/-- The elementary final comparison of polynomial growth exponents. -/
theorem exponent_le_of_eventual_power_bound {a b : ℕ} {c C : ℚ}
    (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop, c * (n : ℚ) ^ a ≤ C * (n : ℚ) ^ b) : a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C / c) (max (N : ℚ) 1))
  have hnN : N ≤ n := by
    exact_mod_cast le_of_lt ((le_max_left (N : ℚ) 1).trans (le_max_right _ _) |>.trans_lt hn)
  have hn1 : (1 : ℚ) < n :=
    ((le_max_right (N : ℚ) 1).trans (le_max_right _ _)).trans_lt hn
  have hnpos : (0 : ℚ) < n := lt_trans zero_lt_one hn1
  have hpow : (n : ℚ) ^ (b + 1) ≤ (n : ℚ) ^ a :=
    pow_le_pow_right₀ hn1.le hba
  have hprod : (c * n) * (n : ℚ) ^ b ≤ C * (n : ℚ) ^ b := by
    calc
      (c * n) * (n : ℚ) ^ b = c * (n : ℚ) ^ (b + 1) := by rw [pow_succ]; ring
      _ ≤ c * (n : ℚ) ^ a := mul_le_mul_of_nonneg_left hpow hc.le
      _ ≤ _ := hN n hnN
  have hcn : c * n ≤ C := (mul_le_mul_iff_left₀ (pow_pos hnpos b)).mp hprod
  have hlarge : C < c * n := by
    have := (le_max_left (C / c) (max (N : ℚ) 1)).trans_lt hn
    have := (div_lt_iff₀ hc).mp this
    simpa [mul_comm] using this
  exact (not_lt_of_ge hcn) hlarge


end PhilipponMultiplicity.Hilbert
namespace PhilipponMultiplicity.Hilbert
variable {ι : Type*} [Fintype ι]

/-- Restrict a multivariate polynomial to an affine ray. -/
def rayPolynomial (F : MvPolynomial ι ℚ) (a E : ι → ℚ) : Polynomial ℚ :=
  eval₂ Polynomial.C (fun i => Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) F

def rayTerm (a E : ι → ℚ) (e : ι →₀ ℕ) (r : ℚ) : Polynomial ℚ :=
  Polynomial.C r * ∏ i, (Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) ^ e i

theorem rayPolynomial_eq_sum (F : MvPolynomial ι ℚ) (a E : ι → ℚ) :
    rayPolynomial F a E = ∑ e ∈ F.support, rayTerm a E e (coeff e F) := by
  classical
  simp only [rayPolynomial,MvPolynomial.eval₂_eq,rayTerm]
  apply Finset.sum_congr rfl
  intro e _
  change Polynomial.C _ * e.prod (fun i n =>
      (Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) ^ n) = _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem rayTerm_degree_and_leadingCoeff (a E : ι → ℚ) (ha : ∀ i, a i ≠ 0)
    (e : ι →₀ ℕ) (r : ℚ) (hr : r ≠ 0) :
    (rayTerm a E e r).natDegree = e.degree ∧
      (rayTerm a E e r).leadingCoeff = r * ∏ i, (a i) ^ e i := by
  classical
  have hn (i : ι) : Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i) ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_linear (ha i),Polynomial.natDegree_zero] at this
    omega
  constructor
  · rw [rayTerm,Polynomial.natDegree_C_mul hr,
      Polynomial.natDegree_prod Finset.univ _ (fun i _ => pow_ne_zero _ (hn i))]
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_linear (ha _),mul_one]
    change (∑ i, e i) = e.sum (fun _ n => n)
    exact (Finsupp.sum_fintype e (fun _ n => n) (fun _ => rfl)).symm
  · simp only [rayTerm,Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_prod,Polynomial.leadingCoeff_pow]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.leadingCoeff_linear (ha i)]

theorem rayPolynomial_natDegree_le (F : MvPolynomial ι ℚ) (a E : ι → ℚ)
    (ha : ∀ i, a i ≠ 0) : (rayPolynomial F a E).natDegree ≤ F.totalDegree := by
  classical
  rw [rayPolynomial_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  rw [(rayTerm_degree_and_leadingCoeff a E ha e _ (mem_support_iff.mp he)).1]
  exact le_totalDegree he

/-- The fixed affine shift has no effect on the leading homogeneous part. -/
theorem rayPolynomial_top_coeff (F : MvPolynomial ι ℚ) (a E : ι → ℚ)
    (ha : ∀ i, a i ≠ 0) :
    (rayPolynomial F a E).coeff F.totalDegree =
      eval a (homogeneousComponent F.totalDegree F) := by
  classical
  rw [rayPolynomial_eq_sum,Polynomial.finsetSum_coeff]
  conv_rhs => arg 2; arg 2; rw [F.as_sum]
  rw [map_sum,eval_sum]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨hdeg,hlc⟩ := rayTerm_degree_and_leadingCoeff a E ha e _ (mem_support_iff.mp he)
  rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff e F) rfl)]
  by_cases hd : e.degree = F.totalDegree
  · rw [if_pos hd.symm,← hd,← hdeg,Polynomial.coeff_natDegree,hlc,eval_monomial]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [hdeg]; exact lt_of_le_of_ne (le_totalDegree he) hd)]
    simp [Ne.symm hd]

theorem eval_top_pos (F : MvPolynomial ι ℚ) (hF : F ≠ 0)
    (hpos : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F)
    (a : ι → ℚ) (ha : ∀ i, 0 < a i) :
    0 < eval a (homogeneousComponent F.totalDegree F) := by
  classical
  rw [← rayPolynomial_top_coeff F a 0 (fun i => (ha i).ne'),
    rayPolynomial_eq_sum,Polynomial.finsetSum_coeff]
  have hterm (e : ι →₀ ℕ) (he : e ∈ F.support) :
      (rayTerm a 0 e (coeff e F)).coeff F.totalDegree =
        if e.degree = F.totalDegree then coeff e F * ∏ i, a i ^ e i else 0 := by
    obtain ⟨hdeg,hlc⟩ := rayTerm_degree_and_leadingCoeff a 0 (fun i => (ha i).ne')
      e _ (mem_support_iff.mp he)
    split_ifs with hd
    · rw [← hd,← hdeg,Polynomial.coeff_natDegree,hlc]
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [hdeg]; exact lt_of_le_of_ne (le_totalDegree he) hd)
  obtain ⟨e,he,hd⟩ := Finset.exists_mem_eq_sup F.support
    (support_nonempty.mpr hF) Finsupp.degree
  change F.totalDegree = e.degree at hd
  apply Finset.sum_pos'
  · intro b hb
    rw [hterm b hb]
    split_ifs with h
    · exact mul_nonneg (hpos b h) (Finset.prod_nonneg fun i _ => pow_nonneg (ha i).le _)
    · exact le_rfl
  · refine ⟨e,he,?_⟩
    rw [hterm e he,if_pos hd.symm]
    exact mul_pos (lt_of_le_of_ne (hpos e hd.symm) (Ne.symm (mem_support_iff.mp he)))
      (Finset.prod_pos fun i _ => pow_pos (ha i) _)

theorem rayPolynomial_degree_and_leadingCoeff (F : MvPolynomial ι ℚ) (hF : F ≠ 0)
    (hpos : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F)
    (a E : ι → ℚ) (ha : ∀ i, 0 < a i) :
    (rayPolynomial F a E).natDegree = F.totalDegree ∧
      (rayPolynomial F a E).leadingCoeff = eval a (homogeneousComponent F.totalDegree F) ∧
      0 < (rayPolynomial F a E).leadingCoeff := by
  have hcoeff := rayPolynomial_top_coeff F a E (fun i => (ha i).ne')
  have hpos' := eval_top_pos F hF hpos a ha
  have hdeg := le_antisymm (rayPolynomial_natDegree_le F a E (fun i => (ha i).ne'))
    (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact hpos'.ne'))
  refine ⟨hdeg,?_,?_⟩
  · simpa only [Polynomial.leadingCoeff,hdeg] using hcoeff
  · simpa only [Polynomial.leadingCoeff,hdeg,hcoeff] using hpos'

theorem rayPolynomial_eval (F : MvPolynomial ι ℚ) (a E : ι → ℚ) (x : ℚ) :
    (rayPolynomial F a E).eval x = eval (fun i => a i * x + E i) F := by
  change (Polynomial.evalRingHom x) (eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) F) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id ℚ := by
    ext r
    simp
  rw [hc,MvPolynomial.eval₂_id]
  have hf : (⇑(Polynomial.evalRingHom x) ∘ fun i =>
      Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) =
        fun i => a i * x + E i := by
    funext i
    simp
  rw [hf]

end PhilipponMultiplicity.Hilbert
namespace PhilipponMultiplicity.Hilbert

theorem natDegree_le_of_eventual_eval_le (P Q : Polynomial ℚ)
    (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff)
    (hle : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  obtain ⟨c,C,hc,hC,hboundsP⟩ := polynomial_eventually_two_sided P hP
  obtain ⟨c',C',hc',hC',hboundsQ⟩ := polynomial_eventually_two_sided Q hQ
  apply exponent_le_of_eventual_power_bound hc (C := C')
  filter_upwards [hboundsP,hboundsQ,hle] with n hnP hnQ hn
  exact hnP.1.trans (hn.trans hnQ.2)

theorem leadingCoeff_le_of_eventual_eval_le (P Q : Polynomial ℚ)
    (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff)
    (hdeg : P.natDegree = Q.natDegree)
    (hle : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.leadingCoeff ≤ Q.leadingCoeff := by
  have hlim (R : Polynomial ℚ) (hR : 0 < R.leadingCoeff) :
      Tendsto (fun n : ℕ => R.eval (n : ℚ) / (n : ℚ) ^ R.natDegree)
        atTop (𝓝 R.leadingCoeff) := by
    have hne : R ≠ 0 := by intro h; simpa [h] using hR
    have hd : R.degree = (Polynomial.X ^ R.natDegree : Polynomial ℚ).degree := by
      rw [Polynomial.degree_X_pow,Polynomial.degree_eq_natDegree hne]
    simpa [Function.comp_def] using (R.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
      (Polynomial.X ^ R.natDegree) hd).comp (tendsto_natCast_atTop_atTop (R := ℚ))
  apply le_of_tendsto_of_tendsto (hlim P hP) (hlim Q hQ)
  filter_upwards [hle] with n hn
  rw [hdeg]
  exact div_le_div_of_nonneg_right hn (pow_nonneg (Nat.cast_nonneg _) _)

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem vanishing_hilbertPolynomial_ne_zero {S : Set M.Point} (hS : S.Nonempty) :
    hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S) ≠ 0 := by
  obtain ⟨d₀,hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension
    (M.vanishingIdeal S) (multigraded_hilbert_polynomial_exists K M _
      (vanishingIdeal_multihomogeneous K M S))
  intro hz
  have h := hd₀ d₀ (fun _ => le_rfl)
  rw [hz,map_zero] at h
  have hp : (0 : ℚ) < hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal S) d₀ := by exact_mod_cast M.hilbertFunction_pos hS d₀
  exact hp.ne' h.symm

theorem exists_ray_hilbertPolynomial {S : Set M.Point} (hS : S.Nonempty)
    (a E : M.FactorIndex → ℕ) (ha : ∀ i, 1 ≤ a i) :
    ∃ P : Polynomial ℚ,
      P.natDegree = (hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal S)).totalDegree ∧
      P.leadingCoeff = eval (fun i => (a i : ℚ))
        (homogeneousComponent (hilbertPolynomial K M.factorCount M.ambientDimension
          (M.vanishingIdeal S)).totalDegree
          (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S))) ∧
      0 < P.leadingCoeff ∧ ∃ N : ℕ, ∀ n ≥ N,
        P.eval (n : ℚ) = (hilbertFunction K M.factorCount M.ambientDimension
          (M.vanishingIdeal S) (fun i => a i * n + E i) : ℚ) := by
  classical
  let F := hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S)
  have hhom := vanishingIdeal_multihomogeneous K M S
  have htop : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F := by
    intro e he
    have h := (multigraded_hilbert_polynomial_top_coefficients K M _ hhom).1 e
    rwa [coeff_homogeneousComponent,if_pos he] at h
  have hap (i : M.FactorIndex) : 0 < (a i : ℚ) := by
    exact_mod_cast (show 0 < a i by have := ha i; omega)
  obtain ⟨hd,hlc,hpos⟩ := rayPolynomial_degree_and_leadingCoeff F
    (vanishing_hilbertPolynomial_ne_zero M hS) htop
    (fun i => (a i : ℚ)) (fun i => (E i : ℚ)) hap
  refine ⟨rayPolynomial F (fun i => (a i : ℚ)) (fun i => (E i : ℚ)),hd,hlc,hpos,?_⟩
  obtain ⟨d₀,hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension
    (M.vanishingIdeal S) (multigraded_hilbert_polynomial_exists K M _ hhom)
  refine ⟨Finset.univ.sup d₀,fun n hn => ?_⟩
  rw [rayPolynomial_eval]
  have h := hd₀ (fun i => a i * n + E i) (fun i =>
    (Finset.le_sup (Finset.mem_univ i)).trans (hn.trans
      ((Nat.le_mul_of_pos_left n (by have := ha i; omega)).trans (Nat.le_add_right _ _))))
  simpa only [Nat.cast_add,Nat.cast_mul] using h

/-- A fixed coordinatewise degree shift does not change the dimension
comparison inferred from Hilbert functions. -/
theorem dimension_le_of_shifted_hilbertFunction_le (S T : Set M.Point)
    (hS : S.Nonempty) (hT : T.Nonempty) (c E : M.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i)
    (hle : ∀ D : M.FactorIndex → ℕ,
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal T)
        (fun i => c i * D i + E i)) :
    (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S)).totalDegree ≤
      (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal T)).totalDegree := by
  obtain ⟨P,hPd,hPlc,hPpos,NP,hP⟩ := exists_ray_hilbertPolynomial M hS (fun _ => 1) 0
    (fun _ => le_rfl)
  obtain ⟨Q,hQd,hQlc,hQpos,NQ,hQ⟩ := exists_ray_hilbertPolynomial M hT c E hc
  rw [← hPd,← hQd]
  apply natDegree_le_of_eventual_eval_le P Q hPpos hQpos
  apply eventually_atTop.mpr
  refine ⟨max NP NQ,fun n hn => ?_⟩
  rw [hP n ((le_max_left _ _).trans hn),hQ n ((le_max_right _ _).trans hn)]
  simpa only [Pi.zero_apply,one_mul,add_zero,Nat.cast_le] using hle (fun _ => n)

/-- At equal Hilbert dimension, the same comparison yields the normalized
degree inequality with exactly the specified coordinatewise scaling. -/
theorem degreeValue_le_of_shifted_hilbertFunction_le (S T : Set M.Point)
    (hS : S.Nonempty) (hT : T.Nonempty) (c E : M.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i)
    (hle : ∀ D : M.FactorIndex → ℕ,
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal T)
        (fun i => c i * D i + E i))
    (hdim : (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S)).totalDegree =
      (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal T)).totalDegree)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    degreeValue K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      degreeValue K M.factorCount M.ambientDimension (M.vanishingIdeal T) (fun i => c i * D i) := by
  obtain ⟨P,hPd,hPlc,hPpos,NP,hP⟩ := exists_ray_hilbertPolynomial M hS D 0 hD
  obtain ⟨Q,hQd,hQlc,hQpos,NQ,hQ⟩ := exists_ray_hilbertPolynomial M hT (fun i => c i * D i) E
    (fun i => by have := hc i; have := hD i; nlinarith)
  have hlc : P.leadingCoeff ≤ Q.leadingCoeff := by
    apply leadingCoeff_le_of_eventual_eval_le P Q hPpos hQpos (by rw [hPd,hQd,hdim])
    apply eventually_atTop.mpr
    refine ⟨max NP NQ,fun n hn => ?_⟩
    rw [hP n ((le_max_left _ _).trans hn),hQ n ((le_max_right _ _).trans hn)]
    simpa only [Pi.zero_apply,add_zero,mul_assoc,Nat.cast_le] using hle (fun i => D i * n)
  rw [hPlc,hQlc] at hlc
  unfold degreeValue degreeForm
  simp only [MvPolynomial.smul_eq_C_mul,map_mul,eval_C]
  rw [hdim]
  exact mul_le_mul_of_nonneg_left (by simpa only [hdim] using hlc) (Nat.cast_nonneg _)

end PhilipponMultiplicity.Hilbert


namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

/-- Translation preserves the actual Hilbert dimension and satisfies the
degree bound from Lemma 4.5. This stronger form works for every subset. -/
theorem translated_dimension_and_degree (c : G.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hbound : TranslationDegreeBound G c)
    (g : G.Point) (V : Set G.Point) :
    varietyDimension G V = varietyDimension G (translate g V) ∧
    ∀ D : G.FactorIndex → ℕ, (∀ i, 1 ≤ D i) →
      hilbertDegreeForm G V D ≤
        hilbertDegreeForm G (translate g V) (fun i => c i * D i) := by
  classical
  by_cases hV : V.Nonempty
  · have hW : (translate g V).Nonempty := hV.image (fun x => g+x)
    have hS := hV.image G.embedding
    have hT := hW.image G.embedding
    have hback : translate (-g) (translate g V) = V := by
      ext x
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
        simpa only [← add_assoc,neg_add_cancel,zero_add] using hz
      · intro hx
        exact ⟨g+x,⟨x,hx,rfl⟩,by simp only [← add_assoc,neg_add_cancel,zero_add]⟩
    obtain ⟨atlas,ha⟩ := hbound g
    obtain ⟨atlas',ha'⟩ := hbound (-g)
    obtain ⟨E,hE⟩ := TranslationSupport.translated_hilbertFunction_le V g c atlas ha
    obtain ⟨E',hE'⟩ := TranslationSupport.translated_hilbertFunction_le (translate g V) (-g)
      c atlas' ha'
    rw [hback] at hE'
    have hd₁ := Hilbert.dimension_le_of_shifted_hilbertFunction_le G.ambient
      (G.embedding '' translate g V) (G.embedding '' V) hT hS c E hc hE
    have hd₂ := Hilbert.dimension_le_of_shifted_hilbertFunction_le G.ambient
      (G.embedding '' V) (G.embedding '' translate g V) hS hT c E' hc hE'
    have heq : varietyDimension G V = varietyDimension G (translate g V) :=
      le_antisymm hd₂ hd₁
    refine ⟨heq,fun D hD => ?_⟩
    have hdeg := Hilbert.degreeValue_le_of_shifted_hilbertFunction_le G.ambient
      (G.embedding '' V) (G.embedding '' translate g V) hS hT c E' hc hE' heq D hD
    change (Hilbert.degreeValue K G.ambient.factorCount G.ambient.ambientDimension
      (G.ambient.vanishingIdeal (G.embedding '' V)) D : ℝ) ≤
      (Hilbert.degreeValue K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (G.embedding '' translate g V)) (fun i => c i * D i) : ℝ)
    exact_mod_cast hdeg
  · have hV' : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hV
    subst V
    have hW : translate g (∅ : Set G.Point) = ∅ := Set.image_empty _
    have hzero : Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal ∅) = 0 := by
      change Hilbert.hilbertPolynomial K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (G.embedding '' ∅)) = 0
      rw [Set.image_empty]
      exact G.ambient.hilbertPolynomial_empty
    rw [hW]
    refine ⟨rfl,fun D hD => ?_⟩
    simp only [hilbertDegreeForm,Hilbert.degreeValue,Hilbert.degreeForm,hzero,
      map_zero,smul_zero,Rat.cast_zero,le_refl]


end PhilipponMultiplicity

end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (c : G.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hbound : TranslationDegreeBound G c)
    (g : G.Point) (V : GroupSubvariety G) :
    varietyDimension G V.carrier = varietyDimension G (PhilipponMultiplicity.translate g V.carrier) ∧
    ∀ D : G.FactorIndex → ℕ, (∀ i, 1 ≤ D i) →
      hilbertDegreeForm G V.carrier D ≤
        hilbertDegreeForm G (PhilipponMultiplicity.translate g V.carrier) (fun i => c i * D i) := by
  exact translated_dimension_and_degree G c hc hbound g V.carrier
