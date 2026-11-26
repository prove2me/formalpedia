-- Prove2me | solution 1 for Rank2Sha.tateShafarevich_isTorsion
-- status  : ACCEPTED   (prove)
-- author  : @barindersbanwait
-- created : 2026-11-26T14:26:28.329922+00:00
-- url     : https://prove2.me/submissions/f5f5cd8a-77f1-46fa-b846-1cb24c1a4a63

import Definitions.Def_Rank2Sha_TateShafarevich
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Torsion
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.LocallyConstant.Basic

/-
Ported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 6d810e58e90d,
Apache License 2.0).
-/

/-!
# Solution of `Rank2Sha.tateShafarevich_isTorsion`

Let `G` be a compact topological group and `X` a topological representation of `G` whose
underlying module is discrete. Every class in `continuousCohomology (n + 1) X` is killed by the
index of an open subgroup of `G`
(`TauCeti.ContinuousCohomology.exists_openSubgroup_index_nsmul_eq_zero`). The proof: a
homogeneous cocycle `f` is a continuous map from `G` to a discrete module, so it is locally
constant, and its right-translation stabilizer `U` is an open subgroup of finite index. The sum
of `f` over a transversal of `U` is a cochain of degree `n` whose coboundary is `[G : U] • f`.

For a number field `K`, `AlgebraicClosure K / K` is Galois, so `Field.absoluteGaloisGroup K` is
compact. The module of `W.galoisRepresentation` has the discrete topology by definition. Hence
`continuousCohomology 1 W.galoisRepresentation` is a torsion group, and so is its subgroup
`W.tateShafarevich`.
-/

-- TauCeti/Topology/CompactOpen.lean
/-- The compact-open topology on the continuous maps from a compact space to a discrete space is
discrete. -/
instance ContinuousMap.discreteTopology {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [DiscreteTopology Y] : DiscreteTopology C(X, Y) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro f
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have hset : ({f} : Set C(X, Y)) =
      ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨?_, fun h ↦ ContinuousMap.ext fun x ↦ h (f x) ⟨x, rfl⟩ rfl⟩
    rintro rfl _ _ _ hx
    exact hx
  rw [hset]
  exact hfin.isOpen_biInter fun y _ ↦ ContinuousMap.isOpen_setOfPred_mapsTo
    (isClosed_singleton.preimage f.continuous).isCompact (isOpen_discrete _)

-- TauCeti/Topology/LocallyConstant/Compact.lean
/-- A locally constant family is locally constant in its parameter, uniformly on a compact set. -/
theorem IsLocallyConstant.exists_isOpen_forall_mem_eq {X P A : Type*} [TopologicalSpace X]
    [TopologicalSpace P] {f : X × P → A} (hf : IsLocallyConstant f)
    {K : Set X} (hK : IsCompact K) (p₀ : P) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ ∀ p ∈ V, ∀ x ∈ K, f (x, p) = f (x, p₀) := by
  have hopen : IsOpen {q : X × P | f q = f (q.1, p₀)} :=
    (hf.prodMk (hf.comp_continuous (continuous_fst.prodMk continuous_const)))
      {a : A × A | a.1 = a.2}
  obtain ⟨u, v, -, hvopen, hKu, hv, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hopen fun q hq ↦ congrArg f (Prod.ext rfl hq.2)
  exact ⟨v, hvopen, hv rfl, fun p hp x hx ↦ huv (Set.mk_mem_prod (hKu hx) hp)⟩

-- TauCeti/Topology/Algebra/Group/LocallyConstant.lean
/-- For a locally constant `f` on a space with continuous multiplication and a compact set `K`,
a family of right translations `σ : P → G` continuous at `p₀` leaves `x ↦ f (x * σ p)` unchanged
on a neighbourhood of `p₀`, uniformly in `x ∈ K`. -/
theorem IsLocallyConstant.exists_isOpen_forall_mem_mul_right_eq {G : Type*} [Mul G]
    [TopologicalSpace G] [ContinuousMul G] {A : Type*}
    {f : G → A} (hf : IsLocallyConstant f) {K : Set G} (hK : IsCompact K) {P : Type*}
    [TopologicalSpace P] {σ : P → G} (p₀ : P) (hσ : ContinuousAt σ p₀) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ ∀ p ∈ V, ∀ x ∈ K, f (x * σ p) = f (x * σ p₀) := by
  obtain ⟨V, hVopen, hVσ, hV⟩ :=
    (hf.comp_continuous continuous_mul).exists_isOpen_forall_mem_eq hK (σ p₀)
  obtain ⟨W, hWV, hWopen, hWp₀⟩ :=
    mem_nhds_iff.mp (hσ.preimage_mem_nhds (hVopen.mem_nhds hVσ))
  exact ⟨W, hWopen, hWp₀, fun p hp x hx ↦ hV (σ p) (hWV hp) x hx⟩

-- TauCeti/Topology/Algebra/Group/LocallyConstant.lean
/-- On a compact space with continuous multiplication, a family of right translations continuous
at `p₀` leaves a locally constant `f` unchanged near `p₀`, uniformly in the translated point. -/
theorem IsLocallyConstant.exists_isOpen_forall_mul_right_eq {G : Type*} [Mul G]
    [TopologicalSpace G] [ContinuousMul G] {A : Type*} [CompactSpace G]
    {f : G → A} (hf : IsLocallyConstant f) {P : Type*} [TopologicalSpace P] {σ : P → G}
    (p₀ : P) (hσ : ContinuousAt σ p₀) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ ∀ p ∈ V, ∀ x : G, f (x * σ p) = f (x * σ p₀) := by
  simpa using exists_isOpen_forall_mem_mul_right_eq hf isCompact_univ p₀ hσ

namespace TauCeti

-- TauCeti/Topology/Algebra/Group/LocallyConstant.lean
/-- The right-translation stabilizer of `f : G → A`: the subgroup of those `g` with
`f (x * g) = f x` for every `x : G`. -/
def rightTranslationStabilizer {G : Type*} [Group G] {A : Type*} (f : G → A) : Subgroup G where
  carrier := {g | ∀ x : G, f (x * g) = f x}
  one_mem' x := by rw [mul_one]
  mul_mem' {g g'} hg hg' x := by rw [← mul_assoc, hg' (x * g), hg x]
  inv_mem' {g} hg x := by rw [← hg (x * g⁻¹), inv_mul_cancel_right]

-- TauCeti/Topology/Algebra/Group/LocallyConstant.lean
@[simp]
theorem mem_rightTranslationStabilizer {G : Type*} [Group G] {A : Type*} {f : G → A} {g : G} :
    g ∈ rightTranslationStabilizer f ↔ ∀ x : G, f (x * g) = f x := Iff.rfl

-- TauCeti/Topology/Algebra/Group/LocallyConstant.lean
/-- A locally constant function on a compact topological group has open right-translation
stabilizer. -/
theorem isOpen_rightTranslationStabilizer {G : Type*} [Group G] {A : Type*} [TopologicalSpace G]
    [ContinuousMul G] [CompactSpace G] {f : G → A} (hf : IsLocallyConstant f) :
    IsOpen (rightTranslationStabilizer f : Set G) := by
  obtain ⟨V, hVopen, hV1, hV⟩ :=
    hf.exists_isOpen_forall_mul_right_eq (1 : G) continuous_id.continuousAt
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hVopen.mem_nhds hV1)
    fun g hg x => ?_)
  simpa using hV g hg x

end TauCeti

-- TauCeti/GroupTheory/Coset/Basic.lean
/-- The chosen representative of the translate `g • q` of a left coset `q` lies in the same coset
as `g` times the chosen representative of `q`. -/
theorem QuotientGroup.mk_out_smul {G : Type*} [Group G] {H : Subgroup G} (g : G) (q : G ⧸ H) :
    ((g • q).out : G ⧸ H) = (g * q.out : G) := by
  simp [← smul_eq_mul]

-- TauCeti/RepresentationTheory/Continuous/Coinduced.lean
/-- Let `f : C(G, V)` be invariant for the coinduced representation `π.coind₁` and invariant
under right translation by a finite-index subgroup `U`. Then the sum of `f` over the transversal
of `U` given by `Quotient.out` is invariant for `π`. -/
theorem ContRepresentation.sum_apply_out_mem_invariants {R G V : Type*} [Ring R]
    [TopologicalSpace R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module R V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul R V] {π : ContRepresentation R G V} {f : C(G, V)}
    (hf : f ∈ π.coind₁.invariants) {U : Subgroup G} [Fintype (G ⧸ U)]
    (hU : U ≤ TauCeti.rightTranslationStabilizer f) :
    ∑ q : G ⧸ U, f q.out ∈ π.invariants := by
  intro g
  rw [map_sum]
  refine Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ fun q => ?_
  have hπ : π g (f q.out) = f (g * q.out) := by
    simpa only [ContRepresentation.coind₁_apply_apply, inv_mul_cancel_left]
      using DFunLike.congr_fun (hf g) (g * q.out)
  obtain ⟨u, hu⟩ : ∃ u : U, g * q.out * u = (g • q).out :=
    ⟨⟨(g * q.out)⁻¹ * (g • q).out, QuotientGroup.eq.mp (QuotientGroup.mk_out_smul g q).symm⟩,
      by simp [mul_assoc]⟩
  rw [hπ, ← hu]
  exact ((TauCeti.mem_rightTranslationStabilizer.mp (hU u.property)) (g * q.out)).symm

-- TauCeti/RepresentationTheory/Homological/ContCohomology/CompactDiscrete.lean
/-- Every term of the coinduced resolution of a discrete representation of a compact group is
discrete. -/
instance TauCeti.discreteTopology_resolutionX {k G : Type*} [Ring k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (X : TopRep k G)
    [DiscreteTopology X.V] (n : ℕ) : DiscreteTopology (TopRep.resolutionX X n).V := by
  induction n with
  | zero => exact ‹DiscreteTopology X.V›
  | succ n ih => exact inferInstanceAs (DiscreteTopology C(G, (TopRep.resolutionX X n).V))

-- TauCeti/RepresentationTheory/Homological/ContCohomology/Resolution/Basic.lean
/-- For `F : C(G, Xₘ)` in degree `m + 1` of the coinduced resolution and finitely many points
`σ i` of `G`, `dₘ (∑ᵢ F (σ i)) + ∑ᵢ (dₘ₊₁ F) (σ i) = |ι| • F`. -/
theorem TopRep.d_sum_apply_add_sum_d_apply {k G : Type*} [Ring k] [TopologicalSpace k] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) {ι : Type*} [Fintype ι]
    (σ : ι → G) (m : ℕ) (F : (resolutionX X (m + 1)).V) :
    (d X m).hom (∑ i, (F : C(G, (resolutionX X m).V)) (σ i)) +
      ∑ i, ((d X (m + 1)).hom F : C(G, (resolutionX X (m + 1)).V)) (σ i) =
        Fintype.card ι • F := by
  rw [map_sum, ← Finset.sum_add_distrib]
  simp [hom_d_succ, ContIntertwiningMap.sub_apply]

namespace CategoryTheory.ShortComplex

-- TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean
/-- The homology of a short complex of topological modules is the cokernel of `S.toCycles`,
carrying the quotient topology. -/
noncomputable def homologyIsoCoker {R : Type*} [Ring R] [TopologicalSpace R]
    (S : ShortComplex (TopModuleCat R)) : S.homology ≅ TopModuleCat.coker S.toCycles :=
  Limits.IsColimit.coconePointUniqueUpToIso S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles)

-- TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean
/-- `homologyIsoCoker` identifies `S.homologyπ` with `TopModuleCat.cokerπ`. -/
@[reassoc (attr := simp)]
theorem homologyπ_comp_homologyIsoCoker_hom {R : Type*} [Ring R] [TopologicalSpace R]
    (S : ShortComplex (TopModuleCat R)) :
    S.homologyπ ≫ (homologyIsoCoker S).hom = TopModuleCat.cokerπ S.toCycles :=
  Limits.IsColimit.comp_coconePointUniqueUpToIso_hom S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles) Limits.WalkingParallelPair.one

-- TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean
/-- The projection onto the concrete cokernel, followed back into homology, is `S.homologyπ`. -/
@[reassoc (attr := simp)]
theorem cokerπ_comp_homologyIsoCoker_inv {R : Type*} [Ring R] [TopologicalSpace R]
    (S : ShortComplex (TopModuleCat R)) :
    TopModuleCat.cokerπ S.toCycles ≫ (homologyIsoCoker S).inv = S.homologyπ :=
  Limits.IsColimit.comp_coconePointUniqueUpToIso_inv S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles) Limits.WalkingParallelPair.one

-- TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean
/-- The class map onto the homology of a short complex of topological modules is surjective. -/
theorem homologyπ_surjective {R : Type*} [Ring R] [TopologicalSpace R]
    (S : ShortComplex (TopModuleCat R)) : Function.Surjective S.homologyπ.hom := by
  intro x
  obtain ⟨y, hy⟩ := TopModuleCat.cokerπ_surjective S.toCycles ((homologyIsoCoker S).hom x)
  refine ⟨y, ?_⟩
  have h := ConcreteCategory.congr_hom (cokerπ_comp_homologyIsoCoker_inv S) y
  simp only [ConcreteCategory.comp_apply] at h
  change S.homologyπ y = x
  rw [← h, hy, Iso.hom_inv_id_apply]

-- TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean
/-- A cycle of a short complex of topological modules has trivial homology class exactly when it
is a boundary. -/
theorem homologyπ_eq_zero_iff {R : Type*} [Ring R] [TopologicalSpace R]
    (S : ShortComplex (TopModuleCat R)) {x : S.cycles} :
    S.homologyπ x = 0 ↔ x ∈ Set.range S.toCycles.hom := by
  rw [← (homologyIsoCoker S).toContinuousLinearEquiv.map_eq_zero_iff]
  have h := ConcreteCategory.congr_hom (homologyπ_comp_homologyIsoCoker_hom S) x
  simp only [ConcreteCategory.comp_apply] at h
  change (homologyIsoCoker S).hom (S.homologyπ x) = 0 ↔ _
  rw [h, TopModuleCat.hom_cokerπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range

-- TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean
/-- The inclusion of the cycles of a short complex of topological modules into its middle term is
injective. -/
theorem iCycles_injective {R : Type*} [Ring R] [TopologicalSpace R]
    (S : ShortComplex (TopModuleCat R)) : Function.Injective S.iCycles.hom :=
  ConcreteCategory.injective_of_mono_of_preservesPullback
    ((forget₂ (TopModuleCat R) TopCat).map S.iCycles)

end CategoryTheory.ShortComplex

namespace HomologicalComplex

open CategoryTheory

-- TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean
/-- The class map onto the degreewise homology of a homological complex of topological modules is
surjective. -/
theorem homologyπ_surjective {R : Type*} [Ring R] [TopologicalSpace R] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex (TopModuleCat R) c) (n : ι) [K.HasHomology n] :
    Function.Surjective (K.homologyπ n).hom :=
  ShortComplex.homologyπ_surjective (K.sc n)

-- TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean
/-- A cycle of a homological complex of topological modules has trivial homology class exactly
when it is a boundary, `m` being the degree preceding `n`. -/
theorem homologyπ_eq_zero_iff {R : Type*} [Ring R] [TopologicalSpace R] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex (TopModuleCat R) c) (n : ι) [K.HasHomology n]
    {m : ι} (hm : c.prev n = m) {x : K.cycles n} :
    K.homologyπ n x = 0 ↔ x ∈ Set.range (K.toCycles m n).hom := by
  subst hm
  exact ShortComplex.homologyπ_eq_zero_iff (K.sc n)

-- TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean
/-- The inclusion of the degree-`n` cycles of a homological complex of topological modules into
its degree-`n` term is injective. -/
theorem iCycles_injective {R : Type*} [Ring R] [TopologicalSpace R] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex (TopModuleCat R) c) (n : ι) :
    Function.Injective (K.iCycles n).hom :=
  ShortComplex.iCycles_injective (K.sc n)

end HomologicalComplex

namespace TauCeti.ContinuousCohomology

open CategoryTheory TopRep _root_.ContinuousCohomology

-- TauCeti/RepresentationTheory/Homological/ContCohomology/Torsion.lean
/-- Over a compact group, every class of `Hⁿ⁺¹(G, X)` for a discrete representation `X` is
annihilated by the index `[G : U]` of some open subgroup `U`. -/
theorem exists_openSubgroup_index_nsmul_eq_zero {k G : Type*} [Ring k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {X : TopRep k G}
    [DiscreteTopology X.V] (n : ℕ) (x : continuousCohomology (n + 1) X) :
    ∃ U : OpenSubgroup G, (U : Subgroup G).index • x = 0 := by
  set K := homogeneousCochains X
  obtain ⟨z, rfl⟩ := K.homologyπ_surjective (n + 1) x
  set c := K.iCycles (n + 1) z
  set f : C(G, (resolutionX X (n + 1)).V) := c.val
  have hf : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 f.continuous
  let U : OpenSubgroup G := ⟨rightTranslationStabilizer f, isOpen_rightTranslationStabilizer hf⟩
  have : Finite (G ⧸ (U : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  let : Fintype (G ⧸ (U : Subgroup G)) := Fintype.ofFinite _
  refine ⟨U, ?_⟩
  have hcocycle : (d X (n + 2)).hom f = 0 := by
    have h := ConcreteCategory.congr_hom (K.iCycles_d (n + 1) (n + 2)) z
    simp only [ConcreteCategory.comp_apply] at h
    exact (homogeneousCochains.d_apply X (n + 1) c).symm.trans (congrArg Subtype.val h)
  let b : K.X n := ⟨∑ q : G ⧸ (U : Subgroup G), f q.out,
    ContRepresentation.sum_apply_out_mem_invariants c.property le_rfl⟩
  have hb : K.toCycles n (n + 1) b = (U : Subgroup G).index • z := by
    refine K.iCycles_injective (n + 1) (Subtype.ext ?_)
    have h := ConcreteCategory.congr_hom (K.toCycles_i n (n + 1)) b
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, map_nsmul, homogeneousCochains.d_apply]
    have hsum := d_sum_apply_add_sum_d_apply X (fun q : G ⧸ (U : Subgroup G) => (q.out : G))
      (n + 1) f
    simp only [hcocycle, ContinuousMap.zero_apply, Finset.sum_const_zero, add_zero] at hsum
    rw [Subgroup.index, Nat.card_eq_fintype_card]
    exact hsum
  rw [← map_nsmul, ← hb]
  exact (K.homologyπ_eq_zero_iff (n + 1) (by simp)).2 ⟨b, rfl⟩

-- TauCeti/RepresentationTheory/Homological/ContCohomology/Torsion.lean
/-- Over a compact group, `Hⁿ⁺¹(G, X)` is a torsion group for every discrete representation
`X`. -/
theorem isAddTorsion_continuousCohomology {k G : Type*} [Ring k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {X : TopRep k G}
    [DiscreteTopology X.V] (n : ℕ) :
    IsAddTorsion (continuousCohomology (n + 1) X) := fun x => by
  obtain ⟨U, hU⟩ := exists_openSubgroup_index_nsmul_eq_zero n x
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨_, Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite), hU⟩

end TauCeti.ContinuousCohomology

namespace Sol.Rank2Sha

/-- The underlying module of `W.galoisRepresentation` carries the discrete topology. -/
theorem discreteTopology_galoisRepresentation {K : Type*} [Field K]
    (W : WeierstrassCurve.Affine K) : DiscreteTopology W.galoisRepresentation.V :=
  ⟨rfl⟩

/-- For a number field `K`, the absolute Galois group of `K` is compact. `K` is perfect, so
`AlgebraicClosure K / K` is a Galois extension, and Mathlib gives compactness of the Galois group
of a Galois extension. -/
theorem compactSpace_absoluteGaloisGroup {K : Type*} [Field K] [NumberField K] :
    CompactSpace (Field.absoluteGaloisGroup K) :=
  inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))

/-- For a Weierstrass curve `W` over a number field `K`, the first continuous cohomology group of
the absolute Galois group of `K` with coefficients in `W.galoisRepresentation` is a torsion
group. -/
theorem isAddTorsion_continuousCohomology_one_galoisRepresentation {K : Type*} [Field K]
    [NumberField K] (W : WeierstrassCurve.Affine K) :
    IsAddTorsion (continuousCohomology 1 W.galoisRepresentation) :=
  have := discreteTopology_galoisRepresentation W
  have := compactSpace_absoluteGaloisGroup (K := K)
  TauCeti.ContinuousCohomology.isAddTorsion_continuousCohomology (X := W.galoisRepresentation) 0

end Sol.Rank2Sha

/-- The Shafarevich--Tate group of a Weierstrass curve over a number field is a torsion
group. -/
theorem solution {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve.Affine K) : IsAddTorsion W.tateShafarevich :=
  (Sol.Rank2Sha.isAddTorsion_continuousCohomology_one_galoisRepresentation W).addSubgroup _
