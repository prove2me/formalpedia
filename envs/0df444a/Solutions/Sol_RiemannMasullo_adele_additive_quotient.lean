-- Prove2me | solution 1 for RiemannMasullo.adele_additive_quotient
-- status  : ACCEPTED   (prove)
-- author  : @koffie
-- created : 2026-11-20T23:16:44.692907+00:00
-- url     : https://prove2.me/submissions/304b65cc-cdf0-44cc-9798-9702b2e6f3de

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/9d5c8b94a1f1b5d8f903f1b04d1e043877e7bb15/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L266-L809
-- Ported to Mathlib 0df444a: helper `qmap_injective`, the archimedean completion map via
-- `UniformSpace.Completion.mapRingHom`, and finiteness of non-integral places.
import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions
import Definitions.Def_RiemannMasullo_IntegralAdeleDiagonal
import Definitions.Def_RiemannMasullo_AdicCompletionNorm
import Theorems.Thm_RiemannMasullo_diagonal_mem_integralAdelesOutside
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion

noncomputable section

namespace RiemannMasullo

open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "AQuot(" F ")" => 𝔸[F] ⧸ AdeleRing.principalSubgroup (𝓞 F) F

local notation "IQuot(" F ", " S ")" =>
  (integralAdelesOutside F S) ⧸ AddMonoidHom.range (RingHom.toAddMonoidHom (integralAdeleDiagonal F S))


/-- Injectivity of an induced map of quotients when the preimage of the target subgroup is
contained in the source subgroup. -/
private theorem qmap_injective {G H : Type*} [AddGroup G] [AddGroup H] (N : AddSubgroup G)
    [N.Normal] (M : AddSubgroup H) [M.Normal] (f : G →+ H) (h : N ≤ M.comap f)
    (h' : M.comap f ≤ N) : Function.Injective (QuotientAddGroup.map N M f h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hx
    exact (QuotientAddGroup.eq_zero_iff a).2 (h' hx)

section AdeleAdditiveQuotient

local notation "Principal(" F ")" => AdeleRing.principalSubgroup (𝓞 F) F
local notation "Integral(" F ")" => integralAdelesOutside F ∅
local notation "IntegralPrincipal(" F ")" =>
  AddMonoidHom.range (RingHom.toAddMonoidHom (integralAdeleDiagonal F ∅))

/-- Integrality in the empty-exception model is coordinatewise integrality. -/
private theorem mem_integralAdeles_iff (a : 𝔸[F]) :
    a ∈ Integral(F) ↔ ∀ v : Primes(F), a.2 v ∈ v.adicCompletionIntegers F := by
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true, true_implies]
  rfl

/-- The integral adele model is open in the full ring of adeles. -/
private theorem isOpen_integralAdeles : IsOpen (Integral(F) : Set 𝔸[F]) := by
  have h : (Integral(F) : Set 𝔸[F]) =
      Prod.snd ⁻¹' {a : 𝔸ᶠ[𝓞 F, F] | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    Set.ext (mem_integralAdeles_iff F)
  rw [h]
  exact (RestrictedProduct.isOpen_forall_mem (fun v : Primes(F) ↦
    Valued.isOpen_integer (v.adicCompletion F))).preimage continuous_snd

/-- The archimedean adele ring and the mixed space have the same product topology. -/
private def infiniteAdeleMixedHomeomorph : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F := by
  classical
  refine ((Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F ↦ v.IsReal)
    (fun v ↦ v.Completion))).trans ?_
  exact (Homeomorph.piCongrRight fun v ↦
    (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph).prodCongr
      ((Homeomorph.piCongrRight fun v ↦ (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) <|
          Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))

/-- Paper: Lemma A.1.2.1, p. 540. The principal adeles are discrete, since the integral
ones project to the integer lattice in the archimedean factor. -/
private theorem isDiscrete_principalAdeles : IsDiscrete (Principal(F) : Set 𝔸[F]) := by
  let e := infiniteAdeleMixedHomeomorph F
  have hL : IsOpen ({0} : Set (mixedEmbedding.integerLattice F)) := isOpen_discrete _
  obtain ⟨U, hU, hzero⟩ := isOpen_induced_iff.mp hL
  have hzero_mem : (0 : mixedEmbedding.mixedSpace F) ∈ U := by
    have hz : (0 : mixedEmbedding.integerLattice F) ∈ ({0} : Set (mixedEmbedding.integerLattice F)) :=
      Set.mem_singleton _
    rw [← hzero] at hz
    exact hz
  apply isDiscrete_iff_discreteTopology.mpr
  change DiscreteTopology (Principal(F))
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  refine isOpen_induced_iff.mpr ⟨(Integral(F) : Set 𝔸[F]) ∩
    (e ∘ Prod.fst) ⁻¹' U, (isOpen_integralAdeles F).inter
      (hU.preimage (e.continuous.comp continuous_fst)), ?_⟩
  ext a
  constructor
  · rintro ⟨ha, hU'⟩
    obtain ⟨x, hx⟩ := a.property
    have hxInt := (diagonal_mem_integralAdelesOutside F ∅ x).mp (hx ▸ ha)
    simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot] at hxInt
    obtain ⟨r, rfl⟩ := hxInt
    have hr : mixedEmbedding F (algebraMap (𝓞 F) F r) ∈ mixedEmbedding.integerLattice F :=
      ⟨r, rfl⟩
    have he : e (algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r)) =
        mixedEmbedding F (algebraMap (𝓞 F) F r) :=
      (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm
    have hm : (⟨_, hr⟩ : mixedEmbedding.integerLattice F) ∈ ({0} : Set _) := by
      rw [← hzero]
      change mixedEmbedding F (algebraMap (𝓞 F) F r) ∈ U
      rw [← he]
      change e (algebraMap F 𝔸[F] (algebraMap (𝓞 F) F r)).1 ∈ U
      rw [hx]
      exact hU'
    have hr0 : algebraMap (𝓞 F) F r = 0 :=
      (mixedEmbedding F).injective (by simpa using congrArg Subtype.val (Set.mem_singleton_iff.mp hm))
    exact Set.mem_singleton_iff.mpr (Subtype.ext (by simpa [hr0] using hx.symm))
  · rintro ha
    have ha' := Set.mem_singleton_iff.mp ha
    subst a
    refine ⟨(Integral(F)).zero_mem, ?_⟩
    change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 ∈ U
    rwa [map_zero]

/-- Every adelic class has a representative integral at all finite places. -/
private theorem exists_sub_diagonal_mem_integralAdeles (a : 𝔸[F]) :
    ∃ x : F, a - algebraMap F 𝔸[F] x ∈ Integral(F) := by
  classical
  have hbad : {v : Primes(F) | 1 < Valued.v (a.2 v)}.Finite := by
    have h := a.2.2
    rw [Filter.eventually_cofinite] at h
    refine h.subset fun v hv hmem => ?_
    exact absurd ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 hmem) (not_le.2 hv)
  let bad := hbad.toFinset
  have hlocal (v : Primes(F)) : ∃ x : F,
      Valued.v (a.2 v - (x : v.adicCompletion F)) ≤ 1 := by
    let U := (fun y : v.adicCompletion F ↦ a.2 v - y) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    have hU : IsOpen U :=
      (Valued.isOpen_integer _).preimage (continuous_const.sub continuous_id)
    have ha : a.2 v ∈ U := by
      change Valued.v (a.2 v - a.2 v) ≤ 1
      simp
    exact (v.denseRange_algebraMap F).mem_nhds (hU.mem_nhds ha)
  choose y hy using hlocal
  let x : Primes(F) → F := fun v ↦ if v ∈ bad then y v else 0
  have hx (v : Primes(F)) : Valued.v (a.2 v - (x v : v.adicCompletion F)) ≤ 1 := by
    by_cases hv : v ∈ bad
    · simpa only [x, if_pos hv] using hy v
    · have hnv : ¬ 1 < Valued.v (a.2 v) := by simpa [bad] using hv
      simpa only [x, if_neg hv, HeightOneSpectrum.adicCompletion.coe_zero, sub_zero] using
        le_of_not_gt hnv
  -- Clear the denominators of the local representatives at the finitely many bad places.
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F)) bad x
  have hd₀ : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hnum (v : Primes(F)) : ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * x v := by
    by_cases hv : v ∈ bad
    · simpa only [IsLocalization.IsInteger, RingHom.mem_rangeS, Algebra.smul_def] using hd v hv
    · exact ⟨0, by simp [x, hv]⟩
  choose r hr using hnum
  let I : Ideal (𝓞 F) := Ideal.span {(d : 𝓞 F)}
  have hI : I ≠ ⊥ := by simp [I, hd₀]
  have hS : {v : Primes(F) | v.asIdeal ∣ I}.Finite := Ideal.finite_factors hI
  let S := hS.toFinset
  let m := fun v : Primes(F) ↦ multiplicity v.asIdeal I
  -- Match the resulting numerators modulo the prime powers dividing the common denominator.
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    HeightOneSpectrum.asIdeal m (fun v _ ↦ v.prime)
    (fun _ _ _ _ h ↦ fun he ↦ h (HeightOneSpectrum.ext he)) (fun v ↦ r v)
  have hb' (v : Primes(F)) : v.intValuation (b - r v) ≤ v.intValuation d := by
    by_cases hv : v ∈ S
    · rw [v.intValuation_eq_exp_neg_multiplicity hd₀, v.intValuation_le_pow_iff_mem]
      exact hb v hv
    · have hn : ¬ v.asIdeal ∣ I := by simpa [S] using hv
      have hd' : v.intValuation (d : 𝓞 F) = 1 :=
        HeightOneSpectrum.intValuation_eq_one_iff.mpr (mt Ideal.dvd_span_singleton.mpr hn)
      rw [hd']
      exact v.intValuation_le_one _
  let D := algebraMap (𝓞 F) F d
  let z := algebraMap (𝓞 F) F b / D
  refine ⟨z, (mem_integralAdeles_iff F _).mpr fun v ↦ ?_⟩
  have hD : D ≠ 0 := (RingOfIntegers.coe_ne_zero_iff (K := F)).mpr hd₀
  have hz : v.valuation F (x v - z) ≤ 1 := by
    rw [(v.valuation F).map_sub_swap, div_sub', ← hr v, ← map_sub, Valuation.map_div,
      v.valuation_of_algebraMap, v.valuation_of_algebraMap]
    · exact div_le_one_of_le₀ (hb' v) zero_le
    · exact hD
  change Valued.v (a.2 v - (z : v.adicCompletion F)) ≤ 1
  rw [← sub_add_sub_cancel (a.2 v) (x v : v.adicCompletion F) (z : v.adicCompletion F)]
  apply (Valued.v : Valuation (v.adicCompletion F) _).map_add_le (hx v)
  change Valued.v (algebraMap F (v.adicCompletion F) (x v) -
    algebraMap F (v.adicCompletion F) z) ≤ 1
  rw [← map_sub]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) _).trans_le hz

/-- Paper: Lemma A.1.2.1, p. 541. Inclusion of the open integral adele model induces a
topological additive isomorphism on taking the quotient by principal adeles. -/
private theorem integralAdeleQuotient_equiv :
    ∃ e : IQuot(F, ∅) ≃ₜ+ AQuot(F), ∀ x,
      e (QuotientAddGroup.mk' (IntegralPrincipal(F)) x) =
        QuotientAddGroup.mk' (Principal(F)) x.val := by
  let i := (Integral(F)).subtype.toAddMonoidHom
  let P := Principal(F)
  let P₀ := IntegralPrincipal(F)
  have hP : P.comap i = P₀ := by
    ext a
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨⟨x, (diagonal_mem_integralAdelesOutside F ∅ x).mp (hx ▸ a.property)⟩,
        Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  let e₀ := QuotientAddGroup.map P₀ P i hP.ge
  have hs : Surjective (QuotientAddGroup.mk ∘ i : Integral(F) → AQuot(F)) := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨x, hx⟩ := exists_sub_diagonal_mem_integralAdeles F a
      refine ⟨⟨_, hx⟩, QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
      change a - algebraMap F 𝔸[F] x - a ∈ P
      rw [sub_right_comm, sub_self, zero_sub, ← map_neg]
      exact ⟨-x, rfl⟩
  let e := AddEquiv.ofBijective e₀ ⟨qmap_injective P₀ P i _ hP.le,
    QuotientAddGroup.map_surjective_of_surjective P₀ P i hs _⟩
  have hq := QuotientAddGroup.isOpenQuotientMap_mk (N := P)
  have hq₀ := QuotientAddGroup.isOpenQuotientMap_mk (N := P₀)
  have hc : Continuous e := hq₀.continuous_comp_iff.mp
    (hq.continuous.comp continuous_subtype_val)
  have ho : IsOpenMap e := hq₀.isOpenMap_iff.mpr
    (hq.isOpenMap.comp (isOpen_integralAdeles F).isOpenMap_subtype_val)
  exact ⟨ContinuousAddEquiv.mk' (e.toEquiv.toHomeomorphOfContinuousOpen hc ho) e.map_add,
    fun _ ↦ rfl⟩

/-- Paper: Lemma A.1.2.1, p. 541. Positive integer multiplication on the quotient is
invertible, since it is invertible on both the adeles and the principal adeles. -/
private theorem adeleQuotient_nsmul_bijective (n : ℕ) (hn : 0 < n) :
    Bijective (fun x : AQuot(F) ↦ n • x) := by
  let P := Principal(F)
  let d := algebraMap F 𝔸[F]
  let q := QuotientAddGroup.mk' P
  have hn' : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmul (a : 𝔸[F]) : n • (d (n : F)⁻¹ * a) = a := by
    rw [nsmul_eq_mul, ← map_natCast d, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn', map_one,
      one_mul]
  constructor
  · intro a b hab
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      induction b using QuotientAddGroup.induction_on with
      | H b =>
        change n • q a = n • q b at hab
        rw [← map_nsmul, ← map_nsmul] at hab
        obtain ⟨x, hx⟩ := QuotientAddGroup.eq_iff_sub_mem.mp hab
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        refine ⟨(n : F)⁻¹ * x, ?_⟩
        rw [map_mul, hx, ← nsmul_sub, nsmul_eq_mul, ← map_natCast d, ← mul_assoc, ← map_mul,
          inv_mul_cancel₀ hn', map_one, one_mul]
  · intro a
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      refine ⟨q (d (n : F)⁻¹ * a), ?_⟩
      change n • q (d (n : F)⁻¹ * a) = q a
      rw [← map_nsmul, hmul]

open scoped Valued in
/-- The local integer rings form a compact subset of the finite adeles. -/
private theorem isCompact_integralFiniteAdeles :
    IsCompact {a : 𝔸ᶠ[𝓞 F, F] | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  let K := fun v : Primes(F) ↦ v.adicCompletion F
  let O := fun v : Primes(F) ↦ (v.adicCompletionIntegers F : Set (K v))
  have (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) := by
    have : LocallyCompactSpace (K v) := locallyCompactSpace_adicCompletion v
    exact (Valued.integer.properSpace_iff_compactSpace_integer (K := K v)
      (Γ₀ := WithZero (Multiplicative ℤ))).mp
        (.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _)
  let j : (∀ v : Primes(F), v.adicCompletionIntegers F) → Πʳ v, [K v, O v]_[𝓟 Set.univ] :=
    fun x ↦ ⟨fun v ↦ x v, Eventually.of_forall fun v ↦ (x v).property⟩
  let i := RestrictedProduct.inclusion K O
    (show cofinite ≤ 𝓟 (Set.univ : Set (Primes(F))) by simp)
  have hj : Continuous j := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi fun v ↦ continuous_subtype_val.comp (continuous_apply v))
  have hc := isCompact_range ((RestrictedProduct.continuous_inclusion _).comp hj :
    Continuous (i ∘ j))
  have h : Set.range (i ∘ j) =
      {a : 𝔸ᶠ[𝓞 F, F] | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
    apply Set.ext
    intro a
    exact ⟨fun ⟨x, hx⟩ v ↦ hx ▸ (x v).property,
      fun ha ↦ ⟨fun v ↦ ⟨a v, ha v⟩, rfl⟩⟩
  rwa [← h]

/-- Paper: Lemma A.1.2.1, p. 540. The adelic quotient is covered by the product of an
archimedean lattice parallelepiped and the compact local integer rings. -/
private theorem compactSpace_adeleQuotient : CompactSpace (AQuot(F)) := by
  classical
  let e := infiniteAdeleMixedHomeomorph F
  let B := mixedEmbedding.latticeBasis F
  let q := QuotientAddGroup.mk' (Principal(F))
  let C : Set 𝔸[F] := (e.symm '' (B.parallelepiped : Set (mixedEmbedding.mixedSpace F))) ×ˢ
    {a : 𝔸ᶠ[𝓞 F, F] | ∀ v, a v ∈ v.adicCompletionIntegers F}
  have hc : IsCompact C :=
    (B.parallelepiped.isCompact.image e.symm.continuous).prod (isCompact_integralFiniteAdeles F)
  have hq : q '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨x, hx⟩ := exists_sub_diagonal_mem_integralAdeles F a
      let a' := a - algebraMap F 𝔸[F] x
      obtain ⟨z, hz, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (e a'.1)
      have hz' := (mixedEmbedding.mem_span_latticeBasis F).mp z.property
      obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, mixedEmbedding F (algebraMap (𝓞 F) F r) = z.val := hz'
      let d := algebraMap F 𝔸[F] (algebraMap (𝓞 F) F r)
      refine ⟨a' + d, ⟨?_, ?_⟩, QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
      · refine ⟨e (a' + d).1, ?_, e.symm_apply_apply _⟩
        apply ZSpan.fundamentalDomain_subset_parallelepiped B
        change _ + (InfiniteAdeleRing.ringEquiv_mixedSpace F) (a'.1) ∈ _ at hz
        change InfiniteAdeleRing.ringEquiv_mixedSpace F (a'.1 + d.1) ∈ _
        rw [map_add, show d.1 = algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r) from rfl,
          ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hr, add_comm]
        exact hz
      · have hd : d ∈ Integral(F) := by
          apply (diagonal_mem_integralAdelesOutside F ∅ _).mpr
          simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot]
          exact ⟨r, rfl⟩
        exact (mem_integralAdeles_iff F _).mp ((Integral(F)).add_mem hx hd)
      · change a - algebraMap F 𝔸[F] x + d - a ∈ Principal(F)
        refine ⟨algebraMap (𝓞 F) F r - x, ?_⟩
        rw [map_sub]
        change d - _ = _
        abel
  rw [← isCompact_univ_iff, ← hq]
  exact hc.image QuotientAddGroup.continuous_mk

section AdeleExtension

variable {L : Type*} [Field L] [NumberField L]

/-- The map on archimedean completions is obtained by completing the isometric field embedding
for the absolute value pulled back from the target place. -/
private theorem exists_infiniteAdeleLocalMap (σ : F →+* L) (w : InfinitePlace L) :
    ∃ f : (w.comap σ).Completion →+* w.Completion, Continuous f ∧
      ∀ x : F, f (x : (w.comap σ).Completion) = (σ x : w.Completion) := by
  let g : WithAbs (w.comap σ).1 →+* WithAbs w.1 :=
    (WithAbs.equiv w.1).symm.toRingHom.comp (σ.comp (WithAbs.equiv (w.comap σ).1).toRingHom)
  have hg : Isometry g := by
    refine AddMonoidHomClass.isometry_of_norm g fun x => ?_
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
    rfl
  let m := UniformSpace.Completion.mapRingHom g hg.continuous
  refine ⟨(InfinitePlace.Completion.equiv w).symm.toRingHom.comp
    (m.comp (InfinitePlace.Completion.equiv (w.comap σ)).toRingHom), ?_, fun x => ?_⟩
  · exact (InfinitePlace.Completion.continuous_ofCompletion w).comp
      (UniformSpace.Completion.continuous_map.comp
        (InfinitePlace.Completion.continuous_toCompletion _))
  · show InfinitePlace.Completion.ofCompletion
      (m ((WithAbs.toAbs (w.comap σ).1 x : WithAbs (w.comap σ).1) : (w.comap σ).1.Completion)) = _
    rw [UniformSpace.Completion.mapRingHom_coe]
    rfl

/-- The map on adic completions is obtained from the uniformly continuous field embedding at
a pair of places related by contraction. It sends local integers to local integers. -/
private theorem exists_finiteAdeleLocalMap [Algebra F L] (w : Primes(L)) :
    let v := w.under (𝓞 F)
    ∃ f : v.adicCompletion F →+* w.adicCompletion L, Continuous f ∧
      (∀ x : F, f (algebraMap F (v.adicCompletion F) x) =
        algebraMap L (w.adicCompletion L) (algebraMap F L x)) ∧
      Set.MapsTo f (v.adicCompletionIntegers F) (w.adicCompletionIntegers L) := by
  dsimp only
  let v := w.under (𝓞 F)
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  let g := algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation L))
  have hg := v.uniformContinuous_algebraMap_liesOver F L w
  let e := UniformSpace.Completion.mapRingHom g hg.continuous
  let f := (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (e.comp (HeightOneSpectrum.adicCompletion.equiv F v).toRingHom)
  have hf : Continuous f := (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion F v))
  have hd (x : F) : f (algebraMap F (v.adicCompletion F) x) =
      algebraMap L (w.adicCompletion L) (algebraMap F L x) := by
    apply (HeightOneSpectrum.adicCompletion.equiv L w).injective
    exact UniformSpace.Completion.mapRingHom_coe hg.continuous ((WithVal.equiv _).symm x)
  refine ⟨f, hf, hd, ?_⟩
  intro x
  refine (v.denseRange_algebraMap F).induction_on x ?_ ?_
  · convert (Valued.isOpen_integer (v.adicCompletion F)).isClosed_compl.union
      ((Valued.isClosed_integer (w.adicCompletion L)).preimage hf) using 1
    exact Set.ext fun _ ↦ imp_iff_not_or
  · intro y hy
    rw [hd]
    change Valued.v ((algebraMap F L y : L) : w.adicCompletion L) ≤ 1
    change Valued.v (y : v.adicCompletion F) ≤ 1 at hy
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hy ⊢
    rw [← v.valuation_liesOver L w]
    exact pow_le_one₀ zero_le hy

/-- Contraction of finite places along an extension of number fields has finite fibers. -/
private theorem tendsto_cofinite_finitePlace_under [Algebra F L] :
    Tendsto (HeightOneSpectrum.under (𝓞 F) : Primes(L) → Primes(F)) cofinite cofinite := by
  apply Tendsto.cofinite_of_finite_preimage_singleton
  intro v
  apply Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
    (hi := HeightOneSpectrum.asIdeal_injective.injOn)
  apply (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).subset
  rintro _ ⟨w, hw, rfl⟩
  have hv : w.under (𝓞 F) = v := Set.mem_singleton_iff.mp hw
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal hv.symm⟩⟩

/-- Paper: Lemma A.1.2.1, p. 541. The local completion embeddings assemble into a
continuous adelic extension that preserves integrality at the finite places. -/
private theorem exists_integralAdeleExtension (σ : F →+* L) :
    ∃ f : 𝔸[F] →+* 𝔸[L], IsAdeleExtension F σ f ∧
      Set.MapsTo f (Integral(F) : Set 𝔸[F]) (Integral(L) : Set 𝔸[L]) := by
  let := σ.toAlgebra
  choose g hg hgDiag using exists_infiniteAdeleLocalMap F σ
  choose h hh hhDiag hhInt using exists_finiteAdeleLocalMap F (L := L)
  let i : InfiniteAdeleRing F →+* InfiniteAdeleRing L :=
    RingHom.pi fun w ↦ (g w).comp (Pi.evalRingHom _ (w.comap σ))
  let k : 𝔸ᶠ[𝓞 F, F] →+* 𝔸ᶠ[𝓞 L, L] :=
    RestrictedProduct.mapAlongRingHom _ _ _ (tendsto_cofinite_finitePlace_under F) h
      (Eventually.of_forall hhInt)
  let f : 𝔸[F] →+* 𝔸[L] := i.prodMap k
  refine ⟨f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (continuous_pi fun w ↦ (hg w).comp (continuous_apply (w.comap σ))).prodMap
      (RestrictedProduct.mapAlong_continuous _ _ _ (tendsto_cofinite_finitePlace_under F)
        _ (Eventually.of_forall hhInt) hh)
  · intro x
    apply Prod.ext
    · funext w
      change g w ((algebraMap F 𝔸[F] x).1 (w.comap σ)) =
        (algebraMap L 𝔸[L] (σ x)).1 w
      simpa only [AdeleRing.algebraMap_fst_apply] using hgDiag w x
    · apply DFunLike.ext
      intro w
      exact hhDiag w x
  · intro w a ha
    change g w (a.1 (w.comap σ)) = 0
    rw [ha, map_zero]
  · intro v w hv a ha
    have he : w.under (𝓞 F) = v := HeightOneSpectrum.ext hv.symm
    subst v
    change h w (a.2 (w.under (𝓞 F))) = 0
    rw [ha, map_zero]
  · intro a ha
    exact (mem_integralAdeles_iff L _).mpr fun w ↦
      hhInt w ((mem_integralAdeles_iff F a).mp ha (w.under (𝓞 F)))

/-- An additive map out of the adeles that factors through a place is determined by its
values on the diagonal, using a continuous section of the place projection. -/
private theorem adeleLocalMap_eq_on_diagonal {A B : Type*} [AddGroup A] [AddGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] (p : 𝔸[F] →+ A) (j : A → 𝔸[F]) (hj : Continuous j)
    (hpj : ∀ x, p (j x) = x) (hd : DenseRange (p ∘ algebraMap F 𝔸[F]))
    (u v : 𝔸[F] →+ B) (hu : Continuous u) (hv : Continuous v)
    (hu₀ : ∀ a, p a = 0 → u a = 0) (hv₀ : ∀ a, p a = 0 → v a = 0)
    (he : ∀ x : F, u (algebraMap F 𝔸[F] x) = v (algebraMap F 𝔸[F] x)) :
    ∀ a : 𝔸[F], u a = v a := by
  have factor (m : 𝔸[F] →+ B) (hm : ∀ a, p a = 0 → m a = 0) (a : 𝔸[F]) :
      m (j (p a)) = m a := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hm
    rw [map_sub, hpj, sub_self]
  have hEq : u ∘ j = v ∘ j := hd.equalizer (hu.comp hj) (hv.comp hj) (funext fun x ↦ by
    exact (factor u hu₀ _).trans ((he x).trans (factor v hv₀ _).symm))
  exact fun a ↦ (factor u hu₀ a).symm.trans ((congrFun hEq (p a)).trans (factor v hv₀ a))

/-- Two adelic extensions agree at every place by density of the field in the corresponding
completion and the kernel condition in the definition of an adelic extension. -/
private theorem adeleExtension_unique (σ : F →+* L) {f g : 𝔸[F] →+* 𝔸[L]}
    (hf : IsAdeleExtension F σ f) (hg : IsAdeleExtension F σ g) : f = g := by
  classical
  apply RingHom.ext
  intro a
  apply Prod.ext
  · funext w
    let v := w.comap σ
    let p := ((Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v).comp
      (RingHom.fst (InfiniteAdeleRing F) (𝔸ᶠ[𝓞 F, F]))).toAddMonoidHom
    let k := ((Pi.evalRingHom (fun w : InfinitePlace L ↦ w.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing L) (𝔸ᶠ[𝓞 L, L]))).toAddMonoidHom
    let j : v.Completion → 𝔸[F] := fun x ↦ (Pi.single v x, 0)
    have hk : Continuous k := (continuous_apply w).comp continuous_fst
    refine adeleLocalMap_eq_on_diagonal F p j ((continuous_single v).prodMk continuous_const)
      (Pi.single_eq_same v) ?_ (k.comp f.toAddMonoidHom) (k.comp g.toAddMonoidHom)
      (hk.comp hf.1) (hk.comp hg.1) (hf.2.2.1 w) (hg.2.2.1 w) ?_ a
    · have h : Surjective (fun y : InfiniteAdeleRing F ↦ y v) :=
        fun x ↦ ⟨Pi.single v x, Pi.single_eq_same v x⟩
      exact h.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) (continuous_apply v)
    · intro x
      exact congrArg k ((hf.2.1 x).trans (hg.2.1 x).symm)
  · apply DFunLike.ext
    intro w
    let := σ.toAlgebra
    let v := w.under (𝓞 F)
    let K := fun v : Primes(F) ↦ v.adicCompletion F
    let O := fun v : Primes(F) ↦ v.adicCompletionIntegers F
    let J := ({v}ᶜ : Set (Primes(F)))
    let j₀ (x : K v) : Πʳ i, [K i, O i]_[𝓟 J] :=
      ⟨Pi.single v x, by
        rw [eventually_principal]
        intro i hi
        exact (Pi.single_eq_of_ne hi x).symm ▸ (O i).zero_mem⟩
    have hj₀ : Continuous j₀ := RestrictedProduct.continuous_rng_of_principal.mpr
      (continuous_single v)
    let i := RestrictedProduct.inclusion K (fun v ↦ (O v : Set (K v)))
      (show cofinite ≤ 𝓟 J by simp [J, le_principal_iff])
    let j : K v → 𝔸[F] := fun x ↦ (0, i (j₀ x))
    have hj : Continuous j := continuous_const.prodMk
      ((RestrictedProduct.continuous_inclusion _).comp hj₀)
    let p := ((RestrictedProduct.evalRingHom K v).comp
      (RingHom.snd (InfiniteAdeleRing F) (𝔸ᶠ[𝓞 F, F]))).toAddMonoidHom
    let k := ((RestrictedProduct.evalRingHom _ w).comp
      (RingHom.snd (InfiniteAdeleRing L) (𝔸ᶠ[𝓞 L, L]))).toAddMonoidHom
    have hk : Continuous k := (RestrictedProduct.continuous_eval w).comp continuous_snd
    refine adeleLocalMap_eq_on_diagonal F p j hj (Pi.single_eq_same v) (v.denseRange_algebraMap F)
      (k.comp f.toAddMonoidHom) (k.comp g.toAddMonoidHom) (hk.comp hf.1) (hk.comp hg.1)
      (hf.2.2.2 v w rfl) (hg.2.2.2 v w rfl) ?_ a
    intro x
    exact congrArg k ((hf.2.1 x).trans (hg.2.1 x).symm)

/-- Paper: Lemma A.1.2.1, p. 541. A continuous adelic extension preserving the integral
model descends to continuous maps on both quotients, with the stated formulas on representatives. -/
private theorem adeleExtension_descends (σ : F →+* L) {f : 𝔸[F] →+* 𝔸[L]}
    (hf : IsAdeleExtension F σ f)
    (hInt : Set.MapsTo f (Integral(F) : Set 𝔸[F]) (Integral(L) : Set 𝔸[L])) :
    ∃ (r : Integral(F) →+ Integral(L)) (c : AQuot(F) →+ AQuot(L))
      (c₀ : IQuot(F, ∅) →+ IQuot(L, ∅)),
      Continuous r ∧ Continuous c ∧ Continuous c₀ ∧ (∀ x, (r x).val = f x.val) ∧
      (∀ a, c (QuotientAddGroup.mk' (Principal(F)) a) =
        QuotientAddGroup.mk' (Principal(L)) (f a)) ∧
      ∀ x, c₀ (QuotientAddGroup.mk' (IntegralPrincipal(F)) x) =
        QuotientAddGroup.mk' (IntegralPrincipal(L)) (r x) := by
  let r := (f.toAddMonoidHom.comp (Integral(F)).subtype.toAddMonoidHom).codRestrict
    (Integral(L)) fun x ↦ hInt x.property
  have hP : Principal(F) ≤ (Principal(L)).comap f.toAddMonoidHom := by
    rintro _ ⟨x, rfl⟩
    exact ⟨σ x, (hf.2.1 x).symm⟩
  have hP₀ : IntegralPrincipal(F) ≤ (IntegralPrincipal(L)).comap r := by
    rintro _ ⟨x, rfl⟩
    have hx : algebraMap L 𝔸[L] (σ x.val) ∈ Integral(L) :=
      hf.2.1 x.val ▸ hInt ((integralAdeleDiagonal F ∅ x).property)
    refine ⟨⟨σ x.val, (diagonal_mem_integralAdelesOutside L ∅ _).mp hx⟩, ?_⟩
    exact Subtype.ext (hf.2.1 x.val).symm
  let c := QuotientAddGroup.map (Principal(F)) (Principal(L)) f.toAddMonoidHom hP
  let c₀ := QuotientAddGroup.map (IntegralPrincipal(F)) (IntegralPrincipal(L)) r hP₀
  have hr : Continuous r := (hf.1.comp continuous_subtype_val).subtype_mk _
  refine ⟨r, c, c₀, hr, ?_, ?_, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · exact QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
      (QuotientAddGroup.continuous_mk.comp hf.1)
  · exact QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
      (QuotientAddGroup.continuous_mk.comp hr)

end AdeleExtension

end AdeleAdditiveQuotient

end RiemannMasullo

open RiemannMasullo Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing

variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "AQuot(" F ")" => 𝔸[F] ⧸ AdeleRing.principalSubgroup (𝓞 F) F
local notation "IQuot(" F ", " S ")" =>
  (RiemannMasullo.integralAdelesOutside F S) ⧸
    AddMonoidHom.range (RingHom.toAddMonoidHom (RiemannMasullo.integralAdeleDiagonal F S))

theorem solution :
    let d := algebraMap F 𝔸[F]
    let q := QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)
    let q₀ := QuotientAddGroup.mk' (integralAdeleDiagonal F ∅).toAddMonoidHom.range
    Injective d ∧ IsClosed (Set.range d) ∧ IsDiscrete (Set.range d) ∧
    Exact d q ∧ IsOpenQuotientMap q ∧ CompactSpace (AQuot(F)) ∧ T2Space (AQuot(F)) ∧
    (∀ n : ℕ, 0 < n → Bijective (fun x : AQuot(F) ↦ n • x)) ∧
    (∃ e : IQuot(F, ∅) ≃ₜ+ (AQuot(F)), ∀ x, e (q₀ x) = q x.val) ∧
    (∀ (L : Type*) [Field L] [NumberField L] (σ : F →+* L),
      (∃! f : 𝔸[F] →+* 𝔸[L], IsAdeleExtension F σ f) ∧
      ∀ f : 𝔸[F] →+* 𝔸[L], IsAdeleExtension F σ f →
        ∃ (r : integralAdelesOutside F ∅ →+ integralAdelesOutside L ∅)
          (c : AQuot(F) →+ AQuot(L)) (c₀ : IQuot(F, ∅) →+ IQuot(L, ∅)),
          Continuous r ∧ Continuous c ∧ Continuous c₀ ∧ (∀ x, (r x).val = f x.val) ∧
          (∀ a, c (q a) = QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 L) L) (f a)) ∧
          ∀ x, c₀ (q₀ x) = QuotientAddGroup.mk' (integralAdeleDiagonal L ∅).toAddMonoidHom.range (r x)) := by
  dsimp only
  have hdisc := isDiscrete_principalAdeles F
  have : T2Space (InfiniteAdeleRing F) := by
    change T2Space ((v : InfinitePlace F) → v.Completion)
    infer_instance
  have : T2Space (𝔸ᶠ[𝓞 F, F]) := by
    change T2Space (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  have : T2Space 𝔸[F] := by
    change T2Space (InfiniteAdeleRing F × 𝔸ᶠ[𝓞 F, F])
    infer_instance
  have hclosed : IsClosed (AdeleRing.principalSubgroup (𝓞 F) F : Set 𝔸[F]) :=
    by
      have : DiscreteTopology (AdeleRing.principalSubgroup (𝓞 F) F) := SetLike.isDiscrete_iff_discreteTopology.1 hdisc
      exact AddSubgroup.isClosed_of_discrete
  refine ⟨AdeleRing.algebraMap_injective _ F, hclosed, hdisc, ?_,
    QuotientAddGroup.isOpenQuotientMap_mk, compactSpace_adeleQuotient F, inferInstance,
    adeleQuotient_nsmul_bijective F, integralAdeleQuotient_equiv F, ?_⟩
  · intro a
    exact QuotientAddGroup.eq_zero_iff a
  · intro L _ _ σ
    obtain ⟨f, hf, hInt⟩ := exists_integralAdeleExtension F σ
    refine ⟨⟨f, hf, fun g hg ↦ adeleExtension_unique F σ hg hf⟩, ?_⟩
    intro g hg
    have he := adeleExtension_unique F σ hg hf
    subst g
    exact adeleExtension_descends F σ hf hInt

