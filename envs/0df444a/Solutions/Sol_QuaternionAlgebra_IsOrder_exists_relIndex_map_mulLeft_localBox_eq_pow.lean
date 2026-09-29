-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_relIndex_map_mulLeft_localBox_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d5f6610d-ef0c-56ee-bf79-73715891d4a8

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_mem_localBox_iff_exists_eq_sum_basis_tmul
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_relIndex_map_mulLeft_localBox_eq_pow
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField

open Module

namespace LocIdxPow

section Lattice

variable {D : Type*} [AddCommGroup D] [Module ℚ D]

theorem span_range_coe_basis (Λ : Submodule ℤ D) {ι : Type*} (c : Basis ι ℤ ↥Λ) :
    Submodule.span ℤ (Set.range fun i => (c i : D)) = Λ := by
  have h1 : Set.range (fun i => (c i : D)) = Λ.subtype '' Set.range c := by
    rw [← Set.range_comp]; rfl
  rw [h1, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_basis_eq_coe (Λ : Submodule ℤ D) (hsp : Submodule.span ℚ (Λ : Set D) = ⊤)
    {ι : Type*} (c : Basis ι ℤ ↥Λ) :
    ∃ b : Basis ι ℚ D, ∀ i, b i = (c i : D) := by
  have hliZ : LinearIndependent ℤ (fun i => (c i : D)) :=
    c.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)
  have hli : LinearIndependent ℚ (fun i => (c i : D)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hspan : ⊤ ≤ Submodule.span ℚ (Set.range fun i => (c i : D)) := by
    rw [← hsp, Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (Set.range fun i => (c i : D)) := by
      rw [span_range_coe_basis Λ c]; exact hx
    exact Submodule.span_subset_span ℤ ℚ _ hx'
  exact ⟨Basis.mk hli hspan, fun i => Basis.mk_apply hli hspan i⟩

theorem exists_basis_basis (Λ : Submodule ℤ D) (hfg : Λ.FG) (hsp : Submodule.span ℚ (Λ : Set D) = ⊤) :
    ∃ (n : ℕ) (c : Basis (Fin n) ℤ ↥Λ) (b : Basis (Fin n) ℚ D), ∀ i, b i = (c i : D) := by
  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors ℤ D := by
    refine ⟨fun {n x} h => ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℚ] at h
    rcases smul_eq_zero.mp h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr h
  haveI : NoZeroSMulDivisors ℤ ↥Λ :=
    ⟨fun {n x} h => by
      rcases (smul_eq_zero.mp (congrArg Subtype.val h : n • (x : D) = 0)) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Subtype.ext h1)⟩
  haveI : Module.Free ℤ ↥Λ := Module.free_of_finite_type_torsion_free'
  let c₀ := Module.Free.chooseBasis ℤ ↥Λ
  let n := Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥Λ)
  let c : Basis (Fin n) ℤ ↥Λ := c₀.reindex (Fintype.equivFin _)
  obtain ⟨b, hb⟩ := exists_basis_eq_coe Λ hsp c
  exact ⟨n, c, b, hb⟩

end Lattice

section Local

open IsDedekindDomain NumberField
open scoped TensorProduct

variable {D : Type*} [Ring D] [Algebra ℚ D] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def coord (b : Basis ι ℚ D) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (ι → v.adicCompletion ℚ) ≃ₗ[ℚ] D ⊗[ℚ] v.adicCompletion ℚ :=
  (Finsupp.linearEquivFunOnFinite ℚ (v.adicCompletion ℚ) ι).symm ≪≫ₗ
    (TensorProduct.finsuppScalarLeft ℚ (v.adicCompletion ℚ) ι).symm ≪≫ₗ
      LinearEquiv.rTensor (v.adicCompletion ℚ) b.repr.symm

theorem coord_single (b : Basis ι ℚ D) (v : HeightOneSpectrum (𝓞 ℚ)) (i : ι) (c : v.adicCompletion ℚ) :
    coord b v (Pi.single i c) = b i ⊗ₜ[ℚ] c := by
  simp only [coord, LinearEquiv.trans_apply]
  have h1 : (Finsupp.linearEquivFunOnFinite ℚ (v.adicCompletion ℚ) ι).symm (Pi.single i c) = Finsupp.single i c := by
    ext j
    simp [Finsupp.linearEquivFunOnFinite, Finsupp.single_apply]
  rw [h1, TensorProduct.finsuppScalarLeft_symm_apply_single, LinearEquiv.rTensor_tmul, Basis.repr_symm_single_one]

theorem coord_apply (b : Basis ι ℚ D) (v : HeightOneSpectrum (𝓞 ℚ)) (f : ι → v.adicCompletion ℚ) :
    coord b v f = ∑ i, b i ⊗ₜ[ℚ] f i := by
  conv_lhs => rw [show f = ∑ i, Pi.single i (f i) from (Finset.univ_sum_single f).symm]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => coord_single b v i (f i)

noncomputable def intBox (ι : Type*) (v : HeightOneSpectrum (𝓞 ℚ)) : AddSubgroup (ι → v.adicCompletion ℚ) :=
  AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers ℚ).toSubring.toAddSubgroup

noncomputable def scaledBox (v : HeightOneSpectrum (𝓞 ℚ)) (a : ι → ℤ) : AddSubgroup (ι → v.adicCompletion ℚ) :=
  AddSubgroup.pi Set.univ fun i =>
    ((v.adicCompletionIntegers ℚ).toSubring.toAddSubgroup).map (AddMonoidHom.mulLeft ((a i : ℤ) : v.adicCompletion ℚ))

theorem mem_intBox_iff (v : HeightOneSpectrum (𝓞 ℚ)) (f : ι → v.adicCompletion ℚ) :
    f ∈ intBox ι v ↔ ∀ i, f i ∈ v.adicCompletionIntegers ℚ := by
  simp [intBox, AddSubgroup.mem_pi]

theorem mem_scaledBox_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a : ι → ℤ) (f : ι → v.adicCompletion ℚ) :
    f ∈ scaledBox v a ↔ ∀ i, ∃ c ∈ v.adicCompletionIntegers ℚ, f i = (a i : v.adicCompletion ℚ) * c := by
  simp only [scaledBox, AddSubgroup.mem_pi, Set.mem_univ, true_implies, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft]
  refine forall_congr' fun i => ⟨?_, ?_⟩
  · rintro ⟨c, hc, h⟩; exact ⟨c, hc, h.symm⟩
  · rintro ⟨c, hc, h⟩; exact ⟨c, hc, h.symm⟩

theorem localBox_eq_map_intBox (b : Basis ι ℚ D) (Λ : Submodule ℤ D)
    (hb : Submodule.span ℤ (Set.range b) = Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v = (intBox ι v).map (coord b v).toAddEquiv.toAddMonoidHom := by
  ext x
  rw [Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul b Λ hb v x, AddSubgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (mem_intBox_iff v c).mpr hc, coord_apply b v c⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, (mem_intBox_iff v f).mp hf, coord_apply b v f⟩

theorem localBox_eq_map_scaledBox (b : Basis ι ℚ D) (a : ι → ℤ) (ha : ∀ i, a i ≠ 0) (Λ : Submodule ℤ D)
    (hb : Submodule.span ℤ (Set.range fun i => (a i : ℚ) • b i) = Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v = (scaledBox v a).map (coord b v).toAddEquiv.toAddMonoidHom := by
  have hu : ∀ i, IsUnit ((a i : ℚ)) := fun i => isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr (ha i))
  let b₂ : Basis ι ℚ D := b.isUnitSMul hu
  have hb₂ : ∀ i, b₂ i = (a i : ℚ) • b i := fun i => Basis.isUnitSMul_apply hu i
  have hb₂' : Submodule.span ℤ (Set.range b₂) = Λ := by
    rw [← hb]; congr 1; ext x; simp only [Set.mem_range, hb₂]
  ext x
  rw [Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul b₂ Λ hb₂' v x, AddSubgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => (a i : v.adicCompletion ℚ) * c i, (mem_scaledBox_iff v a _).mpr fun i => ⟨c i, hc i, rfl⟩, ?_⟩
    show coord b v _ = _
    rw [coord_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb₂, TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, map_intCast]
  · rintro ⟨f, hf, rfl⟩
    obtain hf' := (mem_scaledBox_iff v a f).mp hf
    choose c hc hfc using hf'
    refine ⟨c, hc, ?_⟩
    show coord b v _ = _
    rw [coord_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb₂, TensorProduct.smul_tmul, hfc i]
    congr 1
    rw [Algebra.smul_def, map_intCast]

theorem relIndex_map_equiv {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (A B : AddSubgroup G) :
    (A.map e.toAddMonoidHom).relIndex (B.map e.toAddMonoidHom) = A.relIndex B := by
  rw [AddEquiv.toAddMonoidHom_eq_coe, AddSubgroup.map_equiv_eq_comap_symm e A, AddSubgroup.relIndex_comap,
    AddSubgroup.map_map]
  have : ((e.symm : H ≃+ G) : H →+ G).comp (e : G →+ H) = AddMonoidHom.id G := by
    ext g; simp
  rw [this, AddSubgroup.map_id]

noncomputable def inclBox (ι : Type*) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (ι → ↥(v.adicCompletionIntegers ℚ)) →+ (ι → v.adicCompletion ℚ) :=
  AddMonoidHom.pi fun i =>
    ((v.adicCompletionIntegers ℚ).toSubring.subtype.toAddMonoidHom).comp (Pi.evalAddMonoidHom _ i)

theorem inclBox_apply (v : HeightOneSpectrum (𝓞 ℚ)) (f : ι → ↥(v.adicCompletionIntegers ℚ)) (i : ι) :
    inclBox ι v f i = (f i : v.adicCompletion ℚ) := rfl

theorem map_inclBox_top (v : HeightOneSpectrum (𝓞 ℚ)) : (⊤ : AddSubgroup _).map (inclBox ι v) = intBox ι v := by
  ext x
  rw [AddSubgroup.mem_map, mem_intBox_iff]
  constructor
  · rintro ⟨f, -, rfl⟩ i
    rw [inclBox_apply]; exact (f i).2
  · intro hx
    refine ⟨fun i => ⟨x i, hx i⟩, trivial, funext fun i => rfl⟩

noncomputable def idealBox (v : HeightOneSpectrum (𝓞 ℚ)) (a : ι → ℤ) : AddSubgroup (ι → ↥(v.adicCompletionIntegers ℚ)) :=
  AddSubgroup.pi Set.univ fun i => (Ideal.span {((a i : ℤ) : ↥(v.adicCompletionIntegers ℚ))}).toAddSubgroup

theorem mem_idealBox_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a : ι → ℤ) (f : ι → ↥(v.adicCompletionIntegers ℚ)) :
    f ∈ idealBox v a ↔ ∀ i, f i ∈ Ideal.span {((a i : ℤ) : ↥(v.adicCompletionIntegers ℚ))} := by
  simp [idealBox, AddSubgroup.mem_pi]

theorem comap_inclBox_scaledBox (v : HeightOneSpectrum (𝓞 ℚ)) (a : ι → ℤ) :
    (scaledBox v a).comap (inclBox ι v) = idealBox v a := by
  ext f
  rw [AddSubgroup.mem_comap, mem_scaledBox_iff, mem_idealBox_iff]
  refine forall_congr' fun i => ?_
  rw [inclBox_apply, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc, hfc⟩
    refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul, SubringClass.coe_intCast, hfc, mul_comm]
  · rintro ⟨r, hr⟩
    refine ⟨r, r.2, ?_⟩
    have h1 := congrArg (fun x : ↥(v.adicCompletionIntegers ℚ) => (x : v.adicCompletion ℚ)) hr
    simp only [MulMemClass.coe_mul, SubringClass.coe_intCast] at h1
    rw [← h1, mul_comm]

noncomputable def quotMap (v : HeightOneSpectrum (𝓞 ℚ)) (a : ι → ℤ) :
    (ι → ↥(v.adicCompletionIntegers ℚ)) →+ ((i : ι) → ↥(v.adicCompletionIntegers ℚ) ⧸
      Ideal.span {((a i : ℤ) : ↥(v.adicCompletionIntegers ℚ))}) :=
  AddMonoidHom.pi fun i =>
    ((Ideal.Quotient.mk (Ideal.span {((a i : ℤ) : ↥(v.adicCompletionIntegers ℚ))})).toAddMonoidHom).comp
      (Pi.evalAddMonoidHom _ i)

theorem quotMap_apply (v : HeightOneSpectrum (𝓞 ℚ)) (a : ι → ℤ) (f : ι → ↥(v.adicCompletionIntegers ℚ)) (i : ι) :
    quotMap v a f i = Ideal.Quotient.mk _ (f i) := rfl

theorem index_idealBox (v : HeightOneSpectrum (𝓞 ℚ)) (a : ι → ℤ) :
    (idealBox v a).index =
      ∏ i, Nat.card (↥(v.adicCompletionIntegers ℚ) ⧸
        Ideal.span {((a i : ℤ) : ↥(v.adicCompletionIntegers ℚ))}) := by
  have hsurj : Function.Surjective (quotMap v a) := by
    intro q
    choose r hr using fun i => Ideal.Quotient.mk_surjective (q i)
    exact ⟨r, funext fun i => by rw [quotMap_apply, hr i]⟩
  have hker : (quotMap v a).ker = idealBox v a := by
    ext f
    rw [AddMonoidHom.mem_ker, mem_idealBox_iff, funext_iff]
    refine forall_congr' fun i => ?_
    rw [Pi.zero_apply, quotMap_apply, Ideal.Quotient.eq_zero_iff_mem]
  rw [← hker, AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (quotMap v a) hsurj).toEquiv, Nat.card_pi]

theorem relIndex_scaledBox_intBox (v : HeightOneSpectrum (𝓞 ℚ)) (a : ι → ℤ) :
    (scaledBox v a).relIndex (intBox ι v) =
      ∏ i, Nat.card (↥(v.adicCompletionIntegers ℚ) ⧸
        Ideal.span {((a i : ℤ) : ↥(v.adicCompletionIntegers ℚ))}) := by
  rw [← map_inclBox_top, ← AddSubgroup.relIndex_comap, comap_inclBox_scaledBox, AddSubgroup.relIndex_top_right,
    index_idealBox]

end Local

section WsTwentyOne

theorem natGenerator_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = ℓ := by
  show Rat.HeightOneSpectrum.natGenerator v = ℓ
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ ℓ := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
    rwa [map_natCast] at this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hdvd

theorem exists_unit_mul_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (t₀ : v.adicCompletion ℚ) (ht₀ : t₀ ∈ v.adicCompletionIntegers ℚ) (ht₀0 : t₀ ≠ 0) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers ℚ)ˣ),
      t₀ = ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) * ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n := by
  set t : v.adicCompletionIntegers ℚ := ⟨t₀, ht₀⟩ with htdef
  have ht : t ≠ 0 := fun h => ht₀0 (by rw [htdef] at h; exact congrArg Subtype.val h)
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  set ψ := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v with hψ
  have ht' : ψ t ≠ 0 := fun h => ht (by simpa using congrArg ψ.symm h)
  refine ⟨(ψ t).valuation, Units.map ψ.symm.toRingEquiv.toRingHom.toMonoidHom (PadicInt.unitCoeff ht'), ?_⟩
  show (t : v.adicCompletion ℚ) = _
  have key : t = ψ.symm ((PadicInt.unitCoeff ht' : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) *
      ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) ^ (ψ t).valuation) := by
    rw [← PadicInt.unitCoeff_spec ht']; simp
  have hp : (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
      ((ℓ : ℕ) : v.adicCompletion ℚ) := by
    rw [← natGenerator_eq hℓ v hv]; exact map_natCast (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) _
  have e1 : (t : v.adicCompletion ℚ) =
      ((ψ.symm (PadicInt.unitCoeff ht' : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) *
        (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ^ (ψ t).valuation := by
    conv_lhs => rw [key]
    rw [map_mul, map_pow, map_natCast]
    push_cast
    rfl
  rw [e1, hp]
  rfl

variable {a b : ℚ}

theorem one_tmul_mul_mem_localBox (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  unfold Submodule.localBox at hx ⊢
  have hle : AddSubgroup.closure {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ |
        ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c} ≤
      (AddSubgroup.closure {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ |
        ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}).comap
        (AddMonoidHom.mulLeft ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c)) := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨z, hz, d, hd, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft]
    refine AddSubgroup.subset_closure ⟨z, hz, c * d, mul_mem hc hd, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact hle hx

end WsTwentyOne

section New

variable {a b : ℚ}

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ Submodule.localBox Λ v)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨z, hz, c, hc, rfl⟩ ⟨z', hz', c', hc', rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z * z', hΛ.mul_mem hz hz', c * c', mul_mem hc hc', rfl⟩
  · intro x _
    rw [zero_mul]; exact zero_mem _
  · intro x _
    rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h h'
    rw [add_mul]; exact add_mem h h'
  · intro x y z _ _ _ h h'
    rw [mul_add]; exact add_mem h h'
  · intro x y _ _ h
    convert neg_mem h using 1
    exact neg_mul x y
  · intro x y _ _ h
    convert neg_mem h using 1
    exact mul_neg x y

theorem one_tmul_mul_comm (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) (y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) * y = y * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul z c => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm]
  | add y₁ y₂ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂]

theorem exists_pow_mul_mem_integers (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (c : v.adicCompletion ℚ) :
    ∃ t : ℕ, ((ℓ : ℕ) : v.adicCompletion ℚ) ^ t * c ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := v.adicCompletionIntegers ℚ) c
  have hq0 : (q : v.adicCompletion ℚ) ≠ 0 := fun h => nonZeroDivisors.ne_zero hq ((ZeroMemClass.coe_eq_zero).mp h)
  obtain ⟨n, u, hu⟩ := exists_unit_mul_pow hℓ v hv (q : v.adicCompletion ℚ) q.2 hq0
  refine ⟨n, ?_⟩
  have hu1 : ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) * (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  have hU0 : ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hu1
  have hℓ0 : ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n ≠ 0 := by
    intro h; apply hq0; rw [hu, h, mul_zero]
  have : ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n * ((algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) p / (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) q) =
      (p : v.adicCompletion ℚ) * (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := by
    rw [show ((algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) q) = (q : v.adicCompletion ℚ) from rfl,
      show ((algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) p) = (p : v.adicCompletion ℚ) from rfl, hu, ← mul_div_assoc, mul_comm (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n) (p : v.adicCompletion ℚ),
      mul_div_mul_right _ _ hℓ0, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hu1]
  rw [this]
  exact mul_mem p.2 ((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ).2

theorem exists_pow_mul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    ∃ t : ℕ, ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((ℓ : ℕ) : v.adicCompletion ℚ) ^ t)) * y ∈ Submodule.localBox Λ v := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [mul_zero]; exact zero_mem _⟩
  | tmul z c =>
    obtain ⟨d, hd0, hdz⟩ := QuaternionAlgebra.exists_natCast_smul_mem_of_mem_span (Λ := Λ)
      (y := z) (by rw [hΛ.spanTop]; exact Submodule.mem_top)
    obtain ⟨t, ht⟩ := exists_pow_mul_mem_integers v hℓ hv ((d : ℚ)⁻¹ • c)
    refine ⟨t, AddSubgroup.subset_closure ⟨((d : ℕ) : ℤ) • z, hdz, _, ht, ?_⟩⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    symm
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, TensorProduct.smul_tmul, ← mul_smul_comm, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd0 : (d : ℚ) ≠ 0), one_smul]
  | add y₁ y₂ h₁ h₂ =>
    obtain ⟨t₁, ht₁⟩ := h₁
    obtain ⟨t₂, ht₂⟩ := h₂
    refine ⟨t₁ + t₂, ?_⟩
    rw [mul_add]
    refine add_mem ?_ ?_
    · have hsplit : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((ℓ : ℕ) : v.adicCompletion ℚ) ^ (t₁ + t₂))) =
          ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((ℓ : ℕ) : v.adicCompletion ℚ) ^ t₂)) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((ℓ : ℕ) : v.adicCompletion ℚ) ^ t₁)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pow_add, mul_comm]
      rw [hsplit, mul_assoc]
      exact one_tmul_mul_mem_localBox Λ v (pow_mem (natCast_mem _ ℓ) t₂) ht₁
    · have hsplit : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((ℓ : ℕ) : v.adicCompletion ℚ) ^ (t₁ + t₂))) =
          ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((ℓ : ℕ) : v.adicCompletion ℚ) ^ t₁)) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((ℓ : ℕ) : v.adicCompletion ℚ) ^ t₂)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pow_add]
      rw [hsplit, mul_assoc]
      exact one_tmul_mul_mem_localBox Λ v (pow_mem (natCast_mem _ ℓ) t₁) ht₂

theorem one_tmul_mul_coord {n : ℕ} (bB : Basis (Fin n) ℚ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ)
    (f : Fin n → v.adicCompletion ℚ) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) * coord bB v f = coord bB v (r • f) := by
  rw [coord_apply, coord_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, smul_eq_mul]

theorem map_smul_intBox_eq_scaledBox {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) :
    (intBox (Fin n) v).map (DistribMulAction.toAddMonoidHom (Fin n → v.adicCompletion ℚ) ((m : ℕ) : v.adicCompletion ℚ)) =
      scaledBox v (fun _ : Fin n => ((m : ℕ) : ℤ)) := by
  ext f
  rw [AddSubgroup.mem_map, mem_scaledBox_iff]
  constructor
  · rintro ⟨f₀, hf₀, rfl⟩ i
    refine ⟨f₀ i, (mem_intBox_iff v f₀).mp hf₀ i, ?_⟩
    rw [DistribMulAction.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul, Int.cast_natCast]
  · intro h
    choose c hc hfc using h
    refine ⟨c, (mem_intBox_iff v c).mpr hc, ?_⟩
    funext i
    rw [DistribMulAction.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul, hfc i, Int.cast_natCast]

theorem natCard_quotient_pow (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (T : ℕ) :
    Nat.card (v.adicCompletionIntegers ℚ ⧸ Ideal.span {(((ℓ ^ T : ℕ) : ℤ) : v.adicCompletionIntegers ℚ)}) = ℓ ^ T := by
  rw [Int.cast_natCast,
    IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
      v ℓ hℓ hv (ℓ ^ T) (pow_ne_zero T hℓ.ne_zero), Nat.Prime.factorization_pow hℓ, Finsupp.single_eq_same]

end New

end LocIdxPow

open LocIdxPow in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (hg : g ∈ Submodule.localBox Λ v) (hgu : IsUnit g) :
    ∃ f : ℕ, ((Submodule.localBox Λ v).map (AddMonoidHom.mulLeft g)).relIndex (Submodule.localBox Λ v) = ℓ ^ f := by
  classical
  obtain ⟨n, cB, bB, hbB⟩ := exists_basis_basis (D := ℍ[ℚ, a, b]) Λ hΛ.fg hΛ.spanTop
  have hspan : Submodule.span ℤ (Set.range bB) = Λ := by
    have : Set.range bB = Set.range (fun i => (cB i : ℍ[ℚ, a, b])) := by
      ext x; simp only [Set.mem_range, hbB]
    rw [this]
    exact span_range_coe_basis Λ cB
  have hbox := localBox_eq_map_intBox bB Λ hspan v
  obtain ⟨u, rfl⟩ := hgu
  obtain ⟨T, hT⟩ := exists_pow_mul_mem_localBox hΛ v hℓ hv
    ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
  set r : v.adicCompletion ℚ := ((ℓ : ℕ) : v.adicCompletion ℚ) ^ T with hr
  set S : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
    (Submodule.localBox Λ v).map (AddMonoidHom.mulLeft ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r)) with hSdef

  have hS_le : S ≤ (Submodule.localBox Λ v).map (AddMonoidHom.mulLeft ((u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) * y, ?_, ?_⟩
    · rw [← one_tmul_mul_comm v r]
      exact localBox_mul_mem hΛ v hT hy
    · rw [AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulLeft, mul_assoc, Units.mul_inv_cancel_left]

  have hS_eq : S = (scaledBox v (fun _ : Fin n => ((ℓ ^ T : ℕ) : ℤ))).map (coord bB v).toAddEquiv.toAddMonoidHom := by
    rw [hSdef, hbox, AddSubgroup.map_map, ← map_smul_intBox_eq_scaledBox v (ℓ ^ T), AddSubgroup.map_map]
    congr 1
    ext f
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      DistribMulAction.toAddMonoidHom_apply]
    rw [show ((coord bB v).toAddEquiv.toAddMonoidHom : (Fin n → v.adicCompletion ℚ) → ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = coord bB v from rfl,
      one_tmul_mul_coord, Nat.cast_pow]
  have hS_idx : S.relIndex (Submodule.localBox Λ v) = ℓ ^ (T * n) := by
    rw [hS_eq, hbox, relIndex_map_equiv, relIndex_scaledBox_intBox, Finset.prod_congr rfl
      (fun i _ => natCard_quotient_pow v hℓ hv T), Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hdvd : ((Submodule.localBox Λ v).map (AddMonoidHom.mulLeft ((u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))).relIndex
      (Submodule.localBox Λ v) ∣ ℓ ^ (T * n) := by
    rw [← hS_idx]
    exact AddSubgroup.relIndex_dvd_of_le_left _ hS_le
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hℓ).mp hdvd
  exact ⟨f, hf⟩

end S_QuaternionAlgebra_IsOrder_exists_relIndex_map_mulLeft_localBox_eq_pow
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_relIndex_map_mulLeft_localBox_eq_pow (solution)
