-- Prove2me | solution 1 for Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/12c8a054-8424-5010-9d92-c6279d02c460

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_mem_localBox_iff_exists_eq_sum_basis_tmul
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Module

namespace IndexIsLocal

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

private theorem _root_.IndexIsLocal.finrank_eq (Λ : Submodule ℤ D) (hfg : Λ.FG) (hsp : Submodule.span ℚ (Λ : Set D) = ⊤) :
    Module.finrank ℤ ↥Λ = Module.finrank ℚ D := by
  obtain ⟨n, c, b, -⟩ := exists_basis_basis Λ hfg hsp
  rw [Module.finrank_eq_card_basis c, Module.finrank_eq_card_basis b]

p2m_export "IndexIsLocal" "finrank_eq"
end Lattice

section Global

variable {D : Type*} [AddCommGroup D] [Module ℚ D]

theorem relIndex_eq_natCard (Λ₁ Λ₂ : Submodule ℤ D) :
    Λ₂.toAddSubgroup.relIndex Λ₁.toAddSubgroup = Nat.card (↥Λ₁ ⧸ Λ₂.comap Λ₁.subtype) := by
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card]
  rfl

end Global

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

section Finprod

open IsDedekindDomain NumberField

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 ℚ)) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  let I : Ideal ℤ := Ideal.map e v.asIdeal
  have hI : I = Ideal.span {Submodule.IsPrincipal.generator I} := (Ideal.span_singleton_generator I).symm
  set g := Submodule.IsPrincipal.generator I with hg
  have hIprime : I.IsPrime := Ideal.map_isPrime_of_equiv e
  have hback : Ideal.map (e.symm : ℤ →+* 𝓞 ℚ) I = v.asIdeal := Ideal.map_of_equiv (I := v.asIdeal) e
  have hIne : I ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [← hback, h, Ideal.map_bot]
  have hg0 : g ≠ 0 := fun h => hIne (by rw [hI, h, Ideal.span_singleton_eq_bot])
  have hgprime : Prime g := (Ideal.span_singleton_prime hg0).mp (hI ▸ hIprime)
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgprime, ?_⟩
  have h1 : ((g.natAbs : ℕ) : ℤ) ∈ I := by
    rw [hI, Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.mpr dvd_rfl
  have h2 : e.symm ((g.natAbs : ℕ) : ℤ) ∈ v.asIdeal := by
    rw [← hback]
    exact Ideal.mem_map_of_mem _ h1
  rwa [map_natCast] at h2

theorem prime_eq_of_mem {v : HeightOneSpectrum (𝓞 ℚ)} {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (h : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) (h' : (ℓ' : 𝓞 ℚ) ∈ v.asIdeal) : ℓ = ℓ' := by
  by_contra hne
  have hcop : ℓ.Coprime ℓ' := (Nat.coprime_primes hℓ hℓ').mpr hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h1 : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
    have : ((a : 𝓞 ℚ) * ℓ + (b : 𝓞 ℚ) * ℓ') = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) hab
    rw [← this]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h) (v.asIdeal.mul_mem_left _ h')
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem place_eq_of_mem {v w : HeightOneSpectrum (𝓞 ℚ)} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) (hw : (ℓ : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by
  have hprime : Prime (ℓ : 𝓞 ℚ) := by
    have hZ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
    have h1 : Prime (Rat.ringOfIntegersEquiv.symm (ℓ : ℤ)) := (MulEquiv.prime_iff _).mpr hZ
    rwa [map_natCast] at h1
  have hmax : (Ideal.span {(ℓ : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hprime.ne_zero).mpr hprime).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hprime.ne_zero)
  have hv' : v.asIdeal = Ideal.span {(ℓ : 𝓞 ℚ)} :=
    (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)).symm
  have hw' : w.asIdeal = Ideal.span {(ℓ : 𝓞 ℚ)} :=
    (hmax.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hw)).symm
  exact HeightOneSpectrum.ext (hw'.trans hv'.symm)

theorem exists_place_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) : ∃ v : HeightOneSpectrum (𝓞 ℚ), (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  have hne : Ideal.span {(ℓ : 𝓞 ℚ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have : IsUnit (Rat.ringOfIntegersEquiv (ℓ : 𝓞 ℚ)) := hu.map _
    rw [map_natCast, Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at this
    exact hℓ.one_lt.ne' this
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hM0 : M ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at hle
    exact hℓ.ne_zero (by exact_mod_cast hle)
  exact ⟨⟨M, hM.isPrime, hM0⟩, hle (Ideal.mem_span_singleton_self _)⟩

noncomputable def primeBelow (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ := (exists_prime_mem v).choose

theorem primeBelow_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (primeBelow v).Prime := (exists_prime_mem v).choose_spec.1

theorem primeBelow_mem (v : HeightOneSpectrum (𝓞 ℚ)) : ((primeBelow v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  (exists_prime_mem v).choose_spec.2

theorem finprod_natCard_quotient_eq (m : ℕ) (hm : m ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
      Nat.card (v.adicCompletionIntegers ℚ ⧸ Ideal.span {(m : v.adicCompletionIntegers ℚ)}) = m := by
  classical

  have hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Nat.card (v.adicCompletionIntegers ℚ ⧸ Ideal.span {(m : v.adicCompletionIntegers ℚ)}) =
        primeBelow v ^ m.factorization (primeBelow v) := fun v =>
    IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
      v _ (primeBelow_prime v) (primeBelow_mem v) m hm
  simp_rw [hloc]

  choose pl hpl using fun ℓ : ℕ => fun hℓ : ℓ.Prime => exists_place_of_prime hℓ
  let plf : ℕ → HeightOneSpectrum (𝓞 ℚ) := fun ℓ => if h : ℓ.Prime then pl ℓ h else pl 2 Nat.prime_two
  have hplf : ∀ ℓ, ℓ.Prime → (ℓ : 𝓞 ℚ) ∈ (plf ℓ).asIdeal := fun ℓ hℓ => by
    simp only [plf, dif_pos hℓ]; exact hpl ℓ hℓ
  have hbelow : ∀ ℓ, ℓ.Prime → primeBelow (plf ℓ) = ℓ := fun ℓ hℓ =>
    prime_eq_of_mem (primeBelow_prime _) hℓ (primeBelow_mem _) (hplf ℓ hℓ)
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := m.primeFactors.image plf
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      primeBelow v ^ m.factorization (primeBelow v)) ⊆ S := by
    intro v hv
    rw [Function.mem_mulSupport] at hv
    have hdvd : primeBelow v ∣ m := by
      by_contra hnd
      rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at hv
      exact hv rfl
    have hmem : primeBelow v ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨primeBelow_prime v, hdvd, hm⟩
    refine Finset.mem_image.mpr ⟨primeBelow v, hmem, ?_⟩
    exact place_eq_of_mem (primeBelow_prime v) (primeBelow_mem v) (hplf _ (primeBelow_prime v))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, Finset.prod_image]
  · conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    exact Finset.prod_congr rfl fun ℓ hℓ => by rw [hbelow ℓ (Nat.prime_of_mem_primeFactors hℓ)]
  · intro ℓ hℓ ℓ' hℓ' h
    have h1 := hbelow ℓ (Nat.prime_of_mem_primeFactors hℓ)
    have h2 := hbelow ℓ' (Nat.prime_of_mem_primeFactors hℓ')
    rw [h] at h1
    exact h1.symm.trans h2

end Finprod

section FinprodInt

open IsDedekindDomain NumberField

theorem hasFiniteMulSupport_natCard_quotient (m : ℕ) (hm : m ≠ 0) :
    (fun v : HeightOneSpectrum (𝓞 ℚ) =>
      Nat.card (v.adicCompletionIntegers ℚ ⧸ Ideal.span {(m : v.adicCompletionIntegers ℚ)})).HasFiniteMulSupport := by
  classical
  have hloc : (fun v : HeightOneSpectrum (𝓞 ℚ) =>
      Nat.card (v.adicCompletionIntegers ℚ ⧸ Ideal.span {(m : v.adicCompletionIntegers ℚ)})) =
        fun v => primeBelow v ^ m.factorization (primeBelow v) := funext fun v =>
    IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
      v _ (primeBelow_prime v) (primeBelow_mem v) m hm
  rw [hloc]
  choose pl hpl using fun ℓ : ℕ => fun hℓ : ℓ.Prime => exists_place_of_prime hℓ
  let plf : ℕ → HeightOneSpectrum (𝓞 ℚ) := fun ℓ => if h : ℓ.Prime then pl ℓ h else pl 2 Nat.prime_two
  have hplf : ∀ ℓ, ℓ.Prime → (ℓ : 𝓞 ℚ) ∈ (plf ℓ).asIdeal := fun ℓ hℓ => by
    simp only [plf, dif_pos hℓ]; exact hpl ℓ hℓ
  refine Set.Finite.subset (m.primeFactors.image plf).finite_toSet fun v hv => ?_
  rw [Function.mem_mulSupport] at hv
  have hdvd : primeBelow v ∣ m := by
    by_contra hnd
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at hv
    exact hv rfl
  have hmem : primeBelow v ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨primeBelow_prime v, hdvd, hm⟩
  refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨primeBelow v, hmem, ?_⟩)
  exact place_eq_of_mem (primeBelow_prime v) (primeBelow_mem v) (hplf _ (primeBelow_prime v))

theorem span_intCast_eq (a : ℤ) {R : Type*} [CommRing R] :
    Ideal.span {((a : ℤ) : R)} = Ideal.span {((a.natAbs : ℕ) : R)} := by
  rcases Int.natAbs_eq a with h | h
  · conv_lhs => rw [h]
    rw [Int.cast_natCast]
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]

theorem finprod_natCard_quotient_int_eq (a : ℤ) (ha : a ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
      Nat.card (v.adicCompletionIntegers ℚ ⧸ Ideal.span {((a : ℤ) : v.adicCompletionIntegers ℚ)}) = a.natAbs := by
  simp_rw [span_intCast_eq a]
  exact finprod_natCard_quotient_eq _ (Int.natAbs_ne_zero.mpr ha)

theorem hasFiniteMulSupport_natCard_quotient_int (a : ℤ) (ha : a ≠ 0) :
    (fun v : HeightOneSpectrum (𝓞 ℚ) =>
      Nat.card (v.adicCompletionIntegers ℚ ⧸ Ideal.span {((a : ℤ) : v.adicCompletionIntegers ℚ)})).HasFiniteMulSupport := by
  simp_rw [span_intCast_eq a]
  exact hasFiniteMulSupport_natCard_quotient _ (Int.natAbs_ne_zero.mpr ha)

end FinprodInt

end IndexIsLocal

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    {D : Type*} [Ring D] [Algebra ℚ D] (Λ₁ Λ₂ : Submodule ℤ D)
    (h₁fg : Λ₁.FG) (h₁sp : Submodule.span ℚ (Λ₁ : Set D) = ⊤)
    (h₂fg : Λ₂.FG) (h₂sp : Submodule.span ℚ (Λ₂ : Set D) = ⊤) (hle : Λ₂ ≤ Λ₁) :
    Λ₂.toAddSubgroup.relIndex Λ₁.toAddSubgroup =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), (Submodule.localBox Λ₂ v).relIndex (Submodule.localBox Λ₁ v) := by
  classical

  obtain ⟨n, c₁, b₀, hb₀⟩ := IndexIsLocal.exists_basis_basis (D := D) Λ₁ h₁fg h₁sp
  let N : Submodule ℤ ↥Λ₁ := Λ₂.comap Λ₁.subtype
  have hN : Module.finrank ℤ ↥N = Module.finrank ℤ ↥Λ₁ := by
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle),
      IndexIsLocal.finrank_eq (D := D) Λ₂ h₂fg h₂sp, IndexIsLocal.finrank_eq (D := D) Λ₁ h₁fg h₁sp]

  let top := Submodule.smithNormalFormTopBasis c₁ hN
  let bot := Submodule.smithNormalFormBotBasis c₁ hN
  let a : Fin n → ℤ := Submodule.smithNormalFormCoeffs c₁ hN
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero c₁ hN
  have hbot : ∀ i, ((bot i : ↥Λ₁) : D) = (a i : ℚ) • ((top i : ↥Λ₁) : D) := fun i => by
    rw [Submodule.smithNormalFormBotBasis_def, Submodule.coe_smul, Int.cast_smul_eq_zsmul]

  have hglob : Λ₂.toAddSubgroup.relIndex Λ₁.toAddSubgroup = ∏ i, (a i).natAbs := by
    rw [IndexIsLocal.relIndex_eq_natCard (D := D), Nat.card_congr (Submodule.quotientEquivPiZMod N c₁ hN).toEquiv,
      Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => Nat.card_zmod _

  obtain ⟨b, hb⟩ := IndexIsLocal.exists_basis_eq_coe (D := D) Λ₁ h₁sp top
  have hb₁ : Submodule.span ℤ (Set.range b) = Λ₁ := by
    rw [show Set.range b = Set.range (fun i => ((top i : ↥Λ₁) : D)) from congrArg Set.range (funext hb)]
    exact IndexIsLocal.span_range_coe_basis (D := D) Λ₁ top
  have hb₂ : Submodule.span ℤ (Set.range fun i => (a i : ℚ) • b i) = Λ₂ := by
    let bot' : Basis (Fin n) ℤ ↥Λ₂ := bot.map (Submodule.comapSubtypeEquivOfLe hle)
    have h1 : (fun i => (a i : ℚ) • b i) = fun i => (bot' i : D) := funext fun i => by
      rw [hb, ← hbot]; rfl
    rw [h1]
    exact IndexIsLocal.span_range_coe_basis (D := D) Λ₂ bot'

  have hlocal : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (Submodule.localBox Λ₂ v).relIndex (Submodule.localBox Λ₁ v) =
        ∏ i, Nat.card (↥(v.adicCompletionIntegers ℚ) ⧸
          Ideal.span {((a i : ℤ) : ↥(v.adicCompletionIntegers ℚ))}) := by
    intro v
    rw [IndexIsLocal.localBox_eq_map_intBox b Λ₁ hb₁ v, IndexIsLocal.localBox_eq_map_scaledBox b a ha Λ₂ hb₂ v,
      IndexIsLocal.relIndex_map_equiv, IndexIsLocal.relIndex_scaledBox_intBox]

  rw [hglob, finprod_congr hlocal,
    finprod_prod_comm Finset.univ (fun (v : HeightOneSpectrum (𝓞 ℚ)) (i : Fin n) =>
      Nat.card (↥(v.adicCompletionIntegers ℚ) ⧸ Ideal.span {((a i : ℤ) : ↥(v.adicCompletionIntegers ℚ))}))
      (fun i _ => IndexIsLocal.hasFiniteMulSupport_natCard_quotient_int (a i) (ha i))]
  exact Finset.prod_congr rfl fun i _ => (IndexIsLocal.finprod_natCard_quotient_int_eq (a i) (ha i)).symm

end S_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
end P2MW
export P2MW.S_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox (solution)
