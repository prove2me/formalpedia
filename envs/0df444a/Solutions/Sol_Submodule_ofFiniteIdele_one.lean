-- Prove2me | solution 1 for Submodule.ofFiniteIdele_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/726000e5-1221-542a-840d-9eae0037227b

import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_ofFiniteIdele_one

open scoped TensorProduct Pointwise nonZeroDivisors
open IsDedekindDomain NumberField

noncomputable section

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

def s1_Zhat : Subring 𝔸f where
  carrier := {a | ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => by
    show (a * b) v ∈ _
    have : (a * b) v = a v * b v := rfl
    rw [this]; exact mul_mem (ha v) (hb v)
  one_mem' := fun v => by
    have : (1 : 𝔸f) v = 1 := rfl
    rw [this]; exact one_mem _
  add_mem' := fun {a b} ha hb v => by
    have : (a + b) v = a v + b v := rfl
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := fun v => by
    have : (0 : 𝔸f) v = 0 := rfl
    rw [this]; exact zero_mem _
  neg_mem' := fun {a} ha v => by
    have : (-a) v = -(a v) := rfl
    rw [this]; exact neg_mem (ha v)

theorem s1_mem_Zhat_iff (a : 𝔸f) : a ∈ s1_Zhat ↔ ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

theorem s1_valued_algebraMap_apply (q : ℚ) (v : HOS) :
    Valued.v ((algebraMap ℚ 𝔸f q) v) = v.valuation ℚ q := by
  have h : (algebraMap ℚ 𝔸f q) v = ((WithVal.equiv (v.valuation ℚ)).symm q : v.adicCompletion ℚ) := rfl
  rw [h]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q

theorem s1_algebraMap_apply_mem_integers_iff (q : ℚ) (v : HOS) :
    (algebraMap ℚ 𝔸f q) v ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, s1_valued_algebraMap_apply]

theorem s1_valuation_intCast_le_one (v : HOS) (m : ℤ) : v.valuation ℚ (m : ℚ) ≤ 1 := by
  have h : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := ℚ) v (m : 𝓞 ℚ)
  rwa [map_intCast] at h

theorem s1_valuation_natCast_le_one (v : HOS) (n : ℕ) : v.valuation ℚ (n : ℚ) ≤ 1 := by
  have h := s1_valuation_intCast_le_one v (n : ℤ)
  rwa [Int.cast_natCast] at h

theorem s1_algebraMap_intCast_mem_Zhat (m : ℤ) : algebraMap ℚ 𝔸f (m : ℚ) ∈ s1_Zhat := fun v =>
  (s1_algebraMap_apply_mem_integers_iff _ v).mpr (s1_valuation_intCast_le_one v m)

theorem s1_exists_intCast_eq (r : 𝓞 ℚ) : ∃ m : ℤ, ((r : ℚ)) = (m : ℚ) := by
  refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
  have h0 := Rat.ringOfIntegersEquiv.symm_apply_apply r
  rw [eq_intCast Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)] at h0
  calc (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r := rfl
    _ = algebraMap (𝓞 ℚ) ℚ ((Rat.ringOfIntegersEquiv r : ℤ) : 𝓞 ℚ) := by rw [h0]
    _ = ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) := map_intCast _ _

theorem s1_exists_intCast_of_forall_valuation_le_one (q : ℚ)
    (h : ∀ v : HOS, v.valuation ℚ q ≤ 1) : ∃ m : ℤ, q = (m : ℚ) := by
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q h
  obtain ⟨m, hm⟩ := s1_exists_intCast_eq r
  refine ⟨m, ?_⟩
  rw [← hm]
  exact hr.symm

section BoxGen

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_tmul_mem_finiteAdeleBox {Λ : Submodule ℤ K} {z : K} (hz : z ∈ Λ) {a : 𝔸f}
    (ha : a ∈ s1_Zhat) : z ⊗ₜ[ℚ] a ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, a, ha, rfl⟩

theorem s1_finiteAdeleBox_le_iff {Λ : Submodule ℤ K} {H : AddSubgroup (K ⊗[ℚ] 𝔸f)} :
    Submodule.finiteAdeleBox Λ ≤ H ↔ ∀ z ∈ Λ, ∀ a : 𝔸f, a ∈ s1_Zhat → z ⊗ₜ[ℚ] a ∈ H := by
  unfold Submodule.finiteAdeleBox
  rw [AddSubgroup.closure_le]
  constructor
  · intro h z hz a ha
    exact h ⟨z, hz, a, ha, rfl⟩
  · rintro h x ⟨z, hz, a, ha, rfl⟩
    exact h z hz a ha

end BoxGen

section Slice

variable {K : Type*} [Ring K] [Algebra ℚ K]

def s1_coord {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) : K ⊗[ℚ] 𝔸f →ₗ[ℚ] 𝔸f :=
  TensorProduct.lift ((LinearMap.lsmul ℚ 𝔸f).comp (b.coord i))

theorem s1_coord_tmul {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) (z : K) (a : 𝔸f) :
    s1_coord b i (z ⊗ₜ[ℚ] a) = (b.repr z i) • a := by
  unfold s1_coord
  rw [TensorProduct.lift.tmul]
  rfl

theorem s1_coord_mem_Zhat_of_mem_finiteAdeleBox {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι)
    {t : K ⊗[ℚ] 𝔸f} (ht : t ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))) :
    s1_coord b i t ∈ s1_Zhat := by
  have hle : Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ≤ (s1_Zhat.toAddSubgroup).comap (s1_coord b i).toAddMonoidHom := by
    rw [s1_finiteAdeleBox_le_iff]
    intro z hz a ha
    rw [AddSubgroup.mem_comap]
    show s1_coord b i (z ⊗ₜ[ℚ] a) ∈ s1_Zhat
    rw [s1_coord_tmul]
    obtain ⟨m, hm⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ b z).mp hz i
    rw [← hm, Algebra.smul_def]
    refine mul_mem ?_ ha
    have : (algebraMap ℤ ℚ m) = ((m : ℤ) : ℚ) := by rw [algebraMap_int_eq, Int.coe_castRingHom]
    rw [this]
    exact s1_algebraMap_intCast_mem_Zhat m
  exact hle ht

theorem s1_tmul_one_mem_finiteAdeleBox_iff {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (z : K) :
    z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ↔ z ∈ Submodule.span ℤ (Set.range b) := by
  constructor
  · intro hz
    rw [Module.Basis.mem_span_iff_repr_mem ℤ b z]
    intro i
    have hc := s1_coord_mem_Zhat_of_mem_finiteAdeleBox b i hz
    rw [s1_coord_tmul, Algebra.smul_def, mul_one] at hc
    have hval : ∀ v : HOS, v.valuation ℚ (b.repr z i) ≤ 1 := fun v =>
      (s1_algebraMap_apply_mem_integers_iff _ v).mp (hc v)
    obtain ⟨m, hm⟩ := s1_exists_intCast_of_forall_valuation_le_one _ hval
    refine ⟨m, ?_⟩
    rw [hm, algebraMap_int_eq, Int.coe_castRingHom]
  · intro hz
    exact s1_tmul_mem_finiteAdeleBox hz (one_mem _)

end Slice

section LatticeBasis

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_exists_basis_of_isLattice (M : Submodule ℤ K) [Submodule.IsLattice ℚ M] :
    ∃ (n : ℕ) (bM : Module.Basis (Fin n) ℚ K), Submodule.span ℤ (Set.range bM) = M := by
  classical
  haveI : Module.Finite ℤ ↥M := Submodule.IsLattice.finite ℚ _
  haveI : Module.Free ℤ ↥M := Submodule.IsLattice.free ℚ _
  let n := Module.finrank ℤ ↥M
  let bZ : Module.Basis (Fin n) ℤ ↥M := Module.finBasis ℤ ↥M
  refine ⟨n, bZ.extendOfIsLattice ℚ, ?_⟩
  have hrange : Set.range (bZ.extendOfIsLattice ℚ) = M.subtype '' Set.range bZ := by
    ext x
    simp only [Set.mem_range, Module.Basis.extendOfIsLattice_apply, Set.mem_image,
      Submodule.coe_subtype]
    exact ⟨fun ⟨k, hk⟩ => ⟨bZ k, ⟨k, rfl⟩, hk⟩, fun ⟨y, ⟨k, hk⟩, hy⟩ => ⟨k, by rw [hk]; exact hy⟩⟩
  rw [hrange, ← Submodule.map_span, bZ.span_eq, Submodule.map_top, Submodule.range_subtype]

end LatticeBasis

theorem solution {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D)
    (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) :
    Submodule.ofFiniteIdele Λ 1 = Λ := by
  haveI : Submodule.IsLattice ℚ Λ := ⟨hfg, hspan⟩
  obtain ⟨n, b, hb⟩ := s1_exists_basis_of_isLattice Λ
  ext z
  rw [Submodule.mem_ofFiniteIdele_iff, Units.val_one]
  have h1 : AddMonoidHom.mulLeft (1 : D ⊗[ℚ] 𝔸f) = AddMonoidHom.id _ := by
    ext t
    rw [AddMonoidHom.coe_mulLeft, one_mul, AddMonoidHom.id_apply]
  rw [h1, AddSubgroup.map_id, ← hb, s1_tmul_one_mem_finiteAdeleBox_iff]

end

end S_Submodule_ofFiniteIdele_one
end P2MW
export P2MW.S_Submodule_ofFiniteIdele_one (solution)
