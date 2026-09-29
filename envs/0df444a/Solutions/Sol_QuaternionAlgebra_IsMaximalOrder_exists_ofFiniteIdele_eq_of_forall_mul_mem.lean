-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_ofFiniteIdele_eq_of_forall_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a65cf757-3266-5e7a-8aad-5d40752f3bdd

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Theorems.Thm_Matrix_exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_localBox_iff_of_mem_asIdeal
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_exists_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_of_forall_mul_mem
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_of_forall_mul_mem.QuaternionAlgebra IsDedekindDomain NumberField"

noncomputable section

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re coe_intCast IsMaximalOrder IsEichlerOrder IsDefiniteRamifiedExactlyAt IsOrder IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem IsMaximalOrder.exists_units_forall_mem_localBox_iff_of_mem_asIdeal"
namespace LocallyPrincipalAssembly
p2m_open "QuaternionAlgebra"

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem valued_natCast_eq_one' {n : ℕ} (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    Valued.v (n : v.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := v)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem natCast_ne_zero_of_notMem {n : ℕ} (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    (n : v.adicCompletion ℚ) ≠ 0 := by
  intro h
  have := valued_natCast_eq_one' v hn
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem natCast_inv_mem_integers {n : ℕ} (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    (n : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one' v hn, inv_one]

theorem finite_setOf_intCast_mem {n : ℤ} (hn : n ≠ 0) :
    {w : HeightOneSpectrum (𝓞 ℚ) | (n : 𝓞 ℚ) ∈ w.asIdeal}.Finite := by
  have h := Ideal.finite_factors (I := Ideal.span {(n : 𝓞 ℚ)}) (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hn)
  refine h.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  exact (Ideal.dvd_span_singleton).mpr hw

end Places

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (v : HeightOneSpectrum (𝓞 ℚ))

theorem tmul_mem_localBox (Λ : Submodule ℤ D) {z : D} (hz : z ∈ Λ) {c : v.adicCompletion ℚ}
    (hc : c ∈ v.adicCompletionIntegers ℚ) : z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_mem_localBox {Λ : Submodule ℤ D} (h1 : (1 : D) ∈ Λ) : (1 : D ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v :=
  tmul_mem_localBox v Λ h1 (one_mem _)

theorem one_tmul_mul_mem_localBox (Λ : Submodule ℤ D) {x : D ⊗[ℚ] v.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox Λ v) {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) :
    ((1 : D) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_mem_localBox v Λ hz (mul_mem hc hc')
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx =>
    have e : ((1 : D) ⊗ₜ[ℚ] c) * (-x) = -(((1 : D) ⊗ₜ[ℚ] c) * x) :=
      eq_neg_of_add_eq_zero_left (by rw [← mul_add, neg_add_cancel, mul_zero])
    rw [e]; exact neg_mem hx

theorem localBox_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

theorem localBox_le_of_zsmul_mem {Λ Λ' : Submodule ℤ D} {n : ℤ} (hn : (n : 𝓞 ℚ) ∉ v.asIdeal)
    (h : ∀ z ∈ Λ', n • z ∈ Λ) :
    Submodule.localBox Λ' v ≤ Submodule.localBox Λ v := by

  set N : ℕ := n.natAbs with hN
  have hNv : (N : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hmem
    apply hn
    rcases Int.natAbs_eq n with h' | h'
    · rw [h', Int.cast_natCast]; exact hmem
    · rw [h', Int.cast_neg, Int.cast_natCast]; exact (Submodule.neg_mem_iff _).mpr hmem
  have hNsmul : ∀ z ∈ Λ', (N : ℤ) • z ∈ Λ := by
    intro z hz
    rcases Int.natAbs_eq n with h' | h'
    · rw [hN, ← h']; exact h z hz
    · have : (N : ℤ) • z = -(n • z) := by
        rw [hN, ← neg_zsmul]
        congr 1
        omega
      rw [this]; exact Λ.neg_mem (h z hz)
  unfold Submodule.localBox
  rw [AddSubgroup.closure_le]
  rintro _ ⟨z, hz, c, hc, rfl⟩
  have hN0 := natCast_ne_zero_of_notMem v hNv
  have : z ⊗ₜ[ℚ] c = ((N : ℤ) • z) ⊗ₜ[ℚ] ((N : v.adicCompletion ℚ)⁻¹ * c) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, TensorProduct.smul_tmul, Int.cast_natCast, Algebra.smul_def,
      map_natCast, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  rw [this]
  exact AddSubgroup.subset_closure ⟨(N : ℤ) • z, hNsmul z hz, _, mul_mem (natCast_inv_mem_integers v hNv) hc, rfl⟩

theorem mul_mem_localBox_of {I Λ : Submodule ℤ D} (hmul : ∀ x ∈ I, ∀ y ∈ Λ, x * y ∈ I)
    {x y : D ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox I v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox I v := by
  have step : ∀ s ∈ {x : D ⊗[ℚ] v.adicCompletion ℚ | ∃ z ∈ I, ∃ c : v.adicCompletion ℚ,
      c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c},
      Submodule.localBox Λ v ≤ (Submodule.localBox I v).comap (AddMonoidHom.mulLeft s) := by
    rintro s ⟨z, hz, c, hc, rfl⟩
    unfold Submodule.localBox
    rw [AddSubgroup.closure_le]
    rintro _ ⟨z', hz', c', hc', rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft, Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z * z', hmul z hz z' hz', c * c', mul_mem hc hc', rfl⟩
  have key : Submodule.localBox I v ≤ (Submodule.localBox I v).comap (AddMonoidHom.mulRight y) := by
    unfold Submodule.localBox
    rw [AddSubgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulRight]
    exact step s hs hy
  exact key hx

theorem one_tmul_intCast_mul_mem_localBox {I Λ : Submodule ℤ D} {n : ℤ} (h : ∀ z ∈ Λ, n • z ∈ I)
    {y : D ⊗[ℚ] v.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ v) :
    ((1 : D) ⊗ₜ[ℚ] (n : v.adicCompletion ℚ)) * y ∈ Submodule.localBox I v := by
  induction hy using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hu
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have : z ⊗ₜ[ℚ] ((n : v.adicCompletion ℚ) * c) = (n • z) ⊗ₜ[ℚ] c := by
      rw [← Int.cast_smul_eq_zsmul ℚ, TensorProduct.smul_tmul, Algebra.smul_def, map_intCast]
    rw [this]
    exact tmul_mem_localBox v I (h z hz) hc
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx =>
    have e : ((1 : D) ⊗ₜ[ℚ] (n : v.adicCompletion ℚ)) * (-x) = -(((1 : D) ⊗ₜ[ℚ] (n : v.adicCompletion ℚ)) * x) :=
      eq_neg_of_add_eq_zero_left (by rw [← mul_add, neg_add_cancel, mul_zero])
    rw [e]; exact neg_mem hx

end Box

section Split

variable {a b : ℚ}

theorem charZero_adicCompletion (v : HeightOneSpectrum (𝓞 ℚ)) : CharZero (v.adicCompletion ℚ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective

theorem mem_range_algebraMap_integers_iff (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    x ∈ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).range ↔
      x ∈ v.adicCompletionIntegers ℚ :=
  ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

theorem isEichlerOrder_one_of_isMaximalOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) :
    IsEichlerOrder Λ 1 :=
  ⟨Λ, Λ, hΛ, hΛ, (inf_idem Λ).symm, AddSubgroup.relIndex_self _⟩

theorem exists_units_forall_mem_localBox_iff_of_notMem
    (p : ℕ) [Fact p.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIΛ : I ≤ Λ) (hmul : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I)
    {n : ℤ} (hn : n ≠ 0) (hnI : ∀ μ ∈ Λ, n • μ ∈ I)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ X : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      ∀ t : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        t ∈ Submodule.localBox I v ↔
          ((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * t ∈
            Submodule.localBox Λ v := by
  classical
  haveI := charZero_adicCompletion v

  have h1v : ((1 : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).mp v.isPrime.ne_top
  obtain ⟨φ, hφ1, hφΛ⟩ := QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef
    (isEichlerOrder_one_of_isMaximalOrder hΛ) v hpv h1v

  set R := ↥(v.adicCompletionIntegers ℚ) with hRdef
  set K := v.adicCompletion ℚ with hKdef
  set A := algebraMap R K with hAdef

  have hint : ∀ m : Matrix (Fin 2) (Fin 2) R, φ.symm (m.map A) ∈ Submodule.localBox Λ v := by
    intro m
    rw [hφΛ]
    intro i j
    rw [RingEquiv.apply_symm_apply, Matrix.map_apply]
    exact (m i j).2

  have hφsmul : ∀ (r : K) (M : Matrix (Fin 2) (Fin 2) K),
      φ.symm (r • M) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) * φ.symm M := by
    intro r M
    apply φ.injective
    rw [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply, hφ1, smul_mul_assoc, one_mul]

  set L : AddSubgroup (Matrix (Fin 2) (Fin 2) K) := (Submodule.localBox I v).map φ.toAddMonoidHom with hLdef
  have hLmem : ∀ M, M ∈ L ↔ φ.symm M ∈ Submodule.localBox I v := by
    intro M
    rw [hLdef, AddSubgroup.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      show φ.symm (φ t) ∈ _
      rw [RingEquiv.symm_apply_apply]
      exact ht
    · intro h
      exact ⟨φ.symm M, h, by simp⟩
  have hmulL : ∀ M ∈ L, ∀ m : Matrix (Fin 2) (Fin 2) R, M * m.map A ∈ L := by
    intro M hM m
    rw [hLmem] at hM ⊢
    rw [map_mul]
    exact mul_mem_localBox_of v hmul hM (hint m)
  have hbddL : ∃ d : R, d ≠ 0 ∧ ∀ M ∈ L, ∀ i j, A d * M i j ∈ A.range := by
    refine ⟨1, one_ne_zero, fun M hM i j => ?_⟩
    rw [map_one, one_mul, mem_range_algebraMap_integers_iff]
    rw [hLmem] at hM
    have hM' := (hφΛ (φ.symm M)).mp (localBox_mono v hIΛ hM) i j
    rwa [RingEquiv.apply_symm_apply] at hM'
  have hfullL : ∃ N : R, N ≠ 0 ∧ ∀ m : Matrix (Fin 2) (Fin 2) R, A N • m.map A ∈ L := by
    refine ⟨(n : R), ?_, fun m => ?_⟩
    · intro h
      have : ((n : R) : K) = 0 := by rw [h]; rfl
      rw [SubringClass.coe_intCast] at this
      exact hn (Int.cast_eq_zero.mp this)
    · rw [hLmem, hφsmul]
      have e : A (n : R) = (n : K) := by rw [map_intCast]
      rw [e]
      exact one_tmul_intCast_mul_mem_localBox v hnI (hint m)
  obtain ⟨g, hg⟩ :=
    Matrix.exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing L hmulL hbddL hfullL

  let X : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ := Units.map (φ.symm : Matrix (Fin 2) (Fin 2) K ≃+* _).toRingHom.toMonoidHom g
  have hXinv : ((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) =
      φ.symm ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [Units.coe_map_inv]; rfl
  refine ⟨X, fun t => ?_⟩
  have h1 : t ∈ Submodule.localBox I v ↔ φ t ∈ L := by
    rw [hLmem, RingEquiv.symm_apply_apply]
  have h2 : ((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * t =
      φ.symm (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * φ t) := by
    rw [map_mul, RingEquiv.symm_apply_apply, hXinv]
  rw [h1, hg (φ t), h2, hφΛ (φ.symm _), RingEquiv.apply_symm_apply]
  exact forall_congr' fun i => forall_congr' fun j => mem_range_algebraMap_integers_iff v _

end Split

section Lattice

variable {a b : ℚ}

theorem fg_of_le {Λ I : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : Λ.FG) (hIΛ : I ≤ Λ) : I.FG := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛ
  haveI : IsNoetherian ℤ Λ := isNoetherian_of_isNoetherianRing_of_finite ℤ Λ
  have h := (IsNoetherian.noetherian (I.comap Λ.subtype)).map Λ.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hIΛ] at h

theorem span_eq_top_of_zsmul_mem {Λ I : Submodule ℤ ℍ[ℚ, a, b]} (hspan : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤)
    {n : ℤ} (hn : n ≠ 0) (hnI : ∀ μ ∈ Λ, n • μ ∈ I) : Submodule.span ℚ (I : Set ℍ[ℚ, a, b]) = ⊤ := by
  refine top_unique ?_
  rw [← hspan, Submodule.span_le]
  intro μ hμ
  have e : μ = ((n : ℚ)⁻¹) • ((n • μ : ℍ[ℚ, a, b])) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hnI μ hμ))

end Lattice

end QuaternionAlgebra.LocallyPrincipalAssembly

open QuaternionAlgebra.LocallyPrincipalAssembly in
theorem solution
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIΛ : I ≤ Λ)
    (hmul : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I)
    (hfull : ∃ n : ℤ, n ≠ 0 ∧ ∀ μ ∈ Λ, n • μ ∈ I) :
    ∃ x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.ofFiniteIdele Λ x = I := by
  classical
  obtain ⟨n, hn, hnI⟩ := hfull
  have hΛo : IsOrder Λ := hΛ.1

  have hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ X : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      ∀ t : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, t ∈ Submodule.localBox I v ↔
        ((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * t ∈
          Submodule.localBox Λ v := by
    intro v
    by_cases hpv : (p : 𝓞 ℚ) ∈ v.asIdeal
    · exact QuaternionAlgebra.IsMaximalOrder.exists_units_forall_mem_localBox_iff_of_mem_asIdeal p hdef hΛ I hIΛ
        hmul ⟨n, hn, hnI⟩ v hpv
    · exact exists_units_forall_mem_localBox_iff_of_notMem p hdef hΛ I hIΛ hmul hn hnI v hpv

  have htriv : ∀ v : HeightOneSpectrum (𝓞 ℚ), (n : 𝓞 ℚ) ∉ v.asIdeal →
      Submodule.localBox I v = Submodule.localBox Λ v :=
    fun v hv => le_antisymm (localBox_mono v hIΛ) (localBox_le_of_zsmul_mem v hv hnI)

  let X : ∀ v : HeightOneSpectrum (𝓞 ℚ), (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ := fun v =>
    if Submodule.localBox I v = Submodule.localBox Λ v then 1 else Classical.choose (hloc v)
  have hX : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ),
      t ∈ Submodule.localBox I v ↔
        (((X v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * t ∈
          Submodule.localBox Λ v := by
    intro v t
    by_cases h : Submodule.localBox I v = Submodule.localBox Λ v
    · simp only [X, if_pos h, inv_one, Units.val_one, one_mul, h]
    · simp only [X, if_neg h]
      exact Classical.choose_spec (hloc v) t
  have hX1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), (n : 𝓞 ℚ) ∉ v.asIdeal → X v = 1 := fun v hv => by
    simp only [X, if_pos (htriv v hv)]
  have hcof : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, X v = 1 := by
    rw [Filter.eventually_cofinite]
    refine (finite_setOf_intCast_mem hn).subset fun v hv => ?_
    by_contra hnv
    exact hv (hX1 v hnv)

  obtain ⟨y, hy⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq Λ hΛo.fg hΛo.spanTop
    (fun v => ((X v : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hcof.mono fun v hv => by
      show ((X v : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ _
      rw [hv, Units.val_one]; exact one_mem_localBox v hΛo.one_mem)
  obtain ⟨y', hy'⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq Λ hΛo.fg hΛo.spanTop
    (fun v => (((X v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hcof.mono fun v hv => by
      show (((X v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ _
      rw [hv, inv_one, Units.val_one]; exact one_mem_localBox v hΛo.one_mem)
  have hyy' : y * y' = 1 :=
    Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun v => by rw [map_mul, hy, hy', Units.mul_inv, map_one]
  have hy'y : y' * y = 1 :=
    Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun v => by rw [map_mul, hy, hy', Units.inv_mul, map_one]
  let x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := ⟨y, y', hyy', hy'y⟩
  refine ⟨x, ?_⟩

  have hIfg : I.FG := fg_of_le hΛo.fg hIΛ
  have hIspan : Submodule.span ℚ (I : Set ℍ[ℚ, a, b]) = ⊤ := span_eq_top_of_zsmul_mem hΛo.spanTop hn hnI
  ext z
  rw [Submodule.mem_ofFiniteIdele_iff]

  have step1 : z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) ↔
      y' * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ := by
    constructor
    · rintro ⟨t, ht, hte⟩
      rw [AddMonoidHom.coe_mulLeft] at hte
      have : y' * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) = t := by
        rw [← hte, ← mul_assoc]
        show y' * y * t = t
        rw [hy'y, one_mul]
      rw [this]; exact ht
    · intro h
      refine ⟨_, h, ?_⟩
      rw [AddMonoidHom.coe_mulLeft, ← mul_assoc]
      show y * y' * _ = _
      rw [hyy', one_mul]
  rw [step1, Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛo.fg hΛo.spanTop]

  have step2 : (∀ v : HeightOneSpectrum (𝓞 ℚ), Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
        (y' * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))) ∈ Submodule.localBox Λ v) ↔
      ∀ v : HeightOneSpectrum (𝓞 ℚ), Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
        (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.localBox I v := by
    refine forall_congr' fun v => ?_
    rw [map_mul, hy', hX v]
  rw [step2, ← Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox I hIfg hIspan]

  have step3 := Submodule.mem_ofFiniteIdele_iff I 1 z
  rw [Submodule.ofFiniteIdele_one I hIfg hIspan] at step3
  rw [step3, AddSubgroup.mem_map]
  constructor
  · intro h
    exact ⟨_, h, by rw [Units.val_one, AddMonoidHom.coe_mulLeft, one_mul]⟩
  · rintro ⟨t, ht, hte⟩
    rw [Units.val_one, AddMonoidHom.coe_mulLeft, one_mul] at hte
    rw [← hte]; exact ht

end

end S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_of_forall_mul_mem
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_of_forall_mul_mem (solution)
