-- Prove2me | solution 1 for QuaternionAlgebra.relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e6a4ba56-a3d8-5b36-ba21-90b233c8adaa

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace L1LocalIndexDiag

section IntModel

variable (v : HeightOneSpectrum (𝓞 ℚ))

noncomputable def intMatrixEmb :
    Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ) →+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).mapMatrix

theorem intMatrixEmb_apply (A : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ)) (i j : Fin 2) :
    intMatrixEmb v A i j = ((A i j : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := rfl

theorem intMatrixEmb_injective : Function.Injective (intMatrixEmb v) := by
  intro A B hAB
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun hAB i) j
  rw [intMatrixEmb_apply, intMatrixEmb_apply] at hij
  exact Subtype.ext hij

theorem exists_intMatrixEmb_eq_iff (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    (∃ A, intMatrixEmb v A = M) ↔ ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ := by
  constructor
  · rintro ⟨A, rfl⟩ i j
    exact (A i j).2
  · intro hM
    refine ⟨Matrix.of fun i j => ⟨M i j, hM i j⟩, ?_⟩
    ext i j; rfl

theorem integral_mul {M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ) (hN : ∀ i j, N i j ∈ v.adicCompletionIntegers ℚ) :
    ∀ i j, (M * N) i j ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨A, rfl⟩ := (exists_intMatrixEmb_eq_iff v M).mpr hM
  obtain ⟨B, rfl⟩ := (exists_intMatrixEmb_eq_iff v N).mpr hN
  rw [← map_mul]
  exact (exists_intMatrixEmb_eq_iff v _).mp ⟨A * B, rfl⟩

end IntModel

section Index

variable (v : HeightOneSpectrum (𝓞 ℚ))

def dvdEntrySubgroup (c : v.adicCompletionIntegers ℚ) : AddSubgroup (Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ)) where
  carrier := {X | c ∣ X 1 0}
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq, Matrix.add_apply] at *
    exact dvd_add hX hY
  neg_mem' {X} hX := by
    simp only [Set.mem_setOf_eq, Matrix.neg_apply] at *
    exact (dvd_neg).mpr hX

theorem mem_dvdEntrySubgroup {c : v.adicCompletionIntegers ℚ} {X : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ)} :
    X ∈ dvdEntrySubgroup v c ↔ c ∣ X 1 0 := Iff.rfl

theorem index_dvdEntrySubgroup_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (n : ℕ) :
    (dvdEntrySubgroup v (((ℓ : ℕ) : v.adicCompletionIntegers ℚ) ^ n)).index = ℓ ^ n := by
  classical

  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hpℓ : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = ℓ := by
    show Rat.HeightOneSpectrum.natGenerator v = ℓ
    have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ ℓ := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
      have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
      rwa [map_natCast] at this
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hdvd
  subst hpℓ
  set p : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ) with hp
  let e : v.adicCompletionIntegers ℚ ≃+* ℤ_[p] :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
  let e' : v.adicCompletionIntegers ℚ →+* ℤ_[p] := e
  have he' : ∀ x, e' x = e x := fun x => rfl

  let π₁₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ) →+ v.adicCompletionIntegers ℚ :=
    { toFun := fun X => X 1 0
      map_zero' := rfl
      map_add' := fun X Y => rfl }
  let g : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ) →+ ZMod (p ^ n) :=
    ((PadicInt.toZModPow n).toAddMonoidHom.comp e'.toAddMonoidHom).comp π₁₀
  have hg : ∀ X, g X = PadicInt.toZModPow n (e' (X 1 0)) := fun X => rfl
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨y, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow n) z
    refine ⟨Matrix.of fun i j => if i = 1 ∧ j = 0 then e.symm y else 0, ?_⟩
    rw [hg, Matrix.of_apply, if_pos ⟨rfl, rfl⟩, he', RingEquiv.apply_symm_apply]
  have hpcast : ((p : ℕ) : ℤ_[p]) = e' ((p : ℕ) : v.adicCompletionIntegers ℚ) := by
    rw [map_natCast]
  have hker : g.ker = dvdEntrySubgroup v (((p : ℕ) : v.adicCompletionIntegers ℚ) ^ n) := by
    ext X
    rw [AddMonoidHom.mem_ker, mem_dvdEntrySubgroup, hg, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
      Ideal.mem_span_singleton, hpcast, ← map_pow, he', he']
    exact map_dvd_iff e
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top, Nat.card_zmod]

end Index

end L1LocalIndexDiag

open scoped Quaternion TensorProduct NumberField Pointwise in
open QuaternionAlgebra IsDedekindDomain NumberField L1LocalIndexDiag in
theorem solution
    {a b : ℚ} (hab : a ≠ 0 ∧ b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (A : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hA : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ A ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hki : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ)
    (n : ℕ) (B : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hB : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ B ↔
      (∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ) ∧
        ∀ i j, (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n)⁻¹] *
          ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ z *
          (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
          Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n]) i j ∈ v.adicCompletionIntegers ℚ) :
    B.relIndex A = ℓ ^ n := by
  classical

  set kM : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hkM
  set kiM : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
    ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hkiM
  have hkk : kM * kiM = 1 := by rw [hkM, hkiM]; exact Units.mul_inv k
  have hkk' : kiM * kM = 1 := by rw [hkM, hkiM]; exact Units.inv_mul k
  set Dinv : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
    Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n)⁻¹] with hDinv
  set D : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
    Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n] with hD
  have hℓK : ((ℓ : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) ℓ]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  have hℓnK : (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n) ≠ 0 := pow_ne_zero _ hℓK
  have hℓO : ((ℓ : ℕ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := natCast_mem _ ℓ
  have hℓnO : (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n) ∈ v.adicCompletionIntegers ℚ := pow_mem hℓO n

  let ψ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ →+ Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
    (AddMonoidHom.mulRight kM).comp ((AddMonoidHom.mulLeft kiM).comp φ.toAddMonoidHom)
  have hψ : ∀ z, ψ z = kiM * φ z * kM := fun z => rfl
  have hψinj : Function.Injective ψ := by
    intro z w hzw
    rw [hψ, hψ] at hzw
    have : kM * (kiM * φ z * kM) * kiM = kM * (kiM * φ w * kM) * kiM := by rw [hzw]
    simp only [mul_assoc, hkk] at this
    rw [mul_one, mul_one, ← mul_assoc, ← mul_assoc, hkk, one_mul, one_mul] at this
    exact φ.injective this

  set L : AddSubgroup (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
    (⊤ : AddSubgroup (Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ))).map (intMatrixEmb v).toAddMonoidHom with hLdef
  have hL : ∀ M, M ∈ L ↔ ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ := by
    intro M
    rw [← exists_intMatrixEmb_eq_iff, hLdef, AddSubgroup.mem_map]
    constructor
    · rintro ⟨A, -, rfl⟩; exact ⟨A, rfl⟩
    · rintro ⟨A, rfl⟩; exact ⟨A, trivial, rfl⟩

  have hAL : A.map ψ = L := by
    ext M
    rw [AddSubgroup.mem_map, hL]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hψ]
      exact integral_mul v (integral_mul v hki ((hA z).mp hz)) hk
    · intro hM
      refine ⟨φ.symm (kM * M * kiM), (hA _).mpr ?_, ?_⟩
      · rw [RingEquiv.apply_symm_apply]
        exact integral_mul v (integral_mul v hk hM) hki
      · rw [hψ, RingEquiv.apply_symm_apply]
        simp only [mul_assoc]
        rw [hkk', mul_one, ← mul_assoc, hkk', one_mul]

  have hdiag : ∀ (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (i j : Fin 2),
      (Dinv * M * D) i j = (![(1 : v.adicCompletion ℚ), (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n)⁻¹] i) * M i j *
        (![(1 : v.adicCompletion ℚ), ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n] j) := by
    intro M i j
    rw [hDinv, hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hcond : ∀ X : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ),
      (∀ i j, (Dinv * intMatrixEmb v X * D) i j ∈ v.adicCompletionIntegers ℚ) ↔
        (((ℓ : ℕ) : v.adicCompletionIntegers ℚ) ^ n) ∣ X 1 0 := by
    intro X
    have hent : ∀ i j, intMatrixEmb v X i j = ((X i j : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) :=
      fun i j => rfl
    constructor
    · intro h
      have h10 := h 1 0
      rw [hdiag, hent] at h10
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_fin_one, mul_one] at h10
      refine ⟨⟨_, h10⟩, Subtype.ext ?_⟩
      have e1 : ((((((ℓ : ℕ) : v.adicCompletionIntegers ℚ) ^ n) * ⟨_, h10⟩ : v.adicCompletionIntegers ℚ)) :
          v.adicCompletion ℚ) = (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n) *
            ((((ℓ : ℕ) : v.adicCompletion ℚ) ^ n)⁻¹ * ((X 1 0 : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) := by
        push_cast
        rfl
      rw [e1, ← mul_assoc, mul_inv_cancel₀ hℓnK, one_mul]
    · rintro ⟨T, hT⟩ i j
      rw [hdiag, hent]
      have hX10 : ((X 1 0 : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
          (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n) * ((T : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := by
        have h' := congrArg (fun z : v.adicCompletionIntegers ℚ => (z : v.adicCompletion ℚ)) hT
        push_cast at h'
        exact h'
      fin_cases i <;> fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, one_mul, mul_one]
        exact (X 0 0).2
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_fin_one, one_mul]
        exact mul_mem (X 0 1).2 hℓnO
      · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
          Matrix.cons_val_fin_one, mul_one]
        rw [hX10, ← mul_assoc, inv_mul_cancel₀ hℓnK, one_mul]
        exact T.2
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
          Matrix.cons_val_fin_one]
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hℓnK, one_mul]
        exact (X 1 1).2

  have hBE : B.map ψ = (dvdEntrySubgroup v (((ℓ : ℕ) : v.adicCompletionIntegers ℚ) ^ n)).map
      (intMatrixEmb v).toAddMonoidHom := by
    ext M
    rw [AddSubgroup.mem_map, AddSubgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hz1, hz2⟩ := (hB z).mp hz
      have hint : ∀ i j, ψ z i j ∈ v.adicCompletionIntegers ℚ := by
        rw [hψ]; exact integral_mul v (integral_mul v hki hz1) hk
      obtain ⟨X, hX⟩ := (exists_intMatrixEmb_eq_iff v _).mpr hint
      refine ⟨X, (mem_dvdEntrySubgroup v).mpr ((hcond X).mp ?_), hX⟩
      intro i j
      rw [hX, hψ]
      have := hz2 i j
      rwa [show Dinv * kiM * φ z * kM * D = Dinv * (kiM * φ z * kM) * D from by simp only [mul_assoc]] at this
    · rintro ⟨X, hX, rfl⟩
      rw [mem_dvdEntrySubgroup] at hX
      have hM : ∀ i j, intMatrixEmb v X i j ∈ v.adicCompletionIntegers ℚ := fun i j => (X i j).2
      refine ⟨φ.symm (kM * intMatrixEmb v X * kiM), (hB _).mpr ⟨?_, ?_⟩, ?_⟩
      · rw [RingEquiv.apply_symm_apply]
        exact integral_mul v (integral_mul v hk hM) hki
      · intro i j
        rw [RingEquiv.apply_symm_apply,
          show Dinv * kiM * (kM * intMatrixEmb v X * kiM) * kM * D = Dinv * intMatrixEmb v X * D from by
            simp only [mul_assoc]
            rw [← mul_assoc kiM kM D, hkk', one_mul, ← mul_assoc kiM kM, hkk', one_mul]]
        exact (hcond X).mpr hX i j
      · show ψ (φ.symm (kM * intMatrixEmb v X * kiM)) = intMatrixEmb v X
        rw [hψ, RingEquiv.apply_symm_apply]
        simp only [mul_assoc]
        rw [hkk', mul_one, ← mul_assoc, hkk', one_mul]

  rw [← AddSubgroup.relIndex_map_map_of_injective B A hψinj, hAL, hBE, hLdef,
    AddSubgroup.relIndex_map_map_of_injective _ _ (intMatrixEmb_injective v), AddSubgroup.relIndex_top_right]
  exact index_dvdEntrySubgroup_pow v hℓ hv n

end S_QuaternionAlgebra_relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral
end P2MW
export P2MW.S_QuaternionAlgebra_relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral (solution)
