-- Prove2me | solution 1 for ResidualGaloisRep.isStrictOrdinaryAt_ofResidualGaloisRep_of_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bc3d7a3a-53e3-5f42-9a8a-b071f139533c

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_isStrictOrdinaryAt_ofResidualGaloisRep_of_baseChangeAlong

set_option autoImplicit false

namespace P2mStrictDescent

open Module

section Coord

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
  (b : Basis (Fin 2) A V)

theorem repr_one_eq_zero_of_mem {v : V} (hv : v ∈ A ∙ b 0) : b.repr v 1 = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, if_neg (by decide),
    smul_zero]

theorem mem_of_repr_one_eq_zero {v : V} (hv : b.repr v 1 = 0) : v ∈ A ∙ b 0 := by
  have h := b.sum_repr v
  rw [Fin.sum_univ_two, hv, zero_smul, add_zero] at h
  rw [← h]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem mem_iff_repr_one_eq_zero (v : V) : v ∈ A ∙ b 0 ↔ b.repr v 1 = 0 :=
  ⟨repr_one_eq_zero_of_mem b, mem_of_repr_one_eq_zero b⟩

noncomputable def xc (f : V →ₗ[A] V) : A := b.repr (f (b 0)) 0

noncomputable def yc (f : V →ₗ[A] V) : A := b.repr (f (b 1)) 0

noncomputable def zc (f : V →ₗ[A] V) : A := b.repr (f (b 1)) 1

def Pres (f : V →ₗ[A] V) : Prop := ∀ v ∈ A ∙ b 0, f v ∈ A ∙ b 0

variable {b}

theorem apply_b0 {f : V →ₗ[A] V} (hf : Pres b f) : f (b 0) = xc b f • b 0 := by
  have h := b.sum_repr (f (b 0))
  rw [Fin.sum_univ_two, repr_one_eq_zero_of_mem b (hf _ (Submodule.mem_span_singleton_self _)),
    zero_smul, add_zero] at h
  exact h.symm

theorem apply_b1 (f : V →ₗ[A] V) : f (b 1) = yc b f • b 0 + zc b f • b 1 := by
  have h := b.sum_repr (f (b 1))
  rw [Fin.sum_univ_two] at h
  exact h.symm

theorem repr_b0_one : b.repr (b 0) 1 = 0 := by
  rw [b.repr_self, Finsupp.single_apply, if_neg (by decide)]

theorem repr_b1_one : b.repr (b 1) 1 = 1 := by
  rw [b.repr_self, Finsupp.single_apply, if_pos rfl]

theorem apply_eq_xc_smul {f : V →ₗ[A] V} (hf : Pres b f) {w : V} (hw : w ∈ A ∙ b 0) :
    f w = xc b f • w := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, apply_b0 hf, smul_comm]

theorem sub_zc_smul_mem {f : V →ₗ[A] V} (hf : Pres b f) (v : V) :
    f v - zc b f • v ∈ A ∙ b 0 := by
  rw [mem_iff_repr_one_eq_zero]
  have h := b.sum_repr v
  rw [Fin.sum_univ_two] at h
  rw [← h]
  simp only [map_add, map_sub, map_smul, smul_add, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, smul_eq_mul, apply_b0 hf, apply_b1 f, repr_b0_one, repr_b1_one]
  ring

theorem eq_xc_of_apply_eq_smul {f : V →ₗ[A] V} (_hf : Pres b f) {x : A}
    (hx : f (b 0) = x • b 0) : x = xc b f := by
  have h := congrArg (fun v => b.repr v 0) hx
  simp only [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] at h
  exact h.symm

theorem eq_zc_of_sub_smul_mem {f : V →ₗ[A] V} {z : A} (hz : f (b 1) - z • b 1 ∈ A ∙ b 0) :
    z = zc b f := by
  have h1 := repr_one_eq_zero_of_mem b hz
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, repr_b1_one, smul_eq_mul,
    mul_one, sub_eq_zero] at h1
  exact h1.symm

end Coord

section BC

variable {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') (ρ : ResidualGaloisRep k)

noncomputable abbrev R' : GaloisRepAdic k' :=
  GaloisRepAdic.ofResidualGaloisRep (ρ.baseChangeAlong ψ)

noncomputable def tm (c : k') (v : ρ.V) : (R' ψ ρ).V :=
  letI : Algebra k k' := ψ.toAlgebra
  c ⊗ₜ[k] v

theorem tm_add (c : k') (v w : ρ.V) : tm ψ ρ c (v + w) = tm ψ ρ c v + tm ψ ρ c w := by
  letI : Algebra k k' := ψ.toAlgebra
  show c ⊗ₜ[k] (v + w) = c ⊗ₜ[k] v + c ⊗ₜ[k] w
  exact TensorProduct.tmul_add c v w

theorem tm_sub (c : k') (v w : ρ.V) : tm ψ ρ c (v - w) = tm ψ ρ c v - tm ψ ρ c w := by
  letI : Algebra k k' := ψ.toAlgebra
  show c ⊗ₜ[k] (v - w) = c ⊗ₜ[k] v - c ⊗ₜ[k] w
  exact TensorProduct.tmul_sub c v w

theorem tm_smul (c : k') (a : k) (v : ρ.V) : tm ψ ρ c (a • v) = ψ a • tm ψ ρ c v := by
  letI : Algebra k k' := ψ.toAlgebra
  show c ⊗ₜ[k] (a • v) = ψ a • (c ⊗ₜ[k] v)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← smul_eq_mul,
    TensorProduct.smul_tmul']
  rfl

theorem smul_tm (c c' : k') (v : ρ.V) : c' • tm ψ ρ c v = tm ψ ρ (c' * c) v := by
  letI : Algebra k k' := ψ.toAlgebra
  show c' • (c ⊗ₜ[k] v) = (c' * c) ⊗ₜ[k] v
  rw [TensorProduct.smul_tmul', smul_eq_mul]

theorem tm_zero (c : k') : tm ψ ρ c 0 = 0 := by
  letI : Algebra k k' := ψ.toAlgebra
  show c ⊗ₜ[k] (0 : ρ.V) = 0
  exact TensorProduct.tmul_zero _ c

theorem rho_tm (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : k') (v : ρ.V) :
    (R' ψ ρ).ρ σ (tm ψ ρ c v) = tm ψ ρ c (ρ.ρ σ v) := by
  letI : Algebra k k' := ψ.toAlgebra
  show (ρ.ρ σ).baseChange k' (c ⊗ₜ[k] v) = c ⊗ₜ[k] (ρ.ρ σ v)
  exact LinearMap.baseChange_tmul _ _ _

noncomputable def bcB (b : Basis (Fin 2) k ρ.V) : Basis (Fin 2) k' (R' ψ ρ).V :=
  letI : Algebra k k' := ψ.toAlgebra
  Algebra.TensorProduct.basis k' b

theorem bcB_apply (b : Basis (Fin 2) k ρ.V) (i : Fin 2) : bcB ψ ρ b i = tm ψ ρ 1 (b i) := by
  letI : Algebra k k' := ψ.toAlgebra
  show Algebra.TensorProduct.basis k' b i = (1 : k') ⊗ₜ[k] b i
  exact Algebra.TensorProduct.basis_apply b i

theorem bcB_repr_tm (b : Basis (Fin 2) k ρ.V) (v : ρ.V) (i : Fin 2) :
    (bcB ψ ρ b).repr (tm ψ ρ 1 v) i = ψ (b.repr v i) := by
  letI : Algebra k k' := ψ.toAlgebra
  show (Algebra.TensorProduct.basis k' b).repr ((1 : k') ⊗ₜ[k] v) i = ψ (b.repr v i)
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  rfl

theorem tm_mem_iff (b : Basis (Fin 2) k ρ.V) (v : ρ.V) :
    tm ψ ρ 1 v ∈ k' ∙ bcB ψ ρ b 0 ↔ v ∈ k ∙ b 0 := by
  rw [mem_iff_repr_one_eq_zero, mem_iff_repr_one_eq_zero, bcB_repr_tm,
    map_eq_zero_iff ψ ψ.injective]

theorem tm_one_injective : Function.Injective (tm ψ ρ 1) := by
  intro v w h
  obtain ⟨b⟩ : Nonempty (Basis (Fin 2) k ρ.V) := ⟨Module.finBasisOfFinrankEq k ρ.V ρ.finrank_eq⟩
  apply b.repr.injective
  ext i
  apply ψ.injective
  rw [← bcB_repr_tm, ← bcB_repr_tm, h]

end BC

end P2mStrictDescent

open P2mStrictDescent Module in
theorem solution
    {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') (ρ : ResidualGaloisRep k)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (GaloisRepAdic.ofResidualGaloisRep (ρ.baseChangeAlong ψ)).IsStrictOrdinaryAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsStrictOrdinaryAt p := by
  obtain ⟨hpk', h⟩ := h

  suffices H : (p : k) ∈ IsLocalRing.maximalIdeal k ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∃ L : Submodule k ρ.V,
          (∃ b : Basis (Fin 2) k ρ.V, L = k ∙ b 0) ∧
          (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
          (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) ∧
          (∀ σ ∈ P.decompositionSubgroup ℚ, ∃ x z : k,
            (∀ w ∈ L, ρ.ρ σ w = x • w) ∧ (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) ∧
            ∀ (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
              x - (a : k) * z ∈ Ideal.span {((p ^ n : ℕ) : k)}) from H

  have hp0' : (p : k') = 0 := by
    have hbot : IsLocalRing.maximalIdeal k' = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    rw [hbot, Ideal.mem_bot] at hpk'
    exact hpk'
  have hp0 : (p : k) = 0 := by
    apply ψ.injective
    rw [map_natCast, map_zero, hp0']
  refine ⟨?_, fun P hP => ?_⟩
  · rw [hp0]
    exact Ideal.zero_mem _
  obtain ⟨L', ⟨b', hL'⟩, hD', hI', hS'⟩ := h P hP

  have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  obtain ⟨σ₀, hσ₀I, hσ₀μ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow P hp hP (ZMod.unitOfCoprime 2 h2p)
  have hval : ((ZMod.unitOfCoprime 2 h2p : (ZMod p)ˣ) : ZMod p).val = 2 := by
    rw [ZMod.coe_unitOfCoprime, Nat.cast_ofNat, ZMod.val_ofNat_of_lt]
    exact lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  rw [hval] at hσ₀μ
  have hσ₀D : σ₀ ∈ P.decompositionSubgroup ℚ := Subgroup.map_subtype_le _ hσ₀I

  obtain ⟨x', z', hx', hz', hc'⟩ := hS' σ₀ hσ₀D
  have hz'1 : z' = 1 := by

    have e1 : z' = zc b' ((R' ψ ρ).ρ σ₀) :=
      eq_zc_of_sub_smul_mem (b := b') (by rw [← hL']; exact hz' _)
    have e2 : (1 : k') = zc b' ((R' ψ ρ).ρ σ₀) :=
      eq_zc_of_sub_smul_mem (b := b') (by rw [← hL', one_smul]; exact hI' σ₀ hσ₀I _)
    rw [e1, ← e2]
  have hx'2 : x' = 2 := by
    have h1 := hc' 1 2 (by simpa only [pow_one] using hσ₀μ)
    rw [pow_one, hp0', Ideal.span_singleton_zero, Ideal.mem_bot, hz'1, mul_one, sub_eq_zero] at h1
    exact_mod_cast h1
  have hfixL' : ∀ w ∈ L', (R' ψ ρ).ρ σ₀ w - w = w := by
    intro w hw
    rw [hx' w hw, hx'2, two_smul, add_sub_cancel_right]

  obtain ⟨e⟩ : Nonempty (Basis (Fin 2) k ρ.V) := ⟨Module.finBasisOfFinrankEq k ρ.V ρ.finrank_eq⟩
  have hex : ∃ i : Fin 2, ρ.ρ σ₀ (e i) - e i ≠ 0 := by
    by_contra hall
    push Not at hall

    have htriv : ρ.ρ σ₀ = 1 := by
      refine e.ext fun i => ?_
      rw [Module.End.one_apply]
      exact sub_eq_zero.mp (hall i)
    have hb'0 : b' 0 ∈ L' := by rw [hL']; exact Submodule.mem_span_singleton_self _
    have h1 := hfixL' (b' 0) hb'0
    have h2 : (R' ψ ρ).ρ σ₀ (b' 0) = b' 0 := by
      have : (R' ψ ρ).ρ σ₀ = 1 := by
        show (ρ.baseChangeAlong ψ).ρ σ₀ = 1
        letI : Algebra k k' := ψ.toAlgebra
        show (ρ.ρ σ₀).baseChange k' = 1
        rw [htriv, LinearMap.baseChange_one]
      rw [this, Module.End.one_apply]
    rw [h2, sub_self] at h1
    exact b'.ne_zero 0 h1.symm
  obtain ⟨i, hi⟩ := hex
  set w : ρ.V := ρ.ρ σ₀ (e i) - e i with hw
  have hw' : tm ψ ρ 1 w ∈ L' := by
    rw [hw, tm_sub, ← rho_tm]
    exact hI' σ₀ hσ₀I _
  have hw'ne : tm ψ ρ 1 w ≠ 0 := by
    intro h0
    apply hi
    apply tm_one_injective ψ ρ
    rw [h0, tm_zero]

  have hL'w : L' = k' ∙ tm ψ ρ 1 w := by
    rw [hL'] at hw' ⊢
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw'
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hw'ne hc.symm
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨c⁻¹, by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨c, hc⟩

  have hwne : w ≠ 0 := fun h0 => hw'ne (by rw [h0, tm_zero])
  have hex_u : ∃ u : ρ.V, u ∉ k ∙ w := by
    by_contra hall
    push Not at hall
    have htop : (k ∙ w) = ⊤ := eq_top_iff.mpr fun u _ => hall u
    have h1 : finrank k (k ∙ w) = 1 := finrank_span_singleton hwne
    rw [htop, finrank_top, ρ.finrank_eq] at h1
    exact absurd h1 (by decide)
  obtain ⟨u, hu⟩ := hex_u
  have hli : LinearIndependent k ![w, u] := by
    rw [LinearIndependent.pair_iff' hwne]
    intro a ha
    exact hu (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)
  set b : Basis (Fin 2) k ρ.V := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, ρ.finrank_eq]) with hbdef
  have hb0 : b 0 = w := by
    rw [hbdef, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hb1 : b 1 = u := by
    rw [hbdef, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl

  have hL'b : L' = k' ∙ bcB ψ ρ b 0 := by rw [bcB_apply, hb0, hL'w]

  have presR : ∀ σ ∈ P.decompositionSubgroup ℚ, Pres b (ρ.ρ σ) := by
    intro σ hσ v hv
    rw [← tm_mem_iff ψ ρ b, ← rho_tm, ← hL'b]
    apply hD' σ hσ
    rw [hL'b, tm_mem_iff]
    exact hv
  refine ⟨k ∙ b 0, ⟨b, rfl⟩, fun σ hσ v hv => presR σ hσ v hv, ?_, ?_⟩
  ·
    intro τ hτ v
    rw [← tm_mem_iff ψ ρ b, tm_sub, ← rho_tm, ← hL'b]
    exact hI' τ hτ _
  ·
    intro σ hσ
    have hpres := presR σ hσ
    refine ⟨xc b (ρ.ρ σ), zc b (ρ.ρ σ), fun v hv => apply_eq_xc_smul hpres hv,
      fun v => sub_zc_smul_mem hpres v, fun n c hμ => ?_⟩
    obtain ⟨x', z', hx', hz', hc'⟩ := hS' σ hσ

    have hpres' : Pres (bcB ψ ρ b) ((R' ψ ρ).ρ σ) := by
      intro v hv; rw [← hL'b] at hv ⊢; exact hD' σ hσ v hv
    have ex' : x' = ψ (xc b (ρ.ρ σ)) := by
      have e1 : x' = xc (bcB ψ ρ b) ((R' ψ ρ).ρ σ) :=
        eq_xc_of_apply_eq_smul hpres' (hx' _ (by rw [hL'b]; exact Submodule.mem_span_singleton_self _))
      have e2 : ψ (xc b (ρ.ρ σ)) = xc (bcB ψ ρ b) ((R' ψ ρ).ρ σ) := by
        refine eq_xc_of_apply_eq_smul hpres' ?_
        rw [bcB_apply, rho_tm, apply_b0 hpres, tm_smul]
      rw [e1, ← e2]
    have ez' : z' = ψ (zc b (ρ.ρ σ)) := by
      have e1 : z' = zc (bcB ψ ρ b) ((R' ψ ρ).ρ σ) :=
        eq_zc_of_sub_smul_mem (b := bcB ψ ρ b) (by rw [← hL'b]; exact hz' _)
      have e2 : ψ (zc b (ρ.ρ σ)) = zc (bcB ψ ρ b) ((R' ψ ρ).ρ σ) := by
        refine eq_zc_of_sub_smul_mem (b := bcB ψ ρ b) ?_
        rw [bcB_apply ψ ρ b 1, rho_tm, ← tm_smul, ← tm_sub, tm_mem_iff]
        exact sub_zc_smul_mem hpres _
      rw [e1, ← e2]

    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, Nat.cast_one, Ideal.span_singleton_one]
      exact Submodule.mem_top
    · have hpn : ((p ^ n : ℕ) : k) = 0 := by
        rw [Nat.cast_pow, hp0, zero_pow hn.ne']
      have hpn' : ((p ^ n : ℕ) : k') = 0 := by
        rw [Nat.cast_pow, hp0', zero_pow hn.ne']
      have h1 := hc' n c hμ
      rw [hpn', Ideal.span_singleton_zero, Ideal.mem_bot, ex', ez', ← map_natCast ψ c, ← map_mul,
        ← map_sub, map_eq_zero_iff ψ ψ.injective] at h1
      rw [hpn, Ideal.span_singleton_zero, Ideal.mem_bot]
      exact h1

end S_ResidualGaloisRep_isStrictOrdinaryAt_ofResidualGaloisRep_of_baseChangeAlong
end P2MW
export P2MW.S_ResidualGaloisRep_isStrictOrdinaryAt_ofResidualGaloisRep_of_baseChangeAlong (solution)
