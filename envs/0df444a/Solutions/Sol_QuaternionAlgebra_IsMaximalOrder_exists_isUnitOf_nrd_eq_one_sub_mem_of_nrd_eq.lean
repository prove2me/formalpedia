-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9c0a314f-a7ea-52c7-bbc4-8002beffe603

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsOrder_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_exists_ne_neg_one_of_ne_zero
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_localBox_nrd_eq_one_eq_tmul_add_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

noncomputable section

namespace SaModN

variable {a b : ℚ}

def IsCoord (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (ψ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) : Prop :=
  ∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
    ψ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re,
      algebraMap ℚ (v.adicCompletion ℚ) z.imI, algebraMap ℚ (v.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
        ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])

theorem localTarget {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hqv : (q : 𝓞 ℚ) ∉ v.asIdeal) (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal)
    {N : ℕ} (hNv : (N : 𝓞 ℚ) ∈ v.asIdeal)
    (c : ℍ[ℚ, a, b]) (hc : c ∈ Λ) (k : ℤ) (hnrd : nrd c = 1 + (N : ℚ) * (k : ℚ)) :
    ∃ s ∈ Submodule.localBox Λ v,
      (∀ ψ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
          ψ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re,
            algebraMap ℚ (v.adicCompletion ℚ) z.imI, algebraMap ℚ (v.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
              ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a,
                algebraMap ℚ (v.adicCompletion ℚ) b])) →
        nrd (ψ s) = 1) ∧
      ∃ z ∈ Submodule.localBox Λ v, s = c ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) + (N : ℚ) • z :=
  QuaternionAlgebra.IsMaximalOrder.exists_mem_localBox_nrd_eq_one_eq_tmul_add_smul hB Λ hΛ v hqv hq'v hNv c hc k hnrd

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_injective {w w' : HeightOneSpectrum (𝓞 ℚ)}
    (h : Rat.HeightOneSpectrum.natGenerator w = Rat.HeightOneSpectrum.natGenerator w') : w = w' := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

def placeOf (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

theorem natGenerator_placeOf (p : ℕ) (hp : p.Prime) : Rat.HeightOneSpectrum.natGenerator (placeOf p hp) = p := by
  have := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩
  exact congrArg Subtype.val this

theorem mem_placeOf (p : ℕ) (hp : p.Prime) : (p : 𝓞 ℚ) ∈ (placeOf p hp).asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_placeOf]

theorem eq_placeOf_of_mem {p : ℕ} (hp : p.Prime) {w : HeightOneSpectrum (𝓞 ℚ)} (h : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    w = placeOf p hp := by
  apply natGenerator_injective
  rw [natGenerator_placeOf]
  rw [natCast_mem_asIdeal_iff] at h
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hp).1 h

theorem not_mem_of_prime_ne {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : r ≠ p) :
    (r : 𝓞 ℚ) ∉ (placeOf p hp).asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_placeOf]
  intro h
  exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 h).symm

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem valuation_natCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hn : ¬ Rat.HeightOneSpectrum.natGenerator w ∣ n) : w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_natCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 ?_
  rwa [natCast_mem_asIdeal_iff]

theorem inv_natCast_mem_adicCompletionIntegers (w : HeightOneSpectrum (𝓞 ℚ)) {N : ℕ} (hN : N ≠ 0)
    (hn : ¬ Rat.HeightOneSpectrum.natGenerator w ∣ N) :
    (algebraMap ℚ (w.adicCompletion ℚ) ((N : ℚ)⁻¹)) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, map_inv₀,
    valuation_natCast_eq_one_of_not_dvd w N hn, inv_one]

section box
variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))

theorem tmul_mem_localBox {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) {t : v.adicCompletion ℚ}
    (ht : t ∈ v.adicCompletionIntegers ℚ) : z ⊗ₜ[ℚ] t ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, t, ht, rfl⟩

theorem tmul_one_mem_localBox {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v :=
  tmul_mem_localBox v hz (one_mem _)

theorem mul_mem_localBox (hΛ : IsOrder Λ) {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) : x * y ∈ Submodule.localBox Λ v := by
  unfold Submodule.localBox at *
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    obtain ⟨z', hz', t', ht', rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x hx' =>
      obtain ⟨z, hz, t, ht, rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨z * z', hΛ.mul_mem hz hz', t * t', mul_mem ht ht', rfl⟩
    | zero => rw [zero_mul]; exact zero_mem _
    | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
    | neg x _ hx =>
      have h : -x * (z' ⊗ₜ[ℚ] t') = -(x * (z' ⊗ₜ[ℚ] t')) := neg_mul x _
      rw [h]; exact neg_mem hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
  | neg y _ hy =>
    have h : x * -y = -(x * y) := mul_neg x y
    rw [h]; exact neg_mem hy

theorem one_mem_localBox (hΛ : IsOrder Λ) : (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [Algebra.TensorProduct.one_def]; exact tmul_one_mem_localBox v hΛ.one_mem

theorem natCast_smul_mem_localBox (N : ℕ) {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox Λ v) : (N : ℚ) • x ∈ Submodule.localBox Λ v := by
  rw [Nat.cast_smul_eq_nsmul]; exact AddSubgroup.nsmul_mem _ hx N

theorem integer_mul_mem_localBox (hΛ : IsOrder Λ) {t : v.adicCompletion ℚ} (ht : t ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) * x ∈ Submodule.localBox Λ v :=
  mul_mem_localBox v hΛ (tmul_mem_localBox v hΛ.one_mem ht) hx

theorem ratSmul_eq_mul (r : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    r • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) r) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z t =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem expand (N : ℚ) (x y z z' : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    (x + N • z) * (y + N • z') = x * y + N • (x * z' + z * y + N • (z * z')) := by
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  module

end box

theorem mem_of_forall_tmul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {z : ℍ[ℚ, a, b]}
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v) : z ∈ Λ := by
  rw [← Submodule.ofFiniteIdele_one Λ hΛ.fg hΛ.spanTop, Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  refine ⟨z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ), ?_, ?_⟩
  · rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop]
    intro v
    rw [Submodule.finiteAdeleEvalAt_tmul]
    exact h v
  · simp

theorem star_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨t, ht⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hx).2
  have e : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← add_star_eq_coe_trd]; abel
  rw [e, ← ht]
  refine sub_mem ?_ hx
  have : (((t : ℤ) : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [this]; exact Λ.smul_mem t hΛ.one_mem

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

end SaModN

end

open SaModN in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (c : ℍ[ℚ, a, b]) (hc : c ∈ Λ) (k : ℤ) (hnrd : nrd c = 1 + (N : ℚ) * (k : ℚ)) :
    ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ ∃ z ∈ Λ, u - c = (N : ℤ) • z := by
  classical
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N
  have hD : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x :=
    fun x hx => QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB x hx
  obtain ⟨ha, hb⟩ : a ≠ 0 ∧ b ≠ 0 := by
    have key : ∀ y : ℍ[ℚ, a, b], y ≠ 0 → y * y = 0 → False := by
      intro y hy hyy
      obtain ⟨u, rfl⟩ := hD y hy
      apply hy
      calc (u : ℍ[ℚ, a, b]) = ↑u⁻¹ * (↑u * ↑u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = 0 := by rw [hyy, mul_zero]
    refine ⟨fun h0 => key ⟨0, 1, 0, 0⟩ ?_ ?_, fun h0 => key ⟨0, 0, 1, 0⟩ ?_ ?_⟩
    · intro h; simpa using congrArg QuaternionAlgebra.imI h
    · ext <;> simp [h0]
    · intro h; simpa using congrArg QuaternionAlgebra.imJ h
    · ext <;> simp [h0]

  have main : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ∣ N) →
      ∃ u : ℍ[ℚ, a, b], nrd u = 1 ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), (∀ p ∈ S, (p : 𝓞 ℚ) ∉ v.asIdeal) →
          ∃ z ∈ Submodule.localBox Λ v, u ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) = 1 + (N : ℚ) • z) ∧
        (∀ p ∈ S, ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal →
          ∃ z ∈ Submodule.localBox Λ v,
            u ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) = c ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) + (N : ℚ) • z) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, nrd_one, fun v _ => ⟨0, zero_mem _, ?_⟩, fun p hp => absurd hp (Finset.notMem_empty p)⟩
      rw [smul_zero, add_zero]; rfl
    | insert p S hpS ih =>
      intro hS
      obtain ⟨u', hu'1, hA, hBc⟩ := ih (fun r hr => hS r (Finset.mem_insert_of_mem hr))
      obtain ⟨hp, hpN⟩ := hS p (Finset.mem_insert_self p S)
      have hpq : p ≠ q := by rintro rfl; exact hqN hpN
      have hpq' : p ≠ q' := by rintro rfl; exact hq'N hpN
      set vp := placeOf p hp with hvp
      have hqv : (q : 𝓞 ℚ) ∉ vp.asIdeal := not_mem_of_prime_ne hp (Fact.out) (Ne.symm hpq)
      have hq'v : (q' : 𝓞 ℚ) ∉ vp.asIdeal := not_mem_of_prime_ne hp (Fact.out) (Ne.symm hpq')
      have hNv : (N : 𝓞 ℚ) ∈ vp.asIdeal := by
        rw [natCast_mem_asIdeal_iff, natGenerator_placeOf]; exact hpN
      have hsplit : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] vp.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x := by
        by_contra hall
        push Not at hall
        have : (q : 𝓞 ℚ) ∈ vp.asIdeal ∨ (q' : 𝓞 ℚ) ∈ vp.asIdeal := (hB.2 vp).1 (fun x hx => hall x hx)
        exact this.elim hqv hq'v

      obtain ⟨s, hsΛ, hs1, z₀, hz₀, hsz⟩ := localTarget hB Λ hΛ vp hqv hq'v hNv c hc k hnrd
      obtain hkn := QuaternionAlgebra.IsOrder.exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_forall_isUnit
        hB.1 hD hΛo vp hsplit
      obtain ⟨β, hβ1, hβaway, zv, hzv, hβv⟩ :=
        QuaternionAlgebra.IsOrder.forall_exists_nrd_eq_one_tmul_eq_add_smul_of_exists_ne_neg_one_of_ne_zero
          ha hb hΛo vp hsplit hkn s hs1 N hN0
      have hmul : ∀ w : HeightOneSpectrum (𝓞 ℚ),
          (u' * β) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = (u' ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * (β ⊗ₜ[ℚ] 1) := by
        intro w; rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      have hcmem : ∀ w : HeightOneSpectrum (𝓞 ℚ), c ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w :=
        fun w => tmul_one_mem_localBox w hc
      refine ⟨u' * β, by rw [nrd_mul', hu'1, hβ1, one_mul], ?_, ?_⟩
      ·
        intro v hv
        have hvS : ∀ r ∈ S, (r : 𝓞 ℚ) ∉ v.asIdeal := fun r hr => hv r (Finset.mem_insert_of_mem hr)
        have hvp' : v ≠ vp := by
          intro h; exact hv p (Finset.mem_insert_self p S) (h ▸ mem_placeOf p hp)
        obtain ⟨z₂, hz₂, e₂⟩ := hA v hvS
        obtain ⟨z₁, hz₁, e₁⟩ := hβaway v hvp'
        refine ⟨z₁ + z₂ + (N : ℚ) • (z₂ * z₁), ?_, ?_⟩
        · exact add_mem (add_mem hz₁ hz₂) (natCast_smul_mem_localBox v N (mul_mem_localBox v hΛo hz₂ hz₁))
        · rw [hmul, e₂, e₁, expand]; simp only [one_mul, mul_one]
      ·
        intro r hr v hv
        rcases Finset.mem_insert.1 hr with hrp | hrS
        ·
          rw [hrp] at hv
          have hveq : v = vp := eq_placeOf_of_mem hp hv
          subst hveq
          have hvS : ∀ r' ∈ S, (r' : 𝓞 ℚ) ∉ (placeOf p hp).asIdeal := by
            intro r' hr'
            have hr'p : r' ≠ p := fun h => hpS (h ▸ hr')
            exact not_mem_of_prime_ne hp (hS r' (Finset.mem_insert_of_mem hr')).1 hr'p
          obtain ⟨z₂, hz₂, e₂⟩ := hA _ hvS
          refine ⟨(z₀ + zv) + z₂ * (c ⊗ₜ[ℚ] 1) + (N : ℚ) • (z₂ * (z₀ + zv)), ?_, ?_⟩
          · exact add_mem (add_mem (add_mem hz₀ hzv) (mul_mem_localBox _ hΛo hz₂ (hcmem _)))
              (natCast_smul_mem_localBox _ N (mul_mem_localBox _ hΛo hz₂ (add_mem hz₀ hzv)))
          · have e₁ : β ⊗ₜ[ℚ] (1 : (placeOf p hp).adicCompletion ℚ) = c ⊗ₜ[ℚ] 1 + (N : ℚ) • (z₀ + zv) := by
              rw [hβv, hsz, smul_add]; abel
            rw [hmul, e₂, e₁, expand]; simp only [one_mul]
        ·
          have hrp : r ≠ p := fun h => hpS (h ▸ hrS)
          have hvp' : v ≠ vp := by
            intro h
            exact not_mem_of_prime_ne hp (hS r hr).1 hrp (by rw [← hvp, ← h]; exact hv)
          obtain ⟨z₂, hz₂, e₂⟩ := hBc r hrS v hv
          obtain ⟨z₁, hz₁, e₁⟩ := hβaway v hvp'
          refine ⟨(c ⊗ₜ[ℚ] 1) * z₁ + z₂ + (N : ℚ) • (z₂ * z₁), ?_, ?_⟩
          · exact add_mem (add_mem (mul_mem_localBox v hΛo (hcmem v) hz₁) hz₂)
              (natCast_smul_mem_localBox v N (mul_mem_localBox v hΛo hz₂ hz₁))
          · rw [hmul, e₂, e₁, expand]; simp only [mul_one]

  obtain ⟨u, hu1, hA, hBc⟩ :=
    main N.primeFactors (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩)
  have hcmem : ∀ w : HeightOneSpectrum (𝓞 ℚ), c ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w :=
    fun w => tmul_one_mem_localBox w hc

  have hplaces : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (∃ p ∈ N.primeFactors, (p : 𝓞 ℚ) ∈ v.asIdeal) ∨
        ((∀ p ∈ N.primeFactors, (p : 𝓞 ℚ) ∉ v.asIdeal) ∧ ¬ Rat.HeightOneSpectrum.natGenerator v ∣ N) := by
    intro v
    by_cases h : ∃ p ∈ N.primeFactors, (p : 𝓞 ℚ) ∈ v.asIdeal
    · exact Or.inl h
    · push Not at h
      refine Or.inr ⟨h, fun hdvd => ?_⟩
      have hmem : Rat.HeightOneSpectrum.natGenerator v ∈ N.primeFactors :=
        Nat.mem_primeFactors.2 ⟨Rat.HeightOneSpectrum.prime_natGenerator v, hdvd, hN0⟩
      exact h _ hmem ((natCast_mem_asIdeal_iff v _).2 dvd_rfl)

  have huΛ : u ∈ Λ := by
    apply mem_of_forall_tmul_mem_localBox hΛo
    intro v
    rcases hplaces v with ⟨p, hp, hpv⟩ | ⟨hnone, -⟩
    · obtain ⟨z, hz, e⟩ := hBc p hp v hpv
      rw [e]; exact add_mem (hcmem v) (natCast_smul_mem_localBox v N hz)
    · obtain ⟨z, hz, e⟩ := hA v hnone
      rw [e]; exact add_mem (one_mem_localBox v hΛo) (natCast_smul_mem_localBox v N hz)

  set y : ℍ[ℚ, a, b] := ((N : ℚ)⁻¹) • (u - c) with hy
  have hyΛ : y ∈ Λ := by
    apply mem_of_forall_tmul_mem_localBox hΛo
    intro v
    have ey : y ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) = ((N : ℚ)⁻¹) • (u ⊗ₜ[ℚ] 1 - c ⊗ₜ[ℚ] 1) := by
      rw [hy, ← TensorProduct.smul_tmul', TensorProduct.sub_tmul]
    rcases hplaces v with ⟨p, hp, hpv⟩ | ⟨hnone, hndvd⟩
    · obtain ⟨z, hz, e⟩ := hBc p hp v hpv
      rw [ey, e, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN0 : (N : ℚ) ≠ 0), one_smul]
      exact hz
    · obtain ⟨z, hz, e⟩ := hA v hnone
      have hdiff : u ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) - c ⊗ₜ[ℚ] 1 ∈ Submodule.localBox Λ v := by
        rw [e]; exact sub_mem (add_mem (one_mem_localBox v hΛo) (natCast_smul_mem_localBox v N hz)) (hcmem v)
      rw [ey, ratSmul_eq_mul]
      exact integer_mul_mem_localBox v hΛo (inv_natCast_mem_adicCompletionIntegers v hN0 hndvd) hdiff
  refine ⟨u, ⟨huΛ, star u, star_mem hΛo huΛ, ?_, ?_⟩, hu1, y, hyΛ, ?_⟩
  · rw [mul_star_eq_coe_nrd, hu1]; rfl
  · rw [star_mul_eq_coe_nrd, hu1]; rfl
  · rw [hy, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN0 : (N : ℚ) ≠ 0), one_smul]

end S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq (solution)
