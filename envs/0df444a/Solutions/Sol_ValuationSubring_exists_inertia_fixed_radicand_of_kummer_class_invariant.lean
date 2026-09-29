-- Prove2me | solution 1 for ValuationSubring.exists_inertia_fixed_radicand_of_kummer_class_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c75cbd16-ec83-50d1-80bc-28431048b856

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_inertia_fixed_radicand_of_kummer_class_invariant

set_option autoImplicit false

local notation "𝓠" => AlgebraicClosure ℚ
local notation "𝓖" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace ValuationSubring
p2m_export "ValuationSubring" "ext mul_mem one_mem LiesOverPrime inertiaSubgroupIn exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one"
namespace C3dDescentAux
p2m_open "ValuationSubring"

def FixesMu (m : ℕ) (τ : 𝓖) : Prop :=
  ∀ ξ : 𝓠, ξ ^ m = 1 → τ ξ = ξ

theorem FixesMu.mul {m : ℕ} {τ τ' : 𝓖} (h : FixesMu m τ) (h' : FixesMu m τ') :
    FixesMu m (τ * τ') := fun ξ hξ => by
  rw [AlgEquiv.mul_apply, h' ξ hξ, h ξ hξ]

theorem FixesMu.inv {m : ℕ} {τ : 𝓖} (h : FixesMu m τ) : FixesMu m τ⁻¹ := fun ξ hξ => by
  conv_lhs => rw [← h ξ hξ]
  rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

theorem FixesMu.conj {m : ℕ} {τ : 𝓖} (h : FixesMu m τ) (σ : 𝓖) :
    FixesMu m (σ⁻¹ * τ * σ) := fun ξ hξ => by
  have hσξ : (σ ξ) ^ m = 1 := by rw [← map_pow, hξ, map_one]
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h _ hσξ, AlgEquiv.aut_inv,
    AlgEquiv.symm_apply_apply]

theorem FixesMu.pow_apply {m : ℕ} {τ : 𝓖} (h : FixesMu m τ) :
    ∀ (i : ℕ) (ξ : 𝓠), ξ ^ m = 1 → (τ ^ i) ξ = ξ := by
  intro i
  induction i with
  | zero => intro ξ _; rw [pow_zero, AlgEquiv.one_apply]
  | succ i ih => intro ξ hξ; rw [pow_succ, AlgEquiv.mul_apply, h ξ hξ, ih ξ hξ]

def IsFix (I : Subgroup 𝓖) (m : ℕ) (y : 𝓠) : Prop :=
  ∀ τ ∈ I, FixesMu m τ → τ y = y

section IsFix

variable {I : Subgroup 𝓖} {m : ℕ}

theorem IsFix.add {y z : 𝓠} (hy : IsFix I m y) (hz : IsFix I m z) : IsFix I m (y + z) :=
  fun τ hτ h => by rw [map_add, hy τ hτ h, hz τ hτ h]

theorem IsFix.mul {y z : 𝓠} (hy : IsFix I m y) (hz : IsFix I m z) : IsFix I m (y * z) :=
  fun τ hτ h => by rw [map_mul, hy τ hτ h, hz τ hτ h]

theorem IsFix.pow {y : 𝓠} (hy : IsFix I m y) (k : ℕ) : IsFix I m (y ^ k) :=
  fun τ hτ h => by rw [map_pow, hy τ hτ h]

theorem IsFix.inv {y : 𝓠} (hy : IsFix I m y) : IsFix I m y⁻¹ :=
  fun τ hτ h => by rw [map_inv₀, hy τ hτ h]

theorem IsFix.one : IsFix I m (1 : 𝓠) := fun τ _ _ => map_one τ

theorem IsFix.prod {ι : Type} (s : Finset ι) {f : ι → 𝓠} (hf : ∀ i ∈ s, IsFix I m (f i)) :
    IsFix I m (∏ i ∈ s, f i) := fun τ hτ h => by
  rw [map_prod]
  exact Finset.prod_congr rfl fun i hi => hf i hi τ hτ h

theorem IsFix.sum {ι : Type} (s : Finset ι) {f : ι → 𝓠} (hf : ∀ i ∈ s, IsFix I m (f i)) :
    IsFix I m (∑ i ∈ s, f i) := fun τ hτ h => by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i hi => hf i hi τ hτ h

theorem IsFix.apply {y : 𝓠} (hy : IsFix I m y) {σ : 𝓖} (hσ : σ ∈ I) :
    IsFix I m (σ y) := fun τ hτ h => by
  have key : τ * σ = σ * (σ⁻¹ * τ * σ) := by group
  rw [← AlgEquiv.mul_apply, key, AlgEquiv.mul_apply,
    hy _ (I.mul_mem (I.mul_mem (I.inv_mem hσ) hτ) hσ) (h.conj σ)]

theorem IsFix.pow_apply {y : 𝓠} (hy : IsFix I m y) {σ : 𝓖} (hσ : σ ∈ I) (i : ℕ) :
    IsFix I m ((σ ^ i) y) := hy.apply (I.pow_mem hσ i)

theorem IsFix.forall_apply_eq {y : 𝓠} (hy : IsFix I m y) {σ₀ : 𝓖} (hσ₀ : σ₀ ∈ I)
    (hσ₀y : σ₀ y = y) (hdec : ∀ σ ∈ I, ∃ i : ℕ, FixesMu m ((σ₀ ^ i)⁻¹ * σ)) :
    ∀ σ ∈ I, σ y = y := by
  have hpow : ∀ i : ℕ, (σ₀ ^ i) y = y := fun i => by
    induction i with
    | zero => rw [pow_zero, AlgEquiv.one_apply]
    | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hσ₀y, ih]
  intro σ hσ
  obtain ⟨i, hi⟩ := hdec σ hσ
  have hmem : (σ₀ ^ i)⁻¹ * σ ∈ I := I.mul_mem (I.inv_mem (I.pow_mem hσ₀ i)) hσ
  calc σ y = (σ₀ ^ i * ((σ₀ ^ i)⁻¹ * σ)) y := by rw [mul_inv_cancel_left]
    _ = y := by rw [AlgEquiv.mul_apply, hy _ hmem hi, hpow i]

def fixerSubgroup (I : Subgroup 𝓖) (m : ℕ) : Subgroup 𝓖 where
  carrier := {τ | τ ∈ I ∧ FixesMu m τ}
  mul_mem' := fun ha hb => ⟨I.mul_mem ha.1 hb.1, ha.2.mul hb.2⟩
  one_mem' := ⟨I.one_mem, fun ξ _ => AlgEquiv.one_apply ξ⟩
  inv_mem' := fun ha => ⟨I.inv_mem ha.1, ha.2.inv⟩

theorem isFix_iff_mem_fixedField (y : 𝓠) :
    IsFix I m y ↔ y ∈ IntermediateField.fixedField (fixerSubgroup I m) := by
  rw [IntermediateField.mem_fixedField_iff]
  exact ⟨fun h τ hτ => h τ hτ.1 hτ.2, fun h τ hτ hτ' => h τ ⟨hτ, hτ'⟩⟩

end IsFix

theorem pow_eq_pow_of_modEq {ξ : 𝓠} {m a b : ℕ} (hξ : ξ ^ m = 1) (h : a ≡ b [MOD m]) :
    ξ ^ a = ξ ^ b := by
  rw [← Nat.mod_add_div a m, ← Nat.mod_add_div b m, pow_add, pow_add, pow_mul, pow_mul, hξ,
    one_pow, one_pow, h]

theorem modEq_of_pow_eq_pow {ζ : 𝓠} {m a b : ℕ} [NeZero m] (hζ : IsPrimitiveRoot ζ m)
    (h : ζ ^ a = ζ ^ b) : a ≡ b [MOD m] := by
  have hζu : IsUnit ζ := hζ.isUnit (NeZero.ne m)
  have hu : IsPrimitiveRoot hζu.unit m :=
    IsPrimitiveRoot.coe_units_iff.mp (by rw [hζu.unit_spec]; exact hζ)
  have hpow : hζu.unit ^ a = hζu.unit ^ b := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hζu.unit_spec]
    exact h
  rw [hu.eq_orderOf]
  exact pow_eq_pow_iff_modEq.mp hpow

theorem exists_nat_forall_pow_eq_one_apply_eq_pow (σ : 𝓖) (m : ℕ) [NeZero m] :
    ∃ a : ℕ, ∀ μ : 𝓠, μ ^ m = 1 → σ μ = μ ^ a := by
  obtain ⟨k, hk⟩ := rootsOfUnity.integer_power_of_ringEquiv' m (σ : 𝓠 ≃+* 𝓠)
  refine ⟨(k % (m : ℤ)).toNat, fun μ hμ => ?_⟩
  have ht := hk (rootsOfUnity.mkOfPowEq μ hμ : (𝓠)ˣ) (rootsOfUnity.mkOfPowEq μ hμ).2
  rw [rootsOfUnity.val_mkOfPowEq_coe, AlgEquiv.coe_ringEquiv] at ht
  rw [ht]
  have hn : ((rootsOfUnity.mkOfPowEq μ hμ : (𝓠)ˣ)) ^ m = 1 := (rootsOfUnity.mkOfPowEq μ hμ).2
  rw [zpow_eq_zpow_emod' k hn]
  have h0 : (0 : ℤ) ≤ k % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast (NeZero.ne m))
  conv_lhs => rw [← Int.toNat_of_nonneg h0, zpow_natCast]
  rw [Units.val_pow_eq_pow_val, rootsOfUnity.val_mkOfPowEq_coe]

private theorem _root_.ValuationSubring.C3dDescentAux.exists_generator (I : Subgroup 𝓖) (p N : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : 0 < N) (ζ : 𝓠) (hζ : IsPrimitiveRoot ζ (p ^ N)) :
    ∃ σ₀ ∈ I, ∃ d : ℕ, 0 < d ∧ FixesMu (p ^ N) (σ₀ ^ d) ∧
      (∀ σ ∈ I, ∃ i : ℕ, FixesMu (p ^ N) ((σ₀ ^ i)⁻¹ * σ)) ∧
      (∀ i j : ℕ, i < d → j < d → (σ₀ ^ i) ζ = (σ₀ ^ j) ζ → i = j) := by
  classical
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.one_lt⟩
  have hpos : 0 < p ^ N := pow_pos hp.pos N

  let H : Subgroup (ZMod (p ^ N))ˣ :=
    { carrier := {u | ∃ σ ∈ I, ∀ ξ : 𝓠, ξ ^ p ^ N = 1 → σ ξ = ξ ^ (u : ZMod (p ^ N)).val}
      one_mem' := ⟨1, I.one_mem, fun ξ _ => by
        rw [AlgEquiv.one_apply, Units.val_one, ZMod.val_one, pow_one]⟩
      mul_mem' := by
        rintro u v ⟨σ, hσ, hσu⟩ ⟨τ, hτ, hτv⟩
        refine ⟨σ * τ, I.mul_mem hσ hτ, fun ξ hξ => ?_⟩
        rw [AlgEquiv.mul_apply, hτv ξ hξ, map_pow, hσu ξ hξ, ← pow_mul, Units.val_mul]
        exact pow_eq_pow_of_modEq hξ (by rw [ZMod.val_mul]; exact (Nat.mod_modEq _ _).symm)
      inv_mem' := by
        rintro u ⟨σ, hσ, hσu⟩
        refine ⟨σ⁻¹, I.inv_mem hσ, fun ξ hξ => ?_⟩
        have h1 : σ (ξ ^ ((u⁻¹ : (ZMod (p ^ N))ˣ) : ZMod (p ^ N)).val) = ξ := by
          rw [map_pow, hσu ξ hξ, ← pow_mul]
          conv_rhs => rw [← pow_one ξ]
          refine pow_eq_pow_of_modEq hξ ?_
          rw [← ZMod.val_one (p ^ N), ← Units.val_one, ← mul_inv_cancel u, Units.val_mul,
            ZMod.val_mul]
          exact (Nat.mod_modEq _ _).symm
        conv_lhs => rw [← h1]
        rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply] }

  have hmemH : ∀ σ ∈ I, ∃ u ∈ H, ∀ ξ : 𝓠, ξ ^ p ^ N = 1 → σ ξ = ξ ^ (u : ZMod (p ^ N)).val := by
    intro σ hσ
    obtain ⟨a, ha⟩ := exists_nat_forall_pow_eq_one_apply_eq_pow σ (p ^ N)
    have hcop : a.Coprime (p ^ N) := by
      apply (hζ.pow_iff_coprime hpos a).mp
      rw [← ha ζ hζ.pow_eq_one]
      exact hζ.map_of_injective σ.injective
    have hact : ∀ ξ : 𝓠, ξ ^ p ^ N = 1 →
        σ ξ = ξ ^ ((ZMod.unitOfCoprime a hcop : (ZMod (p ^ N))ˣ) : ZMod (p ^ N)).val := by
      intro ξ hξ
      rw [ha ξ hξ, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact pow_eq_pow_of_modEq hξ (Nat.mod_modEq _ _).symm
    exact ⟨ZMod.unitOfCoprime a hcop, ⟨σ, hσ, hact⟩, hact⟩

  haveI : IsCyclic (ZMod (p ^ N))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 N
  obtain ⟨h₀, hh₀⟩ := IsCyclic.exists_generator (α := H)
  obtain ⟨σ₀, hσ₀I, hσ₀⟩ := h₀.2

  have hσ₀pow : ∀ (i : ℕ) (ξ : 𝓠), ξ ^ p ^ N = 1 →
      (σ₀ ^ i) ξ = ξ ^ (((h₀ : (ZMod (p ^ N))ˣ) ^ i : (ZMod (p ^ N))ˣ) : ZMod (p ^ N)).val := by
    intro i
    induction i with
    | zero =>
      intro ξ _
      rw [pow_zero, pow_zero, AlgEquiv.one_apply, Units.val_one, ZMod.val_one, pow_one]
    | succ i ih =>
      intro ξ hξ
      rw [pow_succ, AlgEquiv.mul_apply, hσ₀ ξ hξ, map_pow, ih ξ hξ, ← pow_mul, pow_succ,
        Units.val_mul]
      exact pow_eq_pow_of_modEq hξ (by rw [ZMod.val_mul]; exact (Nat.mod_modEq _ _).symm)
  refine ⟨σ₀, hσ₀I, orderOf (h₀ : (ZMod (p ^ N))ˣ), orderOf_pos _, ?_, ?_, ?_⟩
  ·
    intro ξ hξ
    rw [hσ₀pow _ ξ hξ, pow_orderOf_eq_one, Units.val_one, ZMod.val_one, pow_one]
  ·
    intro σ hσ
    obtain ⟨u, huH, hu⟩ := hmemH σ hσ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hh₀ ⟨u, huH⟩)
    have hk' : (h₀ : (ZMod (p ^ N))ˣ) ^ k = u := by
      rw [← Subgroup.coe_zpow, hk]
    set d := orderOf (h₀ : (ZMod (p ^ N))ˣ) with hd
    have hd0 : (0 : ℤ) ≤ k % (d : ℤ) := Int.emod_nonneg _ (by exact_mod_cast (orderOf_pos _).ne')
    refine ⟨(k % (d : ℤ)).toNat, fun ξ hξ => ?_⟩
    have hpowk : (h₀ : (ZMod (p ^ N))ˣ) ^ (k % (d : ℤ)).toNat = u := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hd0, zpow_mod_orderOf, hk']
    rw [AlgEquiv.mul_apply, hu ξ hξ, ← hpowk, ← hσ₀pow _ ξ hξ, AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_apply]
  ·
    intro i j hi hj hij
    rw [hσ₀pow i ζ hζ.pow_eq_one, hσ₀pow j ζ hζ.pow_eq_one] at hij
    have hmod := modEq_of_pow_eq_pow hζ hij
    have hval : (((h₀ : (ZMod (p ^ N))ˣ) ^ i : (ZMod (p ^ N))ˣ) : ZMod (p ^ N)).val =
        (((h₀ : (ZMod (p ^ N))ˣ) ^ j : (ZMod (p ^ N))ˣ) : ZMod (p ^ N)).val :=
      Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt _) (ZMod.val_lt _)
    have heq : (h₀ : (ZMod (p ^ N))ˣ) ^ i = (h₀ : (ZMod (p ^ N))ˣ) ^ j :=
      Units.ext (ZMod.val_injective _ hval)
    exact pow_injOn_Iio_orderOf hi hj heq

p2m_export "ValuationSubring.C3dDescentAux" "exists_generator"

theorem exists_isFix_sum_ne_zero (I : Subgroup 𝓖) (m : ℕ) (σ₀ : 𝓖)
    (d : ℕ) (hd : 0 < d) (ζ : 𝓠) (hζ : IsFix I m ζ)
    (hdist : ∀ i j : ℕ, i < d → j < d → (σ₀ ^ i) ζ = (σ₀ ^ j) ζ → i = j)
    (b : ℕ → 𝓠) (hb0 : b 0 = 1) :
    ∃ c : 𝓠, IsFix I m c ∧ ∑ i ∈ Finset.range d, b i * (σ₀ ^ i) c ≠ 0 := by
  classical
  let F := IntermediateField.fixedField (fixerSubgroup I m)
  let fam : Fin d → (F →* 𝓠) := fun i =>
    { toFun := fun c => (σ₀ ^ (i : ℕ)) (c : 𝓠)
      map_one' := by simp
      map_mul' := fun a c => by simp }
  have hinj : Function.Injective fam := by
    intro i j hij
    have h := congrArg (fun f : F →* 𝓠 => f ⟨ζ, (isFix_iff_mem_fixedField ζ).mp hζ⟩) hij
    exact Fin.ext (hdist i j i.2 j.2 h)
  have hli := (linearIndependent_monoidHom F (𝓠)).comp fam hinj
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have hzero : ∑ i : Fin d, b i • ((fam i : F →* 𝓠) : F → 𝓠) = 0 := by
    funext c
    rw [Finset.sum_apply, Pi.zero_apply]
    have h := hall c ((isFix_iff_mem_fixedField (c : 𝓠)).mpr c.2)
    rw [Finset.sum_range] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
    exact h
  have h0 := Fintype.linearIndependent_iff.mp hli (fun i => b i) hzero ⟨0, hd⟩
  exact one_ne_zero (hb0 ▸ h0)

end ValuationSubring.C3dDescentAux

namespace ValuationSubring
p2m_export "ValuationSubring" "ext mul_mem one_mem LiesOverPrime inertiaSubgroupIn exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one"
namespace C3dDescentAux
p2m_open "ValuationSubring"

theorem eq_one_of_pow_eq_one_of_forall_inertia_apply_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (n : ℕ) (P : ValuationSubring (𝓠)) (hP : P.LiesOverPrime p) (η : 𝓠)
    (hη : η ^ p ^ n = 1) (hfix : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ η = η) : η = 1 := by
  classical
  by_contra hne

  have hdvd : orderOf η ∣ p ^ n := orderOf_dvd_of_pow_eq_one hη
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hne hk
  have hprim : IsPrimitiveRoot η (p ^ k) := hk ▸ IsPrimitiveRoot.orderOf η

  have hprim' : IsPrimitiveRoot (η ^ p ^ (k - 1)) p :=
    hprim.pow (pow_pos hp.pos k) (by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)])
  have hfix' : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (η ^ p ^ (k - 1)) = η ^ p ^ (k - 1) :=
    fun σ hσ => by rw [map_pow, hfix σ hσ]

  obtain ⟨σ, hσI, hσ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one P hp hP 1
      (-1)
  set v := ((-1 : (ZMod (p ^ 1))ˣ) : ZMod (p ^ 1)).val with hv
  have h1 : (η ^ p ^ (k - 1)) ^ p ^ 1 = 1 := by rw [pow_one]; exact hprim'.pow_eq_one
  have h2 : (η ^ p ^ (k - 1)) ^ v = η ^ p ^ (k - 1) := ((hσ _ h1).symm.trans (hfix' σ hσI))

  have hpv : p ∣ v + 1 := by
    haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hz : ((v + 1 : ℕ) : ZMod (p ^ 1)) = 0 := by
      rw [Nat.cast_add, Nat.cast_one, hv, ZMod.natCast_zmod_val, Units.val_neg, Units.val_one,
        neg_add_cancel]
    have := (CharP.cast_eq_zero_iff (ZMod (p ^ 1)) (p ^ 1) (v + 1)).mp hz
    rwa [pow_one] at this
  have hsq : (η ^ p ^ (k - 1)) ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := hpv
    calc (η ^ p ^ (k - 1)) ^ 2 = (η ^ p ^ (k - 1)) ^ (v + 1) := by rw [pow_succ _ v, h2, sq]
      _ = 1 := by rw [hc, pow_mul, hprim'.pow_eq_one, one_pow]
  have h2dvd : p ∣ 2 := (hprim'.pow_eq_one_iff_dvd 2).mp hsq
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd)

end ValuationSubring.C3dDescentAux

theorem solution
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N n : ℕ) (hn : n ≤ N)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (x : AlgebraicClosure ℚ) (hx0 : x ≠ 0)
    (hxfix : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → σ ξ = ξ) → σ x = x)
    (hinv : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ w : AlgebraicClosure ℚ,
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) → τ w = w) ∧ σ x = x * w ^ p ^ n) :
    ∃ x' w' : AlgebraicClosure ℚ, x' ≠ 0 ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x' = x') ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) → τ w' = w') ∧
      x = x' * w' ^ p ^ n := by
  classical

  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    obtain rfl : n = 0 := Nat.le_zero.mp hn
    refine ⟨x, 1, hx0, fun σ hσ => hxfix σ hσ (fun ξ hξ => ?_), fun τ _ _ => map_one τ,
      by rw [one_pow, mul_one]⟩
    rw [pow_zero, pow_one] at hξ
    rw [hξ, map_one]
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (𝓠) (p ^ N)
  have hζfix : ValuationSubring.C3dDescentAux.IsFix (P.inertiaSubgroupIn ℚ) (p ^ N) ζ :=
    fun τ _ hτ => hτ ζ hζ.pow_eq_one

  obtain ⟨σ₀, hσ₀I, d, hd, hσ₀d, hdec, hdist⟩ :=
    ValuationSubring.C3dDescentAux.exists_generator (P.inertiaSubgroupIn ℚ) p N hp hp2 hNpos ζ hζ

  obtain ⟨w, hwfix, hw⟩ := hinv σ₀ hσ₀I
  have hwfix' : ValuationSubring.C3dDescentAux.IsFix (P.inertiaSubgroupIn ℚ) (p ^ N) w := hwfix
  have hxfix' : ValuationSubring.C3dDescentAux.IsFix (P.inertiaSubgroupIn ℚ) (p ^ N) x := hxfix
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hp.ne_zero), mul_zero, map_eq_zero_iff _ σ₀.injective] at hw
    exact hx0 hw

  set b : ℕ → 𝓠 := fun i => ∏ j ∈ Finset.range i, (σ₀ ^ j) w with hb
  have hbfix : ∀ i, ValuationSubring.C3dDescentAux.IsFix (P.inertiaSubgroupIn ℚ) (p ^ N) (b i) :=
    fun i => ValuationSubring.C3dDescentAux.IsFix.prod _ fun j _ => hwfix'.pow_apply hσ₀I j
  have hb0 : b 0 = 1 := by simp only [hb, Finset.range_zero, Finset.prod_empty]
  have hbsucc : ∀ i, b (i + 1) = b i * (σ₀ ^ i) w := fun i => by
    simp only [hb, Finset.prod_range_succ]
  have hσb : ∀ i, w * σ₀ (b i) = b (i + 1) := fun i => by
    simp only [hb, map_prod, ← AlgEquiv.mul_apply, ← pow_succ']
    rw [Finset.prod_range_succ', pow_zero, AlgEquiv.one_apply, mul_comm]

  have hσx : ∀ i : ℕ, (σ₀ ^ i) x = x * b i ^ p ^ n := fun i => by
    induction i with
    | zero => rw [pow_zero, AlgEquiv.one_apply, hb0, one_pow, mul_one]
    | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hw, ← hσb i, mul_pow]
      ring

  have hNrm : b d ^ p ^ n = 1 := by
    have h := hσx d
    rw [hxfix' _ ((P.inertiaSubgroupIn ℚ).pow_mem hσ₀I d) hσ₀d] at h
    exact (mul_eq_left₀ hx0).mp h.symm

  have hbdσ₀ : σ₀ (b d) = b d := by
    have h := hσb d
    rw [hbsucc d, hwfix' _ ((P.inertiaSubgroupIn ℚ).pow_mem hσ₀I d) hσ₀d, mul_comm (b d) w]
      at h
    exact mul_left_cancel₀ hw0 h
  have hNrm1 : b d = 1 :=
    ValuationSubring.C3dDescentAux.eq_one_of_pow_eq_one_of_forall_inertia_apply_eq hp hp2 n P hP
      (b d) hNrm ((hbfix d).forall_apply_eq hσ₀I hbdσ₀ hdec)

  obtain ⟨c, hcfix, hu0⟩ :=
    ValuationSubring.C3dDescentAux.exists_isFix_sum_ne_zero (P.inertiaSubgroupIn ℚ) (p ^ N) σ₀ d hd
      ζ hζfix hdist b hb0
  set u := ∑ i ∈ Finset.range d, b i * (σ₀ ^ i) c with hu
  have hufix : ValuationSubring.C3dDescentAux.IsFix (P.inertiaSubgroupIn ℚ) (p ^ N) u :=
    ValuationSubring.C3dDescentAux.IsFix.sum _ fun i _ => (hbfix i).mul (hcfix.pow_apply hσ₀I i)
  have hcd : (σ₀ ^ d) c = c := hcfix _ ((P.inertiaSubgroupIn ℚ).pow_mem hσ₀I d) hσ₀d
  have hσu : w * σ₀ u = u := by
    have step : ∀ i, w * σ₀ (b i * (σ₀ ^ i) c) = b (i + 1) * (σ₀ ^ (i + 1)) c := fun i => by
      rw [map_mul, ← mul_assoc, hσb i, ← AlgEquiv.mul_apply, ← pow_succ']
    have key : ∑ i ∈ Finset.range d, b (i + 1) * (σ₀ ^ (i + 1)) c + b 0 * (σ₀ ^ 0) c =
        u + b d * (σ₀ ^ d) c := by
      rw [← Finset.sum_range_succ' (fun i => b i * (σ₀ ^ i) c) d, Finset.sum_range_succ]
    rw [hb0, pow_zero, AlgEquiv.one_apply, one_mul, hNrm1, hcd, one_mul] at key
    rw [hu, map_sum, Finset.mul_sum]
    simp_rw [step]
    exact add_right_cancel key

  refine ⟨x * u ^ p ^ n, u⁻¹, mul_ne_zero hx0 (pow_ne_zero _ hu0), ?_,
    fun τ hτ h => hufix.inv τ hτ h, ?_⟩
  · refine (hxfix'.mul (hufix.pow _)).forall_apply_eq hσ₀I ?_ hdec
    rw [map_mul, map_pow, hw, mul_assoc, ← mul_pow, hσu]
  · rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu0), mul_one]

end S_ValuationSubring_exists_inertia_fixed_radicand_of_kummer_class_invariant
end P2MW
export P2MW.S_ValuationSubring_exists_inertia_fixed_radicand_of_kummer_class_invariant (solution)
