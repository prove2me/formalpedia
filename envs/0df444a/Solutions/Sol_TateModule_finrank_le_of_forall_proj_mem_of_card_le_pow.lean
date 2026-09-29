-- Prove2me | solution 1 for TateModule.finrank_le_of_forall_proj_mem_of_card_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/29a455c4-f061-5afc-954b-956f369948c0

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateModule_finrank_le_of_forall_proj_mem_of_card_le_pow

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace TateRankBound

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]

theorem proj_natCast_smul (c : ℕ) (x : TateModule p M) (n : ℕ) :
    TateModule.proj p M n ((c : ℤ_[p]) • x) = (c : ℤ) • TateModule.proj p M n x :=
  TateModule.natCast_padicInt_smul_apply c x n

theorem proj_intCast_smul (d : ℤ) (x : TateModule p M) (n : ℕ) :
    TateModule.proj p M n ((d : ℤ_[p]) • x) = d • TateModule.proj p M n x := by
  obtain ⟨c, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · rw [Int.cast_natCast, proj_natCast_smul]
  · rw [Int.cast_neg, Int.cast_natCast, neg_smul, map_neg, proj_natCast_smul, neg_smul]

theorem proj_sum_intCast_smul {ι : Type} (s : Finset ι) (d : ι → ℤ) (x : ι → TateModule p M) (n : ℕ) :
    TateModule.proj p M n (∑ i ∈ s, (d i : ℤ_[p]) • x i) = ∑ i ∈ s, d i • TateModule.proj p M n (x i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => proj_intCast_smul (d i) (x i) n

omit [Fact p.Prime] in
theorem apply_eq_zero_of_pow_smul_apply_eq_zero (x : TateModule p M) {v k j : ℕ} (hj : j + v ≤ k)
    (h : ((p ^ v : ℕ) : ℤ) • (x : ℕ → M) k = 0) : (x : ℕ → M) j = 0 := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hj
  have hc := TateModule.compat_pow x j (v + e)
  rw [show j + (v + e) = k by omega] at hc
  rw [← hc, pow_add, Nat.cast_mul, mul_comm, mul_smul, h, smul_zero]

section Core

variable {r : ℕ} (x : Fin (r + 1) → TateModule p M) (B : ℕ → Finset M)
  (hBcard : ∀ k, (B k).card ≤ p ^ (k * r))
  (hx : ∀ (a : Fin (r + 1) → ℤ) (k : ℕ), TateModule.proj p M k (∑ i, (a i : ℤ_[p]) • x i) ∈ B k)

include hBcard hx

theorem exists_primitive_proj_eq_zero (j : ℕ) :
    ∃ d : Fin (r + 1) → ℤ, (∃ i, ¬ (p : ℤ) ∣ d i) ∧
      ∀ j' ≤ j, TateModule.proj p M j' (∑ i, (d i : ℤ_[p]) • x i) = 0 := by
  classical
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  set c : ℕ := j * r + 1 with hc
  set k : ℕ := c + j with hk

  let A : Type := Fin (r + 1) → Fin (p ^ c) × Fin (p ^ j)
  let val : A → Fin (r + 1) → ℕ := fun a i => ((a i).1 : ℕ) + p ^ c * ((a i).2 : ℕ)
  let g : A → M := fun a => TateModule.proj p M k (∑ i, ((val a i : ℤ) : ℤ_[p]) • x i)
  have hg : ∀ a ∈ (Finset.univ : Finset A), g a ∈ B k := fun a _ => hx _ k
  have hcardA : (Finset.univ : Finset A).card = p ^ (k * (r + 1)) := by
    rw [Finset.card_univ]
    simp only [A, Fintype.card_pi, Fintype.card_prod, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    rw [← pow_add, ← pow_mul, hk]

  have hlt : (B k).card * p ^ (j * (r + 1)) < (Finset.univ : Finset A).card := by
    rw [hcardA]
    calc (B k).card * p ^ (j * (r + 1)) ≤ p ^ (k * r) * p ^ (j * (r + 1)) :=
          Nat.mul_le_mul_right _ (hBcard k)
      _ = p ^ (k * r + j * (r + 1)) := (pow_add _ _ _).symm
      _ < p ^ (k * (r + 1)) := by
          apply Nat.pow_lt_pow_right hp1
          rw [hk, hc]; ring_nf; omega
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hg hlt
  set F : Finset A := Finset.univ.filter (fun a => g a = y) with hF

  have hcardH : (Finset.univ : Finset (Fin (r + 1) → Fin (p ^ j))).card = p ^ (j * (r + 1)) := by
    rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    rw [← pow_mul]
  have hlt2 : (Finset.univ : Finset (Fin (r + 1) → Fin (p ^ j))).card < F.card := by
    rw [hcardH]; exact hy
  obtain ⟨a, ha, b, hb, hab, habhi⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt2
    (f := fun (a : A) (i : Fin (r + 1)) => (a i).2) (fun _ _ => Finset.mem_univ _)
  simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb

  let d : Fin (r + 1) → ℤ := fun i => ((a i).1 : ℤ) - ((b i).1 : ℤ)
  have hhi : ∀ i, (a i).2 = (b i).2 := fun i => congrFun habhi i
  have hval : ∀ i, (val a i : ℤ) - (val b i : ℤ) = d i := by
    intro i
    simp only [val, d, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hhi i]
    ring

  have hdi : ∃ i, d i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hab
    funext i
    have h1 : ((a i).1 : ℤ) = ((b i).1 : ℤ) := sub_eq_zero.mp (hall i)
    exact Prod.ext (Fin.ext (by exact_mod_cast h1)) (hhi i)
  have hsmall : ∀ i, |d i| < (p : ℤ) ^ c := by
    intro i
    have ha' : ((a i).1 : ℤ) < (p : ℤ) ^ c := by exact_mod_cast (a i).1.isLt
    have hb' : ((b i).1 : ℤ) < (p : ℤ) ^ c := by exact_mod_cast (b i).1.isLt
    have ha0 : (0 : ℤ) ≤ ((a i).1 : ℤ) := Nat.cast_nonneg _
    have hb0 : (0 : ℤ) ≤ ((b i).1 : ℤ) := Nat.cast_nonneg _
    simp only [d, abs_lt]
    constructor <;> linarith

  have hdk : TateModule.proj p M k (∑ i, (d i : ℤ_[p]) • x i) = 0 := by
    have h1 : (∑ i, (d i : ℤ_[p]) • x i) =
        (∑ i, ((val a i : ℤ) : ℤ_[p]) • x i) - (∑ i, ((val b i : ℤ) : ℤ_[p]) • x i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, ← Int.cast_sub, hval i]
    rw [h1, map_sub, sub_eq_zero]
    exact ha.trans hb.symm

  have hPc : ¬ ∀ i, (p : ℤ) ^ c ∣ d i := by
    obtain ⟨i, hi⟩ := hdi
    intro hall
    exact hi (Int.eq_zero_of_abs_lt_dvd (hall i) (hsmall i))
  have hQ : ∃ e, ¬ ∀ i, (p : ℤ) ^ (e + 1) ∣ d i := ⟨c - 1, by rwa [Nat.sub_add_cancel (by omega)]⟩
  let v : ℕ := Nat.find hQ
  have hv_spec : ¬ ∀ i, (p : ℤ) ^ (v + 1) ∣ d i := Nat.find_spec hQ
  have hv_le : v ≤ c - 1 := Nat.find_le (by rwa [Nat.sub_add_cancel (by omega)])
  have hv_all : ∀ i, (p : ℤ) ^ v ∣ d i := by
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · intro i; rw [h0, pow_zero]; exact one_dvd _
    · have hmin := Nat.find_min hQ (m := v - 1) (by omega)
      push Not at hmin
      rwa [Nat.sub_add_cancel hpos] at hmin

  choose d' hd' using hv_all
  refine ⟨d', ?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply hv_spec
    intro i
    obtain ⟨t, ht⟩ := hall i
    refine ⟨t, ?_⟩
    rw [hd' i, ht, pow_succ]; ring
  · intro j' hj'

    have hsum : (∑ i, (d i : ℤ_[p]) • x i) = ((p ^ v : ℕ) : ℤ_[p]) • ∑ i, (d' i : ℤ_[p]) • x i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd' i, Int.cast_mul, Int.cast_pow, Int.cast_natCast, mul_smul, Nat.cast_pow]
    rw [hsum, proj_natCast_smul] at hdk
    rw [TateModule.proj_apply]
    exact apply_eq_zero_of_pow_smul_apply_eq_zero _ (by omega) hdk

end Core

theorem proj_smul_eq_of_sub_mem_span {n : ℕ} {a b : ℤ_[p]}
    (h : a - b ∈ Ideal.span {(p : ℤ_[p]) ^ n}) (x : TateModule p M) :
    TateModule.proj p M n (a • x) = TateModule.proj p M n (b • x) := by
  rw [TateModule.proj_apply, TateModule.proj_apply, TateModule.smul_apply, TateModule.smul_apply]
  refine TateModule.natCast_smul_eq_of_zmod_eq (TateModule.torsion x n) ?_
  rw [← TateModule.toZModPow_eq_appr, ← TateModule.toZModPow_eq_appr, ← sub_eq_zero, ← map_sub,
    ← RingHom.mem_ker, PadicInt.ker_toZModPow]
  exact h

section Compact

variable {ι : Type} [Fintype ι] (x : ι → TateModule p M)

theorem isLocallyConstant_proj_sum (n : ℕ) :
    IsLocallyConstant (fun a : ι → ℤ_[p] => TateModule.proj p M n (∑ i, a i • x i)) := by
  have hp : p.Prime := Fact.out
  rw [IsLocallyConstant.iff_exists_open]
  intro a₀
  refine ⟨{a | ∀ i, dist (a i) (a₀ i) < (p : ℝ) ^ ((-(n : ℤ)) + 1)}, ?_, ?_, ?_⟩
  · have : {a : ι → ℤ_[p] | ∀ i, dist (a i) (a₀ i) < (p : ℝ) ^ ((-(n : ℤ)) + 1)} =
        ⋂ i, (fun a : ι → ℤ_[p] => a i) ⁻¹' Metric.ball (a₀ i) ((p : ℝ) ^ ((-(n : ℤ)) + 1)) := by
      ext a; simp [Metric.mem_ball]
    rw [this]
    exact isOpen_iInter_of_finite fun i => (continuous_apply i).isOpen_preimage _ Metric.isOpen_ball
  · intro i
    rw [dist_self]
    exact zpow_pos (by exact_mod_cast hp.pos) _
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => proj_smul_eq_of_sub_mem_span ?_ (x i)
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one,
      ← dist_eq_norm]
    exact ha i

theorem exists_ne_zero_sum_smul_eq_zero
    (h : ∀ j : ℕ, ∃ a : ι → ℤ_[p], (∃ i, IsUnit (a i)) ∧
      ∀ j' ≤ j, TateModule.proj p M j' (∑ i, a i • x i) = 0) :
    ∃ a : ι → ℤ_[p], (∃ i, IsUnit (a i)) ∧ ∑ i, a i • x i = 0 := by
  let U : Set (ι → ℤ_[p]) := {a | ∃ i, IsUnit (a i)}
  let C : ℕ → Set (ι → ℤ_[p]) := fun j => {a | ∀ j' ≤ j, TateModule.proj p M j' (∑ i, a i • x i) = 0}
  have hU : IsClosed U := by
    have : U = ⋃ i, (fun a : ι → ℤ_[p] => ‖a i‖) ⁻¹' {1} := by
      ext a; simp [U, PadicInt.isUnit_iff]
    rw [this]
    exact isClosed_iUnion_of_finite fun i =>
      (isClosed_singleton.preimage ((continuous_apply i).norm))
  have hC : ∀ j, IsClosed (C j) := by
    intro j
    have : C j = ⋂ j' ∈ Finset.range (j + 1),
        {a : ι → ℤ_[p] | TateModule.proj p M j' (∑ i, a i • x i) = 0} := by
      ext a; simp [C]
    rw [this]
    exact isClosed_biInter fun j' _ => (isLocallyConstant_proj_sum x j').isClosed_fiber 0
  let t : ℕ → Set (ι → ℤ_[p]) := fun j => U ∩ C j
  have htd : Directed (· ⊇ ·) t := by
    intro j₁ j₂
    refine ⟨max j₁ j₂, ?_, ?_⟩
    · rintro a ⟨hu, hc⟩; exact ⟨hu, fun j' hj' => hc j' (hj'.trans (le_max_left _ _))⟩
    · rintro a ⟨hu, hc⟩; exact ⟨hu, fun j' hj' => hc j' (hj'.trans (le_max_right _ _))⟩
  have htn : ∀ j, (t j).Nonempty := fun j => by
    obtain ⟨a, hu, hc⟩ := h j
    exact ⟨a, hu, hc⟩
  have htcl : ∀ j, IsClosed (t j) := fun j => hU.inter (hC j)
  have htc : ∀ j, IsCompact (t j) := fun j => (htcl j).isCompact
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl
  rw [Set.mem_iInter] at ha
  refine ⟨a, (ha 0).1, ?_⟩
  refine Subtype.ext (funext fun j => ?_)
  exact (ha j).2 j le_rfl

end Compact

theorem one_tmul_smul (c : ℤ_[p]) (x : TateModule p M) :
    ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (c • x) : ℚ_[p] ⊗[ℤ_[p]] TateModule p M) = (c : ℚ_[p]) • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) := by
  rw [TensorProduct.tmul_smul, ← algebraMap_smul ℚ_[p] c]
  rfl

theorem one_tmul_sum_smul {ι : Type} (s : Finset ι) (c : ι → ℤ_[p]) (x : ι → TateModule p M) :
    ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (∑ i ∈ s, c i • x i) : ℚ_[p] ⊗[ℤ_[p]] TateModule p M) =
      ∑ i ∈ s, (c i : ℚ_[p]) • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x i) := by
  rw [TensorProduct.tmul_sum]
  exact Finset.sum_congr rfl fun i _ => one_tmul_smul (c i) (x i)

theorem exists_smul_eq_one_tmul (v : ℚ_[p] ⊗[ℤ_[p]] TateModule p M) :
    ∃ s : ℤ_[p], s ≠ 0 ∧ ∃ x : TateModule p M, (s : ℚ_[p]) • v = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by rw [TensorProduct.tmul_zero, smul_zero]⟩
  | tmul a x =>
      obtain ⟨b, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) a
      have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
      refine ⟨s, hs0, b • x, ?_⟩
      have hsQ : (algebraMap ℤ_[p] ℚ_[p] s) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).mpr hs0
      rw [TensorProduct.smul_tmul', smul_eq_mul, show (s : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] s from rfl,
        mul_div_cancel₀ _ hsQ, one_tmul_smul, show (b : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] b from rfl,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add v w hv hw =>
      obtain ⟨s, hs, x, hx⟩ := hv
      obtain ⟨t, ht, y, hy⟩ := hw
      refine ⟨s * t, mul_ne_zero hs ht, t • x + s • y, ?_⟩
      rw [smul_add, PadicInt.coe_mul, mul_comm (s : ℚ_[p]), mul_smul, hx, mul_comm (t : ℚ_[p]), mul_smul, hy,
        TensorProduct.tmul_add, one_tmul_smul, one_tmul_smul]

theorem finrank_le (r : ℕ) (K : Submodule ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p M))
    (B : ℕ → Finset M) (hBcard : ∀ k, (B k).card ≤ p ^ (k * r))
    (hK : ∀ x : TateModule p M, ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) ∈ K → ∀ k, TateModule.proj p M k x ∈ B k) :
    Module.finrank ℚ_[p] K ≤ r := by
  by_cases hfin : Module.Finite ℚ_[p] K
  swap
  · rw [Module.finrank_of_not_finite hfin]; exact Nat.zero_le _
  by_contra hlt
  rw [not_le] at hlt
  have hle : r + 1 ≤ Module.finrank ℚ_[p] K := hlt
  haveI : Module.Finite ℚ_[p] K := hfin
  haveI : Module.Free ℚ_[p] K := Module.Free.of_divisionRing ℚ_[p] K
  let b := Module.finBasis ℚ_[p] K
  let v : Fin (r + 1) → K := fun i => b (Fin.castLE hle i)
  have hv : LinearIndependent ℚ_[p] v := b.linearIndependent.comp _ (Fin.castLE_injective hle)

  choose s hs t ht using fun i =>
    exists_smul_eq_one_tmul (p := p) (M := M) ((v i : K) : ℚ_[p] ⊗[ℤ_[p]] TateModule p M)

  have hmem : ∀ a : Fin (r + 1) → ℤ, ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (∑ i, (a i : ℤ_[p]) • t i)) ∈ K := by
    intro a
    rw [one_tmul_sum_smul]
    refine K.sum_mem fun i _ => K.smul_mem _ ?_
    rw [← ht i]
    exact K.smul_mem _ (v i).2
  have hx : ∀ (a : Fin (r + 1) → ℤ) (k : ℕ), TateModule.proj p M k (∑ i, (a i : ℤ_[p]) • t i) ∈ B k :=
    fun a k => hK _ (hmem a) k

  have hdeep : ∀ j : ℕ, ∃ a : Fin (r + 1) → ℤ_[p], (∃ i, IsUnit (a i)) ∧
      ∀ j' ≤ j, TateModule.proj p M j' (∑ i, a i • t i) = 0 := by
    intro j
    obtain ⟨d, ⟨i₀, hi₀⟩, hd⟩ := exists_primitive_proj_eq_zero t B hBcard hx j
    refine ⟨fun i => (d i : ℤ_[p]), ⟨i₀, ?_⟩, hd⟩
    rw [PadicInt.isUnit_iff]
    exact le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp (mt (PadicInt.norm_int_lt_one_iff_dvd (d i₀)).mp hi₀))
  obtain ⟨a, ⟨i₀, hi₀⟩, ha⟩ := exists_ne_zero_sum_smul_eq_zero t hdeep

  have hrel : ∑ i, ((a i : ℚ_[p]) * (s i : ℚ_[p])) • v i = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero]
    simp only [Submodule.coe_smul, mul_smul]
    have : ∀ i, (a i : ℚ_[p]) • ((s i : ℚ_[p]) • ((v i : K) : ℚ_[p] ⊗[ℤ_[p]] TateModule p M)) =
        (a i : ℚ_[p]) • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t i) := fun i => by rw [ht i]
    rw [Finset.sum_congr rfl fun i _ => this i, ← one_tmul_sum_smul, ha, TensorProduct.tmul_zero]
  have hzero := (Fintype.linearIndependent_iff.mp hv) _ hrel i₀
  rcases mul_eq_zero.mp hzero with h1 | h2
  · exact hi₀.ne_zero (PadicInt.coe_eq_zero.mp h1)
  · exact hs i₀ (PadicInt.coe_eq_zero.mp h2)

end TateRankBound

end

open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (r : ℕ)
    (K : Submodule ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p M))
    (B : ℕ → Finset M) (hB : ∀ k, (B k).card ≤ p ^ (k * r))
    (hK : ∀ x : TateModule p M, (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x ∈ K → ∀ k, TateModule.proj p M k x ∈ B k) :
    Module.finrank ℚ_[p] K ≤ r :=
  TateRankBound.finrank_le r K B hB hK

end S_TateModule_finrank_le_of_forall_proj_mem_of_card_le_pow
end P2MW
export P2MW.S_TateModule_finrank_le_of_forall_proj_mem_of_card_le_pow (solution)
