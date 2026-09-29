-- Prove2me | solution 1 for Polynomial.exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2059ec06-c1c9-5df7-b685-977f2ba238a7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line

set_option autoImplicit false

namespace J3aResum

open Finset

theorem hasSum_polynomial_mul {a : ℤ → ℂ} {A Z : ℂ} (hZ : Z ≠ 0) (ha : HasSum (fun n : ℤ => a n * Z ^ n) A)
    (D : Polynomial ℂ) :
    HasSum (fun k : ℤ => (∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * a (k - (i : ℤ))) * Z ^ k)
      (A * D.eval Z) := by
  classical
  have hshift : ∀ i : ℕ, HasSum (fun k : ℤ => D.coeff i * a (k - (i : ℤ)) * Z ^ k) (A * (D.coeff i * Z ^ i)) := by
    intro i
    have h1 : HasSum (fun n : ℤ => D.coeff i * Z ^ i * (a n * Z ^ n)) (D.coeff i * Z ^ i * A) := ha.mul_left _
    have h2 : HasSum (fun k : ℤ => D.coeff i * Z ^ i * (a (k - (i : ℤ)) * Z ^ (k - (i : ℤ)))) (D.coeff i * Z ^ i * A) := by
      rw [← (Equiv.addRight (i : ℤ)).hasSum_iff]
      refine h1.congr_fun fun n => ?_
      simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right]
    rw [show A * (D.coeff i * Z ^ i) = D.coeff i * Z ^ i * A by ring]
    refine h2.congr_fun fun k => ?_
    rw [zpow_sub₀ hZ, zpow_natCast]
    field_simp
  have hsum := hasSum_sum (s := Finset.range (D.natDegree + 1)) fun i _ => hshift i
  rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  refine hsum.congr_fun fun k => ?_
  rw [Finset.sum_mul]

theorem resum_wrap (h : ℤ → ℂ) (q : Polynomial ℂ) (T₀ T₁ : ℤ)
    (h0 : ∀ t : ℤ, t < T₀ → h t = 0)
    (hrec : ∀ t : ℤ, T₁ ≤ t →
      ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * h (t - (i : ℤ)) = 0) :
    ∃ (P : Polynomial ℂ) (m₀ : ℤ), ∀ X : ℂ, X ≠ 0 →
      Summable (fun t : ℤ => h t * X ^ t) →
      (∑' t : ℤ, h t * X ^ t) * q.eval X = X ^ m₀ * P.eval X := by
  classical

  set e : ℤ → ℂ := fun k => ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * h (k - (i : ℤ)) with he
  set n : ℕ := (T₁ - T₀).toNat with hn
  have he0 : ∀ k : ℤ, k ∉ (Finset.range n).image (fun j : ℕ => T₀ + (j : ℤ)) → e k = 0 := by
    intro k hk
    by_cases hlt : k < T₀
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [h0 (k - (i : ℤ)) (by omega), mul_zero]
    · by_cases hge : T₁ ≤ k
      · exact hrec k hge
      · exfalso
        apply hk
        rw [Finset.mem_image]
        refine ⟨(k - T₀).toNat, ?_, ?_⟩
        · rw [Finset.mem_range, hn]
          have : k - T₀ < T₁ - T₀ := by omega
          exact (Int.toNat_lt_toNat (by omega)).mpr this
        · rw [Int.toNat_of_nonneg (by omega)]; ring
  refine ⟨∑ j ∈ Finset.range n, Polynomial.C (e (T₀ + (j : ℤ))) * Polynomial.X ^ j, T₀, fun X hX hsum => ?_⟩
  have hprod : HasSum (fun k : ℤ => e k * X ^ k) ((∑' t : ℤ, h t * X ^ t) * q.eval X) :=
    hasSum_polynomial_mul hX hsum.hasSum q
  have hfin : HasSum (fun k : ℤ => e k * X ^ k)
      (∑ k ∈ (Finset.range n).image (fun j : ℕ => T₀ + (j : ℤ)), e k * X ^ k) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by rw [he0 k hk, zero_mul]
  rw [hprod.unique hfin, Finset.sum_image (fun a _ b _ hab => by exact_mod_cast (add_right_inj T₀).mp hab),
    Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, zpow_add₀ hX,
    zpow_natCast]
  ring

theorem hasSum_finsum_fiber {ι κ : Type*} (ℓ : ι → κ) {f : ι → ℂ} {a : ℂ} (ha : HasSum f a)
    (hfin : ∀ t : κ, (Function.support fun m : {i // ℓ i = t} => f m).Finite) :
    HasSum (fun t : κ => ∑ᶠ m : {i // ℓ i = t}, f m) a := by
  have ha' : HasSum (f ∘ (Equiv.sigmaFiberEquiv ℓ)) a := (Equiv.hasSum_iff (Equiv.sigmaFiberEquiv ℓ)).mpr ha
  refine ha'.sigma fun t => ?_
  have h1 : HasSum (fun m : {i // ℓ i = t} => f m) (∑ᶠ m : {i // ℓ i = t}, f m) := by
    rw [finsum_eq_sum_of_support_subset _ (s := (hfin t).toFinset) (by simp)]
    exact hasSum_sum_of_ne_finset_zero (fun m hm => by simpa using hm)
  refine h1.congr_fun fun m => ?_
  simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]

theorem finsum_subtype_eq_finsum_ite {α : Type*} (p : α → Prop) [DecidablePred p] (f : α → ℂ) :
    ∑ᶠ x : {a // p a}, f x = ∑ᶠ a, if p a then f a else 0 := by
  have h1 : (∑ᶠ a, if p a then f a else 0) = ∑ᶠ a ∈ {a | p a}, f a := by
    rw [finsum_mem_def]
    refine finsum_congr fun a => ?_
    by_cases hp : p a
    · rw [if_pos hp, Set.indicator_of_mem (by simpa using hp)]
    · rw [if_neg hp, Set.indicator_of_notMem (by simpa using hp)]
  rw [h1, ← finsum_set_coe_eq_finsum_mem]
  rfl

theorem finite_fiber (N₁ : ℤ) (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂) (t : ℤ) :
    {n : ℤ × ℤ | N₁ ≤ n.1 ∧ N₁ ≤ n.2 ∧ (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t}.Finite := by
  have he₁' : (1 : ℤ) ≤ e₁ := by exact_mod_cast he₁
  have he₂' : (1 : ℤ) ≤ e₂ := by exact_mod_cast he₂
  refine Set.Finite.subset ((Set.finite_Icc N₁ (|t| + (e₂ : ℤ) * |N₁|)).prod
    (Set.finite_Icc N₁ (|t| + (e₁ : ℤ) * |N₁|))) ?_
  rintro ⟨n₁, n₂⟩ ⟨h1, h2, h3⟩
  simp only [Set.mem_prod, Set.mem_Icc]
  have ht : t ≤ |t| := le_abs_self t
  have hN : -N₁ ≤ |N₁| := neg_le_abs N₁
  have k1 : (e₂ : ℤ) * N₁ ≤ (e₂ : ℤ) * n₂ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have k2 : (e₁ : ℤ) * N₁ ≤ (e₁ : ℤ) * n₁ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have k3 : (e₂ : ℤ) * (-N₁) ≤ (e₂ : ℤ) * |N₁| := mul_le_mul_of_nonneg_left hN (by positivity)
  have k4 : (e₁ : ℤ) * (-N₁) ≤ (e₁ : ℤ) * |N₁| := mul_le_mul_of_nonneg_left hN (by positivity)
  refine ⟨⟨h1, ?_⟩, ⟨h2, ?_⟩⟩
  · rcases le_or_gt 0 n₁ with hn | hn
    · have k5 : n₁ ≤ (e₁ : ℤ) * n₁ := by nlinarith
      nlinarith
    · nlinarith [abs_nonneg t, abs_nonneg N₁]
  · rcases le_or_gt 0 n₂ with hn | hn
    · have k5 : n₂ ≤ (e₂ : ℤ) * n₂ := by nlinarith
      nlinarith
    · nlinarith [abs_nonneg t, abs_nonneg N₁]

end J3aResum

open J3aResum in
theorem solution
    (w : ℤ × ℤ → ℂ) (N₁ : ℤ) (hw : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → w n = 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hc : (∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧ (∀ m : ℤ, m < N → (fun t : ℤ => ∑ᶠ n : ℤ × ℤ, if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then w n else 0) m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * (fun t : ℤ => ∑ᶠ n : ℤ × ℤ, if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then w n else 0) (N + (m : ℤ) - (i : ℤ)) = 0))) :
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, X ≠ 0 →
        Summable (fun n : ℤ × ℤ => w n * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) →
        (∑' n : ℤ × ℤ, w n * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) * Q.eval X = X ^ m₀ * P.eval X := by
  classical
  obtain ⟨N, E, M, hE0, hc0, hcrec⟩ := hc

  set c : ℤ → ℂ := fun t => ∑ᶠ n : ℤ × ℤ, if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then w n else 0 with hcdef
  have hc0' : ∀ t : ℤ, t < N → c t = 0 := fun t ht => hc0 t ht
  have hcrec' : ∀ t : ℤ, N + (M : ℤ) ≤ t →
      ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * c (t - (i : ℤ)) = 0 := by
    intro t ht
    have h1 := hcrec (t - N).toNat (by omega)
    rw [Int.toNat_of_nonneg (by omega)] at h1
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h1
    rw [show N + (t - N) - (i : ℤ) = t - (i : ℤ) by ring]
  obtain ⟨P, m₀, hP⟩ := resum_wrap c E N (N + (M : ℤ)) hc0' hcrec'
  have hE : E ≠ 0 := by
    rintro rfl
    exact hE0 (by simp)
  refine ⟨P, E, m₀, hE, fun X hX hs => ?_⟩

  set ℓ : ℤ × ℤ → ℤ := fun n => (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 with hℓ
  have hfinw : ∀ t : ℤ, (Function.support fun m : {i // ℓ i = t} => w m).Finite := by
    intro t
    refine Set.Finite.subset (Set.Finite.preimage (Subtype.val_injective.injOn)
      (finite_fiber N₁ e₁ e₂ he₁ he₂ t)) ?_
    intro m hm
    rw [Function.mem_support] at hm
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    refine ⟨?_, ?_, m.2⟩
    · by_contra h; exact hm (hw _ (Or.inl (not_le.mp h)))
    · by_contra h; exact hm (hw _ (Or.inr (not_le.mp h)))
  have hfin : ∀ t : ℤ, (Function.support fun m : {i // ℓ i = t} => w m * X ^ ℓ m).Finite := by
    intro t
    refine (hfinw t).subset fun m hm => ?_
    rw [Function.mem_support] at hm ⊢
    exact fun h0 => hm (by rw [h0, zero_mul])

  have hreg : HasSum (fun t : ℤ => ∑ᶠ m : {i // ℓ i = t}, w m * X ^ ℓ m) (∑' n : ℤ × ℤ, w n * X ^ ℓ n) :=
    hasSum_finsum_fiber ℓ hs.hasSum hfin

  have hfib : ∀ t : ℤ, (∑ᶠ m : {i // ℓ i = t}, w m * X ^ ℓ m) = c t * X ^ t := by
    intro t
    have h1 : (∑ᶠ m : {i // ℓ i = t}, w m * X ^ ℓ m) = ∑ᶠ m : {i // ℓ i = t}, w m * X ^ t :=
      finsum_congr fun m => by rw [m.2]
    rw [h1, ← finsum_mul, finsum_subtype_eq_finsum_ite]
  have hreg' : HasSum (fun t : ℤ => c t * X ^ t) (∑' n : ℤ × ℤ, w n * X ^ ℓ n) := by
    simpa only [hfib] using hreg
  have hmain := hP X hX hreg'.summable
  rwa [hreg'.tsum_eq] at hmain

end S_Polynomial_exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line
end P2MW
export P2MW.S_Polynomial_exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line (solution)
