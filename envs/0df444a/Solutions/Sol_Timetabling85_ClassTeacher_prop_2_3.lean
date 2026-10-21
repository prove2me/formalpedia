-- Prove2me | solution 1 for Timetabling85.ClassTeacher.prop_2_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T16:10:12.679989+00:00
-- url     : https://prove2.me/submissions/bc1b2e5b-0e2b-4645-a3a6-919f368fe711

/-
SPDX-License-Identifier: Apache-2.0
Full balanced weekly timetabling Proposition 2.3.
Mathematical source: D. de Werra, An introduction to timetabling,
European Journal of Operational Research 19 (1985), 151–162, section 2.1.
Fresh rational matrix integrality proof by a zero-margin kernel direction
and finite boundary perturbation, dummy-margin completion, and day induction.
All native definitions and hypotheses remain unchanged.
No accepted proof implementation is copied.
-/
import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

-- BEGIN Foundation
open scoped BigOperators

namespace BalancedTimetableProof

end BalancedTimetableProof
-- END Foundation

-- BEGIN FractionalSupport
open scoped BigOperators Classical
open Finset

namespace BalancedTimetableProof

 def Integral (x : ℚ) : Prop := ∃ z : ℤ, x = z

 theorem integral_sum {K : Type*} (s : Finset K) (f : K → ℚ)
    (h : ∀ k ∈ s, Integral (f k)) : Integral (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert k s hk ih =>
    obtain ⟨z, hz⟩ := h k (by simp)
    obtain ⟨w, hw⟩ := ih (fun l hl => h l (by simp [hl]))
    exact ⟨z+w, by simp [Finset.sum_insert hk, hz, hw]⟩

 theorem integral_sub {x y : ℚ} (hx : Integral x) (hy : Integral y) :
    Integral (x-y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a-b, by simp⟩

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def fractional (a : I → J → ℚ) : Finset (I × J) := by
  classical
  exact univ.filter (fun e => ¬ Integral (a e.1 e.2))

@[simp] theorem mem_fractional (a : I → J → ℚ) (i : I) (j : J) :
    (i,j) ∈ fractional a ↔ ¬ Integral (a i j) := by
  classical
  simp [fractional]

omit [Fintype I] in
 theorem another_fractional (a : I → J → ℚ)
    (hr : ∀ i, Integral (∑ j, a i j)) {i : I} {j : J}
    (hj : ¬ Integral (a i j)) : ∃ k, k ≠ j ∧ ¬ Integral (a i k) := by
  classical
  by_contra h
  push Not at h
  have hs : Integral (∑ k ∈ univ.erase j, a i k) :=
    integral_sum _ _ (fun k hk => h k (Finset.mem_erase.mp hk).1)
  have hh := integral_sub (hr i) hs
  have he : (∑ k, a i k) - (∑ k ∈ univ.erase j, a i k) = a i j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    ring
  exact hj (he ▸ hh)

 theorem fractional_count (a : I → J → ℚ)
    (hr : ∀ i, Integral (∑ j, a i j))
    (hc : ∀ j, Integral (∑ i, a i j)) :
    (fractional a |>.image Prod.fst).card +
      (fractional a |>.image Prod.snd).card ≤ (fractional a).card := by
  classical
  let F := fractional a
  have hrow : 2 * (F.image Prod.fst).card ≤ F.card := by
    have hsum := Finset.card_eq_sum_card_fiberwise
      (s := F) (t := F.image Prod.fst) (f := Prod.fst)
      (fun e he => Finset.mem_image_of_mem Prod.fst he)
    rw [hsum]
    calc
      2 * (F.image Prod.fst).card = ∑ i ∈ F.image Prod.fst, 2 := by simp [mul_comm]
      _ ≤ ∑ i ∈ F.image Prod.fst, (F.filter (fun e => e.1 = i)).card := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨⟨i',j⟩, he, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨k, hkj, hk⟩ := another_fractional a hr (mem_fractional a i' j |>.mp he)
        have hsub : {(i',j), (i',k)} ⊆ F.filter (fun e => e.1 = i') := by
          intro e he'
          simp only [Finset.mem_insert, Finset.mem_singleton] at he'
          rcases he' with rfl | rfl
          · simpa [F] using he
          · simp [F, hk]
        have hn : (i',j) ≠ (i',k) := by intro h; exact hkj (Prod.mk.inj h).2.symm
        simpa [hn] using Finset.card_le_card hsub
  have hcol : 2 * (F.image Prod.snd).card ≤ F.card := by
    have hsum := Finset.card_eq_sum_card_fiberwise
      (s := F) (t := F.image Prod.snd) (f := Prod.snd)
      (fun e he => Finset.mem_image_of_mem Prod.snd he)
    rw [hsum]
    calc
      2 * (F.image Prod.snd).card = ∑ j ∈ F.image Prod.snd, 2 := by simp [mul_comm]
      _ ≤ ∑ j ∈ F.image Prod.snd, (F.filter (fun e => e.2 = j)).card := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨⟨i,j'⟩, he, rfl⟩ := Finset.mem_image.mp hj
        obtain ⟨k, hki, hk⟩ := another_fractional (fun j i => a i j) hc
          (mem_fractional a i j' |>.mp he)
        have hsub : {(i,j'), (k,j')} ⊆ F.filter (fun e => e.2 = j') := by
          intro e he'
          simp only [Finset.mem_insert, Finset.mem_singleton] at he'
          rcases he' with rfl | rfl
          · simpa [F] using he
          · simp [F, hk]
        have hn : (i,j') ≠ (k,j') := by intro h; exact hki (Prod.mk.inj h).1.symm
        simpa [hn] using Finset.card_le_card hsub
  change (F.image Prod.fst).card + (F.image Prod.snd).card ≤ F.card
  omega

end BalancedTimetableProof
-- END FractionalSupport

-- BEGIN KernelDirection
open scoped BigOperators Classical
open Finset

namespace BalancedTimetableProof
variable {I J : Type*} [Fintype I] [Fintype J]

 theorem zero_margin_direction (a : I → J → ℚ)
    (hr : ∀ i, Integral (∑ j, a i j))
    (hc : ∀ j, Integral (∑ i, a i j))
    (hne : (fractional a).Nonempty) :
    ∃ d : I → J → ℚ, d ≠ 0 ∧
      (∀ i j, Integral (a i j) → d i j = 0) ∧
      (∀ i, ∑ j, d i j = 0) ∧ (∀ j, ∑ i, d i j = 0) := by
  classical
  let F := fractional a
  let A := F.image Prod.fst
  let B := F.image Prod.snd
  obtain ⟨⟨i0,j0⟩, h0⟩ := hne
  have hi0 : i0 ∈ A := Finset.mem_image_of_mem Prod.fst h0
  let ext (v : F → ℚ) : I → J → ℚ :=
    fun i j => if h : (i,j) ∈ F then v ⟨(i,j),h⟩ else 0
  have headd (v w : F → ℚ) : ext (v+w) = ext v + ext w := by
    funext i j
    dsimp [ext]
    split <;> simp_all
  have hesmul (r : ℚ) (v : F → ℚ) : ext (r • v) = r • ext v := by
    funext i j
    dsimp [ext]
    split <;> simp_all
  let L : (F → ℚ) →ₗ[ℚ] ((A.erase i0 → ℚ) × (B → ℚ)) :=
    { toFun := fun v => (fun i => ∑ j, ext v i j, fun j => ∑ i, ext v i j)
      map_add' := by
        intro v w
        apply Prod.ext <;> funext i <;> simp [headd, Finset.sum_add_distrib]
      map_smul' := by
        intro r v
        apply Prod.ext <;> funext i <;> simp [hesmul, Finset.mul_sum] }
  have hninj : ¬ Function.Injective L := by
    intro hinj
    have hd := L.finrank_le_finrank_of_injective hinj
    have hcount := fractional_count a hr hc
    have hcard : (A.erase i0).card + 1 = A.card := Finset.card_erase_add_one hi0
    simp only [Module.finrank_fintype_fun_eq_card, Module.finrank_prod,
      Fintype.card_coe] at hd
    change F.card ≤ (A.erase i0).card + B.card at hd
    change A.card+B.card ≤ F.card at hcount
    omega
  unfold Function.Injective at hninj
  push Not at hninj
  obtain ⟨v,w,hvw,hne⟩ := hninj
  let z := v-w
  have hz : z ≠ 0 := sub_ne_zero.mpr hne
  have hLz : L z = 0 := by simp [z, map_sub, hvw]
  have hrows : ∀ i ∈ A.erase i0, ∑ j, ext z i j = 0 := by
    intro i hi
    exact congrFun (congrArg Prod.fst hLz) ⟨i,hi⟩
  have hcols : ∀ j ∈ B, ∑ i, ext z i j = 0 := by
    intro j hj
    exact congrFun (congrArg Prod.snd hLz) ⟨j,hj⟩
  have hoff (i : I) (j : J) (h : (i,j) ∉ F) : ext z i j = 0 := by simp [ext,h]
  have hcolall : ∀ j, ∑ i, ext z i j = 0 := by
    intro j
    by_cases hj : j ∈ B
    · exact hcols j hj
    · apply Finset.sum_eq_zero
      intro i _
      apply hoff
      intro he
      exact hj (Finset.mem_image_of_mem Prod.snd he)
  have hrowother : ∀ i, i ≠ i0 → ∑ j, ext z i j = 0 := by
    intro i hi
    by_cases ha : i ∈ A
    · exact hrows i (Finset.mem_erase.mpr ⟨hi,ha⟩)
    · apply Finset.sum_eq_zero
      intro j _
      apply hoff
      intro he
      exact ha (Finset.mem_image_of_mem Prod.fst he)
  have hrowall : ∀ i, ∑ j, ext z i j = 0 := by
    intro i
    by_cases hi : i = i0
    · subst i
      have ht : (∑ i, ∑ j, ext z i j) = 0 := by
        rw [Finset.sum_comm]
        simp [hcolall]
      rwa [Finset.sum_eq_single i0 (fun i _ hi => hrowother i hi)
        (by simp)] at ht
    · exact hrowother i hi
  refine ⟨ext z, ?_, ?_, hrowall, hcolall⟩
  · intro he
    apply hz
    funext e
    have hh := congrFun (congrFun he e.val.1) e.val.2
    simpa [ext, e.property] using hh
  · intro i j hij
    exact hoff i j (by simpa [F] using hij)

end BalancedTimetableProof
-- END KernelDirection

-- BEGIN BoundaryStep
open scoped BigOperators Classical
open Finset

namespace BalancedTimetableProof

 theorem boundary_step {K : Type*} [Fintype K] (a d : K → ℚ)
    (hne : d ≠ 0) (hoff : ∀ k, Integral (a k) → d k = 0) :
    ∃ t : ℚ, 0 < t ∧
      (∀ k, (⌊a k⌋ : ℚ) ≤ a k+t*d k ∧ a k+t*d k ≤ (⌈a k⌉ : ℚ)) ∧
      ∃ k, d k ≠ 0 ∧ Integral (a k+t*d k) := by
  classical
  let S : Finset K := univ.filter (fun k => d k ≠ 0)
  have hS : S.Nonempty := by
    by_contra h
    apply hne
    funext k
    have hn : k ∉ S := by rw [Finset.not_nonempty_iff_eq_empty.mp h]; simp
    simpa [S] using hn
  let time (k : K) : ℚ :=
    if 0 < d k then ((⌈a k⌉ : ℚ)-a k)/d k else
      (a k-(⌊a k⌋ : ℚ))/(-d k)
  have hf (k : K) (hk : k ∈ S) : (⌊a k⌋ : ℚ) < a k := by
    have hn : ¬ Integral (a k) := fun h => (Finset.mem_filter.mp hk).2 (hoff k h)
    refine lt_of_le_of_ne (Int.floor_le _) ?_
    intro he
    exact hn ⟨⌊a k⌋, he.symm⟩
  have hc (k : K) (hk : k ∈ S) : a k < (⌈a k⌉ : ℚ) := by
    have hn : ¬ Integral (a k) := fun h => (Finset.mem_filter.mp hk).2 (hoff k h)
    refine lt_of_le_of_ne (Int.le_ceil _) ?_
    intro he
    exact hn ⟨⌈a k⌉, he⟩
  have htime (k : K) (hk : k ∈ S) : 0 < time k := by
    dsimp [time]
    split_ifs with hd
    · exact div_pos (sub_pos.mpr (hc k hk)) hd
    · exact div_pos (sub_pos.mpr (hf k hk))
        (neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hd) (Finset.mem_filter.mp hk).2))
  obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image S time hS
  refine ⟨time k0, htime k0 hk0, ?_, k0, (Finset.mem_filter.mp hk0).2, ?_⟩
  · intro k
    by_cases hz : d k = 0
    · simpa [hz] using And.intro (Int.floor_le (a k)) (Int.le_ceil (a k))
    have hk : k ∈ S := by simp [S,hz]
    have ht := hmin k hk
    have hp := (htime k0 hk0).le
    by_cases hd : 0 < d k
    · have hh : time k0 * d k ≤ (⌈a k⌉ : ℚ)-a k := by
        apply (le_div_iff₀ hd).mp
        simpa [time,hd] using ht
      have hh0 : 0 ≤ time k0*d k := mul_nonneg hp hd.le
      constructor <;> linarith [Int.floor_le (a k)]
    · have hd' : 0 < -d k := by exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hd) hz)
      have hh : time k0 * (-d k) ≤ a k-(⌊a k⌋ : ℚ) := by
        apply (le_div_iff₀ hd').mp
        simpa [time,hd] using ht
      have hh0 : time k0*d k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp (le_of_not_gt hd)
      constructor <;> linarith [Int.le_ceil (a k)]
  · by_cases hd : 0 < d k0
    · refine ⟨⌈a k0⌉, ?_⟩
      dsimp [time]
      rw [if_pos hd, div_mul_cancel₀ _ (ne_of_gt hd)]
      ring
    · refine ⟨⌊a k0⌋, ?_⟩
      dsimp [time]
      rw [if_neg hd]
      have hz := (Finset.mem_filter.mp hk0).2
      rw [div_neg, neg_mul, div_mul_cancel₀ _ hz]
      simp only [Int.fract]
      ring

end BalancedTimetableProof
-- END BoundaryStep

-- BEGIN IntegralRounding
open scoped BigOperators Classical
open Finset

namespace BalancedTimetableProof
variable {I J : Type*} [Fintype I] [Fintype J]

 theorem integer_margin_rounding (a : I → J → ℚ)
    (hrow : ∀ i, ∃ z : ℤ, (∑ j, a i j) = z)
    (hcol : ∀ j, ∃ z : ℤ, (∑ i, a i j) = z) :
    ∃ b : I → J → ℚ,
      (∀ i j, ∃ z : ℤ, b i j = z) ∧
      (∀ i, ∑ j, b i j = ∑ j, a i j) ∧
      (∀ j, ∑ i, b i j = ∑ i, a i j) ∧
      (∀ i j, (⌊a i j⌋ : ℚ) ≤ b i j ∧ b i j ≤ (⌈a i j⌉ : ℚ)) := by
  classical
  generalize hn : (fractional a).card = n
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases he : (fractional a).Nonempty
    · obtain ⟨d, hd, hoff, hr, hc⟩ := zero_margin_direction a hrow hcol he
      have hdn : (fun e : I × J => d e.1 e.2) ≠ 0 := by
        intro h
        apply hd
        funext i j
        exact congrFun h (i,j)
      obtain ⟨t, _, hb, e, hde, hie⟩ := boundary_step
        (fun e : I × J => a e.1 e.2) (fun e => d e.1 e.2) hdn
        (fun e => hoff e.1 e.2)
      let a' : I → J → ℚ := fun i j => a i j+t*d i j
      have hr' (i : I) : ∑ j, a' i j = ∑ j, a i j := by
        simp [a', Finset.sum_add_distrib, ← Finset.mul_sum, hr]
      have hc' (j : J) : ∑ i, a' i j = ∑ i, a i j := by
        simp [a', Finset.sum_add_distrib, ← Finset.mul_sum, hc]
      have hsub : fractional a' ⊆ fractional a := by
        intro e he'
        apply (mem_fractional a e.1 e.2).mpr
        intro hh
        apply (mem_fractional a' e.1 e.2).mp he'
        simpa [a', hoff e.1 e.2 hh] using hh
      have hstrict : fractional a' ⊂ fractional a := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
        intro heq
        have hea : e ∈ fractional a := by
          apply (mem_fractional a e.1 e.2).mpr
          intro hh
          exact hde (hoff e.1 e.2 hh)
        have hea' : e ∈ fractional a' := heq ▸ hea
        exact (mem_fractional a' e.1 e.2 |>.mp hea') hie
      have hn' : (fractional a').card < n := hn ▸ Finset.card_lt_card hstrict
      obtain ⟨b, hbint, hbr, hbc, hbb⟩ := ih _ hn' a'
        (fun i => (hr' i).symm ▸ hrow i) (fun j => (hc' j).symm ▸ hcol j) rfl
      refine ⟨b, hbint, fun i => (hbr i).trans (hr' i),
        fun j => (hbc j).trans (hc' j), ?_⟩
      intro i j
      have bounds := hb (i,j)
      have hlo : (⌊a i j⌋ : ℚ) ≤ (⌊a' i j⌋ : ℚ) := by
        exact_mod_cast (Int.le_floor.mpr bounds.1)
      have hhi : (⌈a' i j⌉ : ℚ) ≤ (⌈a i j⌉ : ℚ) := by
        exact_mod_cast (Int.ceil_le.mpr bounds.2)
      exact ⟨hlo.trans (hbb i j).1, (hbb i j).2.trans hhi⟩
    · refine ⟨a, ?_, fun _ => rfl, fun _ => rfl, ?_⟩
      · intro i j
        have hnmem : (i,j) ∉ fractional a := fun h => he ⟨_,h⟩
        simpa [Integral] using hnmem
      · intro i j
        exact ⟨Int.floor_le _, Int.le_ceil _⟩

end BalancedTimetableProof
-- END IntegralRounding

-- BEGIN ResidualBounds
open Timetabling85.ClassTeacher
open scoped BigOperators

namespace BalancedTimetableProof

lemma hi_le_self (s p : ℕ) (hp : 0 < p) : hi s p ≤ s := by
  apply Nat.ceil_le.mpr
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  apply (div_le_iff₀ hp').2
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
  have hs : (0 : ℚ) ≤ s := by positivity
  nlinarith

lemma quotient_bounds (s p : ℕ) (hp : 0 < p) :
    lo s p * p ≤ s ∧ s ≤ hi s p * p ∧ hi s p ≤ lo s p + 1 ∧
    (lo s p < hi s p → lo s p * p < s ∧ s < hi s p * p) := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hnon : (0 : ℚ) ≤ (s : ℚ) / p := by positivity
  have hl : ((lo s p : ℕ) : ℚ) ≤ (s : ℚ) / p := Nat.floor_le hnon
  have hu : (s : ℚ) / p ≤ (hi s p : ℕ) := Nat.le_ceil _
  have hgap : hi s p ≤ lo s p + 1 := Nat.ceil_le_floor_add_one _
  refine ⟨?_, ?_, hgap, ?_⟩
  · exact_mod_cast (le_div_iff₀ hp').mp hl
  · exact_mod_cast (div_le_iff₀ hp').mp hu
  · intro hlt
    have hl' : ((lo s p : ℕ) : ℚ) < (s : ℚ) / p := Nat.lt_ceil.mp hlt
    have hu' : (s : ℚ) / p < (hi s p : ℕ) := by
      have h : (s : ℚ) / p < (lo s p : ℕ) + 1 := Nat.lt_floor_add_one _
      have heq : hi s p = lo s p + 1 := by omega
      rw [heq]
      exact_mod_cast h
    exact ⟨by exact_mod_cast (lt_div_iff₀ hp').mp hl',
      by exact_mod_cast (div_lt_iff₀ hp').mp hu'⟩

lemma remaining_bounds (s p v : ℕ) (hp : 2 ≤ p)
    (hv : lo s p ≤ v ∧ v ≤ hi s p) :
    lo s p ≤ lo (s - v) (p - 1) ∧ hi (s - v) (p - 1) ≤ hi s p := by
  have hp0 : 0 < p := by omega
  have hvs : v ≤ s := hv.2.trans (hi_le_self s p hp0)
  obtain ⟨hl, hu, hgap, hstrict⟩ := quotient_bounds s p hp0
  have hsub : s - v + v = s := Nat.sub_add_cancel hvs
  have hpred : p - 1 + 1 = p := by omega
  have hlow : lo s p * (p - 1) ≤ s - v := by
    by_cases h : v ≤ lo s p
    · nlinarith
    · have hlu : lo s p < hi s p := by omega
      have hs := (hstrict hlu).1
      nlinarith
  have hupp : s - v ≤ hi s p * (p - 1) := by
    by_cases h : hi s p ≤ v
    · nlinarith
    · have hlu : lo s p < hi s p := by omega
      have hs := (hstrict hlu).2
      nlinarith
  have hq : (0 : ℚ) < (p - 1 : ℕ) := by exact_mod_cast (show 0 < p - 1 by omega)
  constructor
  · apply Nat.le_floor
    apply (le_div_iff₀ hq).2
    exact_mod_cast hlow
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hq).2
    exact_mod_cast hupp

end BalancedTimetableProof
-- END ResidualBounds

-- BEGIN DummyRounding
open scoped BigOperators

namespace BalancedTimetableProof

lemma rounding_slack_floor (s : ℚ) : ⌊(⌈s⌉ : ℚ) - s⌋ = 0 := by
  simp [sub_eq_add_neg, Int.floor_intCast_add, Int.floor_neg]

lemma rounding_slack_ceil (s : ℚ) : ⌈(⌈s⌉ : ℚ) - s⌉ = ⌈s⌉ - ⌊s⌋ := by
  simp [sub_eq_add_neg, Int.ceil_intCast_add, Int.ceil_neg]

lemma margin_of_slack (s t w : ℚ) (heq : t + w = (⌈s⌉ : ℚ))
    (hw : (⌊(⌈s⌉ : ℚ) - s⌋ : ℚ) ≤ w ∧ w ≤ (⌈(⌈s⌉ : ℚ) - s⌉ : ℚ)) :
    (⌊s⌋ : ℚ) ≤ t ∧ t ≤ (⌈s⌉ : ℚ) := by
  rw [rounding_slack_floor, rounding_slack_ceil] at hw
  push_cast at hw
  constructor <;> linarith

/-- Simultaneously round every entry, row total and column total. -/
theorem simultaneous_rounding {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℚ) :
    ∃ b : I → J → ℚ,
      (∀ i j, ∃ z : ℤ, b i j = (z : ℚ)) ∧
      (∀ i j, (⌊a i j⌋ : ℚ) ≤ b i j ∧ b i j ≤ (⌈a i j⌉ : ℚ)) ∧
      (∀ i, (⌊∑ j, a i j⌋ : ℚ) ≤ ∑ j, b i j ∧
        ∑ j, b i j ≤ (⌈∑ j, a i j⌉ : ℚ)) ∧
      (∀ j, (⌊∑ i, a i j⌋ : ℚ) ≤ ∑ i, b i j ∧
        ∑ i, b i j ≤ (⌈∑ i, a i j⌉ : ℚ)) := by
  classical
  let r : I → ℚ := fun i => (⌈∑ j, a i j⌉ : ℚ) - ∑ j, a i j
  let c : J → ℚ := fun j => (⌈∑ i, a i j⌉ : ℚ) - ∑ i, a i j
  let C : ℚ := ∑ j, c j
  let d : ℚ := (⌈C⌉ : ℚ) - C
  let aug : Option I → Option J → ℚ
    | some i, some j => a i j
    | some i, none => r i
    | none, some j => c j
    | none, none => d
  have hrow : ∀ i, ∃ z : ℤ, (∑ j, aug i j) = (z : ℚ) := by
    intro i
    cases i with
    | none =>
        refine ⟨⌈C⌉, ?_⟩
        simp only [Fintype.sum_option, aug]
        dsimp [d, C]
        ring
    | some i =>
        refine ⟨⌈∑ j, a i j⌉, ?_⟩
        simp only [Fintype.sum_option, aug]
        dsimp [r]
        ring
  have hcol : ∀ j, ∃ z : ℤ, (∑ i, aug i j) = (z : ℚ) := by
    intro j
    cases j with
    | none =>
        refine ⟨⌈C⌉ + (∑ i, ⌈∑ j, a i j⌉) - ∑ j, ⌈∑ i, a i j⌉, ?_⟩
        simp only [Fintype.sum_option, aug]
        dsimp [d, C, c, r]
        simp only [Finset.sum_sub_distrib, Int.cast_add, Int.cast_sub, Int.cast_sum]
        rw [Finset.sum_comm (f := a)]
        ring
    | some j =>
        refine ⟨⌈∑ i, a i j⌉, ?_⟩
        simp only [Fintype.sum_option, aug]
        dsimp [c]
        ring
  obtain ⟨b, hbint, hbrow, hbcol, hbbounds⟩ := integer_margin_rounding aug hrow hcol
  refine ⟨fun i j => b (some i) (some j), ?_, ?_, ?_, ?_⟩
  · intro i j
    exact hbint (some i) (some j)
  · intro i j
    exact hbbounds (some i) (some j)
  · intro i
    apply margin_of_slack (∑ j, a i j) (∑ j, b (some i) (some j)) (b (some i) none)
    · have h := hbrow (some i)
      simp only [Fintype.sum_option, aug] at h
      dsimp [r] at h
      linarith
    · exact hbbounds (some i) none
  · intro j
    apply margin_of_slack (∑ i, a i j) (∑ i, b (some i) (some j)) (b none (some j))
    · have h := hbcol (some j)
      simp only [Fintype.sum_option, aug] at h
      dsimp [c] at h
      linarith
    · exact hbbounds none (some j)

end BalancedTimetableProof
-- END DummyRounding

-- BEGIN OneDay
open Timetabling85.ClassTeacher
open scoped BigOperators

namespace BalancedTimetableProof

lemma nat_bounds_of_int_bounds (s : ℚ) (hs : 0 ≤ s) (v : ℕ)
    (h : (⌊s⌋ : ℚ) ≤ v ∧ (v : ℚ) ≤ (⌈s⌉ : ℚ)) :
    ⌊s⌋₊ ≤ v ∧ v ≤ ⌈s⌉₊ := by
  rw [← natCast_floor_eq_intCast_floor hs, ← natCast_ceil_eq_intCast_ceil hs] at h
  exact_mod_cast h

/-- Natural-valued simultaneous rounding of a nonnegative rational matrix. -/
theorem natural_rounding {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℚ) (ha : ∀ i j, 0 ≤ a i j) :
    ∃ y : I → J → ℕ,
      (∀ i j, ⌊a i j⌋₊ ≤ y i j ∧ y i j ≤ ⌈a i j⌉₊) ∧
      (∀ i, ⌊∑ j, a i j⌋₊ ≤ ∑ j, y i j ∧ ∑ j, y i j ≤ ⌈∑ j, a i j⌉₊) ∧
      (∀ j, ⌊∑ i, a i j⌋₊ ≤ ∑ i, y i j ∧ ∑ i, y i j ≤ ⌈∑ i, a i j⌉₊) := by
  classical
  obtain ⟨b, hbint, hbe, hbr, hbc⟩ := simultaneous_rounding a
  have hb0 : ∀ i j, 0 ≤ b i j := by
    intro i j
    have h : (0 : ℚ) ≤ (⌊a i j⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.mpr (ha i j)
    exact h.trans (hbe i j).1
  let y : I → J → ℕ := fun i j => ⌊b i j⌋₊
  have hy : ∀ i j, (y i j : ℚ) = b i j := by
    intro i j
    dsimp [y]
    rw [natCast_floor_eq_intCast_floor (hb0 i j)]
    obtain ⟨z, hz⟩ := hbint i j
    rw [hz, Int.floor_intCast]
  refine ⟨y, ?_, ?_, ?_⟩
  · intro i j
    apply nat_bounds_of_int_bounds _ (ha i j)
    simpa only [hy] using hbe i j
  · intro i
    apply nat_bounds_of_int_bounds _ (Finset.sum_nonneg fun j _ => ha i j)
    simpa only [Nat.cast_sum, hy] using hbr i
  · intro j
    apply nat_bounds_of_int_bounds _ (Finset.sum_nonneg fun i _ => ha i j)
    simpa only [Nat.cast_sum, hy] using hbc j

/-- One day satisfies all three exact native balancing constraints at once. -/
theorem one_balanced_day {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ y : Fin m → Fin n → ℕ,
      (∀ i, lo (rowSum R i) p ≤ ∑ j, y i j ∧ ∑ j, y i j ≤ hi (rowSum R i) p) ∧
      (∀ j, lo (colSum R j) p ≤ ∑ i, y i j ∧ ∑ i, y i j ≤ hi (colSum R j) p) ∧
      (∀ i j, lo (R i j) p ≤ y i j ∧ y i j ≤ hi (R i j) p) := by
  have _ := hp
  obtain ⟨y, he, hr, hc⟩ := natural_rounding (fun i j => (R i j : ℚ) / p)
    (fun i j => by positivity)
  refine ⟨y, ?_, ?_, he⟩
  · intro i
    simpa only [lo, hi, rowSum, Nat.cast_sum, Finset.sum_div] using hr i
  · intro j
    simpa only [lo, hi, colSum, Nat.cast_sum, Finset.sum_div] using hc j

end BalancedTimetableProof
-- END OneDay

-- BEGIN NativeRoot
open Timetabling85.ClassTeacher
open scoped BigOperators

namespace BalancedTimetableProof

lemma balanced_schedule {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ x : Fin m → Fin n → Fin p → ℕ, IsCT3 R p x := by
  induction p generalizing R with
  | zero => omega
  | succ q ih =>
      by_cases hq : q = 0
      · subst q
        refine ⟨fun i j _ => R i j, ?_⟩
        simp [IsCT3, SchedulesAll, lo, hi, rowSum, colSum, -Nat.cast_sum]
      · have hq0 : 0 < q := Nat.pos_of_ne_zero hq
        have hq2 : 2 ≤ q + 1 := by omega
        obtain ⟨y, hyr, hyc, hye⟩ := one_balanced_day R (q + 1) (by omega)
        have hyR : ∀ i j, y i j ≤ R i j := fun i j =>
          (hye i j).2.trans (hi_le_self _ _ (by omega))
        let R' : Fin m → Fin n → ℕ := fun i j => R i j - y i j
        obtain ⟨z, hzall, hzr, hzc, hze⟩ := ih R' hq0
        have hrow : ∀ i, rowSum R' i = rowSum R i - ∑ j, y i j := by
          intro i
          exact Finset.sum_tsub_distrib _ (fun j _ => hyR i j)
        have hcol : ∀ j, colSum R' j = colSum R j - ∑ i, y i j := by
          intro j
          exact Finset.sum_tsub_distrib _ (fun i _ => hyR i j)
        have hnestR : ∀ i, lo (rowSum R i) (q + 1) ≤ lo (rowSum R' i) q ∧
            hi (rowSum R' i) q ≤ hi (rowSum R i) (q + 1) := by
          intro i
          rw [hrow]
          simpa only [Nat.add_sub_cancel] using remaining_bounds
            (rowSum R i) (q + 1) (∑ j, y i j) hq2 (hyr i)
        have hnestC : ∀ j, lo (colSum R j) (q + 1) ≤ lo (colSum R' j) q ∧
            hi (colSum R' j) q ≤ hi (colSum R j) (q + 1) := by
          intro j
          rw [hcol]
          simpa only [Nat.add_sub_cancel] using remaining_bounds
            (colSum R j) (q + 1) (∑ i, y i j) hq2 (hyc j)
        have hnestE : ∀ i j, lo (R i j) (q + 1) ≤ lo (R' i j) q ∧
            hi (R' i j) q ≤ hi (R i j) (q + 1) := by
          intro i j
          simpa only [Nat.add_sub_cancel, R'] using remaining_bounds
            (R i j) (q + 1) (y i j) hq2 (hye i j)
        let x : Fin m → Fin n → Fin (q + 1) → ℕ :=
          fun i j => Fin.cases (y i j) (fun k => z i j k)
        refine ⟨x, ?_, ?_, ?_, ?_⟩
        · intro i j
          change (∑ k, Fin.cases (y i j) (fun k => z i j k) k) = R i j
          rw [Fin.sum_univ_succ]
          simp only [Fin.cases_zero, Fin.cases_succ]
          rw [hzall i j]
          exact Nat.add_sub_of_le (hyR i j)
        · intro i k
          refine Fin.cases ?_ (fun k => ?_) k
          · simpa only [x, Fin.cases_zero] using hyr i
          · simpa only [x, Fin.cases_succ] using
              And.intro ((hnestR i).1.trans (hzr i k).1) ((hzr i k).2.trans (hnestR i).2)
        · intro j k
          refine Fin.cases ?_ (fun k => ?_) k
          · simpa only [x, Fin.cases_zero] using hyc j
          · simpa only [x, Fin.cases_succ] using
              And.intro ((hnestC j).1.trans (hzc j k).1) ((hzc j k).2.trans (hnestC j).2)
        · intro i j k
          refine Fin.cases ?_ (fun k => ?_) k
          · exact hye i j
          · exact ⟨(hnestE i j).1.trans (hze i j k).1,
              (hze i j k).2.trans (hnestE i j).2⟩

end BalancedTimetableProof

namespace Timetabling85.ClassTeacher

/-- Proposition 2.3 (de Werra 1985, p. 153): for every `m × n` requirement matrix `R` and every
number `p ≥ 1` of days, problem CT3 ((1) and (8)–(10)) has a solution. -/
theorem prop_2_3 {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ x : Fin m → Fin n → Fin p → ℕ, IsCT3 R p x := by
  exact BalancedTimetableProof.balanced_schedule R p hp

end Timetabling85.ClassTeacher
-- END NativeRoot

open Timetabling85.ClassTeacher

theorem solution {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ x : Fin m → Fin n → Fin p → ℕ, IsCT3 R p x :=
  Timetabling85.ClassTeacher.prop_2_3 R p hp
