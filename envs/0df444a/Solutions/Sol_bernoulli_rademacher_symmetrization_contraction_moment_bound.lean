-- Prove2me | solution 1 for bernoulli_rademacher_symmetrization_contraction_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-24T05:56:57.90749+00:00
-- url     : https://prove2.me/submissions/045a0ece-1e04-4b08-984a-a5aa504d6eb5

import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.SymmDiff
open scoped BigOperators

/-
W3 ASSEMBLY: discrete Bernoulli→Rademacher symmetrization (contraction).
Source: Ledoux–Talagrand "Probability in Banach Spaces" (1991) Lemma 6.3;
van der Vaart–Wellner Lemma 2.3.1; Tropp arXiv:1506.04711 Fact 3.1.
TARGET:  ∑_S wt p S ‖centered‖^q ≤ 2^q ∑_S ∑_Es wt p S · rwt · ‖signedSampled‖^q.
-/

namespace W3asm
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def bit (S : Finset κ) (a : κ) : ℝ := if a ∈ S then 1 else 0
noncomputable def wt (p : ℝ) (S : Finset κ) : ℝ :=
  p ^ S.card * (1 - p) ^ (Fintype.card κ - S.card)
noncomputable def rwt : ℝ := ((1:ℝ)/2) ^ Fintype.card κ
def sgn (Es : Finset κ) (a : κ) : ℝ := if a ∈ Es then 1 else -1

noncomputable def centered (p : ℝ) (S : Finset κ) (v : κ → E) : E :=
  ∑ a, (bit S a - p) • v a
noncomputable def ghostDiff (S S' : Finset κ) (v : κ → E) : E :=
  ∑ a, (bit S a - bit S' a) • v a
noncomputable def signedSampled (S Es : Finset κ) (v : κ → E) : E :=
  ∑ a, (sgn Es a * bit S a) • v a
noncomputable def signedDiff (S S' Es : Finset κ) (v : κ → E) : E :=
  ∑ a, (sgn Es a * (bit S a - bit S' a)) • v a

noncomputable def swapOn (Es S S' : Finset κ) : Finset κ := (S \ Es) ∪ (S' ∩ Es)

/-! ### Step-A primitives (banked) -/

theorem wt_sum_one (p : ℝ) : ∑ S : Finset κ, wt p S = 1 := by
  unfold wt
  have huniv : (Finset.univ : Finset (Finset κ)) = (Finset.univ : Finset κ).powerset := by
    ext S; simp
  rw [huniv, ← Finset.card_univ, Finset.sum_pow_mul_eq_add_pow]; simp

theorem wt_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset κ) : 0 ≤ wt p S := by
  unfold wt; have : 0 ≤ 1 - p := by linarith
  positivity

theorem coord_mean (p : ℝ) (a : κ) : ∑ S : Finset κ, wt p S * bit S a = p := by
  have hsplit : ∑ S : Finset κ, wt p S * bit S a
      = ∑ S ∈ Finset.univ.filter (fun S => a ∈ S), wt p S := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro S _
    unfold bit; by_cases h : a ∈ S <;> simp [h]
  rw [hsplit]
  rw [show (Finset.univ.filter (fun S : Finset κ => a ∈ S))
        = (Finset.univ.erase a).powerset.image (insert a) from ?_]
  · rw [Finset.sum_image ?_]
    · have hcardN : Fintype.card κ = (Finset.univ.erase a).card + 1 := by
        have h1 : (Finset.univ.erase a).card = Fintype.card κ - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
        have h2 : 1 ≤ Fintype.card κ := Fintype.card_pos_iff.2 ⟨a⟩
        omega
      have hval : ∀ T ∈ (Finset.univ.erase a).powerset, wt p (insert a T)
            = p * (p ^ T.card * (1 - p) ^ ((Finset.univ.erase a).card - T.card)) := by
        intro T hT
        rw [Finset.mem_powerset] at hT
        have haT : a ∉ T := fun h => (Finset.mem_erase.1 (hT h)).1 rfl
        unfold wt
        rw [Finset.card_insert_of_notMem haT, hcardN]
        have hTle : T.card ≤ (Finset.univ.erase a).card := Finset.card_le_card hT
        rw [show (Finset.univ.erase a).card + 1 - (T.card + 1)
              = (Finset.univ.erase a).card - T.card by omega]; ring
      rw [Finset.sum_congr rfl hval, ← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow]; simp
    · intro T1 hT1 T2 hT2 heq
      rw [Finset.mem_coe, Finset.mem_powerset] at hT1 hT2
      have ha1 : a ∉ T1 := fun h => (Finset.mem_erase.1 (hT1 h)).1 rfl
      have ha2 : a ∉ T2 := fun h => (Finset.mem_erase.1 (hT2 h)).1 rfl
      have := congrArg (fun s => s.erase a) heq
      simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
  · ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_powerset]
    constructor
    · intro hS
      refine ⟨S.erase a, ?_, ?_⟩
      · intro x hx; rw [Finset.mem_erase] at hx
        exact Finset.mem_erase.2 ⟨hx.1, Finset.mem_univ x⟩
      · rw [Finset.insert_erase hS]
    · rintro ⟨T, _, rfl⟩; exact Finset.mem_insert_self a T

theorem rwt_sum_one : ∑ _Es : Finset κ, (rwt (κ := κ)) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]
  unfold rwt
  rw [div_pow, one_pow, Nat.cast_pow, Nat.cast_ofNat, mul_one_div, div_self (by positivity)]

/-! ### Ghost mean + Jensen -/

theorem ghost_mean (p : ℝ) (S : Finset κ) (v : κ → E) :
    centered p S v = ∑ S' : Finset κ, wt p S' • ghostDiff S S' v := by
  unfold centered ghostDiff
  have step1 : ∑ S' : Finset κ, wt p S' • ∑ a, (bit S a - bit S' a) • v a
      = ∑ S' : Finset κ, ∑ a, (wt p S' * (bit S a - bit S' a)) • v a := by
    apply Finset.sum_congr rfl; intro S' _
    rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro a _
    rw [smul_smul]
  rw [step1, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_smul]
  congr 1
  have hexp : ∀ S', wt p S' * (bit S a - bit S' a)
      = wt p S' * bit S a - wt p S' * bit S' a := by intro S'; ring
  rw [Finset.sum_congr rfl (fun S' _ => hexp S')]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, wt_sum_one, coord_mean]; ring

theorem norm_pow_jensen (q : ℕ) (w : κ → ℝ) (x : κ → E)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ‖∑ i, w i • x i‖ ^ q ≤ ∑ i, w i • ‖x i‖ ^ q := by
  have htri : ‖∑ i, w i • x i‖ ≤ ∑ i, w i * ‖x i‖ := by
    calc ‖∑ i, w i • x i‖ ≤ ∑ i, ‖w i • x i‖ := norm_sum_le _ _
      _ = ∑ i, w i * ‖x i‖ := by
          apply Finset.sum_congr rfl; intro i _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 i)]
  have hnn : (0:ℝ) ≤ ‖∑ i, w i • x i‖ := norm_nonneg _
  have hmono : ‖∑ i, w i • x i‖ ^ q ≤ (∑ i, w i * ‖x i‖) ^ q :=
    pow_le_pow_left₀ hnn htri q
  have hcvx := (convexOn_pow (𝕜 := ℝ) q).map_sum_le
    (t := (Finset.univ : Finset κ)) (w := w) (p := fun i => ‖x i‖)
    (fun i _ => hw0 i) (by simpa using hw1)
    (fun i _ => by simp [norm_nonneg])
  simp only [smul_eq_mul] at hcvx ⊢
  exact le_trans hmono hcvx

/-! ### Swap involution + sign symmetry -/

theorem swapOn_mem_in (Es S S' : Finset κ) {a : κ} (h : a ∈ Es) :
    a ∈ swapOn Es S S' ↔ a ∈ S' := by
  unfold swapOn; simp [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, h]
theorem swapOn_mem_out (Es S S' : Finset κ) {a : κ} (h : a ∉ Es) :
    a ∈ swapOn Es S S' ↔ a ∈ S := by
  unfold swapOn; simp [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, h]

theorem swapOn_invol (Es S S' : Finset κ) :
    swapOn Es (swapOn Es S S') (swapOn Es S' S) = S := by
  ext a
  simp only [swapOn, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  by_cases h : a ∈ Es <;> simp [h]

theorem bit_swap_in (Es S S' : Finset κ) {a : κ} (h : a ∈ Es) :
    bit (swapOn Es S S') a = bit S' a := by
  unfold bit; by_cases hS' : a ∈ S'
  · rw [if_pos ((swapOn_mem_in Es S S' h).2 hS'), if_pos hS']
  · rw [if_neg (fun hc => hS' ((swapOn_mem_in Es S S' h).1 hc)), if_neg hS']
theorem bit_swap_out (Es S S' : Finset κ) {a : κ} (h : a ∉ Es) :
    bit (swapOn Es S S') a = bit S a := by
  unfold bit; by_cases hS : a ∈ S
  · rw [if_pos ((swapOn_mem_out Es S S' h).2 hS), if_pos hS]
  · rw [if_neg (fun hc => hS ((swapOn_mem_out Es S S' h).1 hc)), if_neg hS]

theorem bit_swapC (Es S S' : Finset κ) (a : κ) :
    bit (swapOn Esᶜ S S') a - bit (swapOn Esᶜ S' S) a
      = sgn Es a * (bit S a - bit S' a) := by
  unfold sgn
  by_cases h : a ∈ Es
  · have hc : a ∉ Esᶜ := by simp [h]
    rw [if_pos h, bit_swap_out Esᶜ S S' hc, bit_swap_out Esᶜ S' S hc]; ring
  · have hc : a ∈ Esᶜ := by simp [h]
    rw [if_neg h, bit_swap_in Esᶜ S S' hc, bit_swap_in Esᶜ S' S hc]; ring

theorem wt_prod (p : ℝ) (S : Finset κ) :
    wt p S = ∏ a : κ, (if a ∈ S then p else (1-p)) := by
  unfold wt
  rw [Finset.prod_ite (fun _ => p) (fun _ => (1-p))]
  congr 1
  · rw [Finset.prod_const]; congr 1; simp [Finset.filter_mem_eq_inter]
  · rw [Finset.prod_const]; congr 1
    have : (Finset.univ.filter (fun a => a ∉ S)).card
        = Fintype.card κ - (Finset.univ.filter (fun a => a ∈ S)).card := by
      rw [Finset.filter_not, Finset.card_univ_diff]
    rw [this]; congr 1; simp [Finset.filter_mem_eq_inter]

theorem wt_swap_prod (p : ℝ) (Es S S' : Finset κ) :
    wt p (swapOn Es S S') * wt p (swapOn Es S' S) = wt p S * wt p S' := by
  rw [wt_prod, wt_prod, wt_prod, wt_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  have h1 : (a ∈ swapOn Es S S') = (if a ∈ Es then a ∈ S' else a ∈ S) := by
    by_cases h : a ∈ Es
    · simp [propext (swapOn_mem_in Es S S' h), h]
    · simp [propext (swapOn_mem_out Es S S' h), h]
  have h2 : (a ∈ swapOn Es S' S) = (if a ∈ Es then a ∈ S else a ∈ S') := by
    by_cases h : a ∈ Es
    · simp [propext (swapOn_mem_in Es S' S h), h]
    · simp [propext (swapOn_mem_out Es S' S h), h]
  by_cases h : a ∈ Es <;> simp only [h1, h2, h, if_true, if_false] <;>
    by_cases hS : a ∈ S <;> by_cases hS' : a ∈ S' <;> simp [hS, hS'] <;> ring

/-- For every fixed Es: the swap-on-Esᶜ bijection turns the weighted ghostDiff^q sum
into the weighted signedDiff^q sum. -/
theorem ghost_to_signed (p : ℝ) (q : ℕ) (Es : Finset κ) (v : κ → E) :
    ∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖ghostDiff S S' v‖ ^ q
      = ∑ S : Finset κ, ∑ S' : Finset κ,
          wt p S * wt p S' * ‖signedDiff S S' Es v‖ ^ q := by
  -- reindex (S,S') ↦ (swapOn Esᶜ S S', swapOn Esᶜ S' S)
  rw [← Finset.sum_product', ← Finset.sum_product']
  apply Finset.sum_nbij'
    (i := fun ss => (swapOn Esᶜ ss.1 ss.2, swapOn Esᶜ ss.2 ss.1))
    (j := fun ss => (swapOn Esᶜ ss.1 ss.2, swapOn Esᶜ ss.2 ss.1))
  · intro a _; simp
  · intro a _; simp
  · intro ⟨S, S'⟩ _; simp only [Prod.mk.injEq]
    exact ⟨swapOn_invol Esᶜ S S', swapOn_invol Esᶜ S' S⟩
  · intro ⟨S, S'⟩ _; simp only [Prod.mk.injEq]
    exact ⟨swapOn_invol Esᶜ S S', swapOn_invol Esᶜ S' S⟩
  · intro ⟨S, S'⟩ _
    simp only
    -- weight product preserved + ghostDiff(orig) = signedDiff(swapped)
    have hw : wt p (swapOn Esᶜ S S') * wt p (swapOn Esᶜ S' S) = wt p S * wt p S' :=
      wt_swap_prod p Esᶜ S S'
    -- apply bit_swapC at the swapped pair, using involution swap∘swap = id
    have hg : ghostDiff S S' v
        = signedDiff (swapOn Esᶜ S S') (swapOn Esᶜ S' S) Es v := by
      unfold ghostDiff signedDiff
      apply Finset.sum_congr rfl; intro a _
      have key := bit_swapC Es (swapOn Esᶜ S S') (swapOn Esᶜ S' S) a
      rw [swapOn_invol Esᶜ S S', swapOn_invol Esᶜ S' S] at key
      rw [key]
    rw [hw, hg]

/-! ### Stage C: split + fold, and the main theorem -/

/-- tight power-mean: (a+b)^q ≤ 2^(q-1)(a^q+b^q) for q≥1, a,b≥0. -/
theorem add_pow_tight (q : ℕ) (hq : 1 ≤ q) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ q ≤ 2 ^ (q-1) * (a ^ q + b ^ q) := by
  have hcvx := (convexOn_pow (𝕜 := ℝ) q).2
  have key := hcvx (ha : a ∈ Set.Ici (0:ℝ)) (hb : b ∈ Set.Ici (0:ℝ))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at key
  have hhalf : ((1:ℝ)/2 * a + 1/2 * b) = (a+b)/2 := by ring
  rw [hhalf, div_pow] at key
  have h2q : (0:ℝ) < 2 ^ q := by positivity
  rw [div_le_iff₀ h2q] at key
  have hpow : (2:ℝ)^q = 2^(q-1) * 2 := by rw [← pow_succ]; congr 1; omega
  calc (a+b)^q ≤ ((1:ℝ)/2 * a^q + 1/2*b^q) * 2^q := key
    _ = 2^(q-1) * (a^q + b^q) := by rw [hpow]; ring

theorem signedDiff_split (S S' Es : Finset κ) (v : κ → E) :
    signedDiff S S' Es v = signedSampled S Es v - signedSampled S' Es v := by
  unfold signedDiff signedSampled
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _
  rw [← sub_smul]; congr 1; ring

/-- THE W3 TARGET. -/
theorem w3_target (q : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : κ → E) :
    ∑ S : Finset κ, wt p S * ‖centered p S v‖ ^ q
      ≤ 2 ^ q * ∑ S : Finset κ, ∑ Es : Finset κ,
          wt p S * (rwt (κ := κ)) * ‖signedSampled S Es v‖ ^ q := by
  -- Stage A: ghost mean + Jensen, weighted by wt p S
  have hStageA : ∑ S : Finset κ, wt p S * ‖centered p S v‖ ^ q
      ≤ ∑ S : Finset κ, ∑ S' : Finset κ,
          wt p S * wt p S' * ‖ghostDiff S S' v‖ ^ q := by
    apply Finset.sum_le_sum; intro S _
    rw [ghost_mean p S v]
    have hjen := norm_pow_jensen q (wt p) (fun S' => ghostDiff S S' v)
      (wt_nonneg p hp0 hp1) (wt_sum_one p)
    calc wt p S * ‖∑ S' : Finset κ, wt p S' • ghostDiff S S' v‖ ^ q
        ≤ wt p S * ∑ S' : Finset κ, wt p S' • ‖ghostDiff S S' v‖ ^ q := by
          apply mul_le_mul_of_nonneg_left hjen (wt_nonneg p hp0 hp1 S)
      _ = ∑ S' : Finset κ, wt p S * wt p S' * ‖ghostDiff S S' v‖ ^ q := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S' _
          rw [smul_eq_mul]; ring
  -- Stage B: insert the average over signs (each Es gives the same value)
  have hStageB : ∑ S : Finset κ, ∑ S' : Finset κ,
        wt p S * wt p S' * ‖ghostDiff S S' v‖ ^ q
      = ∑ Es : Finset κ, (rwt (κ := κ)) * ∑ S : Finset κ, ∑ S' : Finset κ,
          wt p S * wt p S' * ‖signedDiff S S' Es v‖ ^ q := by
    have hconst : ∀ Es : Finset κ,
        (∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖signedDiff S S' Es v‖ ^ q)
          = ∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖ghostDiff S S' v‖ ^ q :=
      fun Es => (ghost_to_signed p q Es v).symm
    calc ∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖ghostDiff S S' v‖ ^ q
        = 1 * ∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖ghostDiff S S' v‖ ^ q := by
          rw [one_mul]
      _ = (∑ _Es : Finset κ, (rwt (κ := κ))) *
            ∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖ghostDiff S S' v‖ ^ q := by
          rw [rwt_sum_one]
      _ = ∑ Es : Finset κ, (rwt (κ := κ)) *
            ∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖ghostDiff S S' v‖ ^ q := by
          rw [Finset.sum_mul]
      _ = ∑ Es : Finset κ, (rwt (κ := κ)) *
            ∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖signedDiff S S' Es v‖ ^ q := by
          apply Finset.sum_congr rfl; intro Es _; rw [hconst Es]
  -- Stage C per-Es fiber bound (needs q ≥ 1; q=0 handled separately at the end)
  -- per Es: ∑_S ∑_S' wt wt ‖signedDiff S S' Es‖^q ≤ 2^q · ∑_S wt ‖signedSampled S Es‖^q
  have hStageC : ∀ Es : Finset κ,
      (∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖signedDiff S S' Es v‖ ^ q)
        ≤ 2 ^ q * ∑ S : Finset κ, wt p S * ‖signedSampled S Es v‖ ^ q := by
    intro Es
    rcases Nat.eq_zero_or_pos q with hq0 | hq1
    · -- q = 0: both sides equal 1 (wt sums to 1)
      subst hq0
      simp only [pow_zero, mul_one, one_mul]
      have hlhs : ∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' = 1 := by
        have : ∀ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' = wt p S := by
          intro S; rw [← Finset.mul_sum, wt_sum_one, mul_one]
        rw [Finset.sum_congr rfl (fun S _ => this S), wt_sum_one]
      rw [hlhs, wt_sum_one]
    · -- q ≥ 1: tight split + fold
      have hsplit : ∀ S S' : Finset κ,
          ‖signedDiff S S' Es v‖ ^ q
            ≤ 2 ^ (q-1) * (‖signedSampled S Es v‖ ^ q + ‖signedSampled S' Es v‖ ^ q) := by
        intro S S'
        rw [signedDiff_split]
        calc ‖signedSampled S Es v - signedSampled S' Es v‖ ^ q
            ≤ (‖signedSampled S Es v‖ + ‖signedSampled S' Es v‖) ^ q := by
              apply pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _)
          _ ≤ 2 ^ (q-1) * (‖signedSampled S Es v‖ ^ q + ‖signedSampled S' Es v‖ ^ q) :=
              add_pow_tight q hq1 _ _ (norm_nonneg _) (norm_nonneg _)
      calc ∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖signedDiff S S' Es v‖ ^ q
          ≤ ∑ S : Finset κ, ∑ S' : Finset κ,
              wt p S * wt p S' * (2 ^ (q-1) *
                (‖signedSampled S Es v‖ ^ q + ‖signedSampled S' Es v‖ ^ q)) := by
            apply Finset.sum_le_sum; intro S _
            apply Finset.sum_le_sum; intro S' _
            apply mul_le_mul_of_nonneg_left (hsplit S S')
            exact mul_nonneg (wt_nonneg p hp0 hp1 S) (wt_nonneg p hp0 hp1 S')
        _ = 2 ^ q * ∑ S : Finset κ, wt p S * ‖signedSampled S Es v‖ ^ q := by
            -- algebra: split + ∑wt=1 fold; 2^(q-1)·2 = 2^q
            have hpow : (2:ℝ)^q = 2^(q-1) * 2 := by rw [← pow_succ]; congr 1; omega
            rw [hpow]
            -- pull 2^(q-1) out of the double sum
            have hbody : ∀ S S' : Finset κ,
                wt p S * wt p S' * (2 ^ (q-1) *
                  (‖signedSampled S Es v‖ ^ q + ‖signedSampled S' Es v‖ ^ q))
                = 2^(q-1) * (wt p S' * (wt p S * ‖signedSampled S Es v‖ ^ q)
                    + wt p S * (wt p S' * ‖signedSampled S' Es v‖ ^ q)) := by
              intro S S'; ring
            calc ∑ S : Finset κ, ∑ S' : Finset κ,
                  wt p S * wt p S' * (2 ^ (q-1) *
                    (‖signedSampled S Es v‖ ^ q + ‖signedSampled S' Es v‖ ^ q))
                = ∑ S : Finset κ, ∑ S' : Finset κ, 2^(q-1) *
                    (wt p S' * (wt p S * ‖signedSampled S Es v‖ ^ q)
                      + wt p S * (wt p S' * ‖signedSampled S' Es v‖ ^ q)) := by
                  apply Finset.sum_congr rfl; intro S _
                  apply Finset.sum_congr rfl; intro S' _; exact hbody S S'
              _ = 2^(q-1) * ∑ S : Finset κ, ∑ S' : Finset κ,
                    (wt p S' * (wt p S * ‖signedSampled S Es v‖ ^ q)
                      + wt p S * (wt p S' * ‖signedSampled S' Es v‖ ^ q)) := by
                  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _
                  rw [Finset.mul_sum]
              _ = 2^(q-1) * (2 * ∑ S : Finset κ, wt p S * ‖signedSampled S Es v‖ ^ q) := by
                  congr 1
                  -- the fold: each half collapses via ∑ wt = 1
                  have hsum_distrib : ∑ S : Finset κ, ∑ S' : Finset κ,
                        (wt p S' * (wt p S * ‖signedSampled S Es v‖ ^ q)
                          + wt p S * (wt p S' * ‖signedSampled S' Es v‖ ^ q))
                      = (∑ S : Finset κ, ∑ S' : Finset κ,
                          wt p S' * (wt p S * ‖signedSampled S Es v‖ ^ q))
                        + (∑ S : Finset κ, ∑ S' : Finset κ,
                          wt p S * (wt p S' * ‖signedSampled S' Es v‖ ^ q)) := by
                    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro S _
                    rw [← Finset.sum_add_distrib]
                  rw [hsum_distrib]
                  -- first half: ∑_S (∑_S' wt S') (wt S ‖sS S‖^q) = ∑_S wt S ‖sS S‖^q
                  have hhalf1 : ∑ S : Finset κ, ∑ S' : Finset κ,
                        wt p S' * (wt p S * ‖signedSampled S Es v‖ ^ q)
                      = ∑ S : Finset κ, wt p S * ‖signedSampled S Es v‖ ^ q := by
                    apply Finset.sum_congr rfl; intro S _
                    rw [← Finset.sum_mul, wt_sum_one, one_mul]
                  -- second half: ∑_S wt S ∑_S' wt S' ‖sS S'‖^q = ∑_S' wt S' ‖sS S'‖^q
                  have hhalf2 : ∑ S : Finset κ, ∑ S' : Finset κ,
                        wt p S * (wt p S' * ‖signedSampled S' Es v‖ ^ q)
                      = ∑ S : Finset κ, wt p S * ‖signedSampled S Es v‖ ^ q := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl; intro S' _
                    rw [← Finset.sum_mul, wt_sum_one, one_mul]
                  rw [hhalf1, hhalf2]; ring
              _ = 2^(q-1) * 2 * ∑ S : Finset κ, wt p S * ‖signedSampled S Es v‖ ^ q := by ring
  -- assemble: ∑_Es rwt · fiber ≤ ∑_Es rwt · 2^q · (...) = 2^q ∑_S∑_Es wt rwt ‖sS‖^q
  calc ∑ S : Finset κ, wt p S * ‖centered p S v‖ ^ q
      ≤ ∑ Es : Finset κ, (rwt (κ := κ)) *
          ∑ S : Finset κ, ∑ S' : Finset κ, wt p S * wt p S' * ‖signedDiff S S' Es v‖ ^ q :=
        hStageA.trans hStageB.le
    _ ≤ ∑ Es : Finset κ, (rwt (κ := κ)) *
          (2 ^ q * ∑ S : Finset κ, wt p S * ‖signedSampled S Es v‖ ^ q) := by
        apply Finset.sum_le_sum; intro Es _
        apply mul_le_mul_of_nonneg_left (hStageC Es)
        unfold rwt; positivity
    _ = 2 ^ q * ∑ S : Finset κ, ∑ Es : Finset κ,
          wt p S * (rwt (κ := κ)) * ‖signedSampled S Es v‖ ^ q := by
        -- pull 2^q out of the Es-sum on the LHS
        have hL : ∑ Es : Finset κ, (rwt (κ := κ)) *
              (2 ^ q * ∑ S : Finset κ, wt p S * ‖signedSampled S Es v‖ ^ q)
            = 2 ^ q * ∑ Es : Finset κ, ∑ S : Finset κ,
              (rwt (κ := κ)) * (wt p S * ‖signedSampled S Es v‖ ^ q) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Es _
          rw [mul_left_comm, Finset.mul_sum]
        rw [hL]; congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro S _
        apply Finset.sum_congr rfl; intro Es _
        ring

end W3asm

open scoped BigOperators

/-- Discrete Bernoulli→Rademacher symmetrization / contraction (W3).
For `0 ≤ p ≤ 1`, integer `q`, vectors `v : κ → E` in a normed space:
the `q`-th moment of the *centered* Bernoulli sum is dominated, up to `2^q`,
by the doubly-averaged (over Bernoulli `S` and uniform Rademacher signs `Es`)
`q`-th moment of the *sign-randomized sampled* sum.

`Finset κ` encodes a Bernoulli configuration (membership = the bit being `1`);
`Es : Finset κ` encodes a sign pattern (membership = `+1`, else `-1`);
`wt = p^|S|(1-p)^(N-|S|)` is the product-Bernoulli weight, `rwt = 2^{-N}` the
uniform sign weight.

Source: Ledoux–Talagrand, *Probability in Banach Spaces* (1991), Lemma 6.3;
van der Vaart–Wellner, Lemma 2.3.1; Tropp, arXiv:1506.04711, Fact 3.1.
The convexity (Loève `c_r`) step uses `q ≥ 1`; the `q = 0` case is the trivial
`1 ≤ 1`. The constant is exactly `2^q` (= `2^{q-1}` from `c_r` times `2` from the
`S ↔ S'` ghost-fold). -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : κ → E) :
    (∑ S : Finset κ,
        (p ^ S.card * (1 - p) ^ (Fintype.card κ - S.card))
          * ‖∑ a, ((if a ∈ S then (1:ℝ) else 0) - p) • v a‖ ^ q)
      ≤ 2 ^ q * ∑ S : Finset κ, ∑ Es : Finset κ,
          (p ^ S.card * (1 - p) ^ (Fintype.card κ - S.card))
            * (((1:ℝ)/2) ^ Fintype.card κ)
            * ‖∑ a, ((if a ∈ Es then (1:ℝ) else -1) * (if a ∈ S then (1:ℝ) else 0)) • v a‖ ^ q :=
  W3asm.w3_target q p hp0 hp1 v
