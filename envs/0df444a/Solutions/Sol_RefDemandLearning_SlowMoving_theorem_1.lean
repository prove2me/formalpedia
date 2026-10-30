-- Prove2me | solution 1 for RefDemandLearning.SlowMoving.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:41:59.902985+00:00
-- url     : https://prove2.me/submissions/acefa487-9a1a-49bd-83d2-fd41e8633715

import Definitions.Def_RefDemandLearning_SlowMoving_Regret
set_option autoImplicit false
namespace RefDemandLearning.SlowMoving

theorem rd2_step (ζ p r : ℝ) (h0 : 0 ≤ ζ) (hζ : ζ < 1) :
    p * (r - p) ≤ (r ^ 2 - (ζ * r + (1 - ζ) * p) ^ 2) / (2 * (1 - ζ)) := by
  have h1 : 0 < 2 * (1 - ζ) := by linarith
  rw [le_div_iff₀ h1]
  have : (r ^ 2 - (ζ * r + (1 - ζ) * p) ^ 2) - p * (r - p) * (2 * (1 - ζ)) =
      (1 - ζ) * (1 + ζ) * (r - p) ^ 2 := by ring
  have h2 : 0 ≤ (1 - ζ) * (1 + ζ) * (r - p) ^ 2 := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  linarith

theorem rd2_rev (θ : Parameters) (hβ : 0 < θ.beta) (hp1 : 0 ≤ θ.etaPlus)
    (hle : θ.etaPlus ≤ θ.etaMinus) (p r : ℝ) (hp : 0 ≤ p) :
    revenue θ p r ≤ θ.alpha ^ 2 / (4 * θ.beta) + θ.etaPlus * (p * (r - p)) := by
  unfold revenue demand
  have hd : θ.alpha - θ.beta * p + θ.etaPlus * max (r - p) 0 - θ.etaMinus * max (p - r) 0 ≤
      θ.alpha - θ.beta * p + θ.etaPlus * (r - p) := by
    rcases le_total r p with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      nlinarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      nlinarith
  have h1 : p * (θ.alpha - θ.beta * p + θ.etaPlus * max (r - p) 0 - θ.etaMinus * max (p - r) 0) ≤
      p * (θ.alpha - θ.beta * p + θ.etaPlus * (r - p)) := mul_le_mul_of_nonneg_left hd hp
  have h2 : p * (θ.alpha - θ.beta * p) ≤ θ.alpha ^ 2 / (4 * θ.beta) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * θ.beta * p - θ.alpha)]
  nlinarith

theorem rd2_sum (I : PriceInterval) (ρ : Mechanism I) (ζ : ℝ) (h0 : 0 ≤ ζ) (hζ : ζ < 1)
    (hES : ∀ (p : ℕ → Price I) (n : ℕ),
      reference ρ p (n + 1) = ζ * reference ρ p n + (1 - ζ) * (p n : ℝ))
    (θ : Parameters) (hβ : 0 < θ.beta) (hp1 : 0 ≤ θ.etaPlus)
    (hle : θ.etaPlus ≤ θ.etaMinus) (q : ℕ → Price I) (N : ℕ) :
    ∑ n ∈ Finset.range N, revenue θ (q n) (reference ρ q n) ≤
      N * (θ.alpha ^ 2 / (4 * θ.beta)) +
        θ.etaPlus * ((reference ρ q 0 ^ 2 - reference ρ q N ^ 2) / (2 * (1 - ζ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hq : (0 : ℝ) ≤ (q N : ℝ) := le_trans I.nonneg (q N).2.1
    have a1 := rd2_rev θ hβ hp1 hle (q N) (reference ρ q N) hq
    have a2 := rd2_step ζ (q N) (reference ρ q N) h0 hζ
    rw [← hES q N] at a2
    have a3 := mul_le_mul_of_nonneg_left a2 hp1
    push_cast
    have e : θ.etaPlus * ((reference ρ q 0 ^ 2 - reference ρ q N ^ 2) / (2 * (1 - ζ))) +
        θ.etaPlus * ((reference ρ q N ^ 2 - reference ρ q (N + 1) ^ 2) / (2 * (1 - ζ))) =
        θ.etaPlus * ((reference ρ q 0 ^ 2 - reference ρ q (N + 1) ^ 2) / (2 * (1 - ζ))) := by
      ring
    have e2 : ((N : ℝ) + 1) * (θ.alpha ^ 2 / (4 * θ.beta)) =
        (N : ℝ) * (θ.alpha ^ 2 / (4 * θ.beta)) + θ.alpha ^ 2 / (4 * θ.beta) := by ring
    linarith

theorem rd2_const (I : PriceInterval) (ρ : Mechanism I) (ζ : ℝ) (h0 : 0 ≤ ζ)
    (hES : ∀ (p : ℕ → Price I) (n : ℕ),
      reference ρ p (n + 1) = ζ * reference ρ p n + (1 - ζ) * (p n : ℝ))
    (c : Price I) (n : ℕ) :
    |reference ρ (fun _ => c) n - (c : ℝ)| ≤ ζ ^ n * (I.hi - I.lo) := by
  induction n with
  | zero =>
    have h1 : (I.lo : ℝ) ≤ reference ρ (fun _ => c) 0 := (ρ.ref 0 _).2.1
    have h2 : reference ρ (fun _ => c) 0 ≤ I.hi := (ρ.ref 0 _).2.2
    have h3 := c.2.1
    have h4 := c.2.2
    simp only [pow_zero, one_mul]
    rw [abs_le]
    constructor <;> linarith
  | succ k ih =>
    have e1 := hES (fun _ => c) k
    have e3 : reference ρ (fun _ => c) (k + 1) - (c : ℝ) =
        ζ * (reference ρ (fun _ => c) k - (c : ℝ)) := by
      rw [e1]; ring
    rw [e3, abs_mul, abs_of_nonneg h0, pow_succ]
    calc ζ * |reference ρ (fun _ => c) k - (c : ℝ)| ≤ ζ * (ζ ^ k * (I.hi - I.lo)) :=
          mul_le_mul_of_nonneg_left ih h0
      _ = ζ ^ k * ζ * (I.hi - I.lo) := by ring

theorem rd2_bench (B : Bounds) (ρ : Mechanism B.prices) (θ : Parameters) (ζ : ℝ) (h0 : 0 ≤ ζ)
    (hζ : ζ < 1)
    (hES : ∀ (p : ℕ → Price B.prices) (n : ℕ),
      reference ρ p (n + 1) = ζ * reference ρ p n + (1 - ζ) * (p n : ℝ))
    (hβ : 0 < θ.beta) (hp1 : 0 ≤ θ.etaPlus) (hle : θ.etaPlus ≤ θ.etaMinus)
    (c : Price B.prices) (T : ℕ) :
    benchmark B ρ θ T ≤ T * (θ.alpha ^ 2 / (4 * θ.beta)) +
      θ.etaPlus * (B.prices.hi ^ 2 / (2 * (1 - ζ))) := by
  unfold benchmark
  haveI : Nonempty (Fin T → Price B.prices) := ⟨fun _ => c⟩
  apply ciSup_le
  intro P
  let q : ℕ → Price B.prices := fun n => if h : n < T then P ⟨n, h⟩ else c
  have hqP : ∀ j : Fin T, q j.val = P j := fun j => by simp [q, j.isLt]
  have href : ∀ j : Fin T, ρ.ref j.val (fun k => P ⟨k.val, lt_trans k.isLt j.isLt⟩) =
      reference ρ q j.val := by
    intro j
    unfold reference
    have hf : (fun k : Fin j.val => P ⟨k.val, lt_trans k.isLt j.isLt⟩) = fun k => q k.val := by
      funext k
      simp [q, lt_trans k.isLt j.isLt]
    rw [hf]
  have hsum : ∑ j : Fin T, revenue θ (P j)
      (ρ.ref j.val (fun k => P ⟨k.val, lt_trans k.isLt j.isLt⟩)) =
      ∑ n ∈ Finset.range T, revenue θ (q n) (reference ρ q n) := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => revenue θ (q n) (reference ρ q n)) T]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [href j, hqP j]
  rw [hsum]
  have h1 := rd2_sum B.prices ρ ζ h0 hζ hES θ hβ hp1 hle q T
  have hr0a : (B.prices.lo : ℝ) ≤ reference ρ q 0 := (ρ.ref 0 _).2.1
  have hr0b : reference ρ q 0 ≤ B.prices.hi := (ρ.ref 0 _).2.2
  have hlo := B.prices.nonneg
  have hd : 0 < 2 * (1 - ζ) := by linarith
  have h2 : (reference ρ q 0 ^ 2 - reference ρ q T ^ 2) / (2 * (1 - ζ)) ≤
      B.prices.hi ^ 2 / (2 * (1 - ζ)) := by
    apply div_le_div_of_nonneg_right _ hd.le
    nlinarith [sq_nonneg (reference ρ q T)]
  have h3 := mul_le_mul_of_nonneg_left h2 hp1
  linarith

theorem rd2_fixed (B : Bounds) (ρ : Mechanism B.prices) (θ : Parameters) (ζ : ℝ) (h0 : 0 ≤ ζ)
    (hζ : ζ < 1)
    (hES : ∀ (p : ℕ → Price B.prices) (n : ℕ),
      reference ρ p (n + 1) = ζ * reference ρ p n + (1 - ζ) * (p n : ℝ))
    (hβ : 0 < θ.beta) (hp1 : 0 ≤ θ.etaPlus) (hle : θ.etaPlus ≤ θ.etaMinus)
    (hlo : B.prices.lo < optimalBasePrice θ) (hhi : optimalBasePrice θ < B.prices.hi) (T : ℕ) :
    (T : ℝ) * (θ.alpha ^ 2 / (4 * θ.beta)) -
      optimalBasePrice θ * θ.etaMinus * ((B.prices.hi - B.prices.lo) / (1 - ζ)) ≤
      fixedRevenue B ρ θ (optimalBasePrice θ) T := by
  have hl0 := B.prices.nonneg
  have hps : 0 ≤ optimalBasePrice θ := by linarith
  let c : Price B.prices := ⟨optimalBasePrice θ, hlo.le, hhi.le⟩
  have hc : clipPrice B.prices (optimalBasePrice θ) = c := by
    apply Subtype.ext
    show max B.prices.lo (min (optimalBasePrice θ) B.prices.hi) = optimalBasePrice θ
    rw [min_eq_left hhi.le, max_eq_right hlo.le]
  have hRs : optimalBasePrice θ * (θ.alpha - θ.beta * optimalBasePrice θ) =
      θ.alpha ^ 2 / (4 * θ.beta) := by
    unfold optimalBasePrice
    field_simp
    ring
  have hη : 0 ≤ θ.etaMinus := le_trans hp1 hle
  have hterm : ∀ n : ℕ, θ.alpha ^ 2 / (4 * θ.beta) -
      optimalBasePrice θ * θ.etaMinus * (ζ ^ n * (B.prices.hi - B.prices.lo)) ≤
      revenue θ (optimalBasePrice θ) (reference ρ (fun _ => clipPrice B.prices (optimalBasePrice θ)) n) := by
    intro n
    rw [hc]
    have he := rd2_const B.prices ρ ζ h0 hES c n
    have hcc : (c : ℝ) = optimalBasePrice θ := rfl
    rw [hcc] at he
    set f := reference ρ (fun _ => c) n with hf
    unfold revenue demand
    have hm : θ.etaMinus * max (optimalBasePrice θ - f) 0 ≤ θ.etaMinus * (ζ ^ n * (B.prices.hi - B.prices.lo)) := by
      apply mul_le_mul_of_nonneg_left _ hη
      refine le_trans ?_ he
      rcases le_total f (optimalBasePrice θ) with h | h
      · rw [max_eq_left (by linarith)]
        rw [abs_sub_comm]
        exact le_abs_self _
      · rw [max_eq_right (by linarith)]
        exact abs_nonneg _
    have hm2 : 0 ≤ θ.etaPlus * max (f - optimalBasePrice θ) 0 := mul_nonneg hp1 (le_max_right _ _)
    have hm3 : θ.etaMinus * max (optimalBasePrice θ - f) 0 ≤ θ.etaMinus * (ζ ^ n * (B.prices.hi - B.prices.lo)) := hm
    have key : optimalBasePrice θ * (θ.alpha - θ.beta * optimalBasePrice θ +
        θ.etaPlus * max (f - optimalBasePrice θ) 0 - θ.etaMinus * max (optimalBasePrice θ - f) 0) ≥
        optimalBasePrice θ * (θ.alpha - θ.beta * optimalBasePrice θ) -
          optimalBasePrice θ * (θ.etaMinus * (ζ ^ n * (B.prices.hi - B.prices.lo))) := by
      have := mul_le_mul_of_nonneg_left (show
        θ.alpha - θ.beta * optimalBasePrice θ - θ.etaMinus * (ζ ^ n * (B.prices.hi - B.prices.lo)) ≤
        θ.alpha - θ.beta * optimalBasePrice θ +
          θ.etaPlus * max (f - optimalBasePrice θ) 0 - θ.etaMinus * max (optimalBasePrice θ - f) 0 by
        linarith) hps
      linarith
    linarith
  have hgeo : ∑ n ∈ Finset.range T, ζ ^ n * (B.prices.hi - B.prices.lo) ≤
      (B.prices.hi - B.prices.lo) / (1 - ζ) := by
    have hw : 0 < B.prices.hi - B.prices.lo := sub_pos.2 B.prices.lt
    have h1z : 0 < 1 - ζ := sub_pos.2 hζ
    rw [← Finset.sum_mul]
    have hg : (∑ k ∈ Finset.range T, ζ ^ k) * (1 - ζ) = 1 - ζ ^ T := by
      rw [mul_comm]; exact mul_neg_geom_sum ζ T
    have hz : 0 ≤ ζ ^ T := pow_nonneg h0 _
    have : ∑ k ∈ Finset.range T, ζ ^ k ≤ 1 / (1 - ζ) := by
      rw [le_div_iff₀ h1z]; linarith
    calc (∑ k ∈ Finset.range T, ζ ^ k) * (B.prices.hi - B.prices.lo) ≤
          (1 / (1 - ζ)) * (B.prices.hi - B.prices.lo) :=
          mul_le_mul_of_nonneg_right this hw.le
      _ = (B.prices.hi - B.prices.lo) / (1 - ζ) := by ring
  unfold fixedRevenue
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range T) => hterm n)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hk := mul_le_mul_of_nonneg_left hgeo (mul_nonneg hps hη)
  linarith

end RefDemandLearning.SlowMoving

open RefDemandLearning.SlowMoving

theorem solution (B : Bounds) (hB : Standing B) (ρ : Mechanism B.prices)
    (hρ : IsES ρ) (θ : Parameters) (hθ : InTheta B θ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ T : ℕ, 1 ≤ T →
      fixedRegret B ρ θ (optimalBasePrice θ) T ≤ c₁ := by
  obtain ⟨ζ, h0, h1, hES⟩ := hρ
  have hθ' := hθ
  obtain ⟨hal, hβ', hpl', hmi, hle⟩ := hθ
  have hall := hB.2.2.2.2.2.2.2.2.2
  obtain ⟨hb0, -⟩ := hB.2.2
  have hpl := hB.2.2.2.2.1
  have hβ : 0 < θ.beta := lt_of_lt_of_le hb0 hβ'.1
  have hp1 : 0 ≤ θ.etaPlus := le_trans hpl hpl'.1
  obtain ⟨-, hlo, hhi⟩ := hall θ hθ'
  have hlo0 := B.prices.nonneg
  have hps : 0 ≤ optimalBasePrice θ := le_of_lt (lt_of_le_of_lt hlo0 hlo)
  have hη : 0 ≤ θ.etaMinus := le_trans hp1 hle
  have hd : 0 < 1 - ζ := by linarith
  have hhi0 : 0 ≤ B.prices.hi := by linarith
  have hw : 0 ≤ B.prices.hi - B.prices.lo := by linarith
  let c : Price B.prices := ⟨optimalBasePrice θ, hlo.le, hhi.le⟩
  refine ⟨θ.etaPlus * (B.prices.hi ^ 2 / (2 * (1 - ζ))) +
    optimalBasePrice θ * θ.etaMinus * ((B.prices.hi - B.prices.lo) / (1 - ζ)) + 1, ?_, ?_⟩
  · have a1 : 0 ≤ θ.etaPlus * (B.prices.hi ^ 2 / (2 * (1 - ζ))) :=
      mul_nonneg hp1 (div_nonneg (sq_nonneg _) (by linarith))
    have a2 : 0 ≤ optimalBasePrice θ * θ.etaMinus * ((B.prices.hi - B.prices.lo) / (1 - ζ)) :=
      mul_nonneg (mul_nonneg hps hη) (div_nonneg hw hd.le)
    linarith
  · intro T _
    have b1 := rd2_bench B ρ θ ζ h0 h1 hES hβ hp1 hle c T
    have b2 := rd2_fixed B ρ θ ζ h0 h1 hES hβ hp1 hle hlo hhi T
    unfold fixedRegret
    linarith
