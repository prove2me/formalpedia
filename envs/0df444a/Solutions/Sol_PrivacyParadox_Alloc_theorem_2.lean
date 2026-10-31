-- Prove2me | solution 1 for PrivacyParadox.Alloc.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:36:56.532011+00:00
-- url     : https://prove2.me/submissions/c9dae067-f06d-4f54-891d-c9ede7c73f86

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

open PrivacyParadox.Alloc

namespace PPSolT2

lemma U_sub_A (P : Prog) (A A' p : ℕ → ℝ) :
    P.U A p - P.U A' p = P.gam / (P.s * P.theta ^ 2) *
      ∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k * (1 / A k - 1 / A' k) := by
  have h : ∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k * (1 / A k - 1 / A' k)
      = ∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k / A k
        - ∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k / A' k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h]; unfold Prog.U; ring

lemma U_sub_p (P : Prog) (A p q : ℕ → ℝ) :
    P.U A p - P.U A q = ∑ k ∈ Finset.Icc 1 P.K, P.pr k * (p k - q k) * P.Gk A q k
      - P.gam / (P.s * P.theta ^ 2) / P.theta *
        (∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k - ∑ k ∈ Finset.Icc 1 P.K, P.pr k * q k) ^ 2 := by
  set a := P.gam / (P.s * P.theta ^ 2) with ha
  set Sq := ∑ k ∈ Finset.Icc 1 P.K, P.pr k * q k with hSq
  set Sp := ∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k with hSp
  have h : ∑ k ∈ Finset.Icc 1 P.K, P.pr k * (p k - q k) * P.Gk A q k
      = a * (∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k / A k
          - ∑ k ∈ Finset.Icc 1 P.K, P.pr k * q k / A k)
        - (2 * a / P.theta * Sq + 1 / P.theta * (1 - P.theta) * (1 - P.gam)) * (Sp - Sq) := by
    set C := 2 * a / P.theta * Sq + 1 / P.theta * (1 - P.theta) * (1 - P.gam) with hC
    have h0 : ∑ k ∈ Finset.Icc 1 P.K, P.pr k * (p k - q k) * P.Gk A q k
        = ∑ k ∈ Finset.Icc 1 P.K, (a * (P.pr k * p k / A k - P.pr k * q k / A k)
            - C * (P.pr k * p k - P.pr k * q k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold Prog.Gk
      rw [← hSq, ← ha, hC]
      ring
    rw [h0, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
  rw [h]; unfold Prog.U; rw [← ha, ← hSp, ← hSq]; ring

/-- Saddle-point verification: KKT conditions for both players give minimax optimality. -/
lemma saddle (P : Prog) (hP : P.Standing) (As ps : ℕ → ℝ) (lam : ℝ)
    (hAs : P.FeasA As) (hps : P.AdmP ps) (hlam : 0 ≤ lam)
    (hbud : lam * (∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k * As k + P.l) = lam * (P.B / P.s))
    (hAK : ∀ k ∈ Finset.Icc 1 P.K, lam * P.phi k * As k ^ 2 ≤ ps k ∧
      (As k < 1 → ps k = lam * P.phi k * As k ^ 2))
    (hPK : ∀ k ∈ Finset.Icc 1 P.K, (0 < P.Gk As ps k → ps k = 1) ∧ (P.Gk As ps k < 0 → ps k = 0)) :
    ∀ A : ℕ → ℝ, P.FeasA A → ∀ p : ℕ → ℝ, P.AdmP p → P.U As p ≤ P.U A ps := by
  obtain ⟨hK, hpos, hmono, hsum, hθ, hθ1, hγ, hγ1, hs, hD⟩ := hP
  have ha : 0 ≤ P.gam / (P.s * P.theta ^ 2) := by
    have : (0:ℝ) < P.s := by exact_mod_cast hs
    positivity
  intro A hA p hp
  have h1 : P.U As p ≤ P.U As ps := by
    have := U_sub_p P As p ps
    have hterm : ∑ k ∈ Finset.Icc 1 P.K, P.pr k * (p k - ps k) * P.Gk As ps k ≤ 0 := by
      apply Finset.sum_nonpos
      intro k hk
      have hpr := (hpos k hk).1
      obtain ⟨hp0, hp1⟩ := hp k hk
      rcases lt_trichotomy (P.Gk As ps k) 0 with hG | hG | hG
      · rw [(hPK k hk).2 hG]
        have : 0 ≤ P.pr k * (p k - 0) := by nlinarith
        nlinarith
      · rw [hG]; simp
      · rw [(hPK k hk).1 hG]
        have : P.pr k * (p k - 1) ≤ 0 := by nlinarith
        nlinarith
    have hsq : 0 ≤ P.gam / (P.s * P.theta ^ 2) / P.theta *
        (∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k - ∑ k ∈ Finset.Icc 1 P.K, P.pr k * ps k) ^ 2 := by
      apply mul_nonneg (div_nonneg ha hθ.le) (sq_nonneg _)
    linarith
  have h2 : P.U As ps ≤ P.U A ps := by
    have hd := U_sub_A P A As ps
    have hpt : ∀ k ∈ Finset.Icc 1 P.K,
        lam * (P.pr k * P.phi k * As k - P.pr k * P.phi k * A k)
          ≤ P.pr k * ps k * (1 / A k - 1 / As k) := by
      intro k hk
      have hpr := (hpos k hk).1
      have hph := (hpos k hk).2
      obtain ⟨hA0, hA1⟩ := hA.1 k hk
      obtain ⟨hB0, hB1⟩ := hAs.1 k hk
      obtain ⟨hAK1, hAK2⟩ := hAK k hk
      -- ps(1/A − 1/As) − λφ(As − A) = (ps − λφAs²)(1/A − 1/As) + λφ (As−A)²/A
      have key : ps k * (1 / A k - 1 / As k) - lam * P.phi k * (As k - A k)
          = (ps k - lam * P.phi k * As k ^ 2) * (1 / A k - 1 / As k)
            + lam * P.phi k * (As k - A k) ^ 2 / A k := by
        field_simp; ring
      have hfirst : 0 ≤ (ps k - lam * P.phi k * As k ^ 2) * (1 / A k - 1 / As k) := by
        rcases lt_or_eq_of_le hB1 with hlt | heq
        · rw [hAK2 hlt]; simp
        · apply mul_nonneg (by linarith)
          rw [heq]
          rw [sub_nonneg]
          rw [div_le_div_iff₀ (by norm_num) hA0]; linarith
      have hsecond : 0 ≤ lam * P.phi k * (As k - A k) ^ 2 / A k := by positivity
      have : 0 ≤ ps k * (1 / A k - 1 / As k) - lam * P.phi k * (As k - A k) := by
        rw [key]; linarith
      nlinarith
    have hsum2 : lam * (∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k * As k
        - ∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k * A k)
          ≤ ∑ k ∈ Finset.Icc 1 P.K, P.pr k * ps k * (1 / A k - 1 / As k) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum hpt
    have hnn : 0 ≤ lam * (∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k * As k
        - ∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k * A k) := by
      have := hA.2
      nlinarith
    have : 0 ≤ P.U A ps - P.U As ps := by
      rw [hd]; exact mul_nonneg ha (le_trans hnn hsum2)
    linarith
  linarith

noncomputable def W (P : Prog) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 P.K, P.pr k * min (P.phi k) (Real.sqrt t * Real.sqrt (P.phi k))

noncomputable def S (P : Prog) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 P.K, P.pr k * min 1 (P.phi k / t)

/-- The goal statement, as a proposition. -/
def Goal (P : Prog) : Prop :=
    ∃ Astar : ℕ → ℝ, ∃ χ η φhat : ℝ,
      (∀ k ∈ Finset.Icc 1 P.K,
          (P.phi k ≤ φhat → Astar k = χ) ∧ (φhat < P.phi k → Astar k = η / Real.sqrt (P.phi k))) ∧
      P.FeasA Astar ∧ AntitoneOn Astar (Set.Icc 1 P.K) ∧
      ∀ A : ℕ → ℝ, P.FeasA A → ∀ p : ℕ → ℝ, P.AdmP p →
        ∃ p' : ℕ → ℝ, P.AdmP p' ∧ P.U Astar p ≤ P.U A p'

lemma construct (P : Prog) (hP : P.Standing) (t χ τ : ℝ) (ht : 0 < t) (hχ0 : 0 < χ)
    (hχ1 : χ ≤ 1) (hW : χ * W P t = P.B / P.s - P.l) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hτχ : 0 < τ → χ = 1)
    (hg : 0 ≤ P.gam / (P.s * P.theta ^ 2) * (1 / χ - 2 / P.theta * ((1 - τ) * S P t + τ * P.theta))
        - 1 / P.theta * (1 - P.theta) * (1 - P.gam))
    (hg' : 0 < P.gam / (P.s * P.theta ^ 2) * (1 / χ - 2 / P.theta * ((1 - τ) * S P t + τ * P.theta))
        - 1 / P.theta * (1 - P.theta) * (1 - P.gam) →
        ∀ k ∈ Finset.Icc 1 P.K, P.phi k ≤ t → P.phi k = t) :
    Goal P := by
  have hP' := hP
  obtain ⟨hK, hpos, hmono, hsum, hθ, hθ1, hγ, hγ1, hs, hD⟩ := hP'
  set As : ℕ → ℝ := fun k => if P.phi k ≤ t then χ else χ * Real.sqrt t / Real.sqrt (P.phi k)
    with hAsdef
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  -- pointwise facts
  have hlow : ∀ k, P.phi k ≤ t → As k = χ := fun k h => by simp [hAsdef, h]
  have hhigh : ∀ k, t < P.phi k → As k = χ * Real.sqrt t / Real.sqrt (P.phi k) :=
    fun k h => by simp [hAsdef, not_le.2 h]
  have hAsbd : ∀ k ∈ Finset.Icc 1 P.K, 0 < As k ∧ As k ≤ 1 := by
    intro k hk
    have hph := (hpos k hk).2
    rcases le_or_gt (P.phi k) t with h | h
    · rw [hlow k h]; exact ⟨hχ0, hχ1⟩
    · rw [hhigh k h]
      have hsp : Real.sqrt t < Real.sqrt (P.phi k) := Real.sqrt_lt_sqrt ht.le h
      have hsp0 : 0 < Real.sqrt (P.phi k) := Real.sqrt_pos.2 hph
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hsp0]
      nlinarith
  have hphiA : ∀ k ∈ Finset.Icc 1 P.K,
      P.phi k * As k = χ * min (P.phi k) (Real.sqrt t * Real.sqrt (P.phi k)) := by
    intro k hk
    have hph := (hpos k hk).2
    have hsp0 : 0 < Real.sqrt (P.phi k) := Real.sqrt_pos.2 hph
    have hsq : Real.sqrt (P.phi k) * Real.sqrt (P.phi k) = P.phi k := Real.mul_self_sqrt hph.le
    rcases le_or_gt (P.phi k) t with h | h
    · rw [hlow k h]
      have : Real.sqrt (P.phi k) ≤ Real.sqrt t := Real.sqrt_le_sqrt h
      rw [min_eq_left (by nlinarith)]; ring
    · rw [hhigh k h]
      have : Real.sqrt t < Real.sqrt (P.phi k) := Real.sqrt_lt_sqrt ht.le h
      rw [min_eq_right (by nlinarith)]
      field_simp
      nlinarith
  have hbudget : ∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k * As k + P.l = P.B / P.s := by
    have : ∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k * As k = χ * W P t := by
      unfold W; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mul_assoc, hphiA k hk]; ring
    rw [this, hW]; ring
  have hfeas : P.FeasA As := ⟨hAsbd, le_of_eq hbudget⟩
  refine ⟨As, χ, χ * Real.sqrt t, t, ?_, hfeas, ?_, ?_⟩
  · intro k hk
    exact ⟨hlow k, hhigh k⟩
  · intro i hi j hj hij
    have hi' : i ∈ Finset.Icc 1 P.K := by simpa using hi
    have hj' : j ∈ Finset.Icc 1 P.K := by simpa using hj
    have hphij : P.phi i ≤ P.phi j := hmono.monotoneOn hi hj hij
    have hpi := (hpos i hi').2
    have hpj := (hpos j hj').2
    show As j ≤ As i
    rcases le_or_gt (P.phi j) t with h2 | h2
    · rw [hlow j h2, hlow i (le_trans hphij h2)]
    · rcases le_or_gt (P.phi i) t with h1 | h1
      · rw [hlow i h1, hhigh j h2]
        have : Real.sqrt t < Real.sqrt (P.phi j) := Real.sqrt_lt_sqrt ht.le h2
        have hsp0 : 0 < Real.sqrt (P.phi j) := Real.sqrt_pos.2 hpj
        rw [div_le_iff₀ hsp0]
        nlinarith
      · rw [hhigh i h1, hhigh j h2]
        have hsp0 : 0 < Real.sqrt (P.phi i) := Real.sqrt_pos.2 hpi
        have : Real.sqrt (P.phi i) ≤ Real.sqrt (P.phi j) := Real.sqrt_le_sqrt hphij
        apply div_le_div_of_nonneg_left (by positivity) hsp0 this
  · intro A hA p hp
    set ps : ℕ → ℝ := fun k => (1 - τ) * min 1 (P.phi k / t) + τ with hpsdef
    have hmin : ∀ k ∈ Finset.Icc 1 P.K, 0 ≤ min 1 (P.phi k / t) ∧ min 1 (P.phi k / t) ≤ 1 :=
      fun k hk => ⟨le_min zero_le_one (div_nonneg (hpos k hk).2.le ht.le), min_le_left _ _⟩
    have hps : P.AdmP ps := by
      intro k hk
      obtain ⟨h0, h1⟩ := hmin k hk
      simp only [hpsdef]
      constructor <;> nlinarith
    have hSps : ∑ k ∈ Finset.Icc 1 P.K, P.pr k * ps k = (1 - τ) * S P t + τ * P.theta := by
      unfold S; rw [← hsum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hpsdef]; ring
    have hτ : χ < 1 → τ = 0 := by
      intro h
      rcases lt_or_eq_of_le hτ0 with h' | h'
      · exact absurd (hτχ h') (ne_of_lt h)
      · exact h'.symm
    refine ⟨ps, hps, saddle P hP As ps (1 / (χ ^ 2 * t)) hfeas hps (by positivity)
      (by rw [hbudget]) ?_ ?_ A hA p hp⟩
    · intro k hk
      have hph := (hpos k hk).2
      rcases le_or_gt (P.phi k) t with h | h
      · rw [hlow k h]
        have hm : min 1 (P.phi k / t) = P.phi k / t := min_eq_right ((div_le_one ht).2 h)
        have he : 1 / (χ ^ 2 * t) * P.phi k * χ ^ 2 = P.phi k / t := by
          field_simp
        have hps_k : ps k = (1 - τ) * (P.phi k / t) + τ := by simp only [hpsdef, hm]
        rw [he, hps_k]
        have : P.phi k / t ≤ 1 := (div_le_one ht).2 h
        constructor
        · nlinarith
        · intro hc; rw [hτ hc]; ring
      · rw [hhigh k h]
        have hm : min 1 (P.phi k / t) = 1 := min_eq_left ((one_le_div ht).2 h.le)
        have hps_k : ps k = 1 := by simp only [hpsdef, hm]; ring
        have hsp0 : 0 < Real.sqrt (P.phi k) := Real.sqrt_pos.2 hph
        have he : 1 / (χ ^ 2 * t) * P.phi k * (χ * Real.sqrt t / Real.sqrt (P.phi k)) ^ 2 = 1 := by
          rw [div_pow, mul_pow, Real.sq_sqrt ht.le, Real.sq_sqrt hph.le]
          field_simp
        rw [he, hps_k]
        exact ⟨le_rfl, fun _ => rfl⟩
    · intro k hk
      have hph := (hpos k hk).2
      have hGk : P.Gk As ps k = P.gam / (P.s * P.theta ^ 2) *
          (1 / As k - 2 / P.theta * ((1 - τ) * S P t + τ * P.theta))
            - 1 / P.theta * (1 - P.theta) * (1 - P.gam) := by
        unfold Prog.Gk; rw [hSps]
      rcases le_or_gt (P.phi k) t with h | h
      · rw [hGk, hlow k h]
        refine ⟨fun hc => ?_, fun hc => absurd hc (not_lt.2 hg)⟩
        have he := hg' hc k hk h
        simp only [hpsdef, he, div_self ht.ne', min_self]; ring
      · have hm : min 1 (P.phi k / t) = 1 := min_eq_left ((one_le_div ht).2 h.le)
        have hps_k : ps k = 1 := by simp only [hpsdef, hm]; ring
        refine ⟨fun _ => hps_k, fun hc => ?_⟩
        exfalso
        have hle : 1 / χ ≤ 1 / As k := by
          rw [hhigh k h]
          have : Real.sqrt t < Real.sqrt (P.phi k) := Real.sqrt_lt_sqrt ht.le h
          have hsp0 : 0 < Real.sqrt (P.phi k) := Real.sqrt_pos.2 hph
          rw [one_div_div, div_le_div_iff₀ hχ0 (by positivity)]
          nlinarith
        have ha : 0 ≤ P.gam / (P.s * P.theta ^ 2) := by
          have : (0:ℝ) < P.s := by exact_mod_cast hs
          positivity
        rw [hGk] at hc
        have := mul_le_mul_of_nonneg_left (sub_le_sub_right hle
          (2 / P.theta * ((1 - τ) * S P t + τ * P.theta))) ha
        linarith

noncomputable def g (P : Prog) (t : ℝ) : ℝ :=
  P.gam / (P.s * P.theta ^ 2) * (W P t / (P.B / P.s - P.l) - 2 / P.theta * S P t)
    - 1 / P.theta * (1 - P.theta) * (1 - P.gam)

lemma W_cont (P : Prog) : Continuous (W P) := by
  unfold W; fun_prop

lemma S_contOn (P : Prog) : ContinuousOn (S P) (Set.Ioi 0) := by
  unfold S
  apply continuousOn_finset_sum
  intro k _
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.inf continuousOn_const
  apply ContinuousOn.div continuousOn_const continuousOn_id
  intro x hx; exact ne_of_gt hx

lemma goal_holds (P : Prog) (hP : P.Standing) : Goal P := by
  have hP' := hP
  obtain ⟨hK, hpos, hmono, hsum, hθ, hθ1, hγ, hγ1, hs, hD⟩ := hP'
  set D := P.B / P.s - P.l with hDdef
  set a := P.gam / (P.s * P.theta ^ 2) with hadef
  set e := 1 / P.theta * (1 - P.theta) * (1 - P.gam) with hedef
  set Φ := ∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k with hΦ
  have hsR : (0:ℝ) < P.s := by exact_mod_cast hs
  have ha : 0 < a := by positivity
  have he : 0 ≤ e := by
    have : 0 ≤ 1 - P.theta := by linarith
    have : 0 ≤ 1 - P.gam := by linarith
    positivity
  have hKmem : P.K ∈ Finset.Icc 1 P.K := Finset.mem_Icc.2 ⟨hK, le_rfl⟩
  have h1mem : 1 ∈ Finset.Icc 1 P.K := Finset.mem_Icc.2 ⟨le_rfl, hK⟩
  have hphiK : ∀ k ∈ Finset.Icc 1 P.K, P.phi k ≤ P.phi P.K := by
    intro k hk
    exact hmono.monotoneOn (by simpa using hk) (by simpa using hKmem) (Finset.mem_Icc.1 hk).2
  have hphi1 : ∀ k ∈ Finset.Icc 1 P.K, P.phi 1 ≤ P.phi k := by
    intro k hk
    exact hmono.monotoneOn (by simpa using h1mem) (by simpa using hk) (Finset.mem_Icc.1 hk).1
  have hΦpos : 0 < Φ := by
    apply Finset.sum_pos (fun k hk => mul_pos (hpos k hk).1 (hpos k hk).2) ⟨1, h1mem⟩
  have hconstAnti : ∀ c : ℝ, AntitoneOn (fun _ : ℕ => c) (Set.Icc 1 P.K) :=
    fun c _ _ _ _ _ => le_rfl
  by_cases h0 : Φ + P.l ≤ P.B / P.s
  · -- the budget allows `A ≡ 1`
    refine ⟨fun _ => 1, 1, 0, P.phi P.K, ?_, ?_, hconstAnti 1, ?_⟩
    · intro k hk
      exact ⟨fun _ => rfl, fun h => absurd (hphiK k hk) (not_le.2 h)⟩
    · refine ⟨fun k _ => ⟨one_pos, le_rfl⟩, ?_⟩
      simpa [hΦ] using h0
    · intro A hA p hp
      refine ⟨p, hp, ?_⟩
      have hd := U_sub_A P A (fun _ => 1) p
      have : 0 ≤ ∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k * (1 / A k - 1 / (fun _ : ℕ => (1:ℝ)) k) := by
        apply Finset.sum_nonneg
        intro k hk
        obtain ⟨hA0, hA1⟩ := hA.1 k hk
        have : 1 ≤ 1 / A k := by rw [le_div_iff₀ hA0]; linarith
        have := (hp k hk).1
        have := (hpos k hk).1
        simp only
        apply mul_nonneg (by positivity) (by linarith)
      have := mul_nonneg ha.le this
      rw [← hadef] at hd
      linarith
  have hDΦ : D < Φ := by rw [hDdef]; linarith
  by_cases h1 : a * (Φ / D) - e ≤ 0
  · -- the adversary's best response is `p ≡ 0`
    set χ := D / Φ with hχ
    have hχ0 : 0 < χ := div_pos hD hΦpos
    have hχ1 : χ < 1 := (div_lt_one hΦpos).2 hDΦ
    have hbud : ∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k * χ + P.l = P.B / P.s := by
      rw [← Finset.sum_mul, ← hΦ, hχ, mul_div_cancel₀ _ hΦpos.ne', hDdef]; ring
    have hfeas : P.FeasA (fun _ => χ) := ⟨fun _ _ => ⟨hχ0, hχ1.le⟩, le_of_eq hbud⟩
    refine ⟨fun _ => χ, χ, 0, P.phi P.K, ?_, hfeas, hconstAnti χ, ?_⟩
    · intro k hk
      exact ⟨fun _ => rfl, fun h => absurd (hphiK k hk) (not_le.2 h)⟩
    · intro A hA p hp
      have hadm0 : P.AdmP (fun _ => 0) := fun _ _ => ⟨le_rfl, zero_le_one⟩
      refine ⟨fun _ => 0, hadm0, saddle P hP (fun _ => χ) (fun _ => 0) 0 hfeas hadm0 le_rfl
        (by simp) (fun k _ => ⟨by simp, fun _ => by simp⟩) ?_ A hA p hp⟩
      intro k hk
      have hG : P.Gk (fun _ => χ) (fun _ => 0) k = a * (Φ / D) - e := by
        unfold Prog.Gk
        simp only [mul_zero, Finset.sum_const_zero]
        rw [← hadef, ← hedef, hχ, one_div_div]; ring
      rw [hG]
      exact ⟨fun hc => absurd hc (not_lt.2 h1), fun _ => rfl⟩
  · push_neg at h1
    set M := a * (Φ / D) - e with hM
    set φ1 := P.phi 1 with hφ1
    have hφ1pos : 0 < φ1 := (hpos 1 h1mem).2
    set T := max (P.phi P.K) (2 * a * Φ / (P.theta * M)) with hT
    have hTK : P.phi P.K ≤ T := le_max_left _ _
    have hT2 : 2 * a * Φ / (P.theta * M) ≤ T := le_max_right _ _
    have hφ1T : φ1 ≤ T := le_trans (hphiK 1 h1mem) hTK
    have hTpos : 0 < T := lt_of_lt_of_le hφ1pos hφ1T
    have hWT : W P T = Φ := by
      unfold W
      refine Finset.sum_congr rfl fun k hk => ?_
      have hph := (hpos k hk).2
      have : Real.sqrt (P.phi k) ≤ Real.sqrt T := Real.sqrt_le_sqrt (le_trans (hphiK k hk) hTK)
      have hsq : Real.sqrt (P.phi k) * Real.sqrt (P.phi k) = P.phi k := Real.mul_self_sqrt hph.le
      rw [min_eq_left (by nlinarith [Real.sqrt_nonneg (P.phi k)])]
    have hST : S P T = Φ / T := by
      unfold S
      rw [hΦ, Finset.sum_div]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [min_eq_right ((div_le_one hTpos).2 (le_trans (hphiK k hk) hTK))]
      ring
    have hgT : 0 ≤ g P T := by
      unfold g
      rw [← hadef, ← hedef, ← hDdef, hWT, hST]
      have hθM : 0 < P.theta * M := mul_pos hθ h1
      have : 2 * a * Φ ≤ T * (P.theta * M) := by
        rw [div_le_iff₀ hθM] at hT2; linarith
      have h2 : 2 / P.theta * (Φ / T) * a ≤ M := by
        rw [show 2 / P.theta * (Φ / T) * a = 2 * a * Φ / (P.theta * T) by field_simp]
        rw [div_le_iff₀ (mul_pos hθ hTpos)]; linarith
      nlinarith
    have hWTD : 0 ≤ W P T - D := by rw [hWT]; linarith
    -- the generic instance with `τ = 0`
    have inst0 : ∀ t, 0 < t → 0 ≤ g P t → D ≤ W P t →
        (0 < g P t → ∀ k ∈ Finset.Icc 1 P.K, P.phi k ≤ t → P.phi k = t) → Goal P := by
      intro t ht hg hW hg'
      have hWpos : 0 < W P t := lt_of_lt_of_le hD hW
      have hexp : a * (1 / (D / W P t) - 2 / P.theta * ((1 - 0) * S P t + 0 * P.theta)) - e
          = g P t := by
        unfold g; rw [← hadef, ← hedef, ← hDdef, one_div_div]; ring
      refine construct P hP t (D / W P t) 0 ht (div_pos hD hWpos) ((div_le_one hWpos).2 hW)
        (by rw [div_mul_cancel₀ _ hWpos.ne']) le_rfl zero_le_one (fun h => absurd h (lt_irrefl 0))
        ?_ ?_
      · rw [← hadef, ← hedef, hexp]; exact hg
      · rw [← hadef, ← hedef, hexp]; exact hg'
    set u : ℝ → ℝ := fun t => min (g P t) (W P t - D) with hu
    by_cases hu1 : 0 ≤ u φ1
    · have hg1 : 0 ≤ g P φ1 := le_trans hu1 (min_le_left _ _)
      have hW1 : 0 ≤ W P φ1 - D := le_trans hu1 (min_le_right _ _)
      refine inst0 φ1 hφ1pos hg1 (by linarith) ?_
      intro _ k hk hk'
      exact le_antisymm hk' (hphi1 k hk)
    · push_neg at hu1
      have hcont : ContinuousOn u (Set.Icc φ1 T) := by
        have hsub : Set.Icc φ1 T ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hφ1pos hx.1
        have hW' := (W_cont P).continuousOn (s := Set.Icc φ1 T)
        have hS' := (S_contOn P).mono hsub
        apply ContinuousOn.inf
        · unfold g
          exact (continuousOn_const.mul ((hW'.div_const _).sub (continuousOn_const.mul hS'))).sub
            continuousOn_const
        · exact hW'.sub continuousOn_const
      have huT : 0 ≤ u T := le_min hgT hWTD
      obtain ⟨t, ht, hut⟩ := intermediate_value_Icc hφ1T hcont ⟨hu1.le, huT⟩
      have htpos : 0 < t := lt_of_lt_of_le hφ1pos ht.1
      have hgt : 0 ≤ g P t := by
        have := min_le_left (g P t) (W P t - D); simp only [hu] at hut; linarith
      have hWt : 0 ≤ W P t - D := by
        have := min_le_right (g P t) (W P t - D); simp only [hu] at hut; linarith
      simp only [hu] at hut
      rcases min_choice (g P t) (W P t - D) with hc | hc
      · rw [hc] at hut
        exact inst0 t htpos hgt (by linarith) (fun h => absurd hut (ne_of_gt h))
      · rw [hc] at hut
        have hWD : W P t = D := by linarith
        -- the clipped case `χ = 1`
        have hgt' : g P t = a * (1 - 2 / P.theta * S P t) - e := by
          unfold g; rw [← hadef, ← hedef, ← hDdef, hWD, div_self hD.ne']
        have hXθ : (1 - 2 / P.theta * S P t) * P.theta = P.theta - 2 * S P t := by
          field_simp
        have hgθ : g P t * P.theta = a * (P.theta - 2 * S P t) - e * P.theta := by
          rw [hgt', ← hXθ]; ring
        have hSt : S P t ≤ P.theta / 2 := by
          have h5 : 0 ≤ g P t * P.theta := mul_nonneg hgt hθ.le
          have h6 : 0 ≤ e * P.theta := mul_nonneg he hθ.le
          have h7 : 0 ≤ a * (P.theta - 2 * S P t) := by linarith
          have h8 : 0 ≤ P.theta - 2 * S P t := (mul_nonneg_iff_of_pos_left ha).1 h7
          linarith
        have hden : 0 < 2 * a * (P.theta - S P t) := by
          have : 0 < P.theta - S P t := by linarith
          positivity
        obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = g P t * P.theta / (2 * a * (P.theta - S P t)) := ⟨_, rfl⟩
        have hτ0 : 0 ≤ τ := by rw [hτ]; exact div_nonneg (mul_nonneg hgt hθ.le) hden.le
        have hτ1 : τ ≤ 1 := by
          rw [hτ, div_le_one hden, hgθ]
          have h6 : 0 ≤ e * P.theta := mul_nonneg he hθ.le
          have h9 : 0 < a * P.theta := mul_pos ha hθ
          linarith
        have hτeq : τ * (2 * a * (P.theta - S P t)) = g P t * P.theta := by
          rw [hτ, div_mul_cancel₀ _ hden.ne']
        have hθθ : 2 / P.theta * (τ * P.theta) = 2 * τ := by field_simp
        have hexp : a * (1 / 1 - 2 / P.theta * ((1 - τ) * S P t + τ * P.theta)) - e = 0 := by
          have e1 : a * (1 / 1 - 2 / P.theta * ((1 - τ) * S P t + τ * P.theta)) - e
              = (a * (1 - 2 / P.theta * S P t) - e) - a * (2 / P.theta * (τ * P.theta))
                + a * τ * (2 / P.theta * S P t) := by ring
          rw [e1, ← hgt', hθθ]
          have e2 : g P t = τ * (2 * a * (P.theta - S P t)) / P.theta := by
            rw [hτeq, mul_div_cancel_right₀ _ hθ.ne']
          rw [e2]; field_simp; ring
        refine construct P hP t 1 τ htpos one_pos le_rfl (by rw [one_mul, hWD]) hτ0 hτ1
          (fun _ => rfl) ?_ ?_
        · rw [← hadef, ← hedef, hexp]
        · rw [← hadef, ← hedef, hexp]; intro h; exact absurd h (lt_irrefl 0)

end PPSolT2

theorem solution (P : Prog) (hP : P.Standing) :
    ∃ Astar : ℕ → ℝ, ∃ χ η φhat : ℝ,
      (∀ k ∈ Finset.Icc 1 P.K,
          (P.phi k ≤ φhat → Astar k = χ) ∧ (φhat < P.phi k → Astar k = η / Real.sqrt (P.phi k))) ∧
      P.FeasA Astar ∧ AntitoneOn Astar (Set.Icc 1 P.K) ∧
      ∀ A : ℕ → ℝ, P.FeasA A → ∀ p : ℕ → ℝ, P.AdmP p →
        ∃ p' : ℕ → ℝ, P.AdmP p' ∧ P.U Astar p ≤ P.U A p' :=
  PPSolT2.goal_holds P hP
