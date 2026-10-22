-- Prove2me | solution 1 for TwoSidedExp.DemandLimit.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T04:21:34.172105+00:00
-- url     : https://prove2.me/submissions/d6e9f286-b85e-490a-afc7-39e4e71574b1

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

set_option linter.unusedSectionVars false
open Filter Topology MeasureTheory


namespace DLSolB

variable {Γ Θ : Type} [Fintype Γ] [Fintype Θ] [DecidableEq Γ] [DecidableEq Θ]

/-- the per-customer-type bias function -/
noncomputable def hf (aL e A x : ℝ) : ℝ :=
  (x - A) / (e + (1 - aL) * A + aL * x) - x / (e + x) + A / (e + A)

noncomputable def Bf (c : Γ → Θ → ℝ) (γ : Γ) (w : Γ → Θ → ℝ) : ℝ := ∑ θ, c γ θ * w γ θ

noncomputable def Fsum (aL : ℝ) (φ e A : Γ → ℝ) (c : Γ → Θ → ℝ) (w : Γ → Θ → ℝ) : ℝ :=
  ∑ γ, φ γ * hf aL (e γ) (A γ) (Bf c γ w)

lemma quad_of_zero (aL φ0 e A K X : ℝ) (haL0 : 0 < aL) (haL1 : aL < 1) (he : 0 < e) (hA : 0 < A)
    (hX : 0 < X) (h : φ0 * hf aL e A X + K = 0) :
    let k := φ0 * A / (e + A) + K
    let d0 := e + (1 - aL) * A
    (φ0 * (1 - aL) + k * aL) * X ^ 2 + (φ0 * (e - A - d0) + k * (d0 + aL * e)) * X
      + (-φ0 * A * e + k * d0 * e) = 0 := by
  intro k d0
  have hD : 0 < e + (1 - aL) * A + aL * X := by nlinarith
  have hE : 0 < e + X := by linarith
  have hEA : 0 < e + A := by linarith
  unfold hf at h
  have key : (φ0 * ((X - A) / (e + (1 - aL) * A + aL * X) - X / (e + X) + A / (e + A)) + K)
      * ((e + (1 - aL) * A + aL * X) * (e + X)) = 0 := by rw [h]; ring
  rw [← key]
  simp only [k, d0]
  field_simp
  ring

lemma not_both_zero (aL φ0 e A k : ℝ) (haL0 : 0 < aL) (haL1 : aL < 1) (he : 0 < e) (hA : 0 < A)
    (hφ : 0 < φ0) (h2 : φ0 * (1 - aL) + k * aL = 0)
    (h0 : -φ0 * A * e + k * (e + (1 - aL) * A) * e = 0) : False := by
  have h0' : k * (e + (1 - aL) * A) = φ0 * A := by
    have : (k * (e + (1 - aL) * A) - φ0 * A) * e = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hd : 0 < e + (1 - aL) * A := by nlinarith
  have : (φ0 * (1 - aL) + k * aL) * (e + (1 - aL) * A) = 0 := by rw [h2]; ring
  have e2 : (φ0 * (1 - aL) + k * aL) * (e + (1 - aL) * A)
      = φ0 * (1 - aL) * (e + (1 - aL) * A) + aL * (φ0 * A) := by rw [← h0']; ring
  have : 0 < φ0 * (1 - aL) * (e + (1 - aL) * A) + aL * (φ0 * A) := by
    have : 0 < 1 - aL := by linarith
    positivity
  linarith

lemma roots_sum (a2 a1 a0 r1 r2 : ℝ) (hne : r1 ≠ r2) (h1 : a2 * r1 ^ 2 + a1 * r1 + a0 = 0)
    (h2 : a2 * r2 ^ 2 + a1 * r2 + a0 = 0) : (2 * a2 * r1 + a1) + (2 * a2 * r2 + a1) = 0 := by
  have : (r1 - r2) * (a2 * (r1 + r2) + a1) = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · linear_combination 2 * h


section Null
variable (aL : ℝ) (φ e A : Γ → ℝ) (c : Γ → Θ → ℝ) (γ0 : Γ) (θ0 : Θ)

noncomputable def Kf (w : Γ → Θ → ℝ) : ℝ :=
  ∑ γ ∈ Finset.univ.erase γ0, φ γ * hf aL (e γ) (A γ) (Bf c γ w)

noncomputable def kf (w : Γ → Θ → ℝ) : ℝ := φ γ0 * A γ0 / (e γ0 + A γ0) + Kf aL φ e A c γ0 w

noncomputable def a2f (w : Γ → Θ → ℝ) : ℝ := φ γ0 * (1 - aL) + kf aL φ e A c γ0 w * aL
noncomputable def a1f (w : Γ → Θ → ℝ) : ℝ :=
  φ γ0 * (e γ0 - A γ0 - (e γ0 + (1 - aL) * A γ0))
    + kf aL φ e A c γ0 w * ((e γ0 + (1 - aL) * A γ0) + aL * e γ0)
noncomputable def a0f (w : Γ → Θ → ℝ) : ℝ :=
  -φ γ0 * A γ0 * e γ0 + kf aL φ e A c γ0 w * (e γ0 + (1 - aL) * A γ0) * e γ0

noncomputable def Pf (w : Γ → Θ → ℝ) : ℝ :=
  a2f aL φ e A c γ0 w * Bf c γ0 w ^ 2 + a1f aL φ e A c γ0 w * Bf c γ0 w + a0f aL φ e A c γ0 w

noncomputable def Df (w : Γ → Θ → ℝ) : ℝ :=
  2 * a2f aL φ e A c γ0 w * Bf c γ0 w + a1f aL φ e A c γ0 w

def Sset (σ : ℝ → Prop) : Set (Γ → Θ → ℝ) :=
  {w | (∀ γ θ, 0 < w γ θ) ∧ Pf aL φ e A c γ0 w = 0 ∧ σ (Df aL φ e A c γ0 w)}

def Ev : Γ → Θ → ℝ := fun γ θ => if γ = γ0 ∧ θ = θ0 then 1 else 0

lemma Bf_line (w : Γ → Θ → ℝ) (t : ℝ) (γ : Γ) :
    Bf c γ (w + t • Ev γ0 θ0) = Bf c γ w + if γ = γ0 then t * c γ0 θ0 else 0 := by
  unfold Bf Ev
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  by_cases h : γ = γ0
  · subst h; simp [mul_ite, mul_comm]
  · simp [h]

lemma Kf_line (w : Γ → Θ → ℝ) (t : ℝ) :
    Kf aL φ e A c γ0 (w + t • Ev γ0 θ0) = Kf aL φ e A c γ0 w := by
  unfold Kf
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [Bf_line c γ0 θ0 w t γ, if_neg (Finset.ne_of_mem_erase hγ), add_zero]

lemma Bf_meas (γ : Γ) : Measurable (fun w : Γ → Θ → ℝ => Bf c γ w) := by
  unfold Bf; fun_prop

lemma Kf_meas : Measurable (fun w : Γ → Θ → ℝ => Kf aL φ e A c γ0 w) := by
  unfold Kf hf
  have := Bf_meas c
  fun_prop

lemma Sset_meas (σ : ℝ → Prop) (hσ : MeasurableSet {x | σ x}) :
    MeasurableSet (Sset aL φ e A c γ0 σ) := by
  have hK := Kf_meas aL φ e A c γ0
  have hB := Bf_meas c γ0
  have hP : Measurable (fun w : Γ → Θ → ℝ => Pf aL φ e A c γ0 w) := by
    unfold Pf a2f a1f a0f kf; fun_prop
  have hD : Measurable (fun w : Γ → Θ → ℝ => Df aL φ e A c γ0 w) := by
    unfold Df a2f a1f kf; fun_prop
  have hpos : MeasurableSet {w : Γ → Θ → ℝ | ∀ γ θ, 0 < w γ θ} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun γ => MeasurableSet.iInter fun θ =>
      measurableSet_lt measurable_const (by fun_prop)
  exact hpos.inter ((measurableSet_eq_fun hP measurable_const).inter (hD hσ))

lemma Sset_null (σ : ℝ → Prop) (hσm : MeasurableSet {x | σ x})
    (hσ : ∀ a2 a1 a0 r1 r2 : ℝ, r1 ≠ r2 → a2 * r1 ^ 2 + a1 * r1 + a0 = 0 →
      a2 * r2 ^ 2 + a1 * r2 + a0 = 0 → σ (2 * a2 * r1 + a1) → σ (2 * a2 * r2 + a1) →
      a2 = 0 ∧ a0 = 0)
    (haL0 : 0 < aL) (haL1 : aL < 1) (he : 0 < e γ0) (hA : 0 < A γ0) (hφ : 0 < φ γ0)
    (hc : c γ0 θ0 ≠ 0) :
    (volume : Measure (Γ → Θ → ℝ)) (Sset aL φ e A c γ0 σ) = 0 := by
  have : (volume : Measure (Γ → Θ → ℝ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Γ => (volume : Measure (Θ → ℝ)))
  let u : ℕ → Γ → Θ → ℝ := fun n => (1 / ((n : ℝ) + 1)) • Ev γ0 θ0
  apply Measure.addHaar_eq_zero_of_disjoint_translates volume u
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨‖Ev γ0 θ0‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    simp only [u, norm_smul]
    have h1 : ‖(1 / ((n : ℝ) + 1))‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    calc ‖(1 / ((n : ℝ) + 1))‖ * ‖Ev γ0 θ0‖ ≤ 1 * ‖Ev γ0 θ0‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = _ := one_mul _
  · intro n m hnm
    simp only [Function.onFun, Set.singleton_add, Set.disjoint_left, Set.mem_image]
    rintro y ⟨w1, hw1, rfl⟩ ⟨w2, hw2, hw⟩
    -- w2 = w1 + t • Ev
    set t : ℝ := 1 / ((n : ℝ) + 1) - 1 / ((m : ℝ) + 1) with ht
    have hw2' : w2 = w1 + t • Ev γ0 θ0 := by
      have : w2 = u n + w1 - u m := by rw [← hw]; abel
      rw [this]; simp only [u, ht, sub_smul]; abel
    have htne : t ≠ 0 := by
      rw [ht, sub_ne_zero]
      intro h
      apply hnm
      have : ((n : ℝ) + 1) = (m : ℝ) + 1 := by
        field_simp at h; linarith
      exact_mod_cast (by linarith : (n : ℝ) = m)
    have hK : kf aL φ e A c γ0 w2 = kf aL φ e A c γ0 w1 := by
      unfold kf; rw [hw2', Kf_line]
    have hX : Bf c γ0 w2 = Bf c γ0 w1 + t * c γ0 θ0 := by
      rw [hw2', Bf_line, if_pos rfl]
    have hne : Bf c γ0 w1 ≠ Bf c γ0 w2 := by
      rw [hX]; intro h; exact mul_ne_zero htne hc (by linarith)
    obtain ⟨_, hP1, hσ1⟩ := hw1
    obtain ⟨_, hP2, hσ2⟩ := hw2
    unfold Pf a2f a1f a0f at hP1 hP2
    unfold Df a2f a1f at hσ1 hσ2
    rw [hK] at hP2 hσ2
    obtain ⟨h2, h0⟩ := hσ _ _ _ _ _ hne hP1 hP2 hσ1 hσ2
    exact not_both_zero aL (φ γ0) (e γ0) (A γ0) _ haL0 haL1 he hA hφ h2 h0
  · exact Sset_meas aL φ e A c γ0 σ hσm

end Null


lemma Fsum_null [Nonempty Γ] [Nonempty Θ] (aL : ℝ) (φ e A : Γ → ℝ) (c : Γ → Θ → ℝ)
    (haL0 : 0 < aL) (haL1 : aL < 1) (hφ : ∀ γ, 0 < φ γ) (he : ∀ γ, 0 < e γ) (hA : ∀ γ, 0 < A γ)
    (hc : ∀ γ θ, 0 < c γ θ) :
    (volume : Measure (Γ → Θ → ℝ)) {w | (∀ γ θ, 0 < w γ θ) ∧ Fsum aL φ e A c w = 0} = 0 := by
  obtain ⟨γ0⟩ := ‹Nonempty Γ›
  obtain ⟨θ0⟩ := ‹Nonempty Θ›
  have hsub : {w : Γ → Θ → ℝ | (∀ γ θ, 0 < w γ θ) ∧ Fsum aL φ e A c w = 0} ⊆
      (Sset aL φ e A c γ0 (fun x => 0 < x) ∪ Sset aL φ e A c γ0 (fun x => x < 0)) ∪
        Sset aL φ e A c γ0 (fun x => x = 0) := by
    rintro w ⟨hpos, hF⟩
    have hX : 0 < Bf c γ0 w := by
      unfold Bf
      exact Finset.sum_pos (fun θ _ => mul_pos (hc γ0 θ) (hpos γ0 θ)) Finset.univ_nonempty
    have hsplit : Fsum aL φ e A c w = φ γ0 * hf aL (e γ0) (A γ0) (Bf c γ0 w) + Kf aL φ e A c γ0 w := by
      unfold Fsum Kf
      rw [Finset.add_sum_erase _ (fun γ => φ γ * hf aL (e γ) (A γ) (Bf c γ w)) (Finset.mem_univ γ0)]
    rw [hsplit] at hF
    have hP : Pf aL φ e A c γ0 w = 0 := by
      have := quad_of_zero aL (φ γ0) (e γ0) (A γ0) (Kf aL φ e A c γ0 w) (Bf c γ0 w) haL0 haL1
        (he γ0) (hA γ0) hX hF
      unfold Pf a2f a1f a0f kf
      simpa using this
    rcases lt_trichotomy 0 (Df aL φ e A c γ0 w) with h | h | h
    · exact Or.inl (Or.inl ⟨hpos, hP, h⟩)
    · exact Or.inr ⟨hpos, hP, h.symm⟩
    · exact Or.inl (Or.inr ⟨hpos, hP, h⟩)
  refine measure_mono_null hsub (measure_union_null (measure_union_null ?_ ?_) ?_)
  · apply Sset_null aL φ e A c γ0 θ0 _ (measurableSet_lt measurable_const measurable_id)
      _ haL0 haL1 (he γ0) (hA γ0) (hφ γ0) (hc γ0 θ0).ne'
    intro a2 a1 a0 r1 r2 hne h1 h2 s1 s2
    simp only [id_eq] at s1 s2
    have := roots_sum a2 a1 a0 r1 r2 hne h1 h2
    exfalso; linarith
  · apply Sset_null aL φ e A c γ0 θ0 _ (measurableSet_lt measurable_id measurable_const)
      _ haL0 haL1 (he γ0) (hA γ0) (hφ γ0) (hc γ0 θ0).ne'
    intro a2 a1 a0 r1 r2 hne h1 h2 s1 s2
    simp only [id_eq] at s1 s2
    have := roots_sum a2 a1 a0 r1 r2 hne h1 h2
    exfalso; linarith
  · apply Sset_null aL φ e A c γ0 θ0 _ (measurableSet_eq_fun measurable_id measurable_const)
      _ haL0 haL1 (he γ0) (hA γ0) (hφ γ0) (hc γ0 θ0).ne'
    intro a2 a1 a0 r1 r2 hne h1 h2 s1 s2
    simp only [id_eq] at s1 s2
    have ha2 : a2 = 0 := by
      have : 2 * a2 * (r1 - r2) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd (sub_eq_zero.1 h) hne
    have ha1 : a1 = 0 := by rw [ha2] at s1; linarith
    refine ⟨ha2, ?_⟩
    rw [ha2, ha1] at h1; linarith

end DLSolB


namespace DLSol
open TwoSidedExp.DemandLimit

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- Hypotheses on a mean-field system used in the demand-limit argument. -/
structure Good (S : MFSystem ι κ) : Prop where
  phi_nn : ∀ q, 0 ≤ S.φ q
  av_nn : ∀ q p, 0 ≤ S.α q p * S.v q p
  eps_pos : ∀ q, 0 < S.eps q
  nu_pos : ∀ p, 0 < S.ν p

lemma choice_nn_le_one (S : MFSystem ι κ) (hS : Good S) (s : κ → ℝ) (hs : ∀ p, 0 ≤ s p)
    (q : ι) (p : κ) : 0 ≤ S.choice q p s ∧ S.choice q p s ≤ 1 := by
  unfold MFSystem.choice
  have hterm : ∀ p', 0 ≤ S.α q p' * S.v q p' * s p' := fun p' => mul_nonneg (hS.av_nn q p') (hs p')
  have hle : S.α q p * S.v q p * s p ≤ ∑ p', S.α q p' * S.v q p' * s p' :=
    Finset.single_le_sum (f := fun p' => S.α q p' * S.v q p' * s p') (fun p' _ => hterm p')
      (Finset.mem_univ p)
  have hsum : 0 ≤ ∑ p', S.α q p' * S.v q p' * s p' := Finset.sum_nonneg (fun p' _ => hterm p')
  have hden : 0 < S.eps q + ∑ p', S.α q p' * S.v q p' * s p' := by linarith [hS.eps_pos q]
  refine ⟨div_nonneg (hterm p) hden.le, ?_⟩
  rw [div_le_one hden]; linarith [hS.eps_pos q]

lemma steady_tendsto (S : MFSystem ι κ) (hS : Good S) (lam tau : ℕ → ℝ) (hl : ∀ n, 0 < lam n)
    (ht : ∀ n, 0 < tau n) (hlim : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → κ → ℝ) (hs : ∀ n, S.IsSteady (lam n) (tau n) (s n)) (p : κ) :
    Tendsto (fun n => s n p) atTop (𝓝 (S.ρ p)) := by
  set c : ℝ := (∑ q, S.φ q) / S.ν p
  have hbound : ∀ n, 0 ≤ S.ρ p - s n p ∧ S.ρ p - s n p ≤ lam n / tau n * c := by
    intro n
    obtain ⟨hin, heq⟩ := hs n
    have h0 : ∀ p', 0 ≤ s n p' := fun p' => (hin p').1
    refine ⟨by linarith [(hin p).2], ?_⟩
    have hsum : ∑ q, S.φ q * S.choice q p (s n) ≤ ∑ q, S.φ q := by
      apply Finset.sum_le_sum; intro q _
      have := (choice_nn_le_one S hS (s n) h0 q p).2
      nlinarith [hS.phi_nn q]
    have e := heq p
    have hν := hS.nu_pos p
    have htn := ht n
    have hln := hl n
    have key : (S.ρ p - s n p) * (tau n * S.ν p) ≤ lam n * ∑ q, S.φ q := by
      rw [e]; exact mul_le_mul_of_nonneg_left hsum hln.le
    have : lam n / tau n * c = (lam n * ∑ q, S.φ q) / (tau n * S.ν p) := by
      simp only [c]; field_simp
    rw [this, le_div_iff₀ (by positivity)]
    exact key
  have hup : Tendsto (fun n => lam n / tau n * c) atTop (𝓝 0) := by
    simpa using hlim.mul_const c
  have hd : Tendsto (fun n => S.ρ p - s n p) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (hbound n).1) (fun n => (hbound n).2)
  have : Tendsto (fun n => S.ρ p - (S.ρ p - s n p)) atTop (𝓝 (S.ρ p - 0)) :=
    tendsto_const_nhds.sub hd
  simpa using this

lemma choice_tendsto (S : MFSystem ι κ) (s : ℕ → κ → ℝ) (s0 : κ → ℝ)
    (h : ∀ p, Tendsto (fun n => s n p) atTop (𝓝 (s0 p))) (q : ι) (p : κ)
    (hden : S.eps q + ∑ p', S.α q p' * S.v q p' * s0 p' ≠ 0) :
    Tendsto (fun n => S.choice q p (s n)) atTop (𝓝 (S.choice q p s0)) := by
  unfold MFSystem.choice
  apply Tendsto.div _ _ hden
  · exact (h p).const_mul _
  · exact tendsto_const_nhds.add (tendsto_finsetSum _ (fun p' _ => (h p').const_mul _))

/-- The limit of `Σ_p Σ_q φ_q choice(q,p)` along steady states as `λ/τ → 0`. -/
lemma sum_choice_tendsto (S : MFSystem ι κ) (hS : Good S) (hρ : ∀ p, 0 ≤ S.ρ p)
    (lam tau : ℕ → ℝ) (hl : ∀ n, 0 < lam n)
    (ht : ∀ n, 0 < tau n) (hlim : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → κ → ℝ) (hs : ∀ n, S.IsSteady (lam n) (tau n) (s n))
    {β γ' : Type} [Fintype β] [Fintype γ'] (P : β → κ) (Qf : γ' → ι) :
    Tendsto (fun n => ∑ b, ∑ g, S.φ (Qf g) * S.choice (Qf g) (P b) (s n)) atTop
      (𝓝 (∑ b, ∑ g, S.φ (Qf g) * S.choice (Qf g) (P b) S.ρ)) := by
  have hconv := steady_tendsto S hS lam tau hl ht hlim s hs
  apply tendsto_finsetSum _ (fun b _ => tendsto_finsetSum _ (fun g _ => ?_))
  apply Tendsto.const_mul
  apply choice_tendsto S s S.ρ hconv
  have : 0 ≤ ∑ p', S.α (Qf g) p' * S.v (Qf g) p' * S.ρ p' :=
    Finset.sum_nonneg (fun p' _ => mul_nonneg (hS.av_nn _ p') (hρ p'))
  have := hS.eps_pos (Qf g)
  positivity


namespace Model
variable {Γ Θ : Type} [Fintype Γ] [Fintype Θ]

lemma good_expt (M : Model Γ Θ) (hM : M.Standing) (aC aL : ℝ) (h0 : 0 ≤ aC) (h1 : aC ≤ 1) :
    Good (M.expt aC aL) where
  phi_nn q := by
    unfold Model.expt; dsimp only
    split_ifs
    · exact mul_nonneg h0 (hM.phi_pos _).le
    · exact mul_nonneg (by linarith) (hM.phi_pos _).le
  av_nn q p := by
    unfold Model.expt; dsimp only
    split_ifs
    · exact mul_nonneg (hM.alphat_pos _ _).le (hM.vt_pos _ _).le
    · exact mul_nonneg (hM.alpha_pos _ _).le (hM.v_pos _ _).le
  eps_pos q := hM.eps_pos _
  nu_pos p := hM.nu_pos _

lemma rho_nn (M : Model Γ Θ) (hM : M.Standing) (aC aL : ℝ) (h0 : 0 ≤ aL) (h1 : aL ≤ 1) :
    ∀ p, 0 ≤ (M.expt aC aL).ρ p := by
  intro p
  show 0 ≤ M.rhoL aL p
  unfold Model.rhoL
  split_ifs
  · exact mul_nonneg h0 (hM.rho_pos _).le
  · exact mul_nonneg (by linarith) (hM.rho_pos _).le

lemma Q_tendsto (M : Model Γ Θ) (hM : M.Standing) (aC aL : ℝ) (h0 : 0 ≤ aC) (h1 : aC ≤ 1)
    (h0' : 0 ≤ aL) (h1' : aL ≤ 1)
    (lam tau : ℕ → ℝ) (hl : ∀ n, 0 < lam n)
    (ht : ∀ n, 0 < tau n) (hlim : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → Θ × Fin 2 → ℝ) (hs : ∀ n, (M.expt aC aL).IsSteady (lam n) (tau n) (s n))
    (i j : Fin 2) :
    Tendsto (fun n => M.Q (lam n) aC aL (s n) i j / lam n) atTop
      (𝓝 (∑ θ, ∑ γ, (M.expt aC aL).φ (γ, i) * M.pE (γ, i) (θ, j) (M.rhoL aL))) := by
  have := sum_choice_tendsto (M.expt aC aL) (good_expt M hM aC aL h0 h1)
    (rho_nn M hM aC aL h0' h1') lam tau hl ht hlim s hs (fun θ : Θ => (θ, j))
    (fun γ : Γ => (γ, i))
  refine this.congr' (Eventually.of_forall fun n => ?_)
  show _ = (lam n * _) / lam n
  rw [mul_div_cancel_left₀ _ (hl n).ne']

lemma control_identity (M : Model Γ Θ) (γ : Γ) (θ : Θ) :
    M.pE (γ, 0) (θ, 1) (M.rhoL 1) = M.pE (γ, 0) (θ, 0) (M.rhoL 0) := by
  simp [Model.pE, MFSystem.choice, Model.expt, Model.rhoL, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma cr_part (M : Model Γ Θ) (hM : M.Standing) (aC : ℝ) (h0 : 0 < aC) (h1 : aC < 1)
    (lam tau : ℕ → ℝ) (hl : ∀ n, 0 < lam n) (ht : ∀ n, 0 < tau n)
    (hlim : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (sCR sGT sGC : ℕ → Θ × Fin 2 → ℝ)
    (hCR : ∀ n, (M.expt aC 1).IsSteady (lam n) (tau n) (sCR n))
    (hGT : ∀ n, (M.expt 1 1).IsSteady (lam n) (tau n) (sGT n))
    (hGC : ∀ n, (M.expt 0 0).IsSteady (lam n) (tau n) (sGC n)) :
    Tendsto (fun n => M.crEst (lam n) aC (sCR n) / lam n
          - M.gte (lam n) (sGT n) (sGC n) / lam n) atTop (𝓝 0) := by
  have t11 := Q_tendsto M hM aC 1 h0.le h1.le zero_le_one le_rfl lam tau hl ht hlim sCR hCR 1 1
  have t01 := Q_tendsto M hM aC 1 h0.le h1.le zero_le_one le_rfl lam tau hl ht hlim sCR hCR 0 1
  have tGT := Q_tendsto M hM 1 1 zero_le_one le_rfl zero_le_one le_rfl lam tau hl ht hlim sGT hGT 1 1
  have tGC := Q_tendsto M hM 0 0 le_rfl zero_le_one le_rfl zero_le_one lam tau hl ht hlim sGC hGC 0 0
  have hT := ((t11.div_const aC).sub (t01.div_const (1 - aC))).sub (tGT.sub tGC)
  have hfun : (fun n => M.crEst (lam n) aC (sCR n) / lam n
          - M.gte (lam n) (sGT n) (sGC n) / lam n) =
      (fun n => (M.Q (lam n) aC 1 (sCR n) 1 1 / lam n / aC
          - M.Q (lam n) aC 1 (sCR n) 0 1 / lam n / (1 - aC))
          - (M.Q (lam n) 1 1 (sGT n) 1 1 / lam n - M.Q (lam n) 0 0 (sGC n) 0 0 / lam n)) := by
    funext n
    simp only [Model.crEst, Model.gte]
    ring
  rw [hfun]
  convert hT using 2
  have hc : (1 - aC) ≠ 0 := by linarith
  simp only [Model.expt, control_identity, if_true, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
    if_false, mul_assoc, ← Finset.mul_sum]
  field_simp
  ring


noncomputable def Asum (M : Model Γ Θ) (γ : Γ) : ℝ := ∑ θ, M.sys.α γ θ * M.sys.v γ θ * M.sys.ρ θ

lemma den1 (M : Model Γ Θ) (γ : Γ) (a : ℝ) :
    ∑ p, (M.expt 1 1).α (γ, 1) p * (M.expt 1 1).v (γ, 1) p * M.rhoL a p
      = (1 - a) * Asum M γ + a * DLSolB.Bf (fun γ θ => M.αt γ θ * M.sys.ρ θ) γ M.vt := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Model.expt, Model.rhoL, Asum, DLSolB.Bf,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro θ _
  simp
  ring

lemma den0 (M : Model Γ Θ) (γ : Γ) (a : ℝ) :
    ∑ p, (M.expt 1 1).α (γ, 0) p * (M.expt 1 1).v (γ, 0) p * M.rhoL a p = Asum M γ := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Model.expt, Model.rhoL, Asum]
  apply Finset.sum_congr rfl; intro θ _
  simp
  ring

lemma pE11 (M : Model Γ Θ) (γ : Γ) (θ : Θ) (a : ℝ) :
    M.pE (γ, 1) (θ, 1) (M.rhoL a) = M.αt γ θ * M.vt γ θ * (a * M.sys.ρ θ) /
      (M.sys.eps γ + ((1 - a) * Asum M γ + a * DLSolB.Bf (fun γ θ => M.αt γ θ * M.sys.ρ θ) γ M.vt)) := by
  unfold Model.pE MFSystem.choice
  rw [den1]
  simp [Model.expt, Model.rhoL]

lemma pE10 (M : Model Γ Θ) (γ : Γ) (θ : Θ) (a : ℝ) :
    M.pE (γ, 1) (θ, 0) (M.rhoL a) = M.sys.α γ θ * M.sys.v γ θ * ((1 - a) * M.sys.ρ θ) /
      (M.sys.eps γ + ((1 - a) * Asum M γ + a * DLSolB.Bf (fun γ θ => M.αt γ θ * M.sys.ρ θ) γ M.vt)) := by
  unfold Model.pE MFSystem.choice
  rw [den1]
  simp [Model.expt, Model.rhoL]

lemma pE00 (M : Model Γ Θ) (γ : Γ) (θ : Θ) (a : ℝ) :
    M.pE (γ, 0) (θ, 0) (M.rhoL a) = M.sys.α γ θ * M.sys.v γ θ * ((1 - a) * M.sys.ρ θ) /
      (M.sys.eps γ + Asum M γ) := by
  unfold Model.pE MFSystem.choice
  rw [den0]
  simp [Model.expt, Model.rhoL]

noncomputable def LRlim (M : Model Γ Θ) (aL : ℝ) : ℝ :=
  (∑ θ, ∑ γ, (M.expt 1 aL).φ (γ, 1) * M.pE (γ, 1) (θ, 1) (M.rhoL aL)) / aL
    - (∑ θ, ∑ γ, (M.expt 1 aL).φ (γ, 1) * M.pE (γ, 1) (θ, 0) (M.rhoL aL)) / (1 - aL)
    - ((∑ θ, ∑ γ, (M.expt 1 1).φ (γ, 1) * M.pE (γ, 1) (θ, 1) (M.rhoL 1))
      - (∑ θ, ∑ γ, (M.expt 0 0).φ (γ, 0) * M.pE (γ, 0) (θ, 0) (M.rhoL 0)))

lemma LRlim_eq (M : Model Γ Θ) (aL : ℝ) (h0 : 0 < aL) (h1 : aL < 1) :
    LRlim M aL = DLSolB.Fsum aL M.sys.φ M.sys.eps (Asum M) (fun γ θ => M.αt γ θ * M.sys.ρ θ) M.vt := by
  unfold LRlim DLSolB.Fsum DLSolB.hf
  simp only [pE11, pE10, pE00]
  rw [Finset.sum_comm (f := fun θ γ => (M.expt 1 aL).φ (γ, 1) * _),
    Finset.sum_comm (f := fun θ γ => (M.expt 1 aL).φ (γ, 1) * _),
    Finset.sum_comm (f := fun θ γ => (M.expt 1 1).φ (γ, 1) * _),
    Finset.sum_comm (f := fun θ γ => (M.expt 0 0).φ (γ, 0) * _)]
  simp only [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro γ _
  set B := DLSolB.Bf (fun γ θ => M.αt γ θ * M.sys.ρ θ) γ M.vt with hB
  have hBs : ∑ θ, M.αt γ θ * M.vt γ θ * (aL * M.sys.ρ θ) = aL * B := by
    rw [hB, DLSolB.Bf, Finset.mul_sum]; apply Finset.sum_congr rfl; intro θ _; ring
  have hBs1 : ∑ θ, M.αt γ θ * M.vt γ θ * (1 * M.sys.ρ θ) = B := by
    rw [hB, DLSolB.Bf]; apply Finset.sum_congr rfl; intro θ _; ring
  have hAs : ∑ θ, M.sys.α γ θ * M.sys.v γ θ * ((1 - aL) * M.sys.ρ θ) = (1 - aL) * Asum M γ := by
    rw [Asum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro θ _; ring
  have hAs0 : ∑ θ, M.sys.α γ θ * M.sys.v γ θ * ((1 - 0) * M.sys.ρ θ) = Asum M γ := by
    rw [Asum]; apply Finset.sum_congr rfl; intro θ _; ring
  set D := M.sys.eps γ + ((1 - aL) * Asum M γ + aL * B) with hD
  set φ1 := (M.expt 1 aL).φ (γ, 1)
  set φ3 := (M.expt 1 1).φ (γ, 1)
  set φ4 := (M.expt 0 0).φ (γ, 0)
  have hpt : ∀ x, φ1 * (M.αt γ x * M.vt γ x * (aL * M.sys.ρ x) / D) / aL
        - φ1 * (M.sys.α γ x * M.sys.v γ x * ((1 - aL) * M.sys.ρ x) / D) / (1 - aL)
        - (φ3 * (M.αt γ x * M.vt γ x * (1 * M.sys.ρ x) / (M.sys.eps γ + ((1 - 1) * Asum M γ + 1 * B)))
          - φ4 * (M.sys.α γ x * M.sys.v γ x * ((1 - 0) * M.sys.ρ x) / (M.sys.eps γ + Asum M γ)))
      = φ1 / D / aL * (M.αt γ x * M.vt γ x * (aL * M.sys.ρ x))
        - φ1 / D / (1 - aL) * (M.sys.α γ x * M.sys.v γ x * ((1 - aL) * M.sys.ρ x))
        - (φ3 / (M.sys.eps γ + ((1 - 1) * Asum M γ + 1 * B)) * (M.αt γ x * M.vt γ x * (1 * M.sys.ρ x))
          - φ4 / (M.sys.eps γ + Asum M γ) * (M.sys.α γ x * M.sys.v γ x * ((1 - 0) * M.sys.ρ x))) := by
    intro x; ring
  rw [Finset.sum_congr rfl (fun x _ => hpt x)]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hBs, hBs1, hAs, hAs0]
  have hφ1 : φ1 = M.sys.φ γ := by simp [φ1, Model.expt]
  have hφ3 : φ3 = M.sys.φ γ := by simp [φ3, Model.expt]
  have hφ4 : φ4 = M.sys.φ γ := by simp [φ4, Model.expt]
  rw [hφ1, hφ3, hφ4]
  have ha : aL ≠ 0 := h0.ne'
  have hb : 1 - aL ≠ 0 := by linarith
  simp only [sub_self, zero_mul, one_mul, zero_add]
  rw [hD]
  field_simp
  ring


lemma lr_part (M : Model Γ Θ) (hM : M.Standing) (aL : ℝ) (h0 : 0 < aL) (h1 : aL < 1)
    (lam tau : ℕ → ℝ) (hl : ∀ n, 0 < lam n) (ht : ∀ n, 0 < tau n)
    (hlim : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (sLR sGT sGC : ℕ → Θ × Fin 2 → ℝ)
    (hLR : ∀ n, (M.expt 1 aL).IsSteady (lam n) (tau n) (sLR n))
    (hGT : ∀ n, (M.expt 1 1).IsSteady (lam n) (tau n) (sGT n))
    (hGC : ∀ n, (M.expt 0 0).IsSteady (lam n) (tau n) (sGC n)) :
    Tendsto (fun n => M.lrEst (lam n) aL (sLR n) / lam n
          - M.gte (lam n) (sGT n) (sGC n) / lam n) atTop (𝓝 (LRlim M aL)) := by
  have t11 := Q_tendsto M hM 1 aL zero_le_one le_rfl h0.le h1.le lam tau hl ht hlim sLR hLR 1 1
  have t10 := Q_tendsto M hM 1 aL zero_le_one le_rfl h0.le h1.le lam tau hl ht hlim sLR hLR 1 0
  have tGT := Q_tendsto M hM 1 1 zero_le_one le_rfl zero_le_one le_rfl lam tau hl ht hlim sGT hGT 1 1
  have tGC := Q_tendsto M hM 0 0 le_rfl zero_le_one le_rfl zero_le_one lam tau hl ht hlim sGC hGC 0 0
  have hT := ((t11.div_const aL).sub (t10.div_const (1 - aL))).sub (tGT.sub tGC)
  have hfun : (fun n => M.lrEst (lam n) aL (sLR n) / lam n
          - M.gte (lam n) (sGT n) (sGC n) / lam n) =
      (fun n => (M.Q (lam n) 1 aL (sLR n) 1 1 / lam n / aL
          - M.Q (lam n) 1 aL (sLR n) 1 0 / lam n / (1 - aL))
          - (M.Q (lam n) 1 1 (sGT n) 1 1 / lam n - M.Q (lam n) 0 0 (sGC n) 0 0 / lam n)) := by
    funext n
    simp only [Model.lrEst, Model.gte]
    ring
  rw [hfun]
  exact hT

end Model
end DLSol

open TwoSidedExp.DemandLimit in
theorem solution {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ) (hM : M.Standing) :
    (∀ aC : ℝ, 0 < aC → aC < 1 →
      ∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
        Tendsto (fun n => lam n / tau n) atTop (𝓝 0) →
      ∀ (sCR sGT sGC : ℕ → Θ × Fin 2 → ℝ),
        (∀ n, (M.expt aC 1).IsSteady (lam n) (tau n) (sCR n)) →
        (∀ n, (M.expt 1 1).IsSteady (lam n) (tau n) (sGT n)) →
        (∀ n, (M.expt 0 0).IsSteady (lam n) (tau n) (sGC n)) →
      Tendsto (fun n => M.crEst (lam n) aC (sCR n) / lam n
          - M.gte (lam n) (sGT n) (sGC n) / lam n) atTop (𝓝 0)) ∧
    (∀ aL : ℝ, 0 < aL → aL < 1 →
      ∀ᵐ w ∂(volume : Measure (Γ → Θ → ℝ)), (∀ γ θ, 0 < w γ θ) →
        ∃ L : ℝ, L ≠ 0 ∧
          ∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
            Tendsto (fun n => lam n / tau n) atTop (𝓝 0) →
          ∀ (sLR sGT sGC : ℕ → Θ × Fin 2 → ℝ),
            (∀ n, ((M.withVt w).expt 1 aL).IsSteady (lam n) (tau n) (sLR n)) →
            (∀ n, ((M.withVt w).expt 1 1).IsSteady (lam n) (tau n) (sGT n)) →
            (∀ n, ((M.withVt w).expt 0 0).IsSteady (lam n) (tau n) (sGC n)) →
          Tendsto (fun n => (M.withVt w).lrEst (lam n) aL (sLR n) / lam n
              - (M.withVt w).gte (lam n) (sGT n) (sGC n) / lam n) atTop (𝓝 L)) := by
  classical
  refine ⟨fun aC h0 h1 lam tau hl ht hlim sCR sGT sGC hCR hGT hGC =>
    DLSol.Model.cr_part M hM aC h0 h1 lam tau hl ht hlim sCR sGT sGC hCR hGT hGC, ?_⟩
  intro aL h0 h1
  have hΓ : Nonempty Γ := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hM.phi_sum
    simp [Finset.univ_eq_empty] at this
  have hΘ : Nonempty Θ := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hM.rho_sum
    simp [Finset.univ_eq_empty] at this
  have hA : ∀ γ, 0 < DLSol.Model.Asum M γ := fun γ =>
    Finset.sum_pos (fun θ _ => mul_pos (mul_pos (hM.alpha_pos γ θ) (hM.v_pos γ θ)) (hM.rho_pos θ))
      Finset.univ_nonempty
  have hnull := DLSolB.Fsum_null aL M.sys.φ M.sys.eps (DLSol.Model.Asum M)
    (fun γ θ => M.αt γ θ * M.sys.ρ θ) h0 h1 hM.phi_pos hM.eps_pos hA
    (fun γ θ => mul_pos (hM.alphat_pos γ θ) (hM.rho_pos θ))
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw ⊢
  by_contra hcon
  apply hw
  intro hpos
  have hF : DLSolB.Fsum aL M.sys.φ M.sys.eps (DLSol.Model.Asum M)
      (fun γ θ => M.αt γ θ * M.sys.ρ θ) w ≠ 0 := fun h => hcon ⟨hpos, h⟩
  have hMw : (M.withVt w).Standing :=
    { rho_pos := hM.rho_pos, rho_sum := hM.rho_sum, phi_pos := hM.phi_pos, phi_sum := hM.phi_sum,
      alpha_pos := hM.alpha_pos, alpha_le_one := hM.alpha_le_one, alphat_pos := hM.alphat_pos,
      alphat_le_one := hM.alphat_le_one, v_pos := hM.v_pos, vt_pos := hpos, eps_pos := hM.eps_pos,
      nu_pos := hM.nu_pos }
  have hL := DLSol.Model.LRlim_eq (M.withVt w) aL h0 h1
  refine ⟨DLSol.Model.LRlim (M.withVt w) aL, ?_, ?_⟩
  · rw [hL]; exact hF
  · intro lam tau hl ht hlim sLR sGT sGC hLR hGT hGC
    exact DLSol.Model.lr_part (M.withVt w) hMw aL h0 h1 lam tau hl ht hlim sLR sGT sGC hLR hGT hGC
