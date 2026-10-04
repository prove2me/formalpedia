-- Prove2me | solution 1 for TeschlODE.IVP.gronwall_generalized
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:08:02.453789+00:00
-- url     : https://prove2.me/submissions/84230e5b-02a7-4095-a4d4-1d201d7ffb9d

import Mathlib

set_option autoImplicit false

namespace GronwallAux9e0

open Set intervalIntegral

lemma sub_eq (β : ℝ → ℝ) (hβ : Continuous β) (s t : ℝ) :
    ∫ r in s..t, β r = (∫ r in (0:ℝ)..t, β r) - ∫ r in (0:ℝ)..s, β r := by
  rw [integral_interval_sub_left (hβ.intervalIntegrable _ _) (hβ.intervalIntegrable _ _)]

lemma identity (β : ℝ → ℝ) (hβ : Continuous β) (t : ℝ) :
    ∫ s in (0:ℝ)..t, β s * Real.exp (∫ r in s..t, β r)
      = Real.exp (∫ r in (0:ℝ)..t, β r) - 1 := by
  set B : ℝ → ℝ := fun u => ∫ r in (0:ℝ)..u, β r with hBdef
  have hB : ∀ x, HasDerivAt B (β x) x := fun x =>
    (hβ.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hBc : Continuous B := continuous_iff_continuousAt.2 fun x => (hB x).continuousAt
  have hrw : ∀ s, ∫ r in s..t, β r = B t - B s := fun s => sub_eq β hβ s t
  simp_rw [hrw]
  have hd : ∀ x ∈ uIcc (0:ℝ) t, HasDerivAt (fun s => -Real.exp (B t - B s))
      (β x * Real.exp (B t - B x)) x := by
    intro x _
    have h1 : HasDerivAt (fun s => B t - B s) (0 - β x) x :=
      (hasDerivAt_const x (B t)).sub (hB x)
    have h2 := (h1.exp).neg
    have e : β x * Real.exp (B t - B x) = -(Real.exp (B t - B x) * (0 - β x)) := by ring
    rw [e]
    exact h2
  rw [integral_eq_sub_of_hasDerivAt hd]
  · have : B 0 = 0 := by simp [hBdef]
    simp [this]
    ring
  · apply Continuous.intervalIntegrable
    exact hβ.mul (Real.continuous_exp.comp (continuous_const.sub hBc))

lemma core (ψ α β : ℝ → ℝ) (T : ℝ)
    (hψ : Continuous ψ) (hα : Continuous α) (hβ : Continuous β)
    (hβ0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ β t)
    (h : ∀ t ∈ Set.Icc 0 T, ψ t ≤ α t + ∫ s in (0 : ℝ)..t, β s * ψ s) :
    ∀ t ∈ Set.Icc 0 T, ∫ s in (0 : ℝ)..t, β s * ψ s ≤
      ∫ s in (0 : ℝ)..t, α s * β s * Real.exp (∫ r in s..t, β r) := by
  set B : ℝ → ℝ := fun u => ∫ r in (0:ℝ)..u, β r with hBdef
  set Φ : ℝ → ℝ := fun u => ∫ r in (0:ℝ)..u, β r * ψ r with hΦdef
  have hB : ∀ x, HasDerivAt B (β x) x := fun x =>
    (hβ.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hBc : Continuous B := continuous_iff_continuousAt.2 fun x => (hB x).continuousAt
  have hΦ : ∀ x, HasDerivAt Φ (β x * ψ x) x := fun x =>
    ((hβ.mul hψ).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hgc : Continuous fun s => α s * β s * Real.exp (-B s) :=
    (hα.mul hβ).mul (Real.continuous_exp.comp hBc.neg)
  have hI : ∀ x, HasDerivAt (fun u => ∫ s in (0:ℝ)..u, α s * β s * Real.exp (-B s))
      (α x * β x * Real.exp (-B x)) x := fun x =>
    (hgc.integral_hasStrictDerivAt 0 x).hasDerivAt
  set G : ℝ → ℝ := fun u => Φ u * Real.exp (-B u) -
    ∫ s in (0:ℝ)..u, α s * β s * Real.exp (-B s) with hGdef
  have hG : ∀ x, HasDerivAt G (β x * ψ x * Real.exp (-B x) +
      Φ x * (Real.exp (-B x) * (-β x)) - α x * β x * Real.exp (-B x)) x := by
    intro x
    exact ((hΦ x).mul ((hB x).neg.exp)).sub (hI x)
  have hGanti : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact fun x _ => (hG x).continuousAt.continuousWithinAt
    · exact fun x _ => (hG x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hG x).deriv]
      have hx' : x ∈ Icc 0 T := interior_subset hx
      have h1 := h x hx'
      have h2 := hβ0 x hx'
      have h3 := Real.exp_pos (-B x)
      have : β x * ψ x * Real.exp (-B x) + Φ x * (Real.exp (-B x) * (-β x))
          - α x * β x * Real.exp (-B x) = (β x * Real.exp (-B x)) * (ψ x - (α x + Φ x)) := by
        ring
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h2 h3.le) (by linarith)
  intro t ht
  have hT : (0:ℝ) ∈ Icc 0 T := ⟨le_refl _, ht.1.trans ht.2⟩
  have hGt : G t ≤ G 0 := hGanti hT ht ht.1
  have hG0 : G 0 = 0 := by simp [hGdef, hΦdef]
  rw [hG0] at hGt
  have key : Φ t * Real.exp (-B t) ≤ ∫ s in (0:ℝ)..t, α s * β s * Real.exp (-B s) := by
    simp only [hGdef] at hGt; linarith
  have hrw : ∀ s, α s * β s * Real.exp (∫ r in s..t, β r) =
      Real.exp (B t) * (α s * β s * Real.exp (-B s)) := by
    intro s
    rw [sub_eq β hβ s t, sub_eq_add_neg, Real.exp_add]
    ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_const_mul]
  have hE : Real.exp (B t) * Real.exp (-B t) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (B t)
  calc Φ t = Real.exp (B t) * (Φ t * Real.exp (-B t)) := by
        rw [← mul_assoc, mul_comm (Real.exp (B t)) (Φ t), mul_assoc, hE, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left key hpos.le

lemma global (ψ α β : ℝ → ℝ) (T : ℝ)
    (hψ : Continuous ψ) (hα : Continuous α) (hβ : Continuous β)
    (hβ0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ β t)
    (h : ∀ t ∈ Set.Icc 0 T, ψ t ≤ α t + ∫ s in (0 : ℝ)..t, β s * ψ s) :
    (∀ t ∈ Set.Icc 0 T,
      ψ t ≤ α t + ∫ s in (0 : ℝ)..t, α s * β s * Real.exp (∫ r in s..t, β r)) ∧
    ((∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, s ≤ t → α s ≤ α t) →
      ∀ t ∈ Set.Icc 0 T, ψ t ≤ α t * Real.exp (∫ s in (0 : ℝ)..t, β s)) := by
  have P1 : ∀ t ∈ Set.Icc 0 T,
      ψ t ≤ α t + ∫ s in (0 : ℝ)..t, α s * β s * Real.exp (∫ r in s..t, β r) := by
    intro t ht
    have := core ψ α β T hψ hα hβ hβ0 h t ht
    linarith [h t ht]
  refine ⟨P1, ?_⟩
  intro hmono t ht
  have h1 := P1 t ht
  have hcont : ∀ c : ℝ → ℝ, Continuous c → Continuous fun s =>
      c s * β s * Real.exp (∫ r in s..t, β r) := by
    intro c hc
    have : (fun s => ∫ r in s..t, β r) = fun s =>
        (∫ r in (0:ℝ)..t, β r) - ∫ r in (0:ℝ)..s, β r := funext fun s => sub_eq β hβ s t
    have hc2 : Continuous (fun s => ∫ r in s..t, β r) := by
      rw [this]
      exact continuous_const.sub
        (continuous_primitive (fun a b => hβ.intervalIntegrable a b) 0)
    exact (hc.mul hβ).mul (Real.continuous_exp.comp hc2)
  have h2 : ∫ s in (0 : ℝ)..t, α s * β s * Real.exp (∫ r in s..t, β r) ≤
      ∫ s in (0 : ℝ)..t, α t * β s * Real.exp (∫ r in s..t, β r) := by
    apply intervalIntegral.integral_mono_on ht.1
      ((hcont α hα).intervalIntegrable _ _) ((hcont _ continuous_const).intervalIntegrable _ _)
    intro s hs
    have hsI : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have := hmono s hsI t ht hs.2
    have hb := hβ0 s hsI
    have he := Real.exp_pos (∫ r in s..t, β r)
    have : α s * β s ≤ α t * β s := mul_le_mul_of_nonneg_right this hb
    exact mul_le_mul_of_nonneg_right this he.le
  have h3 : ∫ s in (0 : ℝ)..t, α t * β s * Real.exp (∫ r in s..t, β r) =
      α t * (Real.exp (∫ r in (0:ℝ)..t, β r) - 1) := by
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, identity β hβ t]
  have : α t * Real.exp (∫ s in (0 : ℝ)..t, β s) =
      α t + α t * (Real.exp (∫ r in (0:ℝ)..t, β r) - 1) := by ring
  rw [this]
  linarith

end GronwallAux9e0

open Set in
theorem solution (ψ α β : ℝ → ℝ) (T : ℝ)
    (hψ : ContinuousOn ψ (Set.Icc 0 T)) (hα : ContinuousOn α (Set.Icc 0 T))
    (hβ : ContinuousOn β (Set.Icc 0 T)) (hβ0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ β t)
    (h : ∀ t ∈ Set.Icc 0 T, ψ t ≤ α t + ∫ s in (0 : ℝ)..t, β s * ψ s) :
    (∀ t ∈ Set.Icc 0 T,
      ψ t ≤ α t + ∫ s in (0 : ℝ)..t, α s * β s * Real.exp (∫ r in s..t, β r)) ∧
    ((∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, s ≤ t → α s ≤ α t) →
      ∀ t ∈ Set.Icc 0 T, ψ t ≤ α t * Real.exp (∫ s in (0 : ℝ)..t, β s)) := by
  rcases lt_or_ge T 0 with hT | hT
  · refine ⟨fun t ht => absurd (ht.1.trans ht.2) (not_le.2 hT),
      fun _ t ht => absurd (ht.1.trans ht.2) (not_le.2 hT)⟩
  set p : ℝ → ℝ := fun x => (projIcc 0 T hT x : ℝ) with hpdef
  have hpc : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpm : ∀ x, p x ∈ Icc 0 T := fun x => (projIcc 0 T hT x).2
  have hpid : ∀ x ∈ Icc 0 T, p x = x := fun x hx => by
    simp [hpdef, projIcc_of_mem hT hx]
  set ψ' := fun x => ψ (p x)
  set α' := fun x => α (p x)
  set β' := fun x => β (p x)
  have cψ : Continuous ψ' := hψ.comp_continuous hpc hpm
  have cα : Continuous α' := hα.comp_continuous hpc hpm
  have cβ : Continuous β' := hβ.comp_continuous hpc hpm
  have eψ : ∀ x ∈ Icc 0 T, ψ' x = ψ x := fun x hx => by simp [ψ', hpid x hx]
  have eα : ∀ x ∈ Icc 0 T, α' x = α x := fun x hx => by simp [α', hpid x hx]
  have eβ : ∀ x ∈ Icc 0 T, β' x = β x := fun x hx => by simp [β', hpid x hx]
  -- interval [a,t] with 0 ≤ a ≤ t ≤ T lies in Icc 0 T
  have sub : ∀ a t, 0 ≤ a → a ≤ t → t ≤ T → ∀ x ∈ uIcc a t, x ∈ Icc 0 T := by
    intro a t ha hat htT x hx
    rw [uIcc_of_le hat] at hx
    exact ⟨ha.trans hx.1, hx.2.trans htT⟩
  have iβ : ∀ a t, 0 ≤ a → a ≤ t → t ≤ T →
      ∫ r in a..t, β' r = ∫ r in a..t, β r := by
    intro a t ha hat htT
    exact intervalIntegral.integral_congr fun x hx => eβ x (sub a t ha hat htT x hx)
  have iβψ : ∀ t ∈ Icc 0 T, ∫ s in (0:ℝ)..t, β' s * ψ' s = ∫ s in (0:ℝ)..t, β s * ψ s := by
    intro t ht
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx' := sub 0 t le_rfl ht.1 ht.2 x hx
    simp only [eβ x hx', eψ x hx']
  have iαβ : ∀ t ∈ Icc 0 T,
      ∫ s in (0:ℝ)..t, α' s * β' s * Real.exp (∫ r in s..t, β' r) =
      ∫ s in (0:ℝ)..t, α s * β s * Real.exp (∫ r in s..t, β r) := by
    intro t ht
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx' := sub 0 t le_rfl ht.1 ht.2 x hx
    have hxt : x ≤ t := by rw [uIcc_of_le ht.1] at hx; exact hx.2
    simp only [eβ x hx', eα x hx', iβ x t hx'.1 hxt ht.2]
  have hβ0' : ∀ t ∈ Icc 0 T, 0 ≤ β' t := fun t ht => (eβ t ht).symm ▸ hβ0 t ht
  have h' : ∀ t ∈ Icc 0 T, ψ' t ≤ α' t + ∫ s in (0 : ℝ)..t, β' s * ψ' s := by
    intro t ht
    rw [eψ t ht, eα t ht, iβψ t ht]
    exact h t ht
  obtain ⟨Q1, Q2⟩ := GronwallAux9e0.global ψ' α' β' T cψ cα cβ hβ0' h'
  refine ⟨fun t ht => ?_, fun hmono t ht => ?_⟩
  · have := Q1 t ht
    rwa [eψ t ht, eα t ht, iαβ t ht] at this
  · have hmono' : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → α' s ≤ α' t := by
      intro s hs t ht hst
      rw [eα s hs, eα t ht]
      exact hmono s hs t ht hst
    have := Q2 hmono' t ht
    rwa [eψ t ht, eα t ht, iβ 0 t le_rfl ht.1 ht.2] at this
