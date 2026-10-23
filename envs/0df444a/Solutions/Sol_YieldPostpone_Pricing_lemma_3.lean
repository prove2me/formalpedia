-- Prove2me | solution 1 for YieldPostpone.Pricing.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:15:07.805427+00:00
-- url     : https://prove2.me/submissions/a5bc17c4-3dd7-4869-887f-022bc0aed845

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting
import Definitions.Def_YieldPostpone_Interplay_Setting
import Theorems.Thm_YieldPostpone_Interplay_lemma_3

namespace YP5B
open YieldPostpone

def tP (P : Pricing.Params) : Interplay.Params := ⟨P.a, P.b, P.α, P.θ⟩

def tS : Pricing.Scenario → Interplay.Scenario
  | .OA => .OA
  | .OR => .OR
  | .DA => .DA
  | .DR => .DR

def tσ (σ : Pricing.Profile) : Interplay.Profile := ⟨σ.w, σ.Q, σ.q, σ.p, σ.pr⟩

/-- Back-translation of an Interplay profile; under pay-by-order the production map is
replaced by the identity order `Q w q = q` everywhere. -/
def bσ (k : Pricing.Scenario) (τ : Interplay.Profile) : Pricing.Profile :=
  if k.byDelivery then ⟨τ.w, τ.Q, τ.q, τ.p, τ.pr⟩ else ⟨τ.w, fun _ q => q, τ.q, τ.p, τ.pr⟩

lemma spe_to (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (σ : Pricing.Profile)
    (h : Pricing.IsSPE P c k σ) : Interplay.IsSPE (tP P) c (tS k) (tσ σ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases k
  · exact ⟨fun w q _ _ => ⟨fun hd => absurd hd (by decide), fun _ => h1 rfl w q⟩,
      fun hr => absurd hr (by decide), h4, h5, h6⟩
  · exact ⟨fun w q _ _ => ⟨fun hd => absurd hd (by decide), fun _ => h1 rfl w q⟩,
      h3, h4, h5, h6⟩
  · exact ⟨fun w q hw hq => ⟨fun _ => h2 rfl w q hw hq, fun hd => absurd hd (by decide)⟩,
      fun hr => absurd hr (by decide), h4, h5, h6⟩
  · exact ⟨fun w q hw hq => ⟨fun _ => h2 rfl w q hw hq, fun hd => absurd hd (by decide)⟩,
      h3, h4, h5, h6⟩

lemma spe_from (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (τ : Interplay.Profile)
    (h : Interplay.IsSPE (tP P) c (tS k) τ) : Pricing.IsSPE P c k (bσ k τ) := by
  obtain ⟨h1, h3, h4, h5, h6⟩ := h
  cases k
  · -- OA
    have hQ : ∀ w q, Interplay.wAdm (tP P) c .OA w → 0 ≤ q → τ.Q w q = q :=
      fun w q hw hq => (h1 w q hw hq).2 rfl
    have hR : ∀ w q' p', Interplay.wAdm (tP P) c .OA w → 0 ≤ q' →
        Pricing.retailerProfit P .OA (bσ .OA τ) w q' p' =
          Interplay.retailerProfit (tP P) .OA τ w q' p' := by
      intro w q' p' hw hq
      simp only [Pricing.retailerProfit, Interplay.retailerProfit, bσ, hQ w q' hw hq]
      rfl
    refine ⟨fun _ w q => rfl, fun hd => absurd hd (by decide),
      fun hr => absurd hr (by decide), ?_, h5, ?_⟩
    · intro w hw
      obtain ⟨a1, a2, a3⟩ := h4 w hw
      refine ⟨a1, a2, fun q' p' hq hp => ?_⟩
      exact ((hR w q' p' hw hq).trans_le (a3 q' p' hq hp)).trans_eq
        (hR w (τ.q w) (τ.p w) hw a1).symm
    · intro w' hw'
      have e1 : Pricing.supplierValue P c .OA (bσ .OA τ) w' =
          Interplay.supplierValue (tP P) c .OA τ w' := by
        simp only [Pricing.supplierValue, Interplay.supplierValue, bσ,
          hQ w' _ hw' (h4 w' hw').1]
        rfl
      have e2 : Pricing.supplierValue P c .OA (bσ .OA τ) (bσ .OA τ).w =
          Interplay.supplierValue (tP P) c .OA τ τ.w := by
        simp only [Pricing.supplierValue, Interplay.supplierValue, bσ,
          hQ τ.w _ h5 (h4 τ.w h5).1]
        rfl
      rw [e1, e2]; exact h6 w' hw'
  · -- OR
    have hQ : ∀ w q, Interplay.wAdm (tP P) c .OR w → 0 ≤ q → τ.Q w q = q :=
      fun w q hw hq => (h1 w q hw hq).2 rfl
    have hR : ∀ w q' p', Interplay.wAdm (tP P) c .OR w → 0 ≤ q' →
        Pricing.retailerProfit P .OR (bσ .OR τ) w q' p' =
          Interplay.retailerProfit (tP P) .OR τ w q' p' := by
      intro w q' p' hw hq
      simp only [Pricing.retailerProfit, Interplay.retailerProfit, bσ, hQ w q' hw hq]
      rfl
    refine ⟨fun _ w q => rfl, fun hd => absurd hd (by decide),
      h3, ?_, h5, ?_⟩
    · intro w hw
      obtain ⟨a1, a2, a3⟩ := h4 w hw
      refine ⟨a1, a2, fun q' p' hq hp => ?_⟩
      exact ((hR w q' p' hw hq).trans_le (a3 q' p' hq hp)).trans_eq
        (hR w (τ.q w) (τ.p w) hw a1).symm
    · intro w' hw'
      have e1 : Pricing.supplierValue P c .OR (bσ .OR τ) w' =
          Interplay.supplierValue (tP P) c .OR τ w' := by
        simp only [Pricing.supplierValue, Interplay.supplierValue, bσ,
          hQ w' _ hw' (h4 w' hw').1]
        rfl
      have e2 : Pricing.supplierValue P c .OR (bσ .OR τ) (bσ .OR τ).w =
          Interplay.supplierValue (tP P) c .OR τ τ.w := by
        simp only [Pricing.supplierValue, Interplay.supplierValue, bσ,
          hQ τ.w _ h5 (h4 τ.w h5).1]
        rfl
      rw [e1, e2]; exact h6 w' hw'
  · exact ⟨fun hd => absurd hd (by decide), fun _ w q hw hq => (h1 w q hw hq).1 rfl,
      fun hr => absurd hr (by decide), h4, h5, h6⟩
  · exact ⟨fun hd => absurd hd (by decide), fun _ w q hw hq => (h1 w q hw hq).1 rfl,
      h3, h4, h5, h6⟩

lemma piR_eq (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (σ : Pricing.Profile) :
    Pricing.piR P k σ = Interplay.piR (tP P) c (tS k) (tσ σ) := by
  cases k <;> rfl

lemma piS_eq (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (σ : Pricing.Profile) :
    Pricing.piS P c k σ = Interplay.piS (tP P) c (tS k) (tσ σ) := by
  cases k <;> rfl

lemma CS_eq (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (σ : Pricing.Profile) :
    Pricing.CS P k σ = Interplay.CS (tP P) c (tS k) (tσ σ) := by
  cases k <;> rfl

lemma outcome_eq (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (σ : Pricing.Profile) :
    Pricing.outcome P c k σ = (Interplay.piR (tP P) c (tS k) (tσ σ),
      Interplay.piS (tP P) c (tS k) (tσ σ), Interplay.CS (tP P) c (tS k) (tσ σ)) := by
  simp only [Pricing.outcome, piR_eq P c, piS_eq P c, CS_eq P c]

lemma cOA2_eq (P : Pricing.Params) : Pricing.cOA2 P = Interplay.cOA2 (tP P) := by
  simp only [Pricing.cOA2, Interplay.cOA2, Pricing.what, Interplay.what, Pricing.μ,
    Interplay.μ, tP]

end YP5B

open YieldPostpone.Pricing

theorem solution (P : Params) (hP : P.Valid) :
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .DA σ) ∧
      ∀ σ : Profile, IsSPE P c .DA σ →
        (c < cDA P →
          outcome P c .DA σ =
            ((P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2),
             (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2),
             (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2))) ∧
        (cDA P < c →
          outcome P c .DA σ =
            ((P.b * c - P.a * μ P) ^ 2 / (16 * P.b * μ P),
             (P.b * c - P.a * μ P) ^ 2 / (8 * P.b * μ P),
             (P.b * c - P.a * μ P) ^ 2 * (P.α * (2 - P.α) * (1 - P.θ) + P.θ) /
               (32 * P.b * μ P ^ 2))) := by
  intro c hc hc'
  have H := YieldPostpone.Interplay.lemma_3 (YP5B.tP P) hP c hc hc'
  refine ⟨?_, fun σ hσ => ?_⟩
  · obtain ⟨τ, hτ⟩ := H.1
    exact ⟨YP5B.bσ .DA τ, YP5B.spe_from P c .DA τ hτ⟩
  · obtain ⟨h1, h2⟩ := H.2 (YP5B.tσ σ) (YP5B.spe_to P c .DA σ hσ)
    rw [YP5B.outcome_eq P c]
    simp only [Prod.mk.injEq]
    exact ⟨h1, h2⟩
