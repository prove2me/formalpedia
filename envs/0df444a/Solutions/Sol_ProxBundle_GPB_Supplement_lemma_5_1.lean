-- Prove2me | solution 1 for ProxBundle.GPB.Supplement.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:54.439082+00:00
-- url     : https://prove2.me/submissions/50475be4-9a0c-41da-a754-414f2f6150d0

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Definitions.Def_ProxBundle_GPB_Supplement_Adaptive

open ProxBundle
open ProxBundle.GPB
open ProxBundle.GPB.Supplement

/-- Lemma 5.1(a,b), including j=0 and every beta >= 1. -/
theorem solution {n : ℕ} (P : Instance n) (μ Mf Lf Mbar Lbar lam ε β : ℝ)
    (x0 : E n) (A : APBRun n)
    (hμ : 0 ≤ μ) (hMf : 0 ≤ Mf) (hLf : 0 ≤ Lf)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mf Lf)
    (hmin : P.IsMinPair ε Mbar Lbar)
    (hopt : ∃ x : E n, P.IsOpt x) (hx0 : x0 ∈ P.D)
    (hlam : 0 < lam) (hε : 0 < ε) (hβ : 1 ≤ β)
    (hrun : IsAPBRun P lam ε β x0 A) :
    (∀ j : ℕ, 0 ≤ A.τ j ∧ A.τ j ≤ (1 + tauBar μ lam ε Mbar Lbar) / 2) ∧
    (∀ a b : ℕ, IsCycle P A.accepted lam ε a b →
      A.accepted.t P lam b ≤ ε / 2 ∧
        ∀ j : ℕ, a + 1 < j → j ≤ b →
          A.accepted.t P lam j - ε / 4 ≤
            A.τ j * (A.accepted.t P lam (j - 1) - ε / 4)) := by
              classical
              obtain ⟨-, hfc, ⟨hhsc, -⟩, hsub⟩ := hA1
              obtain ⟨hM, hL, hA3b, -⟩ := hmin
              obtain ⟨hr0, hry0, hrτ0, hrs⟩ := hrun
              have hDc : Convex ℝ P.D := hfc.1
              -- descent inequality
              have hdesc : ∀ x ∈ P.D, ∀ y ∈ P.D,
                  P.f y ≤ P.ellf y x + 2 * Mbar * ‖y - x‖ + Lbar / 2 * ‖y - x‖ ^ 2 := by
                intro x hx y hy
                have hpart : ∀ N : ℕ, 1 ≤ N → P.f y ≤ P.ellf y x + 2 * Mbar * ‖y - x‖
                    + Lbar / 2 * ‖y - x‖ ^ 2 * (1 + 1 / (N : ℝ)) := by
                  intro N hN
                  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
                  have hzD : ∀ k : ℕ, k ≤ N → x + ((k : ℝ) / N) • (y - x) ∈ P.D := by
                    intro k hk
                    have hk1 : (k : ℝ) / N ≤ 1 := by
                      rw [div_le_one hN0]; exact_mod_cast hk
                    exact hDc.add_smul_sub_mem hx hy ⟨by positivity, hk1⟩
                  have hind : ∀ k : ℕ, k ≤ N → P.f (x + ((k : ℝ) / N) • (y - x)) ≤
                      P.f x + ((k : ℝ) / N) * inner ℝ (P.f' x) (y - x)
                        + ((k : ℝ) / N) * (2 * Mbar * ‖y - x‖)
                        + Lbar * ‖y - x‖ ^ 2 * ((k : ℝ) * (k + 1) / (2 * N ^ 2)) := by
                    intro k
                    induction k with
                    | zero => intro _; simp
                    | succ k ih =>
                      intro hk
                      have ih' := ih (by omega)
                      have hzk := hzD k (by omega)
                      have hzk1 := hzD (k + 1) hk
                      have h1 := hsub _ hzk1 _ hzk
                      have hA := hA3b _ hzk1 _ hx
                      unfold Instance.ellf at h1
                      have e1 : (x + ((k : ℝ) / N) • (y - x)) - (x + (((k + 1 : ℕ) : ℝ) / N) • (y - x))
                          = (-(1 / (N : ℝ))) • (y - x) := by
                        have : ((k : ℝ) / N) = (((k + 1 : ℕ) : ℝ) / N) + (-(1 / (N : ℝ))) := by
                          push_cast; ring
                        rw [this, add_smul]; abel
                      have e2 : (x + (((k + 1 : ℕ) : ℝ) / N) • (y - x)) - x
                          = (((k + 1 : ℕ) : ℝ) / N) • (y - x) := by abel
                      rw [e1, inner_smul_right] at h1
                      rw [e2, norm_smul, Real.norm_of_nonneg (by positivity)] at hA
                      set z := x + (((k + 1 : ℕ) : ℝ) / N) • (y - x) with hz
                      have hcs : inner ℝ (P.f' z) (y - x) ≤ inner ℝ (P.f' x) (y - x) +
                          (2 * Mbar + Lbar * ((((k + 1 : ℕ) : ℝ) / N) * ‖y - x‖)) * ‖y - x‖ := by
                        have h2 := real_inner_le_norm (P.f' z - P.f' x) (y - x)
                        rw [inner_sub_left] at h2
                        have h3 := mul_le_mul_of_nonneg_right hA (norm_nonneg (y - x))
                        linarith
                      have h4 := mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ 1 / N by positivity)
                      have e3 : (((k + 1 : ℕ) : ℝ) / N) * inner ℝ (P.f' x) (y - x)
                        + (((k + 1 : ℕ) : ℝ) / N) * (2 * Mbar * ‖y - x‖)
                        + Lbar * ‖y - x‖ ^ 2 * (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) / (2 * N ^ 2))
                        = ((k : ℝ) / N) * inner ℝ (P.f' x) (y - x)
                        + ((k : ℝ) / N) * (2 * Mbar * ‖y - x‖)
                        + Lbar * ‖y - x‖ ^ 2 * ((k : ℝ) * (k + 1) / (2 * N ^ 2))
                        + 1 / N * (inner ℝ (P.f' x) (y - x) +
                          (2 * Mbar + Lbar * ((((k + 1 : ℕ) : ℝ) / N) * ‖y - x‖)) * ‖y - x‖) := by
                        push_cast
                        field_simp
                        ring
                      linarith
                  have hfin := hind N le_rfl
                  rw [div_self hN0.ne', one_smul, add_sub_cancel] at hfin
                  have e4 : Lbar * ‖y - x‖ ^ 2 * ((N : ℝ) * (N + 1) / (2 * N ^ 2))
                      = Lbar / 2 * ‖y - x‖ ^ 2 * (1 + 1 / (N : ℝ)) := by
                    field_simp
                  unfold Instance.ellf
                  linarith
                by_contra hcon
                push Not at hcon
                set X := P.f y - (P.ellf y x + 2 * Mbar * ‖y - x‖ + Lbar / 2 * ‖y - x‖ ^ 2) with hX
                have hXpos : 0 < X := by rw [hX]; linarith
                obtain ⟨N, hNgt⟩ := exists_nat_gt (Lbar / 2 * ‖y - x‖ ^ 2 / X)
                have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hNgt
                have hp := hpart N (by exact_mod_cast hNpos)
                rw [div_lt_iff₀ hXpos] at hNgt
                have h5 : X ≤ Lbar / 2 * ‖y - x‖ ^ 2 / N := by
                  rw [hX]
                  have : Lbar / 2 * ‖y - x‖ ^ 2 * (1 + 1 / (N : ℝ)) =
                    Lbar / 2 * ‖y - x‖ ^ 2 + Lbar / 2 * ‖y - x‖ ^ 2 / N := by ring
                  linarith
                rw [le_div_iff₀ hNpos] at h5
                linarith
              -- quadratic growth
              have hgrow : ∀ (G : E n → ℝ) (c x : E n), StrongConvexOn P.D μ G →
                  P.IsProxMin G c lam x → ∀ u ∈ P.D,
                  G x + ‖x - c‖ ^ 2 / (2 * lam) + (μ + 1 / lam) / 2 * ‖x - u‖ ^ 2 ≤
                    G u + ‖u - c‖ ^ 2 / (2 * lam) := by
                intro G c x hG hx u hu
                have hs : ∀ s : ℝ, 0 < s → s < 1 →
                    G x + ‖x - c‖ ^ 2 / (2 * lam) + (1 - s) * ((μ + 1 / lam) / 2 * ‖x - u‖ ^ 2) ≤
                    G u + ‖u - c‖ ^ 2 / (2 * lam) := by
                  intro s hs0 hs1
                  have hsc := hG.2 hx.1 hu (sub_nonneg.2 hs1.le) hs0.le (by ring)
                  have hzD : (1 - s) • x + s • u ∈ P.D :=
                    hDc hx.1 hu (sub_nonneg.2 hs1.le) hs0.le (by ring)
                  have hm := hx.2 _ hzD
                  have hq : ‖(1 - s) • x + s • u - c‖ ^ 2 =
                      (1 - s) * ‖x - c‖ ^ 2 + s * ‖u - c‖ ^ 2 - s * (1 - s) * ‖x - u‖ ^ 2 := by
                    have e1 : (1 - s) • x + s • u - c = (1 - s) • (x - c) + s • (u - c) := by module
                    have e2 : x - u = (x - c) - (u - c) := by abel
                    rw [e1, e2, norm_add_sq_real, norm_sub_sq_real (x - c) (u - c), norm_smul, norm_smul,
                      inner_smul_left, inner_smul_right, Real.norm_of_nonneg hs0.le,
                      Real.norm_of_nonneg (sub_nonneg.2 hs1.le)]
                    simp
                    ring
                  rw [hq] at hm
                  simp only [smul_eq_mul] at hsc
                  have h6 : s * (G x + ‖x - c‖ ^ 2 / (2 * lam) +
                      (1 - s) * ((μ + 1 / lam) / 2 * ‖x - u‖ ^ 2)) ≤
                      s * (G u + ‖u - c‖ ^ 2 / (2 * lam)) := by
                    have e3 : ((1 - s) * ‖x - c‖ ^ 2 + s * ‖u - c‖ ^ 2 - s * (1 - s) * ‖x - u‖ ^ 2)
                        / (2 * lam) = (1 - s) * (‖x - c‖ ^ 2 / (2 * lam)) + s * (‖u - c‖ ^ 2 / (2 * lam))
                          - s * (1 - s) * (1 / lam / 2 * ‖x - u‖ ^ 2) := by
                      field_simp
                    rw [e3] at hm
                    linarith
                  exact le_of_mul_le_mul_left h6 hs0
                by_contra hcon
                push Not at hcon
                set K := (μ + 1 / lam) / 2 * ‖x - u‖ ^ 2 with hK
                have hK0 : 0 ≤ K := by positivity
                set X := G x + ‖x - c‖ ^ 2 / (2 * lam) + K - (G u + ‖u - c‖ ^ 2 / (2 * lam)) with hX
                have hXpos : 0 < X := by rw [hX]; linarith
                have hK1 : 0 < 2 * (K + X) := by linarith
                have hs0 : 0 < X / (2 * (K + X)) := by positivity
                have hs1 : X / (2 * (K + X)) < 1 := by
                  rw [div_lt_one hK1]; linarith
                have h7 := hs _ hs0 hs1
                have h8 : X / (2 * (K + X)) * K < X := by
                  rw [div_mul_eq_mul_div, div_lt_iff₀ hK1]
                  nlinarith
                linarith
              -- strong convexity of cuts
              have hcutsc : ∀ z : E n, StrongConvexOn P.D μ (fun u => P.ellf u z + P.h u) := by
                intro z
                refine ⟨hDc, ?_⟩
                intro x hx y hy a b ha hb hab
                have h1 := hhsc.2 hx hy ha hb hab
                simp only [smul_eq_mul] at h1 ⊢
                have e1 : P.ellf (a • x + b • y) z = a * P.ellf x z + b * P.ellf y z := by
                  unfold Instance.ellf
                  have e2 : a • x + b • y - z = a • (x - z) + b • (y - z) := by
                    have : z = (a + b) • z := by rw [hab, one_smul]
                    conv_lhs => rw [this]
                    module
                  rw [e2, inner_add_right, inner_smul_right, inner_smul_right]
                  have hb' : b = 1 - a := by linarith
                  subst hb'
                  ring
                rw [e1]
                linarith
              have hcomb : ∀ (G H : E n → ℝ) (τ : ℝ), 0 ≤ τ → τ ≤ 1 → StrongConvexOn P.D μ G →
                  StrongConvexOn P.D μ H → StrongConvexOn P.D μ (fun u => τ * G u + (1 - τ) * H u) := by
                intro G H τ h0 h1 hG hH
                refine ⟨hDc, ?_⟩
                intro x hx y hy a b ha hb hab
                have h2 := mul_le_mul_of_nonneg_left (hG.2 hx hy ha hb hab) h0
                have h3 := mul_le_mul_of_nonneg_left (hH.2 hx hy ha hb hab) (sub_nonneg.2 h1)
                simp only [smul_eq_mul] at h2 h3 ⊢
                linarith
              have hcongr : ∀ (G H : E n → ℝ), StrongConvexOn P.D μ G → (∀ u ∈ P.D, H u = G u) →
                  StrongConvexOn P.D μ H := by
                intro G H hG hGH
                refine ⟨hDc, ?_⟩
                intro x hx y hy a b ha hb hab
                rw [hGH _ hx, hGH _ hy, hGH _ (hDc hx hy ha hb hab)]
                exact hG.2 hx hy ha hb hab
              -- accepted trial
              have hacc : ∀ j, 1 ≤ j → IsTrial P lam ε A.accepted j (A.trial j (A.count j - 1)) := by
                intro j hj
                obtain ⟨hc, -, hT, -⟩ := hrs j hj
                exact hT _ (by omega)
              have hprox : ∀ j, 1 ≤ j →
                  P.IsProxMin (A.accepted.Γ j) (A.accepted.xc j) lam (A.accepted.x j) := by
                intro j hj
                obtain ⟨-, -, hp, -⟩ := hacc j hj
                obtain ⟨-, -, -, -, -, -, hx, -, hxc, hΓ⟩ := hrs j hj
                rw [hx, hxc]
                refine ⟨hp.1, fun u hu => ?_⟩
                rw [hΓ _ hu, hΓ _ hp.1]
                exact hp.2 u hu
              have hxD : ∀ j, A.accepted.x j ∈ P.D := by
                intro j
                rcases Nat.eq_zero_or_pos j with h | h
                · rw [h, hr0]; exact hx0
                · exact (hprox j h).1
              have hyx : ∀ j, ∃ i ≤ j, A.accepted.y j = A.accepted.x i := by
                intro j
                rcases Nat.eq_zero_or_pos j with h | h
                · exact ⟨0, by omega, by rw [h, hr0, hry0]⟩
                · obtain ⟨-, -, -, hor, -⟩ := hacc j h
                  obtain ⟨-, -, -, -, -, -, hx, hy, -⟩ := hrs j h
                  rcases hor with ⟨i, hi, he⟩ | he
                  · exact ⟨i, hi.le, by rw [hy, he]⟩
                  · exact ⟨j, le_rfl, by rw [hy, he, hx]⟩
              -- constants
              set κ := 8 * lamMu μ lam * (Mbar ^ 2 + ε * Lbar) with hκ
              have hden : 0 < 1 + lam * μ := by positivity
              have hlm : 0 < lamMu μ lam := div_pos hlam hden
              have hκ0 : 0 ≤ κ := by positivity
              have htb : tauBar μ lam ε Mbar Lbar = κ / (ε + κ) := rfl
              have hεκ : 0 < ε + κ := by linarith
              have htb0 : 0 ≤ tauBar μ lam ε Mbar Lbar := by rw [htb]; positivity
              have htb1 : tauBar μ lam ε Mbar Lbar < 1 := by
                rw [htb, div_lt_one hεκ]; linarith
              -- key: large τ is never rejected
              have hkey : ∀ (j : ℕ) (U : Trial n), 1 ≤ j → IsTrial P lam ε A.accepted j U →
                  (1 ≤ j - 1 → StrongConvexOn P.D μ (A.accepted.Γ (j - 1))) →
                  tauBar μ lam ε Mbar Lbar ≤ U.τ → U.τ ≤ 1 → ¬ Reject P lam ε A.accepted j U := by
                intro j U hj hU hSC hτ hτ1 hrej
                obtain ⟨ht, hrej⟩ := hrej
                have hj1 : j - 1 ≠ 0 := by
                  intro h0
                  rw [h0] at ht
                  simp [Run.t] at ht
                  linarith
                have hj1' : 1 ≤ j - 1 := by omega
                obtain ⟨-, hnull, hp, -, hyb, hyU⟩ := hU
                obtain ⟨hxc, hΓ⟩ := hnull ht
                have hτ0 : 0 ≤ U.τ := htb0.trans hτ
                have hτε : κ * (1 - U.τ) ≤ U.τ * ε := by
                  rw [htb, div_le_iff₀ hεκ] at hτ
                  linarith
                have hg := hgrow _ _ _ (hSC hj1') (hprox _ hj1') U.x hp.1
                have hd := hdesc _ (hxD (j - 1)) _ hp.1
                obtain ⟨i, hi, hyi⟩ := hyx (j - 1)
                have hyy : P.φ U.y ≤ P.φ (A.accepted.y (j - 1)) := by
                  rw [hyi]; exact hyb i (by omega)
                have htj : A.accepted.t P lam (j - 1) = P.φ (A.accepted.y (j - 1)) -
                    (A.accepted.Γ (j - 1) (A.accepted.x (j - 1)) +
                      ‖A.accepted.x (j - 1) - A.accepted.xc (j - 1)‖ ^ 2 / (2 * lam)) := by
                  simp [Run.t, hj1, Run.m]
                have htU : U.t P lam = P.φ U.y - (U.τ * A.accepted.Γ (j - 1) U.x +
                    (1 - U.τ) * (P.ellf U.x (A.accepted.x (j - 1)) + P.h U.x) +
                      ‖U.x - A.accepted.xc (j - 1)‖ ^ 2 / (2 * lam)) := by
                  unfold Trial.t Trial.m
                  rw [hΓ _ hp.1, hxc]
                rw [norm_sub_rev (A.accepted.x (j - 1)) U.x] at hg
                set δ := ‖U.x - A.accepted.x (j - 1)‖ with hδ
                have hδ0 : 0 ≤ δ := norm_nonneg _
                have hlmc : (μ + 1 / lam) / 2 = 1 / (2 * lamMu μ lam) := by
                  unfold lamMu
                  field_simp
                  ring
                rw [hlmc] at hg
                -- scalar estimate
                have hsc : (1 - U.τ) * (2 * Mbar * δ + Lbar / 2 * δ ^ 2) - U.τ * (1 / (2 * lamMu μ lam) * δ ^ 2)
                    ≤ (1 - U.τ) * (ε / 4) := by
                  have h1 : (1 - U.τ) * (4 * (Mbar ^ 2 + ε * Lbar) / ε * δ ^ 2) ≤
                      U.τ * (1 / (2 * lamMu μ lam) * δ ^ 2) := by
                    have h2 := mul_le_mul_of_nonneg_right hτε
                      (show 0 ≤ 1 / (2 * lamMu μ lam * ε) * δ ^ 2 by positivity)
                    have e1 : κ * (1 - U.τ) * (1 / (2 * lamMu μ lam * ε) * δ ^ 2) =
                        (1 - U.τ) * (4 * (Mbar ^ 2 + ε * Lbar) / ε * δ ^ 2) := by
                      rw [hκ]; field_simp; ring
                    have e2 : U.τ * ε * (1 / (2 * lamMu μ lam * ε) * δ ^ 2) =
                        U.τ * (1 / (2 * lamMu μ lam) * δ ^ 2) := by
                      field_simp
                    rw [e1, e2] at h2
                    exact h2
                  have h3 : 2 * Mbar * δ + Lbar / 2 * δ ^ 2 ≤
                      4 * (Mbar ^ 2 + ε * Lbar) / ε * δ ^ 2 + ε / 4 := by
                    have e3 : 4 * (Mbar ^ 2 + ε * Lbar) / ε * δ ^ 2 + ε / 4 =
                        (2 * Mbar * δ) + (4 * Lbar * δ ^ 2) + (4 * Mbar * δ - ε) ^ 2 / (4 * ε) := by
                      field_simp; ring
                    rw [e3]
                    have : 0 ≤ (4 * Mbar * δ - ε) ^ 2 / (4 * ε) := by positivity
                    have : 0 ≤ Lbar * δ ^ 2 := by positivity
                    linarith
                  have h4 := mul_le_mul_of_nonneg_left h3 (sub_nonneg.2 hτ1)
                  linarith
                have hg' := mul_le_mul_of_nonneg_left hg hτ0
                have hd' := mul_le_mul_of_nonneg_left hd (sub_nonneg.2 hτ1)
                have hy1 := mul_le_mul_of_nonneg_left hyy hτ0
                have hy2 := mul_le_mul_of_nonneg_left hyU (sub_nonneg.2 hτ1)
                have hq := mul_nonneg (sub_nonneg.2 hτ1)
                  (show 0 ≤ ‖U.x - A.accepted.xc (j - 1)‖ ^ 2 / (2 * lam) by positivity)
                have hφx : P.φ U.x = P.f U.x + P.h U.x := rfl
                rw [hφx] at hy2
                rw [htj, htU] at hrej
                linarith
              -- main induction
              have hmain : ∀ j : ℕ, (0 ≤ A.τ j ∧ A.τ j ≤ (1 + tauBar μ lam ε Mbar Lbar) / 2) ∧
                  (1 ≤ j → StrongConvexOn P.D μ (A.accepted.Γ j)) := by
                intro j
                induction j with
                | zero => exact ⟨⟨by rw [hrτ0], by rw [hrτ0]; linarith⟩, by omega⟩
                | succ j ih =>
                  obtain ⟨⟨ih0, ih1⟩, ihS⟩ := ih
                  obtain ⟨hc, hτi, hT, hR, hnR, hτj, hx, hy, hxc, hΓ⟩ := hrs (j + 1) (by omega)
                  simp only [Nat.add_sub_cancel] at hτi
                  have hβ0 : 0 < β := by linarith
                  have hq : ∀ q : ℕ, q < A.count (j + 1) → 0 ≤ (A.trial (j + 1) q).τ ∧
                      (A.trial (j + 1) q).τ ≤ (1 + tauBar μ lam ε Mbar Lbar) / 2 := by
                    intro q
                    induction q with
                    | zero =>
                      intro _
                      rw [hτi]
                      exact ⟨by positivity, (div_le_self ih0 hβ).trans ih1⟩
                    | succ q ihq =>
                      intro hlt
                      obtain ⟨hq0, hq1⟩ := ihq (by omega)
                      obtain ⟨hRq, hτq⟩ := hR q hlt
                      have hlt' : (A.trial (j + 1) q).τ < tauBar μ lam ε Mbar Lbar := by
                        by_contra hcon
                        push Not at hcon
                        exact hkey (j + 1) _ (by omega) (hT q (by omega)) (by simpa using ihS) hcon
                          (by linarith) hRq
                      rw [hτq]
                      constructor <;> linarith
                  have hqq := hq (A.count (j + 1) - 1) (by omega)
                  refine ⟨by rw [hτj]; exact hqq, fun _ => ?_⟩
                  obtain ⟨hser, hnull, -⟩ := hacc (j + 1) (by omega)
                  simp only [Nat.add_sub_cancel] at hser hnull
                  refine hcongr (A.trial (j + 1) (A.count (j + 1) - 1)).Γ _ ?_ hΓ
                  by_cases ht : A.accepted.t P lam j ≤ ε / 2
                  · exact hcongr _ _ (hcutsc (A.accepted.x j)) (hser ht).2
                  · push Not at ht
                    have hj0 : 1 ≤ j := by
                      rcases Nat.eq_zero_or_pos j with h0 | h0
                      · rw [h0] at ht
                        simp [Run.t] at ht
                        linarith
                      · exact h0
                    exact hcongr _ _ (hcomb _ _ _ hqq.1 (by linarith [hqq.2]) (ihS hj0)
                      (hcutsc (A.accepted.x j))) (hnull ht).2
              refine ⟨fun j => (hmain j).1, ?_⟩
              rintro a b ⟨hab, hta, htb', hmid⟩
              refine ⟨htb', ?_⟩
              intro j haj hjb
              have ht := hmid (j - 1) (by omega) (by omega)
              obtain ⟨hc, hτi, hT, hR, hnR, hτj, hx, hy, hxc, hΓ⟩ := hrs j (by omega)
              have hle : (A.trial j (A.count j - 1)).t P lam ≤
                  (A.trial j (A.count j - 1)).τ * A.accepted.t P lam (j - 1) +
                    (1 - (A.trial j (A.count j - 1)).τ) * ε / 4 := by
                by_contra hcon
                push Not at hcon
                exact hnR ⟨ht, hcon⟩
              have hp := hacc j (by omega)
              have hj0 : j ≠ 0 := by omega
              have hte : A.accepted.t P lam j = (A.trial j (A.count j - 1)).t P lam := by
                unfold Run.t Run.m Trial.t Trial.m
                rw [if_neg hj0, hx, hy, hxc, hΓ _ hp.2.2.1.1]
              rw [hte, hτj]
              linarith
