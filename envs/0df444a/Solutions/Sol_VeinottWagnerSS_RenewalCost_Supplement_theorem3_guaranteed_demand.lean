-- Prove2me | solution 1 for VeinottWagnerSS.RenewalCost.Supplement.theorem3_guaranteed_demand
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:44.490794+00:00
-- url     : https://prove2.me/submissions/f01f0739-1fb2-4258-b26d-fdb091229358

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers
import Definitions.Def_VeinottWagnerSS_RenewalCost_Supplement_InfiniteHorizon

open scoped ENNReal

open VeinottWagnerSS
open VeinottWagnerSS.RenewalCost
open VeinottWagnerSS.RenewalCost.Supplement

open VeinottWagnerSS.Bounds

/-- Theorem 3, p. 545 (proof: Appendix §4, pp. 551–552). If `φ(k) = 0` for
`k = 0, 1, ⋯, S̄ − s̲`, then the stationary policy `(s̲, S̲)` is optimal, for every initial level
`X₁`, for every finite-period model and for the infinite-period model (discounted for
`0 ≤ α < 1`, average cost for `α = 1`). Here `S̲ = SLow G`, `s̲ = sLow G K` and
`S̄ = SHigh G K α` are the numbers of (21)–(22), p. 537. -/
theorem solution (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (hgap : ∀ k : ℕ, (k : ℤ) ≤ SHigh G K α - sLow G K → φ k = 0) :
    (∀ n : ℕ, 1 ≤ n → IsOptimal φ G K α n (stationary (sLow G K) (SLow G))) ∧
      IsInfOptimal φ G K α (stationary (sLow G K) (SLow G)) := by
        classical
        -- discrete convexity
        have hd : ∀ a b : ℤ, a ≤ b → G (a+1) - G a ≤ G (b+1) - G b := by
          intro a b hab
          obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
          induction k with
          | zero => simp
          | succ k ih =>
            have h2 := hconv (a + k)
            rw [show a + ((k+1:ℕ):ℤ) = a + k + 1 by push_cast; ring,
              show a + (k:ℤ) + 1 + 1 = a + k + 2 by ring]
            linarith [ih (by omega)]
        have hbdd : ∀ c : ℝ, BddBelow {y : ℤ | G y ≤ c} := by
          intro c
          obtain ⟨N, hN⟩ := Filter.eventually_atBot.1 (hG_bot.eventually (Filter.eventually_ge_atTop (c+1)))
          refine ⟨N, fun y hy => ?_⟩
          by_contra hlt
          have := hN y (by simp at hlt; omega)
          simp at hy; linarith
        -- minimizer
        have hMne : ({y : ℤ | ∀ z : ℤ, G y ≤ G z}).Nonempty := by
          obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 (hG_top.eventually (Filter.eventually_ge_atTop (G 0 + 1)))
          obtain ⟨N2, hN2⟩ := Filter.eventually_atBot.1 (hG_bot.eventually (Filter.eventually_ge_atTop (G 0 + 1)))
          obtain ⟨y0, hy0, hmin⟩ := (Finset.Icc (min N2 0) (max N1 0)).exists_min_image G
            ⟨0, by simp⟩
          refine ⟨y0, fun z => ?_⟩
          have h0 := hmin 0 (by simp)
          by_cases hz : z ∈ Finset.Icc (min N2 0) (max N1 0)
          · exact hmin z hz
          · simp only [Finset.mem_Icc, not_and_or, not_le] at hz
            rcases hz with hz | hz
            · have := hN2 z (by omega); linarith
            · have := hN1 z (by omega); linarith
        have hMbdd : BddBelow {y : ℤ | ∀ z : ℤ, G y ≤ G z} := by
          obtain ⟨y0, hy0⟩ := hMne
          exact (hbdd (G y0)).mono (fun y hy => hy y0)
        have hSmem := Int.csInf_mem hMne hMbdd
        set S := SLow G with hS_def
        have hSmem' : ∀ z, G S ≤ G z := hSmem
        set m := G S with hm_def
        set s := sLow G K with hs_def
        set Sb := SHigh G K α with hSb_def
        have hAne : ({y : ℤ | G y ≤ m + K}).Nonempty := ⟨S, by simp; linarith⟩
        have hsmem : G s ≤ m + K := Int.csInf_mem hAne (hbdd _)
        have hsS : s ≤ S := csInf_le (hbdd _) (by simp; linarith)
        have g1 : ∀ z, z < s → m + K < G z := by
          intro z hz
          have := notMem_of_lt_csInf hz (hbdd (m + K))
          simp at this; linarith
        have hBne : ({y : ℤ | S ≤ y ∧ m + α * K ≤ G (y + 1)}).Nonempty := by
          obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hG_top.eventually (Filter.eventually_ge_atTop (m + α * K)))
          exact ⟨max S N, le_max_left _ _, hN _ (by omega)⟩
        have hBbdd : BddBelow ({y : ℤ | S ≤ y ∧ m + α * K ≤ G (y + 1)}) := ⟨S, fun y hy => hy.1⟩
        have hSbmem : S ≤ Sb ∧ m + α * K ≤ G (Sb + 1) := Int.csInf_mem hBne hBbdd
        have hSb_lt : ∀ y, S ≤ y → y < Sb → G (y + 1) < m + α * K := by
          intro y h1 h2
          have := notMem_of_lt_csInf h2 hBbdd
          simp only [Set.mem_setOf_eq, not_and, not_le] at this
          exact this h1
        have hmono : ∀ a b, S ≤ a → a ≤ b → G a ≤ G b := by
          intro a b ha hab
          obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
          induction k with
          | zero => simp
          | succ k ih =>
            have h1 := hd S (a + k) (by omega)
            have h2 := hSmem' (S + 1)
            rw [show a + ((k+1:ℕ):ℤ) = a + k + 1 by push_cast; ring]
            linarith [ih (by omega)]
        have hanti : ∀ a b, a ≤ b → b ≤ S → G b ≤ G a := by
          intro a b hab hb
          obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
          induction k with
          | zero => simp
          | succ k ih =>
            have h1 := hd (a + k) (S - 1) (by omega)
            have h2 := hSmem' (S - 1)
            rw [show S - 1 + 1 = S by ring] at h1
            rw [show a + ((k+1:ℕ):ℤ) = a + k + 1 by push_cast; ring]
            linarith [ih (by omega) (by omega), hm_def]
        have hαK : α * K ≤ K := by nlinarith
        have g2 : ∀ z, s ≤ z → z ≤ Sb → G z ≤ m + K := by
          intro z h1 h2
          by_cases hzS : z ≤ S
          · linarith [hanti s z h1 hzS]
          · have := hSb_lt (z - 1) (by omega) (by omega)
            rw [show z - 1 + 1 = z by ring] at this
            linarith
        have g3 : ∀ y, Sb < y → m + α * K ≤ G y := by
          intro y hy
          linarith [hmono (Sb + 1) y (by omega) (by omega), hSbmem.2]
        have g6 : ∀ ξ : ℕ, φ ξ ≠ 0 → Sb - s < (ξ : ℤ) := by
          intro ξ hξ
          by_contra h
          exact hξ (hgap ξ (by omega))
        have hSSb : S ≤ Sb := hSbmem.1
        obtain ⟨c, hc⟩ : ∃ c : ℤ → ℤ → ℝ≥0∞, ∀ z y, c z y =
            ENNReal.ofReal K * (if z < y then 1 else 0) + ENNReal.ofReal (G y - m) := ⟨_, fun _ _ => rfl⟩
        obtain ⟨W, hW0, hWs⟩ : ∃ W : ℕ → ℤ → ℝ≥0∞, (∀ z, W 0 z = 0) ∧ ∀ k z, W (k+1) z =
            c z (sSRule s S z) + ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * W k (sSRule s S z - ξ) :=
          ⟨fun k => Nat.rec (fun _ => 0) (fun _ Wk z => c z (sSRule s S z) +
            ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * Wk (sSRule s S z - ξ)) k, fun _ => rfl, fun _ _ => rfl⟩
        obtain ⟨R, hR⟩ : ∃ R : ℕ → ℤ → ℝ≥0∞, ∀ k y, R k y =
            ENNReal.ofReal (G y - m) + ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * W k (y - ξ) := ⟨_, fun _ _ => rfl⟩
        have hWlt : ∀ k z, z < s → W (k+1) z = ENNReal.ofReal K + R k S := by
          intro k z hz
          rw [hWs, hR, hc]
          simp only [sSRule, if_pos hz, if_pos (lt_of_lt_of_le hz hsS), mul_one, hm_def, sub_self,
            ENNReal.ofReal_zero, add_zero, zero_add]
        have hWge : ∀ k z, s ≤ z → W (k+1) z = R k z := by
          intro k z hz
          rw [hWs, hR, hc]
          simp only [sSRule, if_neg (not_lt.2 hz), lt_irrefl, if_false, mul_zero, zero_add]
        have hconst : ∀ k z, z < s → W k z = W k (s-1) := by
          intro k z hz
          cases k with
          | zero => rw [hW0, hW0]
          | succ k => rw [hWlt k z hz, hWlt k (s-1) (by omega)]
        have htsum_const : ∀ a : ℝ≥0∞, ∑' ξ : ℕ, φ ξ * a = a := by
          intro a; rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        have hsum_below : ∀ k y, y ≤ Sb → ∑' ξ : ℕ, φ ξ * W k (y - ξ) = W k (s-1) := by
          intro k y hy
          conv_rhs => rw [← htsum_const (W k (s-1))]
          congr 1; ext ξ
          by_cases hξ : φ ξ = 0
          · simp [hξ]
          · rw [hconst k (y - ξ) (by have := g6 ξ hξ; omega)]
        have hRlow : ∀ k y, y ≤ Sb → R k y = ENNReal.ofReal (G y - m) + ENNReal.ofReal α * W k (s-1) := by
          intro k y hy; rw [hR, hsum_below k y hy]
        have hRS : ∀ k, R k S = ENNReal.ofReal α * W k (s-1) := by
          intro k; rw [hRlow k S hSSb, hm_def, sub_self, ENNReal.ofReal_zero, zero_add]
        have hαle : ENNReal.ofReal α ≤ 1 := by simpa using hα₁
        have hsum_le : ∀ (f g : ℤ → ℝ≥0∞), (∀ ξ : ℕ, f ξ ≤ g ξ + ENNReal.ofReal K) →
            ∑' ξ : ℕ, φ ξ * f ξ ≤ ∑' ξ : ℕ, φ ξ * g ξ + ENNReal.ofReal K := by
          intro f g hfg
          calc ∑' ξ : ℕ, φ ξ * f ξ ≤ ∑' ξ : ℕ, φ ξ * (g ξ + ENNReal.ofReal K) :=
                ENNReal.tsum_le_tsum (fun ξ => by gcongr; exact hfg ξ)
            _ = ∑' ξ : ℕ, φ ξ * g ξ + ENNReal.ofReal K := by
                simp only [mul_add]; rw [ENNReal.tsum_add, htsum_const]
        have hind : ∀ k, (∀ w, W k (s-1) ≤ W k w + ENNReal.ofReal K) ∧
            (∀ z y, z ≤ y → W k z ≤ W k y + ENNReal.ofReal K) := by
          intro k
          induction k with
          | zero => exact ⟨fun w => by simp [hW0], fun z y _ => by simp [hW0]⟩
          | succ k ih =>
            obtain ⟨LA, LW⟩ := ih
            have LS : ∀ y, ENNReal.ofReal α * W k (s-1) ≤ R k y := by
              intro y
              by_cases hy : y ≤ Sb
              · rw [hRlow k y hy]; exact le_add_self
              · rw [hR]
                have h1 := hsum_le (fun ξ => W k (s-1)) (fun ξ => W k (y - ξ)) (fun ξ => LA _)
                rw [htsum_const] at h1
                have h2 : ENNReal.ofReal α * ENNReal.ofReal K ≤ ENNReal.ofReal (G y - m) := by
                  rw [← ENNReal.ofReal_mul hα₀]
                  exact ENNReal.ofReal_le_ofReal (by linarith [g3 y (by omega)])
                calc ENNReal.ofReal α * W k (s-1)
                    ≤ ENNReal.ofReal α * (∑' ξ : ℕ, φ ξ * W k (y - ξ) + ENNReal.ofReal K) :=
                      by gcongr
                  _ = ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * W k (y - ξ) + ENNReal.ofReal α * ENNReal.ofReal K := by
                      rw [mul_add]
                  _ ≤ _ := by rw [add_comm]; gcongr
            have LAs : ∀ w, W (k+1) (s-1) ≤ W (k+1) w + ENNReal.ofReal K := by
              intro w
              rw [hWlt k (s-1) (by omega)]
              by_cases hw : w < s
              · rw [hWlt k w hw]; exact le_self_add
              · rw [hWge k w (not_lt.1 hw), hRS, add_comm (ENNReal.ofReal K)]; gcongr; exact LS w
            refine ⟨LAs, ?_⟩
            intro z y hzy
            by_cases hz : z < s
            · rw [hconst (k+1) z hz]; exact LAs y
            · rw [hWge k z (not_lt.1 hz), hWge k y (by omega)]
              by_cases hzb : z ≤ Sb
              · rw [hRlow k z hzb]
                calc ENNReal.ofReal (G z - m) + ENNReal.ofReal α * W k (s-1)
                    ≤ ENNReal.ofReal K + R k y := by
                      gcongr
                      · linarith [g2 z (not_lt.1 hz) hzb]
                      · exact LS y
                  _ = R k y + ENNReal.ofReal K := add_comm _ _
              · rw [hR, hR]
                have h1 := hsum_le (fun ξ => W k (z - ξ)) (fun ξ => W k (y - ξ)) (fun ξ => LW _ _ (by omega))
                have h2 : ENNReal.ofReal (G z - m) ≤ ENNReal.ofReal (G y - m) :=
                  ENNReal.ofReal_le_ofReal (by linarith [hmono z y (by omega) hzy])
                calc ENNReal.ofReal (G z - m) + ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * W k (z - ξ)
                    ≤ ENNReal.ofReal (G y - m) + ENNReal.ofReal α * (∑' ξ : ℕ, φ ξ * W k (y - ξ) + ENNReal.ofReal K) := by
                      gcongr
                  _ = ENNReal.ofReal (G y - m) + ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * W k (y - ξ) + ENNReal.ofReal α * ENNReal.ofReal K := by
                      rw [mul_add, add_assoc]
                  _ ≤ _ := by
                      gcongr
                      exact mul_le_of_le_one_left zero_le hαle
        -- Bellman inequality
        have hbell : ∀ k z y, z ≤ y → W (k+1) z ≤ c z y + ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * W k (y - ξ) := by
          intro k z y hzy
          obtain ⟨LA, LW⟩ := hind k
          have LS : ∀ y, ENNReal.ofReal α * W k (s-1) ≤ R k y := by
            intro y
            by_cases hy : y ≤ Sb
            · rw [hRlow k y hy]; exact le_add_self
            · rw [hR]
              have h1 := hsum_le (fun ξ => W k (s-1)) (fun ξ => W k (y - ξ)) (fun ξ => LA _)
              rw [htsum_const] at h1
              have h2 : ENNReal.ofReal α * ENNReal.ofReal K ≤ ENNReal.ofReal (G y - m) := by
                rw [← ENNReal.ofReal_mul hα₀]
                exact ENNReal.ofReal_le_ofReal (by linarith [g3 y (by omega)])
              calc ENNReal.ofReal α * W k (s-1)
                  ≤ ENNReal.ofReal α * (∑' ξ : ℕ, φ ξ * W k (y - ξ) + ENNReal.ofReal K) :=
                    by gcongr
                _ = ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * W k (y - ξ) + ENNReal.ofReal α * ENNReal.ofReal K := by
                    rw [mul_add]
                _ ≤ _ := by rw [add_comm]; gcongr
          have hRHS : c z y + ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * W k (y - ξ) =
              ENNReal.ofReal K * (if z < y then 1 else 0) + R k y := by
            rw [hc, hR, add_assoc]
          rw [hRHS]
          by_cases hlt : z < y
          · rw [if_pos hlt, mul_one]
            by_cases hz : z < s
            · rw [hWlt k z hz, hRS]; gcongr; exact LS y
            · rw [hWge k z (not_lt.1 hz), add_comm]
              -- R k z ≤ R k y + K
              have := (hind (k+1)).2 z y hzy
              rwa [hWge k z (not_lt.1 hz), hWge k y (by omega)] at this
          · have hyz : y = z := by omega
            subst hyz
            rw [if_neg (lt_irrefl _), mul_zero, zero_add]
            by_cases hz : y < s
            · rw [hWlt k y hz, hRS, hRlow k y (by omega)]
              gcongr
              linarith [g1 y hz]
            · rw [hWge k y (not_lt.1 hz)]
        have hE0 : ∀ f : (Fin 0 → ℕ) → ℝ≥0∞, ∑' h, weight φ h * f h = f Fin.elim0 := by
          intro f
          rw [tsum_eq_single Fin.elim0 (fun b hb => (hb (Subsingleton.elim _ _)).elim)]
          simp [weight]
        have hmarg : ∀ t (f : (Fin (t+1) → ℕ) → ℝ≥0∞), ∑' h, weight φ h * f h =
            ∑' h : Fin t → ℕ, weight φ h * ∑' ξ : ℕ, φ ξ * f (Fin.snoc h ξ) := by
          intro t f
          rw [← (Fin.snocEquiv (fun _ => ℕ)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
          congr 1; ext h
          rw [← ENNReal.tsum_mul_left]
          congr 1; ext ξ
          show weight φ (Fin.snoc h ξ : Fin (t+1) → ℕ) * f (Fin.snoc h ξ) = _
          simp only [weight, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
          ring
        have hw1 : ∀ t, ∑' h : Fin t → ℕ, weight φ h = 1 := by
          intro t
          induction t with
          | zero => simpa using hE0 (fun _ => 1)
          | succ t ih =>
            have := hmarg t (fun _ => 1)
            simp only [mul_one, PMF.tsum_coe] at this
            rw [this]; exact ih
        have hstate_snoc : ∀ (Y : Policy) x t (h : Fin t → ℕ) (ξ : ℕ),
            state Y x (t+1) (Fin.snoc h ξ) = Y t x h - ξ := by
          intro Y x t h ξ
          simp [state, Fin.init_snoc, Fin.snoc_last]
        obtain ⟨e, he⟩ : ∃ e : Policy → ℤ → ℕ → ℝ≥0∞, ∀ Y x t, e Y x t =
            ∑' h : Fin t → ℕ, weight φ h * c (state Y x t h) (Y t x h) := ⟨_, fun _ _ _ => rfl⟩
        have hA : ∀ (Y : Policy) x k j, ∑ t ∈ Finset.range (k+1), ENNReal.ofReal (α ^ t) * e Y x (j+t) =
            e Y x j + ENNReal.ofReal α * ∑ t ∈ Finset.range k, ENNReal.ofReal (α ^ t) * e Y x (j+1+t) := by
          intro Y x k j
          rw [Finset.sum_range_succ', Finset.mul_sum]
          simp only [pow_zero, ENNReal.ofReal_one, one_mul, Nat.add_zero]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl; intro t _
          rw [← mul_assoc, ← ENNReal.ofReal_mul hα₀, ← pow_succ']
          rw [show j + 1 + t = j + (t + 1) by omega]
        have hB : ∀ (Y : Policy) x j (g : ℤ → ℝ≥0∞), ∑' h : Fin j → ℕ, weight φ h *
            (c (state Y x j h) (Y j x h) + ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * g (Y j x h - ξ)) =
            e Y x j + ENNReal.ofReal α * ∑' h : Fin (j+1) → ℕ, weight φ h * g (state Y x (j+1) h) := by
          intro Y x j g
          rw [hmarg, he]
          simp only [hstate_snoc, mul_add]
          rw [ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
          congr 1; congr 1; ext h; ring
        have htele_le : ∀ (Y : Policy), Admissible Y → ∀ x k j,
            ∑' h : Fin j → ℕ, weight φ h * W k (state Y x j h) ≤
              ∑ t ∈ Finset.range k, ENNReal.ofReal (α ^ t) * e Y x (j+t) := by
          intro Y hY x k
          induction k with
          | zero => intro j; simp [hW0]
          | succ k ih =>
            intro j
            calc ∑' h : Fin j → ℕ, weight φ h * W (k+1) (state Y x j h)
                ≤ ∑' h : Fin j → ℕ, weight φ h * (c (state Y x j h) (Y j x h) +
                    ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * W k (Y j x h - ξ)) :=
                  ENNReal.tsum_le_tsum (fun h => by gcongr; exact hbell k _ _ (hY j x h))
              _ = e Y x j + ENNReal.ofReal α * ∑' h : Fin (j+1) → ℕ, weight φ h * W k (state Y x (j+1) h) :=
                  hB Y x j (W k)
              _ ≤ e Y x j + ENNReal.ofReal α * ∑ t ∈ Finset.range k, ENNReal.ofReal (α ^ t) * e Y x (j+1+t) := by
                  gcongr; exact ih (j+1)
              _ = _ := (hA Y x k j).symm
        have hstat : ∀ x t h, stationary s S t x h = sSRule s S (state (stationary s S) x t h) := by
          intro x t h; cases t <;> rfl
        have htele_ge : ∀ x k j,
            ∑ t ∈ Finset.range k, ENNReal.ofReal (α ^ t) * e (stationary s S) x (j+t) ≤
            ∑' h : Fin j → ℕ, weight φ h * W k (state (stationary s S) x j h) := by
          intro x k
          induction k with
          | zero => intro j; simp
          | succ k ih =>
            intro j
            rw [hA]
            calc e (stationary s S) x j + ENNReal.ofReal α * ∑ t ∈ Finset.range k, ENNReal.ofReal (α ^ t) * e (stationary s S) x (j+1+t)
                ≤ e (stationary s S) x j + ENNReal.ofReal α * ∑' h : Fin (j+1) → ℕ, weight φ h * W k (state (stationary s S) x (j+1) h) := by
                  gcongr; exact ih (j+1)
              _ = ∑' h : Fin j → ℕ, weight φ h * (c (state (stationary s S) x j h) (stationary s S j x h) +
                    ENNReal.ofReal α * ∑' ξ : ℕ, φ ξ * W k (stationary s S j x h - ξ)) :=
                  (hB (stationary s S) x j (W k)).symm
              _ = _ := by
                  congr 1; ext h; rw [hWs, ← hstat]
        have hadm : Admissible (stationary s S) := by
          intro t x h
          rw [hstat]; unfold sSRule; split_ifs <;> omega
        have hdist : ∀ (r : ℝ), 0 ≤ r → ∀ u : ℝ≥0∞, (r:EReal) * ((m:EReal) + (u:EReal)) =
            ((r*m : ℝ):EReal) + ((ENNReal.ofReal r * u : ℝ≥0∞):EReal) := by
          intro r hr u
          rcases eq_or_lt_of_le hr with h0 | hpos
          · subst h0; simp
          by_cases hu : u = ⊤
          · subst hu
            rw [ENNReal.mul_top (by simpa using hpos)]
            simp only [EReal.coe_ennreal_top]
            rw [EReal.coe_add_top, EReal.mul_top_of_pos (by exact_mod_cast hpos)]
            exact (EReal.coe_add_top _).symm
          · rw [← EReal.coe_ennreal_toReal hu, ← EReal.coe_ennreal_toReal (by finiteness)]
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr]
            norm_cast; ring
        have hpt : ∀ g : ℝ, m ≤ g → ENNReal.ofReal g + ENNReal.ofReal (-m) =
            ENNReal.ofReal (g - m) + ENNReal.ofReal (-g) + ENNReal.ofReal m := by
          intro g h
          rcases le_total 0 m with hm | hm
          · rw [ENNReal.ofReal_of_nonpos (by linarith : -m ≤ 0), ENNReal.ofReal_of_nonpos (by linarith : -g ≤ 0), add_zero, add_zero, ← ENNReal.ofReal_add (by linarith) hm]
            simp
          rcases le_total 0 g with hg | hg
          · rw [ENNReal.ofReal_of_nonpos hm, ENNReal.ofReal_of_nonpos (by linarith : -g ≤ 0), ← ENNReal.ofReal_add hg (by linarith)]
            simp; ring_nf
          · rw [ENNReal.ofReal_of_nonpos hm, ENNReal.ofReal_of_nonpos hg, ← ENNReal.ofReal_add (by linarith) (by linarith)]
            simp; ring_nf
        have hpc : ∀ (Y : Policy) x t, periodCost φ G K Y x t = (m : EReal) + (e Y x t : EReal) := by
          intro Y x t
          unfold periodCost expectedG orderProb
          set O := ∑' h : Fin t → ℕ, weight φ h * (if state Y x t h < Y t x h then 1 else 0) with hO_def
          set P := ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (Y t x h)) with hP_def
          set N := ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-G (Y t x h)) with hN_def
          set Q := ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (Y t x h) - m) with hQ_def
          have he' : e Y x t = ENNReal.ofReal K * O + Q := by
            rw [he]; simp only [hc, mul_add]
            rw [ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
            congr 1; congr 1; ext h; ring
          have hid : P + ENNReal.ofReal (-m) = Q + N + ENNReal.ofReal m := by
            have h1 : P + ENNReal.ofReal (-m) = ∑' h : Fin t → ℕ, weight φ h *
                (ENNReal.ofReal (G (Y t x h)) + ENNReal.ofReal (-m)) := by
              simp only [mul_add]; rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hw1, one_mul]
            have h2 : Q + N + ENNReal.ofReal m = ∑' h : Fin t → ℕ, weight φ h *
                (ENNReal.ofReal (G (Y t x h) - m) + ENNReal.ofReal (-G (Y t x h)) + ENNReal.ofReal m) := by
              simp only [mul_add]; rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hw1, one_mul]
            rw [h1, h2]
            congr 1; ext h; rw [hpt _ (hSmem' _)]
          have hN : N ≠ ⊤ := by
            apply ne_top_of_le_ne_top (b := ENNReal.ofReal (-m)) ENNReal.ofReal_ne_top
            calc N ≤ ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-m) :=
                  ENNReal.tsum_le_tsum (fun h => by gcongr; linarith [hSmem' (Y t x h)])
              _ = _ := by rw [ENNReal.tsum_mul_right, hw1, one_mul]
          have hO : O ≠ ⊤ := by
            apply ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top
            calc O ≤ ∑' h : Fin t → ℕ, weight φ h * 1 :=
                  ENNReal.tsum_le_tsum (fun h => by gcongr; split_ifs <;> simp)
              _ = _ := by rw [ENNReal.tsum_mul_right, hw1, one_mul]
          have hKe : (K : EReal) = ((ENNReal.ofReal K : ℝ≥0∞) : EReal) := by
            rw [EReal.coe_ennreal_ofReal, max_eq_left hK]
          rw [hKe, ← EReal.coe_ennreal_mul, he']
          have ha : ENNReal.ofReal K * O ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hO
          by_cases hQ : Q = ⊤
          · have hP : P = ⊤ := by
              rw [hQ, top_add, top_add] at hid
              exact (ENNReal.add_eq_top.1 hid).resolve_right ENNReal.ofReal_ne_top
            rw [hP, hQ, add_top, ← EReal.coe_ennreal_toReal hN, ← EReal.coe_ennreal_toReal ha]
            simp
            rw [← EReal.coe_mul]; exact EReal.coe_add_top _
          · have hP : P ≠ ⊤ := by
              intro hP; rw [hP, top_add] at hid
              exact (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hQ, hN⟩, ENNReal.ofReal_ne_top⟩) hid.symm
            have hr := congrArg ENNReal.toReal hid
            rw [ENNReal.toReal_add hP ENNReal.ofReal_ne_top, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hQ, hN⟩) ENNReal.ofReal_ne_top, ENNReal.toReal_add hQ hN] at hr
            rw [← EReal.coe_ennreal_toReal hP, ← EReal.coe_ennreal_toReal hN,
              ← EReal.coe_ennreal_toReal (ENNReal.add_ne_top.2 ⟨ha, hQ⟩), ← EReal.coe_ennreal_toReal ha,
              ENNReal.toReal_add ha hQ]
            rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at hr
            have : max (-m) 0 - max m 0 = -m := by
              rcases le_total 0 m with h | h
              · rw [max_eq_right (by linarith), max_eq_left h]; ring
              · rw [max_eq_left (by linarith), max_eq_right h]; ring
            norm_cast
            linarith
        have hcost : ∀ (Y : Policy) x n, cost φ G K α n x Y =
            ((∑ t ∈ Finset.range n, α ^ t * m : ℝ) : EReal) +
            ((∑ t ∈ Finset.range n, ENNReal.ofReal (α ^ t) * e Y x t : ℝ≥0∞) : EReal) := by
          intro Y x n
          induction n with
          | zero => simp [cost]
          | succ n ih =>
            simp only [cost] at ih ⊢
            rw [Finset.sum_range_succ, ih, hpc, hdist (α ^ n) (pow_nonneg hα₀ n), Finset.sum_range_succ,
              Finset.sum_range_succ, EReal.coe_add, EReal.coe_ennreal_add, add_add_add_comm]
        have hmain : ∀ Y' : Policy, Admissible Y' → ∀ n x,
            cost φ G K α n x (stationary s S) ≤ cost φ G K α n x Y' := by
          intro Y' hY' n x
          rw [hcost, hcost]
          have h1 := htele_ge x n 0
          have h2 := htele_le Y' hY' x n 0
          rw [hE0] at h1 h2
          simp only [zero_add] at h1 h2
          have h3 := h1.trans h2
          gcongr
          exact_mod_cast h3
        refine ⟨fun n _ => ⟨hadm, fun Y' hY' x => hmain Y' hY' n x⟩, hadm, fun Y' hY' x => ?_⟩
        unfold infCost
        split_ifs with hlt
        · unfold discountedCost
          exact Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => hmain Y' hY' n x))
        · have h1 : α = 1 := le_antisymm hα₁ (not_lt.1 hlt)
          subst h1
          unfold averageCost
          exact Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n =>
            PosMulMono.mul_le_mul_of_nonneg_left (EReal.coe_nonneg.2 (inv_nonneg.2 (Nat.cast_nonneg n)))
              (hmain Y' hY' n x)))
