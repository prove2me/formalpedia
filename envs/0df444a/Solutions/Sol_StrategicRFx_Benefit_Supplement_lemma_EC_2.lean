-- Prove2me | solution 1 for StrategicRFx.Benefit.Supplement.lemma_EC_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:47.147539+00:00
-- url     : https://prove2.me/submissions/f424b58f-4398-4f8f-8bc4-ed08d804a775

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Negotiation

open StrategicRFx
open StrategicRFx.Benefit
open StrategicRFx.Benefit.Supplement

theorem solution (P : Params) (h : Standing P) (t : Fin 2 → ℝ)
    (ht : ∀ i, 0 ≤ t i) (i : Fin 2) (hz : t i = 0)
    (r : Negotiation) (hr : IsPriorityResponse P t r) :
    AcceptedImmediately i r := by
      focus
        obtain ⟨hfeas, hmax, hprio, h2⟩ := hr
        have hoo : other (other i) = i := by fin_cases i <;> rfl
        have hneo : other i ≠ i := by fin_cases i <;> decide
        have hsum : P.Pi - t 0 - t 1 = P.Pi - t (other i) := by
          fin_cases i <;> simp_all [other]
        -- payoff of both
        have hboth_le : P.Pi - t (other i) ≤ (r.payoff P t).1 := by
          have := hmax .both trivial; simpa [Negotiation.payoff, hsum] using this
        cases r with
        | both => trivial
        | bargain j a x y =>
          simp only [AcceptedImmediately]
          have hpr : (Negotiation.bargain j a x y).priority P t ≠ 2 := by
            intro h'; exact absurd (h2 h') (by simp)
          -- strictness: both is not tied
          have hlt : P.Pi - t (other i) < leaderBuyer P j t x y := by
            rcases lt_or_eq_of_le hboth_le with h' | h'
            · simpa [Negotiation.payoff] using h'
            · exfalso
              have := hprio .both trivial (by simpa [Negotiation.payoff, hsum] using h')
              have hp : (Negotiation.both).priority P t = 2 := by simp [Negotiation.priority]
              have hle : (Negotiation.bargain j a x y).priority P t ≤ 2 := by
                unfold Negotiation.priority; dsimp only; split_ifs <;> simp
              omega
          have hj : j = i ∨ j = other i := by fin_cases i <;> fin_cases j <;> simp [other]
          rcases hj with hji | hji
          · subst j
            cases a with
            | true => exact ⟨rfl, rfl⟩
            | false =>
              exfalso
              have hL : IsLeaderSolution P i false t x y := hfeas
              have hRS0 : resSupplier P i false t = 0 := by simp [resSupplier]
              have hAS0 : resSupplier P i true t = 0 := by simp [resSupplier, hz]
              set DR := resBuyer P i false t with hDR
              set DA := resBuyer P i true t with hDA
              have hθo := h.θ_pos (other i)
              have hθo1 := h.θ_lt_one (other i)
              have hφ := h.θ_pos i
              have hφ1 := h.θ_lt_one i
              have hEi := h.PiEx_lt i
              have hAo := h.PiExAt_pos (other i)
              have hAi := h.PiExAt_lt i
              have hDA1 : P.Pi - t (other i) ≤ DA := by
                rw [hDA]; unfold resBuyer; simp only [if_true]; rw [hz]; exact le_trans (by linarith) (le_max_left _ _)
              have hDA2 : P.Pi - P.θ (other i) * (P.Pi - P.PiExAt (other i)) ≤ DA := by
                rw [hDA]; unfold resBuyer; simp [followerSplit, hz]
              have hDRA : DR < DA := by
                rw [hDR]; unfold resBuyer; simp only [Bool.false_eq_true, if_false]
                apply max_lt
                · have k1 := mul_pos (sub_pos.mpr hθo1) (sub_pos.mpr hEi)
                  have k2 := mul_pos hθo hAo
                  linarith only [k1, k2, hDA2]
                · have k1 := mul_pos hθo (sub_pos.mpr hAi)
                  linarith only [k1, hDA1, hEi]
              obtain ⟨xA, yA, hAL⟩ : ∃ xA yA, IsLeaderSolution P i true t xA yA := by
                set D := resBuyer P i true t with hD
                have hDeq : D = max (P.Pi - t (other i)) (P.Pi - P.θ (other i) * (P.Pi - P.PiExAt (other i))) := by
                  rw [hD]; simp [resBuyer, followerSplit, hz]
                have hθo := h.θ_pos (other i)
                have hθo1 := h.θ_lt_one (other i)
                have hφ := h.θ_pos i
                have hφ1 := h.θ_lt_one i
                have hT := ht (other i)
                have hEA := h.PiExAt_lt (other i)
                let g : ℝ → ℝ := fun π => leaderBuyer P i t π (min (P.PiEx (other i)) (P.Pi - π))
                have hgc : Continuous g := by
                  show Continuous fun π => leaderBuyer P i t π (min (P.PiEx (other i)) (P.Pi - π))
                  unfold leaderBuyer followerSplit; fun_prop
                have hg_le : ∀ π, g π ≤ P.Pi - π := by
                  intro π; show leaderBuyer P i t π _ ≤ _
                  unfold leaderBuyer followerSplit
                  have : 0 ≤ P.Pi - π - min (P.PiEx (other i)) (P.Pi - π) := by
                    have := min_le_right (P.PiEx (other i)) (P.Pi - π); linarith
                  have : 0 ≤ min (t (other i)) (P.θ (other i) * (P.Pi - π - min (P.PiEx (other i)) (P.Pi - π))) :=
                    le_min hT (mul_nonneg hθo.le this)
                  linarith
                have hg_ge : ∀ x y, leaderFeasible P i true t x y → leaderBuyer P i t x y ≤ g x := by
                  intro x y hf
                  show _ ≤ leaderBuyer P i t x _
                  unfold leaderBuyer followerSplit
                  have h1 := hf.1; have h2 := hf.2.1
                  have : y ≤ min (P.PiEx (other i)) (P.Pi - x) := le_min h2 (by linarith)
                  have : P.θ (other i) * (P.Pi - x - min (P.PiEx (other i)) (P.Pi - x)) ≤ P.θ (other i) * (P.Pi - x - y) :=
                    mul_le_mul_of_nonneg_left (by linarith) hθo.le
                  have := min_le_min_left (t (other i)) this
                  linarith
                let S : Set ℝ := Set.Icc 0 (P.Pi - D) ∩ {π | D ≤ g π}
                have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_le continuous_const hgc)
                have hg0 : D ≤ g 0 := by
                  show D ≤ leaderBuyer P i t 0 _
                  have hE := h.PiEx_lt (other i)
                  have hm : min (P.PiEx (other i)) (P.Pi - 0) = P.PiEx (other i) := min_eq_left (by linarith)
                  unfold leaderBuyer followerSplit; rw [hm, hDeq]
                  rcases min_choice (t (other i)) (P.θ (other i) * (P.Pi - 0 - P.PiEx (other i))) with hc | hc <;>
                    rw [hc] <;> apply max_le <;> linarith only [min_le_left (t (other i)) (P.θ (other i) * (P.Pi - 0 - P.PiEx (other i))), min_le_right (t (other i)) (P.θ (other i) * (P.Pi - 0 - P.PiEx (other i))), hc, mul_lt_mul_of_pos_left hEA hθo]
                have h0 : (0:ℝ) ∈ S := by
                  refine ⟨⟨le_rfl, ?_⟩, hg0⟩
                  have := hg_le 0
                  linarith
                let f : ℝ → ℝ := fun π => nashProduct (P.θ i) (π - 0) (g π - D)
                have hfc : ContinuousOn f S := by
                  apply Continuous.continuousOn
                  show Continuous fun π => (π - 0) ^ (P.θ i) * (g π - D) ^ (1 - P.θ i)
                  have h1 : 0 ≤ P.θ i := hφ.le
                  have h2 : 0 ≤ 1 - P.θ i := by linarith
                  fun_prop
                obtain ⟨π0, hπ0S, hmaxon⟩ := hS.exists_isMaxOn ⟨0, h0⟩ hfc
                refine ⟨π0, min (P.PiEx (other i)) (P.Pi - π0), ⟨?_, min_le_left _ _, ?_, ?_⟩, ?_⟩
                · have := min_le_right (P.PiEx (other i)) (P.Pi - π0); linarith
                · simp only [resSupplier, if_true, hz]; exact hπ0S.1.1
                · exact hπ0S.2
                · intro x y hf
                  have hxS : x ∈ S := by
                    have := hg_ge x y hf
                    have := hg_le x
                    have := hf.2.2.2
                    have := hf.2.2.1
                    simp only [resSupplier, if_true, hz] at this
                    exact ⟨⟨this, by linarith⟩, by show D ≤ g x; linarith⟩
                  have hm := hmaxon hxS
                  simp only [Set.mem_ofPred_eq] at hm
                  have hres : resSupplier P i true t = 0 := by simp [resSupplier, hz]
                  rw [hres, ← hD]
                  refine le_trans ?_ hm
                  show nashProduct _ _ _ ≤ nashProduct _ _ _
                  unfold nashProduct
                  have hx0 : 0 ≤ x - 0 := by have := hf.2.2.1; rw [hres] at this; linarith
                  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx0 _)
                  apply Real.rpow_le_rpow (by linarith [hf.2.2.2]) (by linarith [hg_ge x y hf]) (by linarith)
              set BA := leaderBuyer P i t xA yA with hBA
              set BR := leaderBuyer P i t x y with hBR
              have hBAD : DA ≤ BA := hAL.1.2.2.2
              have hBRD : DR ≤ BR := hL.1.2.2.2
              have key : BR ≤ BA := by
                by_contra hcon
                push Not at hcon
                have hRA : leaderFeasible P i true t x y :=
                  ⟨hL.1.1, hL.1.2.1, by have := hL.1.2.2.1; rw [hRS0] at this; rw [hAS0]; exact this, by linarith⟩
                have hAR : leaderFeasible P i false t xA yA :=
                  ⟨hAL.1.1, hAL.1.2.1, by have := hAL.1.2.2.1; rw [hAS0] at this; rw [hRS0]; exact this, by linarith⟩
                have h1 := hAL.2 x y hRA
                have h2 := hL.2 xA yA hAR
                rw [hAS0, ← hBR, ← hBA] at h1
                rw [hRS0, ← hBR, ← hBA] at h2
                simp only [nashProduct, sub_zero] at h1 h2
                have hx0 : 0 ≤ x := by have := hL.1.2.2.1; rwa [hRS0] at this
                have hxA0 : 0 ≤ xA := by have := hAL.1.2.2.1; rwa [hAS0] at this
                have hp : 0 < 1 - P.θ i := by linarith
                -- xA > 0
                have hxApos : 0 < xA := by
                  rcases lt_or_eq_of_le hxA0 with h' | h'
                  · exact h'
                  · exfalso
                    set ε := (BR - DA) / 2 with hε
                    have hεpos : 0 < ε := by rw [hε]; linarith
                    have hfe : leaderFeasible P i true t (x + ε) (y - ε) := by
                      refine ⟨by have := hL.1.1; linarith, by have := hL.1.2.1; linarith, by rw [hAS0]; linarith, ?_⟩
                      have : leaderBuyer P i t (x + ε) (y - ε) = BR - ε := by
                        rw [hBR]; unfold leaderBuyer followerSplit; ring_nf
                      rw [this]; linarith
                    have h3 := hAL.2 _ _ hfe
                    have : leaderBuyer P i t (x + ε) (y - ε) = BR - ε := by
                      rw [hBR]; unfold leaderBuyer followerSplit; ring_nf
                    rw [this, hAS0, ← h', ← hDA] at h3
                    simp only [nashProduct, sub_zero, Real.zero_rpow hφ.ne', zero_mul] at h3
                    have : 0 < (x + ε) ^ P.θ i * (BR - ε - DA) ^ (1 - P.θ i) :=
                      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (by linarith) _)
                    linarith
                have hxpos : 0 < x := by
                  rcases lt_or_eq_of_le hx0 with h' | h'
                  · exact h'
                  · exfalso
                    rw [← h', Real.zero_rpow hφ.ne', zero_mul] at h2
                    have : 0 < xA ^ P.θ i * (BA - DR) ^ (1 - P.θ i) :=
                      mul_pos (Real.rpow_pos_of_pos hxApos _) (Real.rpow_pos_of_pos (by linarith) _)
                    linarith
                rw [← hDA] at h1
                rw [← hDR] at h2
                have hm := mul_le_mul h1 h2 (mul_nonneg (Real.rpow_nonneg hxA0 _) (Real.rpow_nonneg (by linarith) _)) (mul_nonneg (Real.rpow_nonneg hxA0 _) (Real.rpow_nonneg (by linarith) _))
                have e1 : x ^ P.θ i * (BR - DA) ^ (1 - P.θ i) * (xA ^ P.θ i * (BA - DR) ^ (1 - P.θ i))
                    = (x ^ P.θ i * xA ^ P.θ i) * ((BR - DA) * (BA - DR)) ^ (1 - P.θ i) := by
                  rw [Real.mul_rpow (by linarith) (by linarith)]; ring
                have e2 : xA ^ P.θ i * (BA - DA) ^ (1 - P.θ i) * (x ^ P.θ i * (BR - DR) ^ (1 - P.θ i))
                    = (x ^ P.θ i * xA ^ P.θ i) * ((BA - DA) * (BR - DR)) ^ (1 - P.θ i) := by
                  rw [Real.mul_rpow (by linarith) (by linarith)]; ring
                rw [e1, e2] at hm
                have hc : 0 < x ^ P.θ i * xA ^ P.θ i :=
                  mul_pos (Real.rpow_pos_of_pos hxpos _) (Real.rpow_pos_of_pos hxApos _)
                have hm2 := le_of_mul_le_mul_left hm hc
                have hm3 : (BR - DA) * (BA - DR) ≤ (BA - DA) * (BR - DR) := by
                  by_contra hh
                  push Not at hh
                  have := Real.rpow_lt_rpow (mul_nonneg (by linarith only [hcon, hBAD]) (by linarith only [hBRD, hDRA, hBAD, hcon])) hh hp
                  linarith
                have hpp := mul_pos (sub_pos.mpr hDRA) (sub_pos.mpr hcon)
                linarith only [hm3, hpp]
              have hs := hmax (.bargain i true xA yA) hAL
              have hs' := hprio (.bargain i true xA yA) hAL (by
                simp only [Negotiation.payoff]; exact le_antisymm (by simpa [Negotiation.payoff] using hs) key)
              have hpr0 : (Negotiation.bargain i false x y).priority P t = 0 := by
                unfold Negotiation.priority; simp
              have hps : 1 ≤ (Negotiation.bargain i true xA yA).priority P t := by
                unfold Negotiation.priority; dsimp only
                split_ifs with hh1 hh2 <;> first | exact absurd rfl hh2 | norm_num
              omega
          · subst j
            exfalso
            have hL : IsLeaderSolution P (other i) a t x y := hfeas
            have hF : 0 ≤ P.Pi - x - y := hL.1.1
            have hacc : AcceptsFollower P (other i) t x y := by
              unfold AcceptsFollower followerSplit; rw [hoo, hz]
              exact mul_nonneg (h.θ_pos _).le hF
            cases a with
            | true =>
              apply hpr; unfold Negotiation.priority; simp [hacc]
            | false =>
              obtain ⟨u0, y0, hsol, hge⟩ : ∃ u0 y0, IsLeaderSolution P i true t u0 y0 ∧
                  leaderBuyer P (other i) t x y ≤ leaderBuyer P i t u0 y0 := by
                have hθo := h.θ_pos (other i)
                have hθo1 := h.θ_lt_one (other i)
                have hφ := h.θ_pos i
                have hφ1 := h.θ_lt_one i
                have hT := ht (other i)
                have hEA := h.PiExAt_lt (other i)
                have hEAi := h.PiExAt_lt i
                have hE := h.PiEx_lt (other i)
                have hAj := h.PiExAt_pos (other i)
                have hAi := h.PiExAt_pos i
                have hres0 : resSupplier P (other i) false t = 0 := by simp [resSupplier]
                have hDj : resBuyer P (other i) false t = (1 - P.θ i) * P.PiEx (other i) + P.θ i * P.PiExAt (other i) := by
                  unfold resBuyer; simp only [Bool.false_eq_true, if_false]; rw [hoo, hz]
                  have := mul_pos hφ hAj
                  rw [sub_zero]; apply max_eq_right; linarith
                have hLB : ∀ x' y', 0 ≤ P.Pi - x' - y' → leaderBuyer P (other i) t x' y' = P.Pi - x' := by
                  intro x' y' hs; unfold leaderBuyer followerSplit; rw [hoo, hz, min_eq_left (mul_nonneg (h.θ_pos _).le hs)]; ring
                set Dj := (1 - P.θ i) * P.PiEx (other i) + P.θ i * P.PiExAt (other i) with hDjdef
                set K := P.Pi - Dj with hK
                have hKpos : 0 < K := by rw [hK, hDjdef]; linarith only [hE, mul_pos hφ (sub_pos.mpr hEA)]
                have hDjpos : 0 < Dj := by rw [hDjdef]; linarith only [mul_pos (sub_pos.mpr hφ1) (hAj.trans hEA), mul_pos hφ hAj]
                set φ := P.θ (other i) with hφdef
                set x0 := φ * K with hx0
                have hrB : leaderBuyer P (other i) t x y = P.Pi - x := hLB x y hL.1.1
                have hx0x : x0 ≤ x := by
                  have hxnn : 0 ≤ x := by have := hL.1.2.2.1; rwa [hres0] at this
                  have hKx : 0 ≤ K - x := by have := hL.1.2.2.2; rw [hDj, hrB] at this; rw [hK]; linarith
                  have hKx0 : 0 < K - x0 := by rw [hx0]; linarith only [mul_pos (sub_pos.mpr hθo1) hKpos]
                  have hs0 : 0 ≤ P.Pi - x0 - 0 := by linarith only [hKx0, hDjpos, hK]
                  have hf0 : leaderFeasible P (other i) false t x0 0 := by
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · exact hs0
                    · rw [hoo]; linarith
                    · rw [hres0]; positivity
                    · rw [hDj, hLB _ _ hs0]; linarith only [hKx0, hK]
                  have h1 := hL.2 x0 0 hf0
                  rw [hres0, hDj, hLB _ _ hs0, hrB] at h1
                  simp only [nashProduct, sub_zero] at h1
                  rw [show P.Pi - x0 - Dj = K - x0 by rw [hK]; ring, show P.Pi - x - Dj = K - x by rw [hK]; ring] at h1
                  by_contra hcon
                  push Not at hcon
                  have hx0p : 0 < x0 := by positivity
                  have hs := Real.geom_mean_lt_arith_mean_weighted_iff_of_pos Finset.univ ![φ, 1 - φ] ![x / x0, (K - x) / (K - x0)]
                    (by intro k _; fin_cases k <;> simp <;> linarith) (by simp [Fin.sum_univ_two])
                    (by intro k _; fin_cases k <;> simp <;> positivity)
                  simp only [Fin.sum_univ_two, Fin.prod_univ_two] at hs
                  simp at hs
                  have hne : x / x0 ≠ (K - x) / (K - x0) := by
                    intro he
                    rw [div_eq_div_iff hx0p.ne' hKx0.ne'] at he
                    rw [hx0] at he hcon
                    have : x * (K - φ * K) - (K - x) * (φ * K) = (x - φ * K) * K := by ring
                    have k1 := mul_pos (sub_pos.mpr hcon) hKpos
                    linarith only [k1, this, he]
                  have hlt2 := hs.2 (Or.inl hne)
                  have hsum1 : φ * (x / x0) + (1 - φ) * ((K - x) / (K - x0)) = 1 := by
                    rw [hx0, show K - φ * K = (1 - φ) * K by ring]
                    have : (1 - φ) ≠ 0 := by linarith
                    field_simp; ring
                  rw [hsum1, Real.div_rpow hxnn hx0p.le, Real.div_rpow hKx hKx0.le, div_mul_div_comm,
                    div_lt_one (mul_pos (Real.rpow_pos_of_pos hx0p _) (Real.rpow_pos_of_pos hKx0 _))] at hlt2
                  linarith
                have hxT : x < t (other i) := by rw [hrB] at hlt; linarith
                set θ := P.θ i with hθdef
                set E := P.PiEx (other i) with hEdef
                set Aj := P.PiExAt (other i) with hAjdef
                set T := t (other i) with hTdef
                have hTφ : φ * (P.Pi - E) < T := by
                  have : P.Pi - E < K := by rw [hK, hDjdef]; linarith only [mul_pos hφ (sub_pos.mpr hEA)]
                  have := mul_lt_mul_of_pos_left this hθo
                  linarith
                set D := resBuyer P i true t with hD
                have hDeq : D = max (P.Pi - T) (P.Pi - φ * (P.Pi - Aj)) := by
                  rw [hD]; simp [resBuyer, followerSplit, hz]; rfl
                have hD1 : P.Pi - φ * (P.Pi - Aj) ≤ D := by rw [hDeq]; exact le_max_right _ _
                have hDlt : D < (1 - φ) * P.Pi + φ * E := by
                  have := mul_lt_mul_of_pos_left hEA hθo
                  rw [hDeq]; apply max_lt
                  · linarith
                  · linarith
                have hPD : 0 < P.Pi - D := by
                  have hTp : 0 < T := by have := mul_pos hθo (show 0 < P.Pi - E by linarith); linarith
                  have := mul_pos hθo (show 0 < P.Pi - Aj by linarith)
                  have := max_lt (show P.Pi - T < P.Pi by linarith) (show P.Pi - φ * (P.Pi - Aj) < P.Pi by linarith)
                  rw [hDeq]; linarith
                set G := (1 - φ) * P.Pi + φ * E - D with hGdef
                have hG : 0 < G := by rw [hGdef]; linarith
                have hres : resSupplier P i true t = 0 := by simp [resSupplier, hz]
                have hbounds : ∀ x' y', leaderFeasible P i true t x' y' →
                    leaderBuyer P i t x' y' ≤ P.Pi - x' ∧ leaderBuyer P i t x' y' ≤ (1 - φ) * (P.Pi - x') + φ * E := by
                  intro x' y' hf
                  have hs := hf.1; have hy := hf.2.1
                  have hx' : 0 ≤ x' := by have := hf.2.2.1; rwa [hres] at this
                  have hlb : leaderBuyer P i t x' y' = P.Pi - x' - min T (φ * (P.Pi - x' - y')) := rfl
                  rw [hlb]
                  have hm0 : 0 ≤ min T (φ * (P.Pi - x' - y')) := le_min hT (mul_nonneg hθo.le hs)
                  have hm1 : φ * (P.Pi - x' - E) ≤ min T (φ * (P.Pi - x' - y')) := by
                    apply le_min
                    · have := mul_le_mul_of_nonneg_left (show P.Pi - x' - E ≤ P.Pi - E by linarith) hθo.le; linarith
                    · exact mul_le_mul_of_nonneg_left (by linarith) hθo.le
                  constructor <;> linarith
                have amgm : ∀ u0 v0 u v : ℝ, 0 < u0 → 0 < v0 → 0 ≤ u → 0 ≤ v →
                    θ * (u / u0) + (1 - θ) * (v / v0) ≤ 1 → u ^ θ * v ^ (1 - θ) ≤ u0 ^ θ * v0 ^ (1 - θ) := by
                  intro u0 v0 u v hu0 hv0 hu hv hl
                  have := Real.geom_mean_le_arith_mean2_weighted (w₁ := θ) (w₂ := 1 - θ) (p₁ := u / u0) (p₂ := v / v0)
                    hφ.le (by linarith) (by positivity) (by positivity) (by ring)
                  rw [Real.div_rpow hu hu0.le, Real.div_rpow hv hv0.le, div_mul_div_comm] at this
                  have := le_trans this hl
                  rwa [div_le_one (mul_pos (Real.rpow_pos_of_pos hu0 _) (Real.rpow_pos_of_pos hv0 _))] at this
                have cand : ∀ u0 y0, leaderFeasible P i true t u0 y0 → 0 < u0 → 0 < leaderBuyer P i t u0 y0 - D →
                    (∀ u v, 0 ≤ u → 0 ≤ v → v ≤ P.Pi - D - u → v ≤ G - (1 - φ) * u →
                      θ * (u / u0) + (1 - θ) * (v / (leaderBuyer P i t u0 y0 - D)) ≤ 1) →
                    IsLeaderSolution P i true t u0 y0 := by
                  intro u0 y0 hf hu0 hv0 hlin
                  refine ⟨hf, fun x' y' hf' => ?_⟩
                  rw [hres, ← hD]
                  unfold nashProduct; simp only [sub_zero]
                  have hx' : 0 ≤ x' := by have := hf'.2.2.1; rwa [hres] at this
                  have hb := hbounds x' y' hf'
                  have hDB := hf'.2.2.2
                  rw [← hD] at hDB
                  apply amgm _ _ _ _ hu0 hv0 hx' (by linarith)
                  apply hlin _ _ hx' (by linarith) (by linarith) (by rw [hGdef]; linarith)
                have hxx : P.Pi - x ≤ P.Pi - x0 := by linarith
                rw [hrB]
                have hGd : G = (1-φ)*P.Pi + φ*E - D := hGdef
                have hx0K : x0 = φ * (P.Pi - ((1-θ)*E + θ*Aj)) := rfl
                have hDD1 : 0 ≤ θ * (D - (P.Pi - φ * (P.Pi - Aj))) := mul_nonneg hφ.le (by linarith)
                have h1φ : 0 < 1 - φ := by linarith
                by_cases ha : θ * G / (1 - φ) ≤ P.Pi - E
                · set u0 := θ * G / (1 - φ) with hu0
                  have hu0p : 0 < u0 := by rw [hu0]; positivity
                  have hu0G : (1 - φ) * u0 = θ * G := by rw [hu0]; field_simp
                  have hlB : leaderBuyer P i t u0 E = P.Pi - u0 - φ * (P.Pi - u0 - E) := by
                    have h1 : φ * (P.Pi - u0 - E) ≤ T := by
                      have := mul_le_mul_of_nonneg_left (show P.Pi - u0 - E ≤ P.Pi - E by linarith) hθo.le; linarith
                    show P.Pi - u0 - min T (φ * (P.Pi - u0 - E)) = _
                    rw [min_eq_right h1]
                  have hv0 : leaderBuyer P i t u0 E - D = (1 - θ) * G := by
                    rw [hlB]; linear_combination (-1:ℝ) * hGd - hu0G
                  have hv0p : 0 < (1-θ)*G := mul_pos (by linarith) hG
                  have hf : leaderFeasible P i true t u0 E := by
                    refine ⟨?_, le_rfl, ?_, ?_⟩
                    · show 0 ≤ P.Pi - u0 - E; linarith only [ha]
                    · rw [hres]; exact hu0p.le
                    · show D ≤ leaderBuyer P i t u0 E; linarith only [hv0, hv0p]
                  refine ⟨u0, E, cand u0 E hf hu0p (by rw [hv0]; exact hv0p) ?_, ?_⟩
                  · intro u v hu hv h1 h2
                    rw [hv0]
                    have hne1 : (1 - θ) ≠ 0 := by linarith
                    have hne2 : θ ≠ 0 := hφ.ne'
                    have hne3 : G ≠ 0 := hG.ne'
                    have hne4 : 1 - φ ≠ 0 := h1φ.ne'
                    have : θ * (u / u0) + (1 - θ) * (v / ((1 - θ) * G)) = ((1 - φ) * u + v) / G := by
                      rw [hu0]; field_simp
                    rw [this, div_le_one hG]; linarith
                  · have hθG : θ * G = θ * ((1-φ)*P.Pi + φ*E - D) := by rw [hGd]
                    rw [hx0K] at hxx
                    have hlB2 : leaderBuyer P i t u0 E = D + (1 - θ) * G := by linarith only [hv0]
                    rw [hlB2]
                    linear_combination hxx + hDD1 + hθG
                by_cases hb : P.Pi - E ≤ θ * (P.Pi - D)
                · set u0 := θ * (P.Pi - D) with hu0
                  have hu0p : 0 < u0 := by rw [hu0]; positivity
                  have hlB : leaderBuyer P i t u0 (P.Pi - u0) = P.Pi - u0 := by
                    show P.Pi - u0 - min T (φ * (P.Pi - u0 - (P.Pi - u0))) = _
                    rw [show P.Pi - u0 - (P.Pi - u0) = 0 by ring, mul_zero, min_eq_right hT]; ring
                  have hv0 : leaderBuyer P i t u0 (P.Pi - u0) - D = (1 - θ) * (P.Pi - D) := by rw [hlB, hu0]; ring
                  have hv0p : 0 < (1-θ)*(P.Pi - D) := mul_pos (by linarith) hPD
                  have hf : leaderFeasible P i true t u0 (P.Pi - u0) := by
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · show 0 ≤ P.Pi - u0 - (P.Pi - u0); linarith
                    · show P.Pi - u0 ≤ E; linarith
                    · rw [hres]; exact hu0p.le
                    · show D ≤ leaderBuyer P i t u0 (P.Pi - u0); linarith only [hv0, hv0p]
                  refine ⟨u0, P.Pi - u0, cand u0 _ hf hu0p (by rw [hv0]; exact hv0p) ?_, ?_⟩
                  · intro u v hu hv h1 h2
                    rw [hv0]
                    have hne1 : (1 - θ) ≠ 0 := by linarith
                    have hne2 : θ ≠ 0 := hφ.ne'
                    have hne3 : P.Pi - D ≠ 0 := hPD.ne'
                    have : θ * (u / u0) + (1 - θ) * (v / ((1 - θ) * (P.Pi - D))) = (u + v) / (P.Pi - D) := by
                      rw [hu0]; field_simp
                    rw [this, div_le_one hPD]; linarith
                  · rw [hlB]
                    have : 0 ≤ φ * (1 - θ) * (P.Pi - E) := mul_nonneg (mul_nonneg hθo.le (by linarith)) (by linarith)
                    rw [hx0K] at hxx
                    rw [hu0]; linarith
                · push Not at ha hb
                  have ha' : (1 - φ) * (P.Pi - E) < θ * G := by
                    rw [lt_div_iff₀ h1φ] at ha; linarith
                  have hGle : G ≤ φ * (E - Aj) := by rw [hGd]; linarith
                  have hED : 0 < E - D := by
                    have : θ * G < G := by have := mul_lt_mul_of_pos_right hφ1 hG; linarith
                    rw [hGd] at this ha'; linarith
                  have hu0p : 0 < P.Pi - E := by linarith
                  have hlB : leaderBuyer P i t (P.Pi - E) E = E := by
                    show P.Pi - (P.Pi - E) - min T (φ * (P.Pi - (P.Pi - E) - E)) = _
                    rw [show P.Pi - (P.Pi - E) - E = 0 by ring, mul_zero, min_eq_right hT]; ring
                  have hf : leaderFeasible P i true t (P.Pi - E) E := by
                    refine ⟨?_, le_rfl, ?_, ?_⟩
                    · show 0 ≤ P.Pi - (P.Pi - E) - E; linarith
                    · rw [hres]; exact hu0p.le
                    · show D ≤ leaderBuyer P i t (P.Pi - E) E; rw [hlB]; linarith
                  refine ⟨P.Pi - E, E, cand _ E hf hu0p (by rw [hlB]; linarith) ?_, ?_⟩
                  · intro u v hu hv h1 h2
                    rw [hlB]
                    have hne1 : P.Pi - E ≠ 0 := hu0p.ne'
                    have hne2 : E - D ≠ 0 := hED.ne'
                    have : θ * (u / (P.Pi - E)) + (1 - θ) * (v / (E - D)) =
                        (θ * u * (E - D) + (1 - θ) * v * (P.Pi - E)) / ((P.Pi - E) * (E - D)) := by
                      field_simp
                    rw [this, div_le_one (mul_pos hu0p hED)]
                    have hGe : G = (E - D) + (1 - φ) * (P.Pi - E) := by rw [hGd]; ring
                    have h1θ : 0 ≤ (1 - θ) * (P.Pi - E) := mul_nonneg (by linarith) hu0p.le
                    rcases le_total u (P.Pi - E) with hu' | hu'
                    · have k1 := mul_nonneg (sub_nonneg.mpr hu') (show 0 ≤ θ * G - (1 - φ) * (P.Pi - E) by linarith)
                      have k2 := mul_le_mul_of_nonneg_left h2 h1θ
                      rw [hGe] at k1 k2
                      linear_combination k1 + k2
                    · have hθe : θ * (E - D) ≤ (1 - θ) * (P.Pi - E) := by
                        have : θ * (P.Pi - D) = θ * (P.Pi - E) + θ * (E - D) := by ring
                        linarith
                      have k1 := mul_nonneg (sub_nonneg.mpr hu') (show 0 ≤ (1 - θ) * (P.Pi - E) - θ * (E - D) by linarith)
                      have k2 := mul_le_mul_of_nonneg_left h1 h1θ
                      linear_combination k1 + k2
                  · rw [hlB]
                    have := mul_le_mul_of_nonneg_left hGle hφ.le
                    rw [hx0K] at hxx
                    linarith
              have hs := hmax (.bargain i true u0 y0) hsol
              have hs' := hprio (.bargain i true u0 y0) hsol
                (le_antisymm (by simpa [Negotiation.payoff] using hs) (by simpa [Negotiation.payoff] using hge))
              have hpr0 : (Negotiation.bargain (other i) false x y).priority P t = 0 := by
                unfold Negotiation.priority; simp
              have hps : 1 ≤ (Negotiation.bargain i true u0 y0).priority P t := by
                unfold Negotiation.priority; dsimp only
                split_ifs with hh1 hh2 <;> first | exact absurd rfl hh2 | norm_num
              omega
