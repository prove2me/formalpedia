-- Prove2me | solution 1 for RobustPrefLearn.MTP.Supplement.theorem_b5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:09.012621+00:00
-- url     : https://prove2.me/submissions/bada82d0-24f3-40ca-8968-71a71685fc3d

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Supplement_Dueling

open scoped ENNReal

open RobustPrefLearn
open RobustPrefLearn.MTP
open RobustPrefLearn.MTP.Supplement

/-- Appendix B.5, p.49. Corrected domain 0 < δ ≤ 1/2; the printed
δ ∈ (0,1) is refuted by the one-vote, uniform-pair policy recorded in DISPROOF.md.
No extra positivity assumption on the information is imposed. -/
theorem solution (K : ℕ) (hK : 2 ≤ K) (δ : ℝ) (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (P : Comparison K) (hP : P ∈ ComparisonClass K) (π : Policy K)
    (hπ : DuelingPAC δ π) :
    ENNReal.ofReal (kl δ (1 - δ)) / duelingInfo P ≤ expTau π (duelingPref P) := by
      classical
      set f := duelingPref P with hf
      -- expected number of displays of S before stopping
      set N : DS K → ℝ≥0∞ := fun S => ∑' t : ℕ, ∑ v : Fin t → Step K,
        if survives π (toHist v) then pathProb π f (toHist v) * π.disp (toHist v) S else 0 with hN
      set KLS : Comparison K → DS K → ℝ := fun Q S =>
        ∑ i, ∑ j, if i < j ∧ S.1 = {i, j} then kl (P i j) (Q i j) else 0 with hKLS
      have hNsum : ∑ S, N S = expTau π f := by
        simp only [hN, expTau, probGT]
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        congr 1; ext t
        rw [Finset.sum_comm]
        congr 1; ext v
        split_ifs
        · rw [← Finset.mul_sum, hπ.1.1 (toHist v), mul_one]
        · simp
      have hNpair : ∀ S : DS K, S.1.card ≠ 2 → N S = 0 := by
        intro S hS
        simp [hN, hπ.1.2 _ S hS]
      have hkl_nonneg : ∀ x y : ℝ, 0 < x → x < 1 → 0 < y → y < 1 → 0 ≤ kl x y := by
        intro x y hx0 hx1 hy0 hy1
        have h1 := InformationTheory.klFun_nonneg (le_of_lt (div_pos hx0 hy0))
        have h2 := InformationTheory.klFun_nonneg (le_of_lt (div_pos (sub_pos.2 hx1) (sub_pos.2 hy1)))
        have : kl x y = y * InformationTheory.klFun (x / y)
            + (1 - y) * InformationTheory.klFun ((1 - x) / (1 - y)) := by
          unfold kl InformationTheory.klFun
          have hy1' : (1 - y) ≠ 0 := by linarith
          field_simp
          ring
        rw [this]
        have : 0 < 1 - y := by linarith
        positivity
      have hClass01 : ∀ Q ∈ ComparisonClass K, ∀ i j, 0 < Q i j ∧ Q i j < 1 := by
        intro Q hQ i j
        obtain ⟨h1, h2⟩ := hQ.1 i j
        have h3 := (hQ.1 j i).1
        exact ⟨h1, by linarith⟩
      have hKLS_nonneg : ∀ Q ∈ ComparisonClass K, ∀ S, 0 ≤ KLS Q S := by
        intro Q hQ S
        apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
        split_ifs
        · exact hkl_nonneg _ _ (hClass01 P hP i j).1 (hClass01 P hP i j).2
            (hClass01 Q hQ i j).1 (hClass01 Q hQ i j).2
        · exact le_rfl
      have hAltNe : ∃ Q, Q ∈ duelingAlt P := by
        obtain ⟨i, hi⟩ := hP.2
        obtain ⟨j, hji⟩ : ∃ j : Fin K, j ≠ i := by
          by_cases h0 : i.val = 0
          · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at h0; simp at h0⟩
          · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [← h])⟩
        set Q : Comparison K := fun a b =>
          if a = b then 1/2 else if a = j then 3/4 else if b = j then 1/4 else 1/2 with hQdef
        have hK1 : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
        have hcard : ∀ k : Fin K, ((Finset.univ.erase k).card : ℝ) = (K : ℝ) - 1 := by
          intro k; rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, Nat.cast_sub (by omega)]; simp
        have hsj : bordaScore Q j = 3/4 := by
          unfold bordaScore
          rw [Finset.sum_congr rfl (g := fun _ => (3/4 : ℝ)) (fun b hb => by
            have : j ≠ b := fun h => (Finset.mem_erase.1 hb).1 h.symm
            simp [hQdef, this])]
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
          have : (K : ℝ) - 1 ≠ 0 := by linarith
          field_simp
        have hsk : ∀ k, k ≠ j → bordaScore Q k < 3/4 := by
          intro k hk
          unfold bordaScore
          rw [Finset.sum_congr rfl (g := fun b => (1/2 : ℝ) - if b = j then 1/4 else 0) (fun b hb => by
            have : k ≠ b := fun h => (Finset.mem_erase.1 hb).1 h.symm
            by_cases hbj : b = j
            · simp [hQdef, this, hk, hbj]; norm_num
            · simp [hQdef, this, hk, hbj])]
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard,
            Finset.sum_ite_eq' , if_pos (Finset.mem_erase.2 ⟨fun h => hk h.symm, Finset.mem_univ _⟩)]
          rw [div_lt_iff₀ (by linarith)]
          nlinarith
        refine ⟨Q, ⟨fun a b => ?_, j, fun k hk => by rw [hsj]; exact hsk k hk⟩, fun i' hi' hQi' => ?_⟩
        · constructor
          · simp only [hQdef]; split_ifs <;> norm_num
          · simp only [hQdef]
            by_cases hab : a = b
            · subst hab; norm_num
            · have hba : b ≠ a := fun h => hab h.symm
              by_cases haj : a = j
              · subst haj; simp [hab, hba]; norm_num
              · by_cases hbj : b = j
                · subst hbj; simp [hab, hba, haj]; norm_num
                · simp [hab, hba, haj, hbj]; norm_num
        · have hii : i' = i := by
            by_contra hne
            have h1 := hi i' hne
            have h2 := hi' i (fun h => hne h.symm)
            linarith
          subst hii
          have h1 := hQi' j hji
          rw [hsj] at h1
          have h2 := hsk i' (fun h => hji h.symm)
          linarith
      -- the change-of-measure lemma
      have ML : expTau π f < ⊤ → ∀ Q ∈ duelingAlt P,
          ENNReal.ofReal (kl δ (1 - δ)) ≤ ∑ S, N S * ENNReal.ofReal (KLS Q S) := by
        intro hTfin Q hQ
        set g := duelingPref Q with hg
        set pE : ℝ≥0∞ := ∑' t : ℕ, ∑ v : Fin t → Step K,
          if stopsAt π (toHist v) ∧ BordaWinner P (π.select (toHist v))
          then pathProb π f (toHist v) else 0 with hpEdef
        set qE : ℝ≥0∞ := ∑' t : ℕ, ∑ v : Fin t → Step K,
          if stopsAt π (toHist v) ∧ BordaWinner P (π.select (toHist v))
          then pathProb π g (toHist v) else 0 with hqEdef
        -- (c) under Q, the event "select P's winner" is a wrong answer
        have hqE : qE ≤ ENNReal.ofReal δ := by
          refine le_trans ?_ (hπ.2 Q hQ.1).2
          refine ENNReal.tsum_le_tsum (fun t => Finset.sum_le_sum (fun v _ => ?_))
          by_cases h : stopsAt π (toHist v) ∧ BordaWinner P (π.select (toHist v))
          · rw [if_pos h, if_pos ⟨h.1, hQ.2 _ h.2⟩]
          · rw [if_neg h]; exact bot_le
        -- (b) under P, the event has probability at least 1 - δ
        have hpE : 1 - ENNReal.ofReal δ ≤ pE := by
          obtain ⟨hstop, hwrong⟩ := hπ.2 P hP
          have hsplit : probStop π f = pE + duelingProbWrong π P := by
            simp only [probStop, duelingProbWrong, hpEdef]
            rw [← ENNReal.tsum_add]
            refine tsum_congr (fun t => ?_)
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun v _ => ?_)
            by_cases h1 : stopsAt π (toHist v) <;> by_cases h2 : BordaWinner P (π.select (toHist v)) <;>
              simp [h1, h2, hf]
          rw [tsub_le_iff_right, ← hstop, hsplit]
          gcongr
        have hpE1 : pE ≤ 1 := by
          rw [← (hπ.2 P hP).1]
          refine ENNReal.tsum_le_tsum (fun t => Finset.sum_le_sum (fun v _ => ?_))
          by_cases h : stopsAt π (toHist v) ∧ BordaWinner P (π.select (toHist v))
          · rw [if_pos h, if_pos h.1, hf]
          · rw [if_neg h]; exact bot_le
        have hsnoc : ∀ (t : ℕ) (F : List (Step K) → ℝ),
            ∑ v : Fin (t+1) → Step K, F (toHist v)
              = ∑ w : Fin t → Step K, ∑ x : Step K, F (x :: toHist w) := by
          intro t F
          rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Step K)) (fun p => F (p.1 :: toHist p.2))
            (fun v => F (toHist v))]
          · rw [Fintype.sum_prod_type, Finset.sum_comm]
          · intro p
            simp only [Fin.snocEquiv, Equiv.coe_fn_mk, toHist]
            rw [List.ofFn_succ']
            simp [Fin.snoc_castSucc, Fin.snoc_last]
        have hpref_nonneg : ∀ R ∈ ComparisonClass K, ∀ S X, 0 ≤ duelingPref R S X := by
          intro R hR S X
          unfold duelingPref
          split_ifs
          · exact Finset.sum_nonneg (fun j _ => (hR.1 _ j).1.le)
          · exact le_rfl
        have hpair : ∀ S : DS K, S.1.card = 2 → ∃ a b : Fin K, a < b ∧ S.1 = {a, b} := by
          intro S hS
          obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.1 hS
          rcases lt_or_gt_of_ne hab with h | h
          · exact ⟨a, b, h, he⟩
          · exact ⟨b, a, h, by rw [he, Finset.pair_comm]⟩
        have hpref_pair : ∀ (R : Comparison K) (S : DS K) (a b : Fin K), a ≠ b → S.1 = {a, b} →
            duelingPref R S a = R a b ∧ duelingPref R S b = R b a ∧
            ∀ X, X ≠ a → X ≠ b → duelingPref R S X = 0 := by
          intro R S a b hab hS
          have hc : S.1.card = 2 := by rw [hS]; exact Finset.card_pair hab
          refine ⟨?_, ?_, ?_⟩
          · simp [duelingPref, hc, hS, Finset.erase_insert, hab]
          · simp [duelingPref, hS, Finset.card_pair hab, Finset.erase_insert_of_ne hab, hab.symm]
          · intro X h1 h2
            simp [duelingPref, hS, h1, h2]
        have hdisp_fin : ∀ h S, π.disp h S ≠ ⊤ := by
          intro h S
          have : π.disp h S ≤ 1 := by
            rw [← hπ.1.1 h]; exact Finset.single_le_sum (f := π.disp h) (fun _ _ => bot_le) (Finset.mem_univ S)
          exact ne_top_of_le_ne_top ENNReal.one_ne_top this
        have hpath_fin : ∀ (R : Pref K) h, pathProb π R h ≠ ⊤ := by
          intro R h
          induction h with
          | nil => simp [pathProb]
          | cons x h ih =>
            obtain ⟨S, X⟩ := x
            simp only [pathProb]
            exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ih (hdisp_fin _ _)) ENNReal.ofReal_ne_top
        set p : List (Step K) → ℝ := fun h => (pathProb π f h).toReal with hpdef
        set q : List (Step K) → ℝ := fun h => (pathProb π g h).toReal with hqdef
        set d : List (Step K) → DS K → ℝ := fun h S => (π.disp h S).toReal with hddef
        have hp_cons : ∀ h (x : Step K), p (x :: h) = p h * d h x.1 * f x.1 x.2 := by
          intro h x
          obtain ⟨S, X⟩ := x
          simp only [hpdef, hddef, pathProb, ENNReal.toReal_mul]
          rw [ENNReal.toReal_ofReal (hpref_nonneg P hP S X)]
        have hq_cons : ∀ h (x : Step K), q (x :: h) = q h * d h x.1 * g x.1 x.2 := by
          intro h x
          obtain ⟨S, X⟩ := x
          simp only [hqdef, hddef, pathProb, ENNReal.toReal_mul]
          rw [ENNReal.toReal_ofReal (hpref_nonneg Q hQ.1 S X)]
        have hp_nil : p [] = 1 := by simp [hpdef, pathProb]
        have hq_nil : q [] = 1 := by simp [hqdef, pathProb]
        have hp_nn : ∀ h, 0 ≤ p h := fun h => ENNReal.toReal_nonneg
        have hq_nn : ∀ h, 0 ≤ q h := fun h => ENNReal.toReal_nonneg
        have hd_nn : ∀ h S, 0 ≤ d h S := fun h S => ENNReal.toReal_nonneg
        have hd_sum : ∀ h, ∑ S, d h S = 1 := by
          intro h
          simp only [hddef]
          rw [← ENNReal.toReal_sum (fun S _ => hdisp_fin h S), hπ.1.1 h]; simp
        have hd_pair : ∀ h S, S.1.card ≠ 2 → d h S = 0 := by
          intro h S hS; simp [hddef, hπ.1.2 h S hS]
        have hfg_pos : ∀ S X, 0 < f S X → 0 < g S X := by
          intro S X hfx
          have hc : S.1.card = 2 ∧ X ∈ S.1 := by
            by_contra hc
            simp [hf, duelingPref, hc] at hfx
          simp only [hg, duelingPref, if_pos hc]
          refine Finset.sum_pos (fun j _ => (hClass01 Q hQ.1 X j).1) ?_
          rw [← Finset.card_pos, Finset.card_erase_of_mem hc.2, hc.1]; norm_num
        have hmp : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 < a * b → 0 < a ∧ 0 < b := fun a b ha hb h =>
          ⟨lt_of_le_of_ne ha (by rintro rfl; simp at h), lt_of_le_of_ne hb (by rintro rfl; simp at h)⟩
        have hac : ∀ h, 0 < p h → 0 < q h := by
          intro h
          induction h with
          | nil => intro _; rw [hq_nil]; norm_num
          | cons x h ih =>
            intro hx
            rw [hp_cons] at hx
            rw [hq_cons]
            obtain ⟨h1, h2⟩ := (hmp _ _ (mul_nonneg (hp_nn _) (hd_nn _ _))
              (hpref_nonneg P hP _ _)) hx
            obtain ⟨h3, h4⟩ := hmp _ _ (hp_nn _) (hd_nn _ _) h1
            exact mul_pos (mul_pos (ih h3) h4) (hfg_pos _ _ h2)
        -- frontier sums
        set Alive : List (Step K) → Prop := fun h => ∀ j, 1 ≤ j → j ≤ h.length → ¬ π.stop (h.drop j)
          with hAlive
        set Fr : ℕ → (List (Step K) → ℝ) → ℝ := fun t Φ =>
          (∑ s ∈ Finset.range t, ∑ v : Fin s → Step K,
            (if stopsAt π (toHist v) then Φ (toHist v) else 0)) +
          ∑ v : Fin t → Step K, (if Alive (toHist v) then Φ (toHist v) else 0) with hFr
        have hAliveCons : ∀ x h, Alive (x :: h) ↔ survives π h := by
          intro x h
          simp only [hAlive, survives]
          constructor
          · intro H j hj
            have := H (j+1) (by omega) (by simp; omega)
            simpa using this
          · intro H j h1 h2
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            simp at h2
            simpa using H j' (by omega)
        have hAliveSplit : ∀ h (r : ℝ), (if Alive h then r else 0)
            = (if stopsAt π h then r else 0) + (if survives π h then r else 0) := by
          intro h r
          have hs : survives π h ↔ ¬ π.stop h ∧ Alive h := by
            simp only [survives, hAlive]
            constructor
            · intro H; exact ⟨by simpa using H 0 (by omega), fun j _ hj => H j hj⟩
            · intro H j hj
              rcases Nat.eq_zero_or_pos j with rfl | hj0
              · simpa using H.1
              · exact H.2 j hj0 hj
          have hst : stopsAt π h ↔ π.stop h ∧ Alive h := Iff.rfl
          by_cases h1 : π.stop h <;> by_cases h2 : Alive h
          · rw [if_pos h2, if_pos (hst.2 ⟨h1, h2⟩), if_neg (fun H => (hs.1 H).1 h1), add_zero]
          · rw [if_neg h2, if_neg (fun H => h2 (hst.1 H).2), if_neg (fun H => h2 (hs.1 H).2), add_zero]
          · rw [if_pos h2, if_neg (fun H => h1 (hst.1 H).1), if_pos (hs.2 ⟨h1, h2⟩), zero_add]
          · rw [if_neg h2, if_neg (fun H => h2 (hst.1 H).2), if_neg (fun H => h2 (hs.1 H).2), add_zero]
        have hFr_step : ∀ (Φ ρ : List (Step K) → ℝ), (∀ h, survives π h → ∑ x, Φ (x :: h) = Φ h + ρ h) →
            ∀ t, Fr (t+1) Φ = Fr t Φ + ∑ v : Fin t → Step K,
              (if survives π (toHist v) then ρ (toHist v) else 0) := by
          intro Φ ρ hΦ t
          simp only [hFr]
          rw [Finset.sum_range_succ, hsnoc t (fun h => if Alive h then Φ h else 0)]
          simp only [hAliveCons]
          have e1 : ∀ w : Fin t → Step K, (∑ x : Step K, if survives π (toHist w) then Φ (x :: toHist w) else 0)
              = (if survives π (toHist w) then Φ (toHist w) else 0) +
                (if survives π (toHist w) then ρ (toHist w) else 0) := by
            intro w
            by_cases hs : survives π (toHist w)
            · simp only [if_pos hs]; exact hΦ _ hs
            · simp [hs]
          simp only [e1, Finset.sum_add_distrib, hAliveSplit]
          ring
        have hFr_zero : ∀ Φ, Fr 0 Φ = Φ [] := by
          intro Φ
          simp only [hFr, Finset.range_zero, Finset.sum_empty, zero_add]
          have hA : Alive [] := fun j hj h0 => absurd h0 (by simp; omega)
          rw [Fintype.sum_unique]
          have : toHist (default : Fin 0 → Step K) = [] := by simp [toHist]
          rw [this, if_pos hA]
        have hFr_add : ∀ t Φ Ψ, Fr t (fun h => Φ h + Ψ h) = Fr t Φ + Fr t Ψ := by
          intro t Φ Ψ
          have e : ∀ (c : Prop) [Decidable c] (x y : ℝ), (if c then x + y else 0)
              = (if c then x else 0) + (if c then y else 0) := by
            intros; split_ifs <;> simp
          simp only [hFr, e, Finset.sum_add_distrib]; ring
        have hFr_smul : ∀ t c Φ, Fr t (fun h => c * Φ h) = c * Fr t Φ := by
          intro t c Φ
          have e : ∀ (b : Prop) [Decidable b] (x : ℝ), (if b then c * x else 0) = c * (if b then x else 0) := by
            intros; split_ifs <;> simp
          simp only [hFr, e, ← Finset.mul_sum, mul_add]
        have hFr_mono : ∀ t Φ Ψ, (∀ h, Φ h ≤ Ψ h) → Fr t Φ ≤ Fr t Ψ := by
          intro t Φ Ψ hle
          simp only [hFr]
          gcongr with s _ v _ v _
          · split_ifs
            · exact hle _
            · exact le_rfl
          · split_ifs
            · exact hle _
            · exact le_rfl
        have hfsum : ∀ (R : Comparison K), R ∈ ComparisonClass K → ∀ S : DS K, S.1.card = 2 →
            ∑ X, duelingPref R S X = 1 := by
          intro R hR S hS
          obtain ⟨a, b, hab, he⟩ := hpair S hS
          obtain ⟨h1, h2, h3⟩ := hpref_pair R S a b hab.ne he
          rw [Fintype.sum_eq_add a b hab.ne (fun X hX => h3 X hX.1 hX.2), h1, h2]
          exact (hR.1 a b).2
        have hmass : ∀ (r : List (Step K) → ℝ) (R : Comparison K), R ∈ ComparisonClass K →
            (∀ h x, r (x :: h) = r h * d h x.1 * duelingPref R x.1 x.2) →
            ∀ h, ∑ x, r (x :: h) = r h + 0 := by
          intro r R hR hr h
          simp only [hr, Fintype.sum_prod_type, add_zero]
          have : ∀ S : DS K, ∑ X, r h * d h S * duelingPref R S X = r h * d h S := by
            intro S
            by_cases hS : S.1.card = 2
            · rw [← Finset.mul_sum, hfsum R hR S hS, mul_one]
            · simp [hd_pair h S hS]
          simp only [this, ← Finset.mul_sum, hd_sum, mul_one]
        have hFr_p : ∀ t, Fr t p = 1 := by
          intro t
          induction t with
          | zero => rw [hFr_zero, hp_nil]
          | succ t ih =>
            rw [hFr_step p (fun _ => 0) (fun h _ => hmass p P hP hp_cons h), ih]; simp
        have hFr_q : ∀ t, Fr t q = 1 := by
          intro t
          induction t with
          | zero => rw [hFr_zero, hq_nil]
          | succ t ih =>
            rw [hFr_step q (fun _ => 0) (fun h _ => hmass q Q hQ.1 hq_cons h), ih]; simp
        set KS : DS K → ℝ := fun S => ∑ X, f S X * Real.log (f S X / g S X) with hKS
        have hchain : ∀ h, ∑ x, p (x :: h) * Real.log (p (x :: h) / q (x :: h))
            = p h * Real.log (p h / q h) + p h * ∑ S, d h S * KS S := by
          intro h
          rcases (hp_nn h).eq_or_lt with h0 | hpos
          · simp [hp_cons, ← h0]
          have hqpos := hac h hpos
          simp only [Fintype.sum_prod_type]
          have hS : ∀ S : DS K, ∑ X, p (⟨S, X⟩ :: h) * Real.log (p (⟨S, X⟩ :: h) / q (⟨S, X⟩ :: h))
              = p h * d h S * Real.log (p h / q h) + p h * (d h S * KS S) := by
            intro S
            rcases (hd_nn h S).eq_or_lt with hd0 | hdpos
            · simp [hp_cons, ← hd0]
            have hS2 : S.1.card = 2 := by
              by_contra hc; exact hdpos.ne' (hd_pair h S hc)
            have hterm : ∀ X, p (⟨S, X⟩ :: h) * Real.log (p (⟨S, X⟩ :: h) / q (⟨S, X⟩ :: h))
                = p h * d h S * f S X * Real.log (p h / q h) + p h * (d h S * (f S X * Real.log (f S X / g S X))) := by
              intro X
              rw [hp_cons, hq_cons]
              rcases (hpref_nonneg P hP S X).eq_or_lt with hf0 | hfpos
              · have hf0' : f S X = 0 := hf0.symm
                simp [hf0']
              have hgpos := hfg_pos S X hfpos
              have : p h * d h S * f S X / (q h * d h S * g S X) = (p h / q h) * (f S X / g S X) := by
                field_simp
              simp only at this ⊢
              rw [this, Real.log_mul (by positivity) (by positivity)]
              ring
            simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hKS]
            rw [show (∑ X, f S X) = 1 from hfsum P hP S hS2]; ring
          simp only [hS, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hd_sum]; ring
        have hFr_KL : ∀ t, Fr t (fun h => p h * Real.log (p h / q h))
            = ∑ s ∈ Finset.range t, ∑ v : Fin s → Step K,
              (if survives π (toHist v) then p (toHist v) * ∑ S, d (toHist v) S * KS S else 0) := by
          intro t
          induction t with
          | zero => rw [hFr_zero (fun h => p h * Real.log (p h / q h)), hp_nil, hq_nil]; simp
          | succ t ih =>
            rw [hFr_step (fun h => p h * Real.log (p h / q h)) (fun h => p h * ∑ S, d h S * KS S)
              (fun h _ => hchain h) t, ih, Finset.sum_range_succ]
        have hKSeq : ∀ S : DS K, S.1.card = 2 → KS S = KLS Q S := by
          intro S hS
          obtain ⟨a, b, hab, he⟩ := hpair S hS
          obtain ⟨p1, p2, p3⟩ := hpref_pair P S a b hab.ne he
          obtain ⟨q1, q2, q3⟩ := hpref_pair Q S a b hab.ne he
          have hPba : P b a = 1 - P a b := by linarith [(hP.1 a b).2]
          have hQba : Q b a = 1 - Q a b := by linarith [(hQ.1.1 a b).2]
          have lhs : KS S = kl (P a b) (Q a b) := by
            simp only [hKS, hf, hg]
            rw [Fintype.sum_eq_add a b hab.ne (fun X hX => by rw [p3 X hX.1 hX.2, zero_mul]),
              p1, p2, q1, q2, hPba, hQba]
            rfl
          have hiff : ∀ i j : Fin K, (i < j ∧ S.1 = {i, j}) ↔ (i = a ∧ j = b) := by
            intro i j
            constructor
            · rintro ⟨hij, h2⟩
              rw [he] at h2
              have ha : a ∈ ({i, j} : Finset (Fin K)) := by rw [← h2]; simp
              have hb : b ∈ ({i, j} : Finset (Fin K)) := by rw [← h2]; simp
              simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
              rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
              · exact absurd hab (lt_irrefl _)
              · exact ⟨rfl, rfl⟩
              · exact absurd (hab.trans hij) (lt_irrefl _)
              · exact absurd hab (lt_irrefl _)
            · rintro ⟨rfl, rfl⟩; exact ⟨hab, he⟩
          rw [lhs]
          simp only [hKLS, hiff]
          rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp),
            Finset.sum_eq_single b (fun j _ hj => by simp [hj]) (by simp)]
          simp
        have hNfin : ∀ S, N S ≠ ⊤ := fun S => ne_top_of_le_ne_top hTfin.ne (by
          rw [← hNsum]; exact Finset.single_le_sum (f := N) (fun _ _ => bot_le) (Finset.mem_univ S))
        have hNpart : ∀ (t : ℕ) S, ∑ s ∈ Finset.range t, ∑ v : Fin s → Step K,
            (if survives π (toHist v) then p (toHist v) * d (toHist v) S else 0) ≤ (N S).toReal := by
          intro t S
          have e : ∀ s : ℕ, ∑ v : Fin s → Step K,
              (if survives π (toHist v) then p (toHist v) * d (toHist v) S else 0)
              = (∑ v : Fin s → Step K,
                if survives π (toHist v) then pathProb π f (toHist v) * π.disp (toHist v) S else 0).toReal := by
            intro s
            rw [ENNReal.toReal_sum]
            · refine Finset.sum_congr rfl (fun v _ => ?_)
              split_ifs
              · simp only [hpdef, hddef, ENNReal.toReal_mul]
              · simp
            · intro v _
              split_ifs
              · exact ENNReal.mul_ne_top (hpath_fin _ _) (hdisp_fin _ _)
              · exact ENNReal.zero_ne_top
          have hle : ∑ s ∈ Finset.range t, (∑ v : Fin s → Step K,
                if survives π (toHist v) then pathProb π f (toHist v) * π.disp (toHist v) S else 0) ≤ N S := by
            simp only [hN]; exact ENNReal.sum_le_tsum _
          simp only [e]
          rw [← ENNReal.toReal_sum]
          · exact ENNReal.toReal_mono (hNfin S) hle
          · intro s hs
            refine ne_top_of_le_ne_top (hNfin S) (le_trans ?_ hle)
            exact Finset.single_le_sum (f := fun s : ℕ => ∑ v : Fin s → Step K,
                if survives π (toHist v) then pathProb π f (toHist v) * π.disp (toHist v) S else 0)
                (fun _ _ => bot_le) hs
        set R : ℝ := ∑ S, (N S).toReal * KLS Q S with hR
        have hupper : ∀ t, Fr t (fun h => p h * Real.log (p h / q h)) ≤ R := by
          intro t
          rw [hFr_KL]
          have e : ∀ h : List (Step K), (if survives π h then p h * ∑ S, d h S * KS S else 0)
              = ∑ S, (if survives π h then p h * d h S else 0) * KLS Q S := by
            intro h
            have e2 : ∀ S, d h S * KS S = d h S * KLS Q S := by
              intro S
              by_cases hS : S.1.card = 2
              · rw [hKSeq S hS]
              · rw [hd_pair h S hS, zero_mul, zero_mul]
            split_ifs
            · rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun S _ => ?_)
              rw [e2 S, mul_assoc]
            · simp
          have e3 : ∑ s ∈ Finset.range t, ∑ v : Fin s → Step K,
              (if survives π (toHist v) then p (toHist v) * ∑ S, d (toHist v) S * KS S else 0)
              = ∑ S, (∑ s ∈ Finset.range t, ∑ v : Fin s → Step K,
                (if survives π (toHist v) then p (toHist v) * d (toHist v) S else 0)) * KLS Q S := by
            simp only [e, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun s _ => ?_)
            rw [Finset.sum_comm]
          rw [e3, hR]
          exact Finset.sum_le_sum (fun S _ =>
            mul_le_mul_of_nonneg_right (hNpart t S) (hKLS_nonneg Q hQ.1 S))
        -- lower bound
        set I : List (Step K) → Prop := fun h => stopsAt π h ∧ BordaWinner P (π.select h) with hI
        have hFrI : ∀ (r : List (Step K) → ℝ) t, Fr t (fun h => if I h then r h else 0)
            = ∑ s ∈ Finset.range (t+1), ∑ v : Fin s → Step K, (if I (toHist v) then r (toHist v) else 0) := by
          intro r t
          have e1 : ∀ h, (if stopsAt π h then (if I h then r h else 0) else 0) = if I h then r h else 0 := by
            intro h
            by_cases hi : I h
            · rw [if_pos hi.1]
            · simp [hi]
          have e2 : ∀ h, (if Alive h then (if I h then r h else 0) else 0) = if I h then r h else 0 := by
            intro h
            by_cases hi : I h
            · rw [if_pos hi.1.2]
            · simp [hi]
          simp only [hFr, e1, e2]
          rw [Finset.sum_range_succ]
        have hEreal : ∀ (F : Pref K) (s : ℕ), ∑ v : Fin s → Step K,
              (if I (toHist v) then (pathProb π F (toHist v)).toReal else 0)
              = (∑ v : Fin s → Step K, if I (toHist v) then pathProb π F (toHist v) else 0).toReal := by
          intro F s
          rw [ENNReal.toReal_sum]
          · refine Finset.sum_congr rfl (fun v _ => ?_)
            split_ifs <;> simp
          · intro v _
            split_ifs
            · exact hpath_fin _ _
            · exact ENNReal.zero_ne_top
        have hEfin : ∀ (F : Pref K) (s : ℕ),
              (∑ v : Fin s → Step K, if I (toHist v) then pathProb π F (toHist v) else 0) ≠ ⊤ := by
          intro F s
          refine ENNReal.sum_ne_top.2 (fun v _ => ?_)
          split_ifs
          · exact hpath_fin _ _
          · exact ENNReal.zero_ne_top
        have hb : ∀ t, Fr t (fun h => if I h then q h else 0) ≤ δ := by
          intro t
          rw [hFrI]
          simp only [hqdef, hEreal]
          rw [← ENNReal.toReal_sum (fun s _ => hEfin g s)]
          refine ENNReal.toReal_le_of_le_ofReal hδ0.le (le_trans ?_ hqE)
          rw [hqEdef]; exact ENNReal.sum_le_tsum _
        have ha : Filter.Tendsto (fun t => Fr t (fun h => if I h then p h else 0)) Filter.atTop
            (nhds pE.toReal) := by
          have h1 : Filter.Tendsto (fun t : ℕ => ∑ s ∈ Finset.range t,
              (∑ v : Fin s → Step K, if I (toHist v) then pathProb π f (toHist v) else 0))
              Filter.atTop (nhds pE) := by
            rw [hpEdef]; exact ENNReal.tendsto_nat_tsum _
          have h2 := (ENNReal.tendsto_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hpE1)).comp
            (h1.comp (Filter.tendsto_add_atTop_nat 1))
          refine h2.congr (fun t => ?_)
          rw [hFrI]
          simp only [hpdef, hEreal, Function.comp]
          rw [ENNReal.toReal_sum (fun s _ => hEfin f s)]
        have hpEreal : 1 - δ ≤ pE.toReal := by
          have h1 := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hpE1) hpE
          rw [ENNReal.toReal_sub_of_le (by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)) ENNReal.one_ne_top,
            ENNReal.toReal_ofReal hδ0.le] at h1
          simpa using h1
        have h1δ : 0 < 1 - δ := by linarith
        set u : ℝ := (1 - δ) / δ with hu
        set w : ℝ := δ / (1 - δ) with hw
        have hu0 : 0 < u := div_pos h1δ hδ0
        have hw0 : 0 < w := div_pos hδ0 h1δ
        have huw : w ≤ u := by
          have h1 : w ≤ 1 := by rw [hw, div_le_one h1δ]; linarith
          have h2 : 1 ≤ u := by rw [hu, one_le_div hδ0]; linarith
          linarith
        have hlogw : Real.log w = - Real.log u := by
          rw [← Real.log_inv, hu, hw, inv_div]
        have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by rw [hu, one_le_div hδ0]; linarith)
        have huw1 : u * δ + w * (1 - δ) = 1 := by
          rw [hu, hw]; field_simp; ring
        have hpt : ∀ (c : ℝ), 0 < c → ∀ h, p h * Real.log c + p h - c * q h
            ≤ p h * Real.log (p h / q h) := by
          intro c hc h
          rcases (hp_nn h).eq_or_lt with h0 | hpos
          · rw [← h0]; have := mul_nonneg hc.le (hq_nn h); simp; exact this
          have hqpos := hac h hpos
          have h1 := Real.log_le_sub_one_of_pos (div_pos (mul_pos hc hqpos) hpos)
          rw [Real.log_div (mul_pos hc hqpos).ne' hpos.ne', Real.log_mul hc.ne' hqpos.ne'] at h1
          rw [Real.log_div hpos.ne' hqpos.ne']
          have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
          have h3 : p h * (c * q h / p h - 1) = c * q h - p h := by field_simp
          rw [h3] at h2
          nlinarith
        have hlow : ∀ t, (2 * Fr t (fun h => if I h then p h else 0) - 1) * Real.log u
            ≤ Fr t (fun h => p h * Real.log (p h / q h)) := by
          intro t
          have hm := hFr_mono t
            (fun h => ((2 * Real.log u) * (if I h then p h else 0) + (1 - Real.log u) * p h)
              + ((w - u) * (if I h then q h else 0) + (-w) * q h))
            (fun h => p h * Real.log (p h / q h)) (by
              intro h
              by_cases hi : I h
              · have := hpt u hu0 h
                simp only [if_pos hi]; linarith
              · have := hpt w hw0 h
                rw [hlogw] at this
                simp only [if_neg hi]; linarith)
          rw [hFr_add t (fun h => (2 * Real.log u) * (if I h then p h else 0) + (1 - Real.log u) * p h)
              (fun h => (w - u) * (if I h then q h else 0) + (-w) * q h),
            hFr_add t (fun h => (2 * Real.log u) * (if I h then p h else 0)) (fun h => (1 - Real.log u) * p h),
            hFr_add t (fun h => (w - u) * (if I h then q h else 0)) (fun h => (-w) * q h),
            hFr_smul t (2 * Real.log u) (fun h => if I h then p h else 0), hFr_smul t (1 - Real.log u) p,
            hFr_smul t (w - u) (fun h => if I h then q h else 0), hFr_smul t (-w) q, hFr_p, hFr_q] at hm
          have hbt := mul_le_mul_of_nonneg_left (hb t) (sub_nonneg.2 huw)
          linarith
        have hfinal : kl δ (1 - δ) ≤ R := by
          have h1 : (2 * pE.toReal - 1) * Real.log u ≤ R :=
            le_of_tendsto (((ha.const_mul 2).sub_const 1).mul_const (Real.log u))
              (Filter.Eventually.of_forall (fun t => (hlow t).trans (hupper t)))
          have h2 : kl δ (1 - δ) = (1 - 2 * δ) * Real.log u := by
            unfold kl
            rw [show (1 - (1 - δ)) = δ by ring, ← hu, ← hw, hlogw]; ring
          rw [h2]
          refine le_trans ?_ h1
          exact mul_le_mul_of_nonneg_right (by linarith) hlogu
        calc ENNReal.ofReal (kl δ (1 - δ)) ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hfinal
          _ = ∑ S, N S * ENNReal.ofReal (KLS Q S) := by
            rw [hR, ENNReal.ofReal_sum_of_nonneg (fun S _ => mul_nonneg ENNReal.toReal_nonneg
              (hKLS_nonneg Q hQ.1 S))]
            refine Finset.sum_congr rfl (fun S _ => ?_)
            rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hNfin S)]
      -- assembly
      rcases eq_top_or_lt_top (expTau π f) with hT | hT
      · rw [hT]; exact le_top
      have ML' := ML hT
      set T := expTau π f with hTdef
      have hNle : ∀ S, N S ≤ T := fun S => by
        rw [← hNsum]; exact Finset.single_le_sum (f := N) (fun _ _ => bot_le) (Finset.mem_univ S)
      have hNfin : ∀ S, N S ≠ ⊤ := fun S => ne_top_of_le_ne_top hT.ne (hNle S)
      by_cases hT0 : T = 0
      · -- then the kl term is zero
        have hN0 : ∀ S, N S = 0 := fun S => le_antisymm (hT0 ▸ hNle S) bot_le
        obtain ⟨Q, hQ⟩ := hAltNe
        have := ML' Q hQ
        simp only [hN0, zero_mul, Finset.sum_const_zero, nonpos_iff_eq_zero] at this
        rw [this, ENNReal.zero_div]; exact bot_le
      · set lam : DS K → ℝ := fun S => (N S / T).toReal with hlam
        have hlam_simp : lam ∈ pairSimplex K := by
          refine ⟨⟨fun S => ENNReal.toReal_nonneg, ?_⟩, fun S hS => by simp [hlam, hNpair S hS]⟩
          rw [← ENNReal.toReal_sum (fun S _ => ENNReal.div_ne_top (hNfin S) hT0)]
          simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul, hNsum, ENNReal.mul_inv_cancel hT0 hT.ne]; simp
        have hdiv : ∀ Q ∈ ComparisonClass K, duelingDiv lam P Q = ∑ S, lam S * KLS Q S := by
          intro Q hQ
          simp only [duelingDiv, pairWeight, hKLS, Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          split_ifs with hij
          · rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun S _ => ?_)
            by_cases hS : S.1 = {i, j} <;> simp [hS, hij]
          · simp [hij]
        have key : ENNReal.ofReal (kl δ (1 - δ)) / T ≤ duelingInfo P := by
          refine le_trans ?_ (le_iSup₂ (f := fun lam _ => ⨅ Q ∈ duelingAlt P,
            ENNReal.ofReal (duelingDiv lam P Q)) lam hlam_simp)
          refine le_iInf₂ (fun Q hQ => ?_)
          rw [hdiv Q hQ.1, ENNReal.div_le_iff hT0 hT.ne]
          refine le_trans (ML' Q hQ) (le_of_eq ?_)
          rw [ENNReal.ofReal_sum_of_nonneg (fun S _ => mul_nonneg ENNReal.toReal_nonneg
            (hKLS_nonneg Q hQ.1 S)), Finset.sum_mul]
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
          rw [ENNReal.ofReal_toReal (ENNReal.div_ne_top (hNfin S) hT0)]
          rw [mul_comm (N S / T), mul_assoc, ENNReal.div_mul_cancel hT0 hT.ne, mul_comm]
        apply ENNReal.div_le_of_le_mul
        calc ENNReal.ofReal (kl δ (1 - δ)) = ENNReal.ofReal (kl δ (1 - δ)) / T * T :=
              (ENNReal.div_mul_cancel hT0 hT.ne).symm
          _ ≤ duelingInfo P * T := by gcongr
          _ = T * duelingInfo P := mul_comm _ _
