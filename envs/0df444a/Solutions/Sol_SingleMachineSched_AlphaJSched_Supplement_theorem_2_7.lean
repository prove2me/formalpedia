-- Prove2me | solution 1 for SingleMachineSched.AlphaJSched.Supplement.theorem_2_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:05.155026+00:00
-- url     : https://prove2.me/submissions/14a7287d-eac1-4a4c-98b4-b2480839eb08

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_InfiniteD
import Definitions.Def_SingleMachineSched_Shared_PreemptiveSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR
import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule

open SingleMachineSched
open SingleMachineSched.AlphaJSched
open SingleMachineSched.AlphaJSched.Supplement

/-- Theorem 2.7, all three polyhedral conclusions. In (ii) the displayed map
into ℝ^N is restricted to finite first moments; see DISPROOF.md for the divergent-tail case. -/
theorem solution {n : ℕ} (p r : Fin n → ℕ) (hp : ∀ j, 0 < p j) :
    ({M : Fin n → ℝ | Shared.FeasibleR p r M} =
      convexHull ℝ {M | ∃ A : Fin n → Set ℝ,
        Shared.IsPreemptiveSchedule p r A ∧
          M = fun j => Shared.meanBusyTime p A j}) ∧
    (∀ M ∈ Set.extremePoints ℝ {M : Fin n → ℝ | Shared.FeasibleR p r M},
      ∃ σ : Equiv.Perm (Fin n),
        M = fun j => mLP (p ∘ σ) (r ∘ σ) (σ.symm j)) ∧
    ({M : Fin n → ℝ | Shared.FeasibleR p r M} =
      mMap p '' {y | FeasibleDinf p r y ∧
        ∀ j, Summable (fun τ : ℕ => y j τ * ((τ : ℝ) + 1 / 2))}) := by
          classical
          set P : Set (Fin n → ℝ) := {M | Shared.FeasibleR p r M} with hPdef
          set V : Set (Fin n → ℝ) :=
            Set.range (fun σ : Equiv.Perm (Fin n) => fun j => mLP (p ∘ σ) (r ∘ σ) (σ.symm j)) with hVdef
          -- P is convex
          have hPconv : Convex ℝ P := by
            intro M hM N hN a b ha hb hab S hS
            have h1 := hM S hS
            have h2 := hN S hS
            have : ∑ j ∈ S, (p j : ℝ) * (a • M + b • N) j
                = a * ∑ j ∈ S, (p j : ℝ) * M j + b * ∑ j ∈ S, (p j : ℝ) * N j := by
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun j _ => by ring
            rw [this]
            have e : Shared.pSum p S * (Shared.rmin r S hS + Shared.pSum p S / 2) = a * (Shared.pSum p S * (Shared.rmin r S hS + Shared.pSum p S / 2)) + b * (Shared.pSum p S * (Shared.rmin r S hS + Shared.pSum p S / 2)) := by rw [← add_mul, hab, one_mul]
            rw [e]
            exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
          -- P is upward closed
          have hPup : ∀ M ∈ P, ∀ d : Fin n → ℝ, (∀ j, 0 ≤ d j) → M + d ∈ P := by
            intro M hM d hd S hS
            have h1 := hM S hS
            have : ∑ j ∈ S, (p j : ℝ) * M j ≤ ∑ j ∈ S, (p j : ℝ) * (M + d) j := by
              apply Finset.sum_le_sum
              intro j _
              have := hd j
              simp only [Pi.add_apply]
              have : (0:ℝ) ≤ p j := by positivity
              nlinarith
            linarith
          set Sg : Set (Fin n → ℝ) := {M | ∃ A : Fin n → Set ℝ,
                Shared.IsPreemptiveSchedule p r A ∧
                  M = fun j => Shared.meanBusyTime p A j} with hSgdef
          -- HARD (measure theory): a set of measure m inside [a, ∞) has ∫ t ≥ m (a + m/2)
          open MeasureTheory in
          have bath : ∀ (B : Set ℝ) (a : ℝ), MeasurableSet B → B ⊆ Set.Ici a → Bornology.IsBounded B →
              volume B ≠ ⊤ →
              (volume B).toReal * (a + (volume B).toReal / 2) ≤ ∫ t in B, t := by
            intro B a hBm hBa hBb hBfin
            set m := (volume B).toReal with hm
            have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
            set c := a + m with hc
            set I := Set.Icc a c with hI
            have hintB : IntegrableOn (fun t : ℝ => t) B :=
              (continuous_id.integrableOn_Icc (a := sInf B) (b := sSup B)).mono_set hBb.subset_Icc_sInf_sSup
            have hintBc : IntegrableOn (fun t : ℝ => t - c) B := hintB.sub (integrableOn_const hBfin)
            have hintIc : IntegrableOn (fun t : ℝ => t - c) I :=
              (continuous_id.sub continuous_const).integrableOn_Icc
            have hpt : ∀ t, I.indicator (fun t : ℝ => t - c) t ≤ B.indicator (fun t : ℝ => t - c) t := by
              intro t
              by_cases htI : t ∈ I <;> by_cases htB : t ∈ B
              · simp [htI, htB]
              · simp only [Set.indicator_of_mem htI, Set.indicator_of_notMem htB]
                linarith [htI.2]
              · simp only [Set.indicator_of_mem htB, Set.indicator_of_notMem htI]
                have := hBa htB
                simp only [hI, Set.mem_Icc, not_and_or, not_le] at htI
                simp only [Set.mem_Ici] at this
                rcases htI with h | h <;> linarith
              · simp [htI, htB]
            have hle : ∫ t in I, (t - c) ≤ ∫ t in B, (t - c) := by
              rw [← integral_indicator measurableSet_Icc, ← integral_indicator hBm]
              exact integral_mono (hintIc.integrable_indicator measurableSet_Icc)
                (hintBc.integrable_indicator hBm) hpt
            have hIval : ∫ t in I, (t - c) = -(m ^ 2) / 2 := by
              rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
              rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x), integral_id]
              simp [hc]
            have hBval : ∫ t in B, (t - c) = (∫ t in B, t) - c * m := by
              rw [integral_sub hintB (integrableOn_const hBfin)]
              simp [Measure.real, hm, mul_comm]
            rw [hIval, hBval] at hle
            rw [hc] at hle
            nlinarith
          open MeasureTheory in
          have hSgP : Sg ⊆ P := by
            intro M hM
            rw [hSgdef] at hM
            obtain ⟨A, hA, rfl⟩ := hM
            rw [hPdef]
            intro S hS
            have hint1 : ∀ j, IntegrableOn (fun t : ℝ => t) (A j) := fun j =>
              (continuous_id.integrableOn_Icc (a := sInf (A j)) (b := sSup (A j))).mono_set
                (hA.bounded j).subset_Icc_sInf_sSup
            set B := ⋃ j ∈ S, A j with hB
            have hBm : MeasurableSet B := Finset.measurableSet_biUnion S (fun j _ => hA.measurable j)
            have hvol : volume B = ∑ j ∈ S, (p j : ENNReal) := by
              rw [hB, measure_biUnion_finset (fun i _ j _ hij => hA.disjoint hij) (fun j _ => hA.measurable j)]
              exact Finset.sum_congr rfl fun j _ => hA.volume_eq j
            have hBfin : volume B ≠ ⊤ := by
              rw [hvol]; exact ENNReal.sum_ne_top.2 fun j _ => ENNReal.natCast_ne_top _
            have hmB : (volume B).toReal = Shared.pSum p S := by
              rw [hvol, ENNReal.toReal_sum (fun _ _ => ENNReal.natCast_ne_top _)]
              simp [Shared.pSum]
            have hBa : B ⊆ Set.Ici (Shared.rmin r S hS) := by
              intro t ht
              simp only [hB, Set.mem_iUnion] at ht
              obtain ⟨j, hj, htj⟩ := ht
              have := hA.release j htj
              simp only [Set.mem_Ici] at this ⊢
              exact le_trans (Finset.inf'_le _ hj) this
            have hBb : Bornology.IsBounded B := (Bornology.isBounded_biUnion_finset S).2 fun j _ => hA.bounded j
            have hint : ∫ t in B, t = ∑ j ∈ S, ∫ t in A j, t :=
              integral_biUnion_finset S (fun j _ => hA.measurable j) (fun i _ j _ hij => hA.disjoint hij)
                (fun j _ => hint1 j)
            have key := bath B _ hBm hBa hBb hBfin
            rw [hmB, hint] at key
            refine key.trans (le_of_eq ?_)
            refine Finset.sum_congr rfl fun j _ => ?_
            have : (p j : ℝ) ≠ 0 := by exact_mod_cast (hp j).ne'
            simp only [Shared.meanBusyTime]
            rw [← mul_assoc, mul_one_div_cancel this, one_mul]
          -- HARD (combinatorics of lpRemaining): the LP schedule is a preemptive schedule
          open MeasureTheory in
          have hLPsched : ∀ p' r' : Fin n → ℕ, Shared.IsPreemptiveSchedule p' r' (lpSet p' r') := by
            intro p' r'
            have F1 : ∀ τ j, lpRemaining p' r' (τ+1) j =
                if lpRun p' r' τ = some j then lpRemaining p' r' τ j - 1 else lpRemaining p' r' τ j := by
              intro τ j; rfl
            have F2 : ∀ τ j, lpRun p' r' τ = some j → r' j ≤ τ ∧ 0 < lpRemaining p' r' τ j := by
              intro τ j h
              unfold lpRun lpPick at h
              split_ifs at h with hne
              · cases h
                have := Finset.min'_mem _ hne
                simpa using this
            have F2' : ∀ τ, (∃ j, r' j ≤ τ ∧ 0 < lpRemaining p' r' τ j) → ∃ k, lpRun p' r' τ = some k := by
              intro τ ⟨j, hj⟩
              unfold lpRun lpPick
              rw [dif_pos ⟨j, by simpa using hj⟩]
              exact ⟨_, rfl⟩
            have Fmono : ∀ τ j, lpRemaining p' r' (τ+1) j ≤ lpRemaining p' r' τ j := by
              intro τ j; rw [F1]; split_ifs <;> omega
            have F3 : ∀ τ j, ((Finset.range τ).filter (fun τ' => lpRun p' r' τ' = some j)).card
                + lpRemaining p' r' τ j = p' j := by
              intro τ j
              induction τ with
              | zero => simp [lpRemaining]
              | succ τ ih =>
                rw [Finset.range_add_one, Finset.filter_insert, F1]
                by_cases h : lpRun p' r' τ = some j
                · have := (F2 τ j h).2
                  rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
                  omega
                · rw [if_neg h, if_neg h]; exact ih
            set mr := Finset.univ.sup r' with hmr
            have hrle : ∀ j, r' j ≤ mr := fun j => Finset.le_sup (Finset.mem_univ j)
            set R : ℕ → ℕ := fun τ => ∑ j, lpRemaining p' r' τ j with hR
            have F4 : ∀ τ, mr ≤ τ → 0 < R τ → R (τ+1) + 1 = R τ := by
              intro τ hτ hpos
              obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => 0) (by simpa using hpos)
              obtain ⟨k, hk⟩ := F2' τ ⟨j, (hrle j).trans hτ, hj⟩
              have hk2 := (F2 τ k hk).2
              simp only [hR]
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
              rw [F1, if_pos hk]
              have : ∑ x ∈ Finset.univ.erase k, lpRemaining p' r' (τ + 1) x = ∑ x ∈ Finset.univ.erase k, lpRemaining p' r' τ x := by
                refine Finset.sum_congr rfl fun x hx => ?_
                rw [F1, if_neg]
                intro h; rw [hk] at h; exact (Finset.ne_of_mem_erase hx) (Option.some_injective _ h).symm
              rw [this]; omega
            have Fmono' : ∀ τ, R (τ+1) ≤ R τ := fun τ => Finset.sum_le_sum fun j _ => Fmono τ j
            have F5 : ∀ k, R (mr + k) + k ≤ ∑ j, p' j ∨ R (mr + k) = 0 := by
              intro k
              induction k with
              | zero =>
                left
                simp only [hR, add_zero]
                have := fun j => F3 mr j
                calc ∑ j, lpRemaining p' r' mr j ≤ ∑ j, p' j := Finset.sum_le_sum fun j _ => by have := this j; omega
              | succ k ih =>
                show R (mr + k + 1) + (k + 1) ≤ ∑ j, p' j ∨ R (mr + k + 1) = 0
                rcases Nat.eq_zero_or_pos (R (mr + k)) with h0 | hpos
                · right; have := Fmono' (mr + k); omega
                · have := F4 (mr + k) (by omega) hpos
                  rcases ih with ih | ih <;> omega
            set H := mr + ∑ j, p' j with hH
            have F6 : ∀ τ, H ≤ τ → ∀ j, lpRemaining p' r' τ j = 0 := by
              have h0 : R H = 0 := by
                have h : R H + ∑ j, p' j ≤ ∑ j, p' j ∨ R H = 0 := F5 _
                omega
              intro τ hτ
              obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hτ
              have : R (H + d) = 0 := by
                induction d with
                | zero => simpa using h0
                | succ d ih => have := Fmono' (H + d); show R (H + d + 1) = 0; omega
              intro j
              have := (Finset.sum_eq_zero_iff.1 this) j (Finset.mem_univ j)
              exact this
            have F7 : ∀ τ j, lpRun p' r' τ = some j → τ < H := by
              intro τ j h
              by_contra hc
              have := (F2 τ j h).2
              rw [F6 τ (by omega) j] at this
              exact lt_irrefl _ this
            have F8 : ∀ j, ((Finset.range H).filter (fun τ' => lpRun p' r' τ' = some j)).card = p' j := by
              intro j; have := F3 H j; rw [F6 H le_rfl j] at this; simpa using this
            have F9 : ∀ j, lpSet p' r' j = ⋃ τ ∈ (Finset.range H).filter (fun τ' => lpRun p' r' τ' = some j),
                Set.Ico (τ : ℝ) (τ + 1) := by
              intro j
              ext x
              simp only [lpSet, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, exists_prop]
              constructor
              · rintro ⟨τ, h, hx⟩; exact ⟨τ, ⟨F7 τ j h, h⟩, hx⟩
              · rintro ⟨τ, ⟨-, h⟩, hx⟩; exact ⟨τ, h, hx⟩
            have Ico_uniq : ∀ (τ1 τ2 : ℕ) (x : ℝ), x ∈ Set.Ico (τ1 : ℝ) (τ1 + 1) → x ∈ Set.Ico (τ2 : ℝ) (τ2 + 1) → τ1 = τ2 := by
              intro τ1 τ2 x h1 h2
              have a1 : (τ1 : ℝ) < τ2 + 1 := lt_of_le_of_lt h1.1 h2.2
              have a2 : (τ2 : ℝ) < τ1 + 1 := lt_of_le_of_lt h2.1 h1.2
              have b1 : τ1 < τ2 + 1 := by exact_mod_cast a1
              have b2 : τ2 < τ1 + 1 := by exact_mod_cast a2
              omega
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro j; rw [F9]; exact Finset.measurableSet_biUnion _ (fun _ _ => measurableSet_Ico)
            · intro j x hx
              simp only [lpSet, Set.mem_iUnion] at hx
              obtain ⟨τ, h, hx⟩ := hx
              have := (F2 τ j h).1
              have : (r' j : ℝ) ≤ τ := by exact_mod_cast this
              exact this.trans hx.1
            · intro j
              rw [F9, measure_biUnion_finset]
              · simp only [Real.volume_Ico, add_sub_cancel_left, ENNReal.ofReal_one, Finset.sum_const, nsmul_eq_mul, mul_one, F8]
              · intro τ1 _ τ2 _ hne
                rw [Function.onFun, Set.disjoint_left]
                intro x h1 h2
                exact hne (Ico_uniq τ1 τ2 x h1 h2)
              · intro _ _; exact measurableSet_Ico
            · intro j k hjk
              rw [Function.onFun, Set.disjoint_left]
              intro x h1 h2
              simp only [lpSet, Set.mem_iUnion] at h1 h2
              obtain ⟨τ1, e1, h1⟩ := h1
              obtain ⟨τ2, e2, h2⟩ := h2
              have := Ico_uniq τ1 τ2 x h1 h2
              subst this
              rw [e1] at e2
              exact hjk (Option.some_injective _ e2)
            · intro j
              refine (Metric.isBounded_Icc (0:ℝ) H).subset ?_
              intro x hx
              simp only [lpSet, Set.mem_iUnion] at hx
              obtain ⟨τ, h, hx⟩ := hx
              have := F7 τ j h
              have : (τ : ℝ) + 1 ≤ H := by exact_mod_cast this
              exact ⟨le_trans (Nat.cast_nonneg _) hx.1, by linarith [hx.2]⟩
          have hVSg : V ⊆ Sg := by
            intro v hv
            rw [hVdef] at hv
            obtain ⟨σ, rfl⟩ := hv
            rw [hSgdef]
            refine ⟨fun j => lpSet (p ∘ σ) (r ∘ σ) (σ.symm j), ?_, ?_⟩
            · have h := hLPsched (p ∘ σ) (r ∘ σ)
              refine ⟨fun j => h.measurable _, fun j => by simpa using h.release (σ.symm j),
                fun j => by simpa using h.volume_eq (σ.symm j), ?_, fun j => h.bounded _⟩
              intro i k hik
              exact h.disjoint (fun e => hik (σ.symm.injective e))
            · funext j
              simp [mLP, AlphaJSched.meanBusyTime, Shared.meanBusyTime]
          have hVP : V ⊆ P := hVSg.trans hSgP
          -- HARD (measure theory): delaying one job far beyond the schedule
          open MeasureTheory in
          have hshift : ∀ s ∈ Sg, ∀ j : Fin n, ∀ t : ℝ, 0 ≤ t →
              s + t • (Pi.single j 1 : Fin n → ℝ) ∈ convexHull ℝ Sg := by
            intro s hs j t ht
            have hs' := hs
            rw [hSgdef] at hs'
            obtain ⟨A, hA, rfl⟩ := hs'
            obtain ⟨K0, hK0⟩ := (Bornology.isBounded_iUnion.2 fun i => hA.bounded i).subset_closedBall 0
            set K := max K0 0 with hK
            have hAK : ∀ i, ∀ x ∈ A i, |x| ≤ K := by
              intro i x hx
              have := hK0 (Set.mem_iUnion.2 ⟨i, hx⟩)
              rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
              exact this.trans (le_max_left _ _)
            set T : ℝ := t + 2 * K + 1 with hT
            have hK0' : 0 ≤ K := le_max_right _ _
            have hTpos : 0 < T := by rw [hT]; linarith
            have hmp : MeasurePreserving (fun x : ℝ => x - T) volume volume := measurePreserving_sub_right volume T
            have hemb : MeasurableEmbedding (fun x : ℝ => x - T) := measurableEmbedding_subRight T
            set A' : Fin n → Set ℝ := fun i => if i = j then (fun x : ℝ => x - T) ⁻¹' A j else A i with hA'
            have hA'j : A' j = (fun x : ℝ => x - T) ⁻¹' A j := by simp [hA']
            have hA'i : ∀ i, i ≠ j → A' i = A i := fun i hi => by simp [hA', hi]
            have hsched : Shared.IsPreemptiveSchedule p r A' := by
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · intro i
                by_cases hi : i = j
                · subst hi; rw [hA'j]; exact (hA.measurable i).preimage hemb.measurable
                · rw [hA'i i hi]; exact hA.measurable i
              · intro i
                by_cases hi : i = j
                · subst hi; rw [hA'j]
                  intro x hx
                  have := hA.release i hx
                  simp only [Set.mem_Ici] at this ⊢
                  linarith
                · rw [hA'i i hi]; exact hA.release i
              · intro i
                by_cases hi : i = j
                · subst hi; rw [hA'j, hmp.measure_preimage (hA.measurable i).nullMeasurableSet]
                  exact hA.volume_eq i
                · rw [hA'i i hi]; exact hA.volume_eq i
              · intro i k hik
                have farj : ∀ x ∈ A' j, K < x := by
                  intro x hx
                  rw [hA'j] at hx
                  have := hAK j _ hx
                  have h2 : -K ≤ x - T := (abs_le.1 this).1
                  linarith
                have nearj : ∀ i, i ≠ j → ∀ x ∈ A' i, x ≤ K := by
                  intro i hi x hx
                  rw [hA'i i hi] at hx
                  exact (abs_le.1 (hAK i x hx)).2
                by_cases hi : i = j
                · subst hi
                  have hk : k ≠ i := fun h => hik h.symm
                  rw [Function.onFun, Set.disjoint_left]
                  intro x hx hx'
                  linarith [farj x hx, nearj k hk x hx']
                by_cases hk : k = j
                · subst hk
                  rw [Function.onFun, Set.disjoint_left]
                  intro x hx hx'
                  linarith [farj x hx', nearj i hi x hx]
                · simp only [Function.onFun]
                  rw [hA'i i hi, hA'i k hk]
                  exact hA.disjoint hik
              · intro i
                by_cases hi : i = j
                · subst hi; rw [hA'j]
                  refine (Metric.isBounded_Icc (T - K) (T + K)).subset ?_
                  intro x hx
                  have h3 : -K ≤ x - T ∧ x - T ≤ K := abs_le.1 (hAK i _ hx)
                  constructor <;> linarith [h3.1, h3.2]
                · rw [hA'i i hi]; exact hA.bounded i
            have hint1 : IntegrableOn (fun t : ℝ => t) (A j) :=
              (continuous_id.integrableOn_Icc (a := sInf (A j)) (b := sSup (A j))).mono_set
                (hA.bounded j).subset_Icc_sInf_sSup
            have hmean : (fun i => Shared.meanBusyTime p A' i) =
                (fun i => Shared.meanBusyTime p A i) + T • (Pi.single j 1 : Fin n → ℝ) := by
              funext i
              by_cases hi : i = j
              · subst hi
                simp only [Shared.meanBusyTime, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
                rw [hA'j]
                have := hmp.setIntegral_preimage_emb hemb (fun y => y + T) (A i)
                simp only [sub_add_cancel] at this
                rw [this, integral_add hint1 (integrableOn_const (by rw [hA.volume_eq i]; exact ENNReal.natCast_ne_top _))]
                simp only [setIntegral_const, Measure.real, hA.volume_eq i, ENNReal.toReal_natCast, smul_eq_mul]
                have : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne'
                field_simp
              · simp only [Shared.meanBusyTime, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_eq_mul, mul_zero, add_zero]
                rw [hA'i i hi]
            have hmem : (fun i => Shared.meanBusyTime p A i) + T • (Pi.single j 1 : Fin n → ℝ) ∈ Sg := by
              rw [hSgdef]; exact ⟨A', hsched, hmean.symm⟩
            have hconv := convex_convexHull ℝ Sg (subset_convexHull ℝ Sg hs) (subset_convexHull ℝ Sg hmem)
              (a := 1 - t / T) (b := t / T) (by rw [sub_nonneg, div_le_one hTpos]; linarith)
              (div_nonneg ht hTpos.le) (by ring)
            convert hconv using 1
            rw [smul_add, smul_smul, ← add_assoc, ← add_smul]
            have : t / T * T = t := by field_simp
            rw [this]; simp
          have htrans : ∀ c : Fin n → ℝ, (∀ s ∈ Sg, s + c ∈ convexHull ℝ Sg) →
              ∀ x ∈ convexHull ℝ Sg, x + c ∈ convexHull ℝ Sg := by
            intro c hc
            have hconv : Convex ℝ {x : Fin n → ℝ | x + c ∈ convexHull ℝ Sg} := by
              intro x hx y hy a b ha hb hab
              have := convex_convexHull ℝ Sg hx hy ha hb hab
              simp only [Set.mem_ofPred_eq] at this ⊢
              convert this using 1
              rw [smul_add, smul_add]
              have : c = a • c + b • c := by rw [← add_smul, hab, one_smul]
              conv_lhs => rw [this]
              abel
            intro x hx
            exact convexHull_min (fun s hs => hc s hs) hconv hx
          have hdom : ∀ x ∈ convexHull ℝ Sg, ∀ d : Fin n → ℝ, (∀ j, 0 ≤ d j) →
              x + d ∈ convexHull ℝ Sg := by
            intro x hx d hd
            have key : ∀ T : Finset (Fin n),
                x + ∑ j ∈ T, d j • (Pi.single j 1 : Fin n → ℝ) ∈ convexHull ℝ Sg := by
              intro T
              induction T using Finset.induction_on with
              | empty => simpa using hx
              | insert a T haT ih =>
                rw [Finset.sum_insert haT]
                have := htrans (d a • (Pi.single a 1 : Fin n → ℝ))
                  (fun s hs => hshift s hs a (d a) (hd a)) _ ih
                convert this using 1
                abel
            have := key Finset.univ
            convert this using 2
            conv_lhs => rw [pi_eq_sum_univ d]
            refine Finset.sum_congr rfl fun j _ => ?_
            congr 1
            ext i; simp [Pi.single_apply, eq_comm]
          have hLPfacts : ∀ p' r' : Fin n → ℕ, ∃ H : ℕ, (∀ τ j, lpRun p' r' τ = some j → τ < H ∧ r' j ≤ τ) ∧
             (∀ j, ((Finset.range H).filter (fun τ => lpRun p' r' τ = some j)).card = p' j) := by
            intro p' r'
            have F1 : ∀ τ j, lpRemaining p' r' (τ+1) j =
                if lpRun p' r' τ = some j then lpRemaining p' r' τ j - 1 else lpRemaining p' r' τ j := by
              intro τ j; rfl
            have F2 : ∀ τ j, lpRun p' r' τ = some j → r' j ≤ τ ∧ 0 < lpRemaining p' r' τ j := by
              intro τ j h
              unfold lpRun lpPick at h
              split_ifs at h with hne
              · cases h
                have := Finset.min'_mem _ hne
                simpa using this
            have F2' : ∀ τ, (∃ j, r' j ≤ τ ∧ 0 < lpRemaining p' r' τ j) → ∃ k, lpRun p' r' τ = some k := by
              intro τ ⟨j, hj⟩
              unfold lpRun lpPick
              rw [dif_pos ⟨j, by simpa using hj⟩]
              exact ⟨_, rfl⟩
            have Fmono : ∀ τ j, lpRemaining p' r' (τ+1) j ≤ lpRemaining p' r' τ j := by
              intro τ j; rw [F1]; split_ifs <;> omega
            have F3 : ∀ τ j, ((Finset.range τ).filter (fun τ' => lpRun p' r' τ' = some j)).card
                + lpRemaining p' r' τ j = p' j := by
              intro τ j
              induction τ with
              | zero => simp [lpRemaining]
              | succ τ ih =>
                rw [Finset.range_add_one, Finset.filter_insert, F1]
                by_cases h : lpRun p' r' τ = some j
                · have := (F2 τ j h).2
                  rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
                  omega
                · rw [if_neg h, if_neg h]; exact ih
            set mr := Finset.univ.sup r' with hmr
            have hrle : ∀ j, r' j ≤ mr := fun j => Finset.le_sup (Finset.mem_univ j)
            set R : ℕ → ℕ := fun τ => ∑ j, lpRemaining p' r' τ j with hR
            have F4 : ∀ τ, mr ≤ τ → 0 < R τ → R (τ+1) + 1 = R τ := by
              intro τ hτ hpos
              obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => 0) (by simpa using hpos)
              obtain ⟨k, hk⟩ := F2' τ ⟨j, (hrle j).trans hτ, hj⟩
              have hk2 := (F2 τ k hk).2
              simp only [hR]
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
              rw [F1, if_pos hk]
              have : ∑ x ∈ Finset.univ.erase k, lpRemaining p' r' (τ + 1) x = ∑ x ∈ Finset.univ.erase k, lpRemaining p' r' τ x := by
                refine Finset.sum_congr rfl fun x hx => ?_
                rw [F1, if_neg]
                intro h; rw [hk] at h; exact (Finset.ne_of_mem_erase hx) (Option.some_injective _ h).symm
              rw [this]; omega
            have Fmono' : ∀ τ, R (τ+1) ≤ R τ := fun τ => Finset.sum_le_sum fun j _ => Fmono τ j
            have F5 : ∀ k, R (mr + k) + k ≤ ∑ j, p' j ∨ R (mr + k) = 0 := by
              intro k
              induction k with
              | zero =>
                left
                simp only [hR, add_zero]
                have := fun j => F3 mr j
                calc ∑ j, lpRemaining p' r' mr j ≤ ∑ j, p' j := Finset.sum_le_sum fun j _ => by have := this j; omega
              | succ k ih =>
                show R (mr + k + 1) + (k + 1) ≤ ∑ j, p' j ∨ R (mr + k + 1) = 0
                rcases Nat.eq_zero_or_pos (R (mr + k)) with h0 | hpos
                · right; have := Fmono' (mr + k); omega
                · have := F4 (mr + k) (by omega) hpos
                  rcases ih with ih | ih <;> omega
            set H := mr + ∑ j, p' j with hH
            have F6 : ∀ τ, H ≤ τ → ∀ j, lpRemaining p' r' τ j = 0 := by
              have h0 : R H = 0 := by
                have h : R H + ∑ j, p' j ≤ ∑ j, p' j ∨ R H = 0 := F5 _
                omega
              intro τ hτ
              obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hτ
              have : R (H + d) = 0 := by
                induction d with
                | zero => simpa using h0
                | succ d ih => have := Fmono' (H + d); show R (H + d + 1) = 0; omega
              intro j
              have := (Finset.sum_eq_zero_iff.1 this) j (Finset.mem_univ j)
              exact this
            have F7 : ∀ τ j, lpRun p' r' τ = some j → τ < H := by
              intro τ j h
              by_contra hc
              have := (F2 τ j h).2
              rw [F6 τ (by omega) j] at this
              exact lt_irrefl _ this
            have F8 : ∀ j, ((Finset.range H).filter (fun τ' => lpRun p' r' τ' = some j)).card = p' j := by
              intro j; have := F3 H j; rw [F6 H le_rfl j] at this; simpa using this
            exact ⟨H, fun τ j h => ⟨F7 τ j h, (F2 τ j h).1⟩, F8⟩
          have hWC : ∀ p' r' : Fin n → ℕ, ∀ τ i, (∀ j ≤ i, lpRun p' r' τ ≠ some j) → r' i ≤ τ →
              ∀ τ', lpRun p' r' τ' = some i → τ' < τ := by
            intro p' r' τ i hno hri τ' hrun
            by_contra hge
            push Not at hge
            have F1 : ∀ τ j, lpRemaining p' r' (τ+1) j =
                if lpRun p' r' τ = some j then lpRemaining p' r' τ j - 1 else lpRemaining p' r' τ j := by
              intro τ j; rfl
            have Fmono : ∀ j, Antitone (fun τ => lpRemaining p' r' τ j) := by
              intro j
              refine antitone_nat_of_succ_le fun τ => ?_
              rw [F1]; split_ifs <;> omega
            have hpos : 0 < lpRemaining p' r' τ' i := by
              unfold lpRun lpPick at hrun
              split_ifs at hrun with hne
              · cases hrun
                have := Finset.min'_mem _ hne
                exact (Finset.mem_filter.1 this).2.2
            have hpos2 : 0 < lpRemaining p' r' τ i := lt_of_lt_of_le hpos (Fmono i hge)
            have hmem : i ∈ Finset.univ.filter (fun j => r' j ≤ τ ∧ 0 < lpRemaining p' r' τ j) :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, hri, hpos2⟩
            refine hno _ (Finset.min'_le _ i hmem) ?_
            unfold lpRun lpPick
            rw [dif_pos ⟨i, hmem⟩]
          -- general work-conserving bound
          have hblock : ∀ (p' r' : Fin n → ℕ) (M : Fin n → ℝ) (g : ℕ → Option (Fin n)) (H : ℕ),
              (∀ j, 0 < p' j) → Shared.FeasibleR p' r' M →
              (∀ τ j, g τ = some j → τ < H ∧ r' j ≤ τ) →
              (∀ j, ((Finset.range H).filter (fun τ => g τ = some j)).card = p' j) →
              ∀ S : Finset (Fin n),
              (∀ τ, (∀ j ∈ S, g τ ≠ some j) → ∀ j ∈ S, r' j ≤ τ → ∀ τ', g τ' = some j → τ' < τ) →
              ∑ j ∈ S, ∑ τ ∈ (Finset.range H).filter (fun τ => g τ = some j), ((τ : ℝ) + 1 / 2)
                ≤ ∑ j ∈ S, (p' j : ℝ) * M j := by
            intro p' r' M g H hp' hM hg hcard S
            induction S using Finset.strongInduction with
            | H S ih =>
            intro hwc
            rcases S.eq_empty_or_nonempty with rfl | hS
            · simp
            obtain ⟨j0, hj0S, hj0⟩ := Finset.exists_mem_eq_inf' hS (fun j => (r' j : ℝ))
            have hrmin : Shared.rmin r' S hS = (r' j0 : ℝ) := hj0
            have hj0min : ∀ j ∈ S, r' j0 ≤ r' j := by
              intro j hj
              have : (r' j0 : ℝ) ≤ r' j := hj0 ▸ Finset.inf'_le (fun j => (r' j : ℝ)) hj
              exact_mod_cast this
            by_cases hgap : ∃ τ, r' j0 ≤ τ ∧ (∀ j ∈ S, g τ ≠ some j) ∧ ∃ τ', τ < τ' ∧ ∃ j ∈ S, g τ' = some j
            · obtain ⟨τ, hτ, hno, τ', hττ', j1, hj1, hgj1⟩ := hgap
              have hfin : ∀ j ∈ S, r' j ≤ τ → ∀ τ', g τ' = some j → τ' < τ := hwc τ hno
              have hj1r : τ < r' j1 := by
                by_contra h
                have := hfin j1 hj1 (by omega) τ' hgj1
                omega
              have h1 := ih (S.filter (fun j => r' j ≤ τ))
                (Finset.filter_ssubset.2 ⟨j1, hj1, by omega⟩) (by
                  intro τ1 hno1 j hj hrj τ2 hg2
                  rw [Finset.mem_filter] at hj
                  by_cases h : ∀ i ∈ S, g τ1 ≠ some i
                  · exact hwc τ1 h j hj.1 hrj τ2 hg2
                  · push Not at h
                    obtain ⟨i, hi, hgi⟩ := h
                    have hri : τ < r' i := by
                      by_contra hc
                      exact hno1 i (Finset.mem_filter.2 ⟨hi, by omega⟩) hgi
                    have := (hg τ1 i hgi).2
                    have := hfin j hj.1 hj.2 τ2 hg2
                    omega)
              have h2 := ih (S.filter (fun j => ¬ r' j ≤ τ))
                (Finset.filter_ssubset.2 ⟨j0, hj0S, by omega⟩) (by
                  intro τ1 hno1 j hj hrj τ2 hg2
                  rw [Finset.mem_filter] at hj
                  by_cases h : ∀ i ∈ S, g τ1 ≠ some i
                  · exact hwc τ1 h j hj.1 hrj τ2 hg2
                  · push Not at h
                    obtain ⟨i, hi, hgi⟩ := h
                    have hri : r' i ≤ τ := by
                      by_contra hc
                      exact hno1 i (Finset.mem_filter.2 ⟨hi, hc⟩) hgi
                    have := hfin i hi hri τ1 hgi
                    omega)
              rw [← Finset.sum_filter_add_sum_filter_not S (fun j => r' j ≤ τ),
                ← Finset.sum_filter_add_sum_filter_not S (fun j => r' j ≤ τ) (fun j => (p' j : ℝ) * M j)]
              exact add_le_add h1 h2
            · set T : Finset ℕ := S.biUnion (fun j => (Finset.range H).filter (fun τ => g τ = some j)) with hT
              have hdisj : Set.PairwiseDisjoint (↑S : Set (Fin n))
                  (fun j => (Finset.range H).filter (fun τ => g τ = some j)) := by
                intro i _ j _ hij
                rw [Function.onFun, Finset.disjoint_left]
                intro τ h1 h2
                rw [Finset.mem_filter] at h1 h2
                exact hij (Option.some_injective _ (h1.2.symm.trans h2.2))
              have hsumT : ∑ j ∈ S, ∑ τ ∈ (Finset.range H).filter (fun τ => g τ = some j), ((τ : ℝ) + 1 / 2)
                  = ∑ τ ∈ T, ((τ : ℝ) + 1 / 2) := (Finset.sum_biUnion hdisj).symm
              have hcT : T.card = ∑ j ∈ S, p' j := by
                rw [hT, Finset.card_biUnion hdisj]
                exact Finset.sum_congr rfl fun j _ => hcard j
              have hmemT : ∀ τ, τ ∈ T ↔ ∃ j ∈ S, g τ = some j := by
                intro τ
                simp only [hT, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
                constructor
                · rintro ⟨j, hj, -, h⟩; exact ⟨j, hj, h⟩
                · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (hg τ j h).1, h⟩
              have hTne : T.Nonempty := by
                rw [← Finset.card_pos, hcT]
                exact Finset.sum_pos (fun j _ => hp' j) hS
              set N := T.max' hTne with hN
              have hNT : N ∈ T := T.max'_mem hTne
              have hTeq : T = Finset.Ico (r' j0) (N + 1) := by
                ext τ
                rw [Finset.mem_Ico]
                constructor
                · intro h
                  have h3 := T.le_max' τ h
                  obtain ⟨j, hj, hgj⟩ := (hmemT τ).1 h
                  have := (hg τ j hgj).2
                  have := hj0min j hj
                  omega
                · rintro ⟨h1, h2⟩
                  by_contra hc
                  have hne : τ ≠ N := fun h => hc (h ▸ hNT)
                  refine hgap ⟨τ, h1, fun j hj hgj => hc ((hmemT τ).2 ⟨j, hj, hgj⟩), N, by omega, ?_⟩
                  exact (hmemT N).1 hNT
              have hNm : T = Finset.Ico (r' j0) (r' j0 + ∑ j ∈ S, p' j) := by
                have hc2 := hcT
                rw [hTeq, Nat.card_Ico] at hc2
                have : 0 < ∑ j ∈ S, p' j := Finset.sum_pos (fun j _ => hp' j) hS
                rw [hTeq]
                congr 1
                omega
              have hclosed : ∀ k : ℕ, ∑ τ ∈ Finset.Ico (r' j0) (r' j0 + k), ((τ : ℝ) + 1 / 2)
                  = (k : ℝ) * ((r' j0 : ℝ) + (k : ℝ) / 2) := by
                intro k
                induction k with
                | zero => simp
                | succ k ih =>
                  rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), ih]; push_cast; ring
              have hpS : Shared.pSum p' S = ((∑ j ∈ S, p' j : ℕ) : ℝ) := by
                simp [Shared.pSum]
              have key := hM S hS
              rw [hrmin, hpS] at key
              rw [hsumT, hNm, hclosed]
              exact key
          -- Abel summation
          have hAbel : ∀ c d : Fin n → ℝ, Antitone c → (∀ i, 0 ≤ c i) →
              (∀ k : ℕ, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), d i) →
              0 ≤ ∑ i, c i * d i := by
            intro c d hc hc0 hd
            set C : ℕ → ℝ := fun m => if h : m < n then c ⟨m, h⟩ else 0 with hC
            have hC0 : ∀ m, 0 ≤ C m := by
              intro m; simp only [hC]; split_ifs
              · exact hc0 _
              · exact le_rfl
            have hCanti : ∀ m, C (m + 1) ≤ C m := by
              intro m
              simp only [hC]
              split_ifs with h1 h2 h2
              · exact hc (by simp [Fin.le_def])
              · omega
              · exact hc0 _
              · exact le_rfl
            have Q : ∀ m, C m * ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), d i ≤
                ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), c i * d i := by
              intro m
              induction m with
              | zero => simp
              | succ m ih =>
                by_cases h : m < n
                · have hins : Finset.univ.filter (fun i : Fin n => i.val < m + 1) =
                      insert ⟨m, h⟩ (Finset.univ.filter (fun i : Fin n => i.val < m)) := by
                    ext i
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
                    omega
                  have hD := hd (m + 1)
                  refine (mul_le_mul_of_nonneg_right (hCanti m) hD).trans ?_
                  rw [hins, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
                  have : C m = c ⟨m, h⟩ := by simp [hC, h]
                  rw [this] at ih ⊢
                  linarith
                · have hsame : Finset.univ.filter (fun i : Fin n => i.val < m + 1) =
                      Finset.univ.filter (fun i : Fin n => i.val < m) := by
                    ext i
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                    have := i.isLt
                    omega
                  have e1 : C m = 0 := by simp [hC, h]
                  have e2 : C (m+1) = 0 := by simp only [hC]; rw [dif_neg (by omega)]
                  rw [hsame, e2]; rw [e1] at ih; exact ih
            have := Q n
            have hall : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
              ext i; simp
            rw [hall] at this
            refine le_trans (mul_nonneg (hC0 n) ?_) this
            have := hd n; rwa [hall] at this
          open MeasureTheory in
          have hmLP : ∀ (p' r' : Fin n → ℕ) (H : ℕ), (∀ j, 0 < p' j) →
              (∀ τ j, lpRun p' r' τ = some j → τ < H ∧ r' j ≤ τ) → ∀ j,
              (p' j : ℝ) * mLP p' r' j =
                ∑ τ ∈ (Finset.range H).filter (fun τ => lpRun p' r' τ = some j), ((τ : ℝ) + 1 / 2) := by
            intro p' r' H hp' hH1 j
            have hne : (p' j : ℝ) ≠ 0 := by exact_mod_cast (hp' j).ne'
            simp only [mLP, AlphaJSched.meanBusyTime]
            rw [← mul_assoc, mul_one_div_cancel hne, one_mul]
            have hset : lpSet p' r' j = ⋃ τ ∈ (Finset.range H).filter
                (fun τ => lpRun p' r' τ = some j), Set.Ico (τ : ℝ) (τ + 1) := by
              ext x
              simp only [lpSet, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, exists_prop]
              constructor
              · rintro ⟨τ, h, hx⟩; exact ⟨τ, ⟨(hH1 τ _ h).1, h⟩, hx⟩
              · rintro ⟨τ, ⟨-, h⟩, hx⟩; exact ⟨τ, h, hx⟩
            rw [hset, integral_biUnion_finset]
            · refine Finset.sum_congr rfl fun τ _ => ?_
              rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_id]
              ring
            · intro _ _; exact measurableSet_Ico
            · intro τ1 _ τ2 _ hne
              rw [Function.onFun, Set.disjoint_left]
              intro x h1 h2
              apply hne
              have a1 : (τ1 : ℝ) < τ2 + 1 := lt_of_le_of_lt h1.1 h2.2
              have a2 : (τ2 : ℝ) < τ1 + 1 := lt_of_le_of_lt h2.1 h1.2
              have b1 : τ1 < τ2 + 1 := by exact_mod_cast a1
              have b2 : τ2 < τ1 + 1 := by exact_mod_cast a2
              omega
            · intro τ _
              exact continuous_id.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
          have hL : ∀ w : Fin n → ℝ, (∀ j, 0 ≤ w j) →
              ∃ v ∈ V, ∀ M ∈ P, ∑ j, w j * v j ≤ ∑ j, w j * M j := by
            intro w hw
            set f : Fin n → ℝ := fun j => -(w j / (p j : ℝ)) with hf
            set σ : Equiv.Perm (Fin n) := Tuple.sort f with hσ
            have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
            refine ⟨fun j => mLP (p ∘ σ) (r ∘ σ) (σ.symm j), ⟨σ, rfl⟩, ?_⟩
            intro M hM
            have hM' : Shared.FeasibleR (p ∘ σ) (r ∘ σ) (M ∘ σ) := by
              intro S hS
              have hS' : (S.map σ.toEmbedding).Nonempty := hS.map
              have key := hM (S.map σ.toEmbedding) hS'
              have e1 : Shared.pSum p (S.map σ.toEmbedding) = Shared.pSum (p ∘ σ) S := by
                simp [Shared.pSum, Finset.sum_map]
              have e2 : Shared.rmin r (S.map σ.toEmbedding) hS' = Shared.rmin (r ∘ σ) S hS := by
                simp only [Shared.rmin]
                rw [Finset.inf'_map]
                rfl
              rw [e1, e2, Finset.sum_map] at key
              exact key
            have hp' : ∀ j, 0 < (p ∘ σ) j := fun j => hp _
            obtain ⟨H, hH1, hH2⟩ := hLPfacts (p ∘ σ) (r ∘ σ)
            have hpre : ∀ k : ℕ, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
                (((p ∘ σ) i : ℝ) * (M ∘ σ) i - ((p ∘ σ) i : ℝ) * mLP (p ∘ σ) (r ∘ σ) i) := by
              intro k
              rw [Finset.sum_sub_distrib, sub_nonneg]
              have := hblock (p ∘ σ) (r ∘ σ) (M ∘ σ) (lpRun (p ∘ σ) (r ∘ σ)) H hp' hM' hH1 hH2
                (Finset.univ.filter (fun i : Fin n => i.val < k)) (by
                  intro τ hno j hj hrj τ' hrun
                  refine hWC _ _ τ j ?_ hrj τ' hrun
                  intro i hi
                  refine hno i ?_
                  rw [Finset.mem_filter] at hj ⊢
                  refine ⟨Finset.mem_univ _, lt_of_le_of_lt ?_ hj.2⟩
                  exact hi)
              refine le_trans (le_of_eq ?_) this
              exact Finset.sum_congr rfl fun j _ => hmLP _ _ H hp' hH1 j
            have hab := hAbel (fun i => w (σ i) / (p (σ i) : ℝ)) _
              (fun i j hij => by have := hmono hij; simp only [hf, Function.comp_apply] at this; linarith)
              (fun i => div_nonneg (hw _) (Nat.cast_nonneg _)) hpre
            rw [← Equiv.sum_comp σ, ← Equiv.sum_comp σ (fun j => w j * M j), ← sub_nonneg,
              ← Finset.sum_sub_distrib]
            refine hab.trans (le_of_eq ?_)
            refine Finset.sum_congr rfl fun i _ => ?_
            have hne : (p (σ i) : ℝ) ≠ 0 := by exact_mod_cast (hp (σ i)).ne'
            simp only [Function.comp_apply, Equiv.symm_apply_apply]
            field_simp
          open Pointwise in
          have hK : ∀ M ∈ P, ∃ v ∈ convexHull ℝ V, ∀ j, v j ≤ M j := by
            intro M hM
            set C : Set (Fin n → ℝ) := {x | ∀ j, 0 ≤ x j} with hC
            have hCc : IsClosed C := by
              rw [hC]; simp only [Set.ofPred_forall]
              exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
            have hCconv : Convex ℝ C := by
              intro x hx y hy a b ha hb _ j
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              have := hx j; have := hy j; positivity
            have hVfin : V.Finite := Set.finite_range _
            have hQc : IsClosed (convexHull ℝ V + C) :=
              hCc.add_left_of_isCompact (hVfin.isCompact_convexHull (𝕜 := ℝ))
            have hQconv : Convex ℝ (convexHull ℝ V + C) := Convex.add (𝕜 := ℝ) (convex_convexHull ℝ V) hCconv
            by_cases hMQ : M ∈ convexHull ℝ V + C
            · obtain ⟨v, hv, c, hc, rfl⟩ := hMQ
              exact ⟨v, hv, fun j => by simp only [Pi.add_apply]; linarith [hc j]⟩
            exfalso
            obtain ⟨f, u, hfM, hfQ⟩ := geometric_hahn_banach_point_closed hQconv hQc hMQ
            set w : Fin n → ℝ := fun j => f (Pi.single j 1) with hw
            have hfx : ∀ x : Fin n → ℝ, f x = ∑ j, w j * x j := by
              intro x
              conv_lhs => rw [pi_eq_sum_univ x]
              rw [map_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [map_smul, smul_eq_mul, hw, mul_comm]
              congr 2
              ext i; simp [Pi.single_apply, eq_comm]
            have hVne : V.Nonempty := Set.range_nonempty _
            obtain ⟨v0, hv0⟩ := hVne
            have hwnn : ∀ j, 0 ≤ w j := by
              intro j
              by_contra hneg
              push Not at hneg
              set t : ℝ := (f v0 - u) / (- w j) + 1 with ht
              have hmem : v0 + t • Pi.single j 1 ∈ convexHull ℝ V + C := by
                refine ⟨v0, subset_convexHull ℝ V hv0, t • Pi.single j 1, ?_, rfl⟩
                have hfv0 : u < f v0 := by
                  have := hfQ v0 ⟨v0, subset_convexHull ℝ V hv0, 0, fun _ => le_refl 0, by simp⟩
                  exact this
                have htpos : 0 ≤ t := by
                  rw [ht]
                  have : 0 ≤ (f v0 - u) / (- w j) := div_nonneg (by linarith) (by linarith)
                  linarith
                intro i
                simp only [Pi.smul_apply, smul_eq_mul]
                by_cases hij : i = j
                · subst hij; simp [htpos]
                · simp [hij]
              have h1 := hfQ _ hmem
              rw [map_add, map_smul, smul_eq_mul] at h1
              have h2 : f (Pi.single j 1) = w j := rfl
              rw [h2, ht] at h1
              have hne : (-w j) ≠ 0 := by linarith
              have hne' : w j ≠ 0 := by linarith
              have : (f v0 - u) / -w j * w j = -(f v0 - u) := by
                field_simp
              nlinarith
            obtain ⟨v, hvV, hvopt⟩ := hL w hwnn
            have h1 := hfQ v ⟨v, subset_convexHull ℝ V hvV, 0, fun _ => le_refl 0, by simp⟩
            have h2 := hvopt M hM
            rw [hfx] at h1 hfM
            linarith
          have hconvVP : convexHull ℝ V ⊆ P := convexHull_min hVP hPconv
          have partII : ∀ M ∈ Set.extremePoints ℝ P, M ∈ V := by
            intro M hM
            obtain ⟨v, hv, hvM⟩ := hK M hM.1
            have hvP : v ∈ P := hconvVP hv
            have hwP : M + (M - v) ∈ P := hPup M hM.1 _ (fun j => by simp [hvM j])
            have hmid : M ∈ openSegment ℝ v (M + (M - v)) := by
              refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
              ext j; simp; ring
            have := hM.2 hvP hwP hmid
            have hMV : M ∈ convexHull ℝ V := this ▸ hv
            have hext : M ∈ Set.extremePoints ℝ (convexHull ℝ V) :=
              inter_extremePoints_subset_extremePoints_of_subset hconvVP ⟨hMV, hM⟩
            exact extremePoints_convexHull_subset hext
          open MeasureTheory in
          have hVfin : ∀ σ : Equiv.Perm (Fin n), ∃ y : Fin n → ℕ → ℝ, FeasibleDinf p r y ∧
              (∃ H : ℕ, ∀ j τ, H ≤ τ → y j τ = 0) ∧
              mMap p y = fun j => mLP (p ∘ σ) (r ∘ σ) (σ.symm j) := by
            intro σ
            obtain ⟨H, hH1, hH2⟩ := hLPfacts (p ∘ σ) (r ∘ σ)
            set y : Fin n → ℕ → ℝ := fun j τ => if lpRun (p ∘ σ) (r ∘ σ) τ = some (σ.symm j) then 1 else 0 with hy
            have hsupp : ∀ j τ, τ ∉ Finset.range H → y j τ = 0 := by
              intro j τ hτ
              simp only [hy]; rw [if_neg]
              intro h; exact hτ (Finset.mem_range.2 (hH1 τ _ h).1)
            have hfin : ∀ (j : Fin n) (g : ℕ → ℝ), HasSum (fun τ => y j τ * g τ)
                (∑ τ ∈ (Finset.range H).filter (fun τ => lpRun (p ∘ σ) (r ∘ σ) τ = some (σ.symm j)), g τ) := by
              intro j g
              have := (hasSum_sum_of_ne_finset_zero (fun τ hτ => by simp [hsupp j τ hτ]) :
                HasSum (fun τ => y j τ * g τ) (∑ τ ∈ Finset.range H, y j τ * g τ))
              convert this using 1
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun τ _ => ?_
              simp only [hy]; split_ifs <;> simp
            refine ⟨y, ⟨?_, ?_, ?_, ?_⟩, ⟨H, fun j τ hτ => hsupp j τ (by simpa using hτ)⟩, ?_⟩
            · intro j τ; simp only [hy]; split_ifs <;> norm_num
            · intro j τ hτ
              simp only [hy]; rw [if_neg]
              intro h; have := (hH1 τ _ h).2; simp at this; omega
            · intro τ
              simp only [hy]
              rw [← Equiv.sum_comp σ]
              simp only [Equiv.symm_apply_apply]
              rcases hrun : lpRun (p ∘ σ) (r ∘ σ) τ with _ | k
              · simp
              · simp
            · intro j
              have := hfin j (fun _ => 1)
              simp only [mul_one, Finset.sum_const, nsmul_eq_mul, mul_one, hH2] at this
              simpa using this
            · funext j
              simp only [mMap, mLP, AlphaJSched.meanBusyTime, Function.comp_apply, Equiv.apply_symm_apply]
              congr 1
              rw [(hfin j (fun τ => (τ : ℝ) + 1 / 2)).tsum_eq]
              have hset : lpSet (p ∘ σ) (r ∘ σ) (σ.symm j) = ⋃ τ ∈ (Finset.range H).filter
                  (fun τ => lpRun (p ∘ σ) (r ∘ σ) τ = some (σ.symm j)), Set.Ico (τ : ℝ) (τ + 1) := by
                ext x
                simp only [lpSet, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, exists_prop]
                constructor
                · rintro ⟨τ, h, hx⟩; exact ⟨τ, ⟨(hH1 τ _ h).1, h⟩, hx⟩
                · rintro ⟨τ, ⟨-, h⟩, hx⟩; exact ⟨τ, h, hx⟩
              rw [hset, integral_biUnion_finset]
              · refine Finset.sum_congr rfl fun τ _ => ?_
                rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_id]
                ring
              · intro _ _; exact measurableSet_Ico
              · intro τ1 _ τ2 _ hne
                rw [Function.onFun, Set.disjoint_left]
                intro x h1 h2
                apply hne
                have a1 : (τ1 : ℝ) < τ2 + 1 := lt_of_le_of_lt h1.1 h2.2
                have a2 : (τ2 : ℝ) < τ1 + 1 := lt_of_le_of_lt h2.1 h1.2
                have b1 : τ1 < τ2 + 1 := by exact_mod_cast a1
                have b2 : τ2 < τ1 + 1 := by exact_mod_cast a2
                omega
              · intro τ _
                exact continuous_id.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
          refine ⟨?_, ?_, ?_⟩
          · apply Set.Subset.antisymm
            · intro M hM
              obtain ⟨v, hv, hvM⟩ := hK M hM
              have hv' : v ∈ convexHull ℝ Sg := convexHull_mono hVSg hv
              have := hdom v hv' (M - v) (fun j => by simp [hvM j])
              simpa using this
            · exact convexHull_min hSgP hPconv
          · intro M hM
            obtain ⟨σ, hσ⟩ := partII M hM
            exact ⟨σ, hσ.symm⟩
          · set Y : Set (Fin n → ℕ → ℝ) := {y | FeasibleDinf p r y ∧
                ∀ j, Summable (fun τ : ℕ => y j τ * ((τ : ℝ) + 1 / 2))} with hYdef
            set Z : Set (Fin n → ℝ) := mMap p '' Y with hZdef
            -- HARD (discrete version of the schedule bound)
            have hZP : Z ⊆ P := by
              have hdisc : ∀ (R m : ℕ) (z : ℕ → ℝ), (∀ τ, 0 ≤ z τ) → (∀ τ, z τ ≤ 1) → (∀ τ, τ < R → z τ = 0) →
                  HasSum z (m : ℝ) → Summable (fun τ : ℕ => z τ * ((τ : ℝ) + 1 / 2)) →
                  (m : ℝ) * ((R : ℝ) + (m : ℝ) / 2) ≤ ∑' τ : ℕ, z τ * ((τ : ℝ) + 1 / 2) := by
                intro R m z h0 h1 hr hs hm
                have hclosed : ∀ k : ℕ, (k : ℝ) * ((R : ℝ) + (k : ℝ) / 2)
                    = ∑ x ∈ Finset.range k, (((R + x : ℕ) : ℝ) + 1 / 2) := by
                  intro k
                  induction k with
                  | zero => simp
                  | succ k ih => rw [Finset.sum_range_succ, ← ih]; push_cast; ring
                set e : ℕ → ℝ := fun τ => if R ≤ τ ∧ τ < R + m then 1 else 0 with he
                have esupp : ∀ τ ∉ Finset.range (R + m), e τ = 0 := by
                  intro τ hτ; simp at hτ; simp [he]; omega
                have heS : HasSum e (m : ℝ) := by
                  have := (hasSum_sum_of_ne_finset_zero esupp : HasSum e (∑ τ ∈ Finset.range (R+m), e τ))
                  convert this using 1
                  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le R) (Nat.le_add_right R m)]
                  rw [Finset.sum_eq_zero (fun τ hτ => by simp at hτ; simp [he]; omega), zero_add]
                  rw [Finset.sum_congr rfl (fun τ hτ => by simp at hτ; simp [he]; omega : ∀ τ ∈ Finset.Ico R (R+m), e τ = 1)]
                  simp
                have hem : HasSum (fun τ : ℕ => e τ * ((τ : ℝ) + 1 / 2)) ((m : ℝ) * ((R : ℝ) + (m : ℝ) / 2)) := by
                  have := (hasSum_sum_of_ne_finset_zero (fun τ hτ => by simp [esupp τ hτ]) :
                    HasSum (fun τ : ℕ => e τ * ((τ : ℝ) + 1 / 2)) (∑ τ ∈ Finset.range (R+m), e τ * ((τ : ℝ) + 1 / 2)))
                  convert this using 1
                  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le R) (Nat.le_add_right R m)]
                  rw [Finset.sum_eq_zero (fun τ hτ => by simp at hτ; simp [he]; omega), zero_add]
                  rw [Finset.sum_congr rfl (fun τ hτ => by simp at hτ; simp [he]; omega : ∀ τ ∈ Finset.Ico R (R+m), e τ * ((τ : ℝ) + 1 / 2) = (τ : ℝ) + 1/2)]
                  rw [Finset.sum_Ico_eq_sum_range]
                  simp only [add_tsub_cancel_left]
                  exact hclosed m
                set c : ℝ := (R : ℝ) + m - 1 / 2 with hc
                have hterm : ∀ τ : ℕ, e τ * ((τ : ℝ) + 1 / 2) + (z τ - e τ) * (c + 1 / 2)
                    ≤ z τ * ((τ : ℝ) + 1 / 2) := by
                  intro τ
                  have key : 0 ≤ (z τ - e τ) * ((τ : ℝ) - c) := by
                    by_cases hA : τ < R
                    · simp [he, hr τ hA, show ¬ (R ≤ τ ∧ τ < R + m) by omega]
                    by_cases hB : τ < R + m
                    · have hE : e τ = 1 := by simp [he]; omega
                      rw [hE]
                      have : (τ : ℝ) + 1 ≤ R + m := by exact_mod_cast hB
                      have := h1 τ
                      nlinarith
                    · have hE : e τ = 0 := by simp [he]; omega
                      rw [hE]
                      have : (R : ℝ) + m ≤ τ := by exact_mod_cast (not_lt.mp hB)
                      have := h0 τ
                      nlinarith
                  nlinarith
                have hsum2 : HasSum (fun τ : ℕ => e τ * ((τ : ℝ) + 1 / 2) + (z τ - e τ) * (c + 1 / 2))
                    ((m : ℝ) * ((R : ℝ) + (m : ℝ) / 2) + ((m:ℝ) - m) * (c + 1/2)) :=
                  hem.add ((hs.sub heS).mul_right _)
                have := hasSum_le hterm hsum2 hm.hasSum
                simpa using this
              rintro _ ⟨y, ⟨⟨h0, hr, hc, hs⟩, hm⟩, rfl⟩ S hS
              obtain ⟨j0, hj0S, hj0⟩ := Finset.exists_mem_eq_inf' hS (fun j => (r j : ℝ))
              have hrmin : Shared.rmin r S hS = (r j0 : ℝ) := hj0
              have hpS : Shared.pSum p S = ((∑ j ∈ S, p j : ℕ) : ℝ) := by
                simp [Shared.pSum]
              have hz0 : ∀ τ, 0 ≤ ∑ j ∈ S, y j τ := fun τ => Finset.sum_nonneg fun j _ => h0 j τ
              have hz1 : ∀ τ, ∑ j ∈ S, y j τ ≤ 1 := fun τ =>
                (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
                  (fun j _ _ => h0 j τ)).trans (hc τ)
              have hzr : ∀ τ, τ < r j0 → ∑ j ∈ S, y j τ = 0 := by
                intro τ hτ
                refine Finset.sum_eq_zero fun j hj => hr j τ ?_
                have : (r j0 : ℝ) ≤ r j := hj0 ▸ Finset.inf'_le (fun j => (r j : ℝ)) hj
                have : r j0 ≤ r j := by exact_mod_cast this
                omega
              have hzs : HasSum (fun τ => ∑ j ∈ S, y j τ) ((∑ j ∈ S, p j : ℕ) : ℝ) := by
                push_cast
                exact hasSum_sum fun j _ => hs j
              have hzm : Summable (fun τ : ℕ => (∑ j ∈ S, y j τ) * ((τ : ℝ) + 1 / 2)) := by
                simp only [Finset.sum_mul]
                exact summable_sum fun j _ => hm j
              have key := hdisc (r j0) (∑ j ∈ S, p j) _ hz0 hz1 hzr hzs hzm
              rw [hrmin, hpS]
              refine key.trans (le_of_eq ?_)
              simp only [mMap, Finset.sum_mul]
              rw [Summable.tsum_finsetSum (fun j _ => hm j)]
              refine Finset.sum_congr rfl fun j _ => ?_
              have : (p j : ℝ) ≠ 0 := by exact_mod_cast (hp j).ne'
              rw [← mul_assoc, mul_one_div_cancel this, one_mul]
            have hVZ : ∀ v ∈ V, ∀ d : Fin n → ℝ, (∀ j, 0 ≤ d j) → v + d ∈ Z := by
              intro v hv d hd
              obtain ⟨σ, rfl⟩ := hv
              obtain ⟨y, ⟨hy0, hyr, hyc, hys⟩, ⟨H, hH⟩, hym⟩ := hVfin σ
              obtain ⟨K1, hK1⟩ := exists_nat_ge (∑ j, d j)
              set K : ℕ := K1 + H + 1 with hKdef
              have hdK : ∀ j, d j ≤ K := by
                intro j
                have h1 : d j ≤ ∑ j, d j := Finset.single_le_sum (fun i _ => hd i) (Finset.mem_univ j)
                have : (K1 : ℝ) ≤ K := by exact_mod_cast (by omega : K1 ≤ K)
                linarith
              set D : Fin n → ℕ := fun j => (j.val + 1) * K with hD
              have hDK : ∀ j, K ≤ D j := fun j => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
              have hDpos : ∀ j, (0:ℝ) < D j := fun j => by
                have := hDK j
                exact_mod_cast (by omega : 0 < D j)
              have hdD : ∀ j, d j ≤ D j := fun j => (hdK j).trans (by exact_mod_cast hDK j)
              set l : Fin n → ℝ := fun j => d j / D j with hl
              have hl0 : ∀ j, 0 ≤ l j := fun j => div_nonneg (hd j) (hDpos j).le
              have hl1 : ∀ j, l j ≤ 1 := fun j => (div_le_one (hDpos j)).2 (hdD j)
              have hlD : ∀ j, l j * D j = d j := fun j => div_mul_cancel₀ _ (hDpos j).ne'
              set s : Fin n → ℕ → ℝ := fun j τ => if D j ≤ τ then y j (τ - D j) else 0 with hs
              have hs0 : ∀ j τ, 0 ≤ s j τ := by
                intro j τ; simp only [hs]; split_ifs
                · exact hy0 _ _
                · exact le_rfl
              have hsadd : ∀ j τ, s j (τ + D j) = y j τ := by intro j τ; simp [hs]
              have hsoff : ∀ j τ, τ ∉ Set.range (fun τ => τ + D j) → s j τ = 0 := by
                intro j τ hτ
                simp only [hs]; rw [if_neg]
                intro h; exact hτ ⟨τ - D j, by simp only []; omega⟩
              have hy1 : ∀ j τ, y j τ ≤ 1 := fun j τ =>
                (Finset.single_le_sum (fun i _ => hy0 i τ) (Finset.mem_univ j)).trans (hyc τ)
              have hymS : ∀ j, HasSum (fun τ : ℕ => y j τ * ((τ : ℝ) + 1 / 2))
                  (∑' τ : ℕ, y j τ * ((τ : ℝ) + 1 / 2)) := by
                intro j
                refine Summable.hasSum (summable_of_ne_finset_zero (s := Finset.range H) ?_)
                intro τ hτ
                rw [hH j τ (by simpa using hτ), zero_mul]
              have hsS : ∀ j, HasSum (s j) (p j : ℝ) := by
                intro j
                refine ((add_left_injective (D j)).hasSum_iff (f := s j) (hsoff j)).1 ?_
                have : s j ∘ (fun τ => τ + D j) = fun τ => y j τ := by
                  ext τ; exact hsadd j τ
                rw [this]; exact hys j
              have hsm : ∀ j, HasSum (fun τ : ℕ => s j τ * ((τ : ℝ) + 1 / 2))
                  ((∑' τ : ℕ, y j τ * ((τ : ℝ) + 1 / 2)) + p j * D j) := by
                intro j
                refine ((add_left_injective (D j)).hasSum_iff (f := fun τ : ℕ => s j τ * ((τ : ℝ) + 1 / 2))
                  (fun τ hτ => by rw [hsoff j τ hτ, zero_mul])).1 ?_
                have : (fun τ : ℕ => s j τ * ((τ : ℝ) + 1 / 2)) ∘ (fun τ => τ + D j)
                    = fun τ : ℕ => y j τ * ((τ : ℝ) + 1 / 2) + y j τ * D j := by
                  ext τ
                  simp only [Function.comp_apply, hsadd]
                  push_cast; ring
                rw [this]
                exact (hymS j).add ((hys j).mul_right _)
              have hmS : ∀ j, HasSum (fun τ : ℕ => ((1 - l j) * y j τ + l j * s j τ) * ((τ : ℝ) + 1 / 2))
                  ((∑' τ : ℕ, y j τ * ((τ : ℝ) + 1 / 2)) + p j * d j) := by
                intro j
                have := ((hymS j).mul_left (1 - l j)).add ((hsm j).mul_left (l j))
                have e1 : (fun τ : ℕ => ((1 - l j) * y j τ + l j * s j τ) * ((τ : ℝ) + 1 / 2)) =
                    fun τ : ℕ => (1 - l j) * (y j τ * ((τ : ℝ) + 1 / 2)) + l j * (s j τ * ((τ : ℝ) + 1 / 2)) := by
                  ext τ; ring
                have e2 : (∑' τ : ℕ, y j τ * ((τ : ℝ) + 1 / 2)) + p j * d j =
                    (1 - l j) * (∑' τ : ℕ, y j τ * ((τ : ℝ) + 1 / 2)) +
                      l j * ((∑' τ : ℕ, y j τ * ((τ : ℝ) + 1 / 2)) + p j * D j) := by
                  rw [← hlD j]; ring
                rw [e1, e2]; exact this
              refine ⟨fun j τ => (1 - l j) * y j τ + l j * s j τ, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
              · intro j τ
                have h1 : 0 ≤ 1 - l j := by linarith [hl1 j]
                exact add_nonneg (mul_nonneg h1 (hy0 j τ)) (mul_nonneg (hl0 j) (hs0 j τ))
              · intro j τ hτ
                have : s j τ = 0 := by
                  simp only [hs]; split_ifs
                  · exact hyr j _ (by omega)
                  · rfl
                simp only [this, hyr j τ hτ, mul_zero, add_zero]
              · intro τ
                by_cases hτ : τ < K
                · refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hyc τ)
                  have : s j τ = 0 := by
                    simp only [hs]; rw [if_neg]
                    have := hDK j; omega
                  simp only [this]
                  nlinarith [hl0 j, hy0 j τ]
                · have hfirst : ∀ j, y j τ = 0 := fun j => hH j τ (by omega)
                  simp only [hfirst, mul_zero, zero_add]
                  have hKpos : 0 < K := by omega
                  have hzero : ∀ j : Fin n, j.val + 1 ≠ τ / K → l j * s j τ = 0 := by
                    intro j hj
                    have : s j τ = 0 := by
                      simp only [hs]; split_ifs with h
                      · refine hH j _ ?_
                        by_contra hc
                        apply hj
                        symm
                        rw [Nat.div_eq_iff hKpos]
                        simp only [hD] at h hc
                        omega
                      · rfl
                    rw [this, mul_zero]
                  have hs1 : ∀ j, l j * s j τ ≤ 1 := by
                    intro j
                    have : s j τ ≤ 1 := by
                      simp only [hs]; split_ifs
                      · exact hy1 _ _
                      · norm_num
                    exact mul_le_one₀ (hl1 j) (hs0 j τ) this
                  by_cases hex : ∃ j : Fin n, j.val + 1 = τ / K
                  · obtain ⟨j, hj⟩ := hex
                    rw [Finset.sum_eq_single j]
                    · exact hs1 j
                    · intro i _ hij
                      refine hzero i fun h => hij (Fin.ext (by omega))
                    · intro h; exact absurd (Finset.mem_univ j) h
                  · push Not at hex
                    rw [Finset.sum_eq_zero fun j _ => hzero j (hex j)]
                    norm_num
              · intro j
                have := ((hys j).mul_left (1 - l j)).add ((hsS j).mul_left (l j))
                have e2 : (p j : ℝ) = (1 - l j) * p j + l j * p j := by ring
                rw [e2]; exact this
              · intro j; exact (hmS j).summable
              · funext j
                have hv := congrFun hym j
                simp only [mMap] at hv ⊢
                rw [(hmS j).tsum_eq, Pi.add_apply, ← hv]
                have hne : (p j : ℝ) ≠ 0 := by exact_mod_cast (hp j).ne'
                rw [mul_add, ← mul_assoc, one_div_mul_cancel hne, one_mul]
            have hZconv : Convex ℝ Z := by
              rintro _ ⟨y, ⟨⟨hy0, hyr, hyc, hys⟩, hym⟩, rfl⟩ _ ⟨y', ⟨⟨hy0', hyr', hyc', hys'⟩, hym'⟩, rfl⟩
                a b ha hb hab
              refine ⟨a • y + b • y', ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
              · intro j τ
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                have := hy0 j τ; have := hy0' j τ; positivity
              · intro j τ hτ
                simp [hyr j τ hτ, hyr' j τ hτ]
              · intro τ
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                have h1 := hyc τ; have h2 := hyc' τ
                nlinarith
              · intro j
                have := ((hys j).mul_left a).add ((hys' j).mul_left b)
                rw [← add_mul, hab, one_mul] at this
                have e : (fun τ => (a • y + b • y') j τ) = fun τ => a * y j τ + b * y' j τ := by
                  ext τ; simp
                rw [e]; exact this
              · intro j
                have := ((hym j).mul_left a).add ((hym' j).mul_left b)
                refine this.congr (fun τ => ?_)
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
              · ext j
                simp only [mMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                have e : (∑' τ : ℕ, (a * y j τ + b * y' j τ) * ((τ : ℝ) + 1 / 2))
                    = a * ∑' τ : ℕ, y j τ * ((τ : ℝ) + 1 / 2) + b * ∑' τ : ℕ, y' j τ * ((τ : ℝ) + 1 / 2) := by
                  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add ((hym j).mul_left a) ((hym' j).mul_left b)]
                  congr 1; ext τ; ring
                rw [e]; ring
            apply Set.Subset.antisymm
            · intro M hM
              obtain ⟨v, hv, hvM⟩ := hK M hM
              have hconv2 : Convex ℝ {x : Fin n → ℝ | x + (M - v) ∈ Z} := by
                intro x hx y hy a b ha hb hab
                have := hZconv hx hy ha hb hab
                simp only [Set.mem_ofPred_eq] at this ⊢
                convert this using 1
                rw [smul_add, smul_add]
                have : M - v = a • (M - v) + b • (M - v) := by rw [← add_smul, hab, one_smul]
                conv_lhs => rw [this]
                abel
              have hsub : V ⊆ {x : Fin n → ℝ | x + (M - v) ∈ Z} :=
                fun w hw => hVZ w hw (M - v) (fun j => by simp [hvM j])
              have := convexHull_min hsub hconv2 hv
              simpa using this
            · exact hZP
