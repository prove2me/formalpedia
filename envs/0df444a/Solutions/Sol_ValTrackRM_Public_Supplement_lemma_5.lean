-- Prove2me | solution 1 for ValTrackRM.Public.Supplement.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:45.833806+00:00
-- url     : https://prove2.me/submissions/a889bcfe-9690-494a-8bbc-99960f595a54

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Sampling

open ValTrackRM
open ValTrackRM.Public
open ValTrackRM.Public.Supplement

theorem solution
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (ν : ℕ → PMF (Fin (m + 1))) (C : ℕ) (hC : 1 ≤ C) (T : ℕ) :
    firstPartition (publicRun r sel ν C false T) T ∧
    firstPartition (publicRun r sel ν C true T) T ∧
    (∀ (t : ℕ), 1 ≤ t → t ≤ T + 1 → ∀ h : FirstHistory m t,
      firstMass r sel ν C T false t h = firstMass r sel ν C T true t h) := by
        classical
        have avg_branch : ∀ {α β : Type} (xs : List (α × ℝ)) (f : α → List (β × ℝ)) (g : β → ℝ),
            average (branch xs f) g = average xs (fun x => average (f x) g) := by
          intro α β xs f g
          induction xs with
          | nil => simp [average, branch]
          | cons x xs ih =>
            simp only [branch, average, List.flatMap_cons, List.map_append, List.sum_append,
              List.map_map, List.map_cons, List.sum_cons] at ih ⊢
            rw [ih]; congr 1
            rw [← List.sum_map_mul_left]
            congr 1; apply List.map_congr_left; intro y _; simp only [Function.comp_apply]; ring
        have avg_single : ∀ {α : Type} (x : α) (w : ℝ) (g : α → ℝ), average [(x, w)] g = w * g x := by
          intros; simp [average]
        have avg_congr : ∀ {α : Type} (xs : List (α × ℝ)) (f g : α → ℝ),
            (∀ x ∈ xs, f x.1 = g x.1) → average xs f = average xs g := by
          intro α xs f g hfg
          unfold average; congr 1; apply List.map_congr_left; intro x hx; rw [hfg x hx]
        have avg_const : ∀ {α : Type} (xs : List (α × ℝ)) (c : ℝ),
            average xs (fun _ => c) = average xs (fun _ => 1) * c := by
          intro α xs c
          unfold average; rw [← List.sum_map_mul_right]; congr 1; apply List.map_congr_left
          intros; ring
        have mem_branch : ∀ {α β : Type} (xs : List (α × ℝ)) (f : α → List (β × ℝ)) (x : β × ℝ),
            x ∈ branch xs f → ∃ y ∈ xs, ∃ z ∈ f y.1, x = (z.1, y.2 * z.2) := by
          intro α β xs f x hx
          simp only [branch, List.mem_flatMap, List.mem_map] at hx
          obtain ⟨y, hy, z, hz, rfl⟩ := hx
          exact ⟨y, hy, z, hz, rfl⟩
        have hfin : ∀ {n : ℕ} (f : Fin n → ℝ), ((List.finRange n).map f).sum = ∑ i, f i := by
          intro n f; rw [Fin.sum_univ_def]
        have hpdm : ∀ {β : Type} (K : Price m → ℝ) (F : Price m × ℝ → β × ℝ) (G : β → ℝ),
            average ((priceDraw K).map F) G = ∑ p, (F (p, K p)).2 * G (F (p, K p)).1 := by
          intro β K F G
          simp only [average, priceDraw, List.map_map]
          rw [← hfin]; rfl
        have hpd : ∀ (K : Price m → ℝ) (G : Price m → ℝ),
            average (priceDraw K) G = ∑ p, K p * G p := by
          intro K G
          simp only [average, priceDraw, List.map_map]
          rw [← hfin]; rfl
        have hvd : ∀ i (G : Fin (m + 1) → ℝ),
            average (valueDraw (ν i)) G = ∑ v, (ν i v).toReal * G v := by
          intro i G
          simp only [average, valueDraw, List.map_map]
          rw [← hfin]; rfl
        have hvd1 : ∀ i, ∑ v, (ν i v).toReal = 1 := by
          intro i
          rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ _)]
          have h1 := PMF.tsum_coe (ν i); rw [tsum_fintype] at h1; rw [h1]; simp
        have hvdm : ∀ i, average (valueDraw (ν i)) (fun _ => 1) = 1 := by
          intro i; rw [hvd]; simpa using hvd1 i
        -- reject mass
        have K2 : ∑ p : Price m, reject p = 1 := by
          simp only [reject]
          have : ∀ p : Price m, (p.val = m ↔ p = Fin.last m) := by
            intro p; rw [Fin.ext_iff, Fin.val_last]
          simp only [this]; simp
        have hnn : ∀ j, j ≤ m → 0 ≤ r j := by
          intro j
          induction j with
          | zero => intro _; rw [hr0]
          | succ j ih => intro hj; have := hr j (by omega); linarith [ih (by omega)]
        have hqpos : ∀ j, 1 ≤ j → j ≤ m → 0 < qj r j := by
          intro j h1 h2
          have hlt := hr (j - 1) (by omega)
          rw [show j - 1 + 1 = j by omega] at hlt
          have h0 := hnn (j - 1) (by omega)
          have hp : 0 < r j := by linarith
          unfold qj
          rw [sub_pos, div_lt_one hp]; exact hlt
        have K1 : ∀ (L : Fin k → Fin (m + 1)) (s : Fin k → Bool), ∑ p, unitPrice r sel L s p = 1 := by
          intro L s
          unfold unitPrice
          split_ifs with hc
          · set ℓ := (L (sel L)).val with hℓ
            have hqT : 0 < qTot r m ℓ := by
              unfold qTot
              apply Finset.sum_pos
              · intro j hj; rw [Finset.mem_Ioc] at hj; exact hqpos j (by omega) hj.2
              · exact ⟨m, by rw [Finset.mem_Ioc]; omega⟩
            have hsum : ∑ p : Price m, (if ℓ < p.val + 1 ∧ p.val < m then qj r (p.val + 1) else 0)
                = qTot r m ℓ := by
              rw [← Finset.sum_filter]
              unfold qTot
              apply Finset.sum_bij (fun p _ => p.val + 1)
              · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
                rw [Finset.mem_Ioc]; omega
              · intro a _ b _ hab; exact Fin.ext (by omega)
              · intro j hj; rw [Finset.mem_Ioc] at hj
                refine ⟨⟨j - 1, by omega⟩, ?_, ?_⟩
                · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
                · simp only; omega
              · intros; rfl
            calc ∑ p : Price m, (if ℓ < p.val + 1 ∧ p.val < m then offerProb r m ℓ (p.val + 1) else 0)
                = (∑ p : Price m, (if ℓ < p.val + 1 ∧ p.val < m then qj r (p.val + 1) else 0))
                    / qTot r m ℓ := by
                  rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro p _
                  split_ifs <;> simp [offerProb]
              _ = 1 := by rw [hsum, div_self hqT.ne']
          · exact K2
        have K3 : ∀ t a, ∑ p, expKernel r sel ν t a p = 1 := by
          intro t a
          unfold expKernel
          split_ifs with hc
          · exact K2
          · simp only [not_or] at hc
            have : ∑ p, jointA1Price r sel ν (t - 1) a p = jointA1Stock r sel ν (t - 1) a := by
              simp only [jointA1Price, jointA1Stock, a1Joint, a1Stock]
              rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun W _ => ?_
              rw [← Finset.mul_sum]; congr 1
              rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun s _ => ?_
              rw [← Finset.mul_sum]; congr 1
              split_ifs <;> simp [K1]
            rw [← Finset.sum_div, this, div_self hc.2]
        have avg1 : ∀ {α : Type} (xs : List (α × ℝ)) (c : ℝ),
            average xs (fun _ => 1) = 1 → average xs (fun _ => c) = c := by
          intro α xs c h; rw [avg_const, h, one_mul]
        have hsim : ∀ n, average (simulate r sel ν n) (fun _ => 1) = 1 := by
          intro n
          induction n with
          | zero => simp [simulate, average]
          | succ n ih =>
            rw [simulate, avg_branch]
            conv_rhs => rw [← ih]
            congr 1; funext st
            simp only [avg_branch, avg_single, mul_one, hvdm, hpd, K1]
        have htr : ∀ n a fuel, average (trials r sel ν n a fuel) (fun _ => 1) = 1 := by
          intro n a fuel
          induction fuel with
          | zero => simp [trials, average]
          | succ fuel ih =>
            rw [trials, avg_branch]
            conv_rhs => rw [← hsim n]
            congr 1; funext st
            split_ifs
            · simp [average]
            · rw [avg_branch]; simp only [avg_single, mul_one, ih]
        have hsp1 : ∀ t a b, average (samplePrice r sel ν C t a b) (fun _ => 1) = 1 := by
          intro t a b
          unfold samplePrice
          rw [avg_branch]
          conv_rhs => rw [← htr (t - 1) a (C * (k + 1) * t ^ 2)]
          congr 1; funext res
          split
          · rw [hpdm]; simp only [mul_one]; exact K1 _ _
          · rw [hpdm]; simp only [mul_one]
            cases b
            · exact K2
            · exact K3 _ _
        have hsp2 : ∀ t a (G : RoundChoice m → ℝ) (c : ℝ), (∀ ch : RoundChoice m, ch.failed = true → G ch = c) →
            average (samplePrice r sel ν C t a false) G = average (samplePrice r sel ν C t a true) G := by
          intro t a G c hG
          have hG' : ∀ p o tr, G ⟨true, p, o, tr⟩ = c := fun _ _ _ => hG _ rfl
          unfold samplePrice
          rw [avg_branch, avg_branch]; congr 1; funext res
          split
          · rfl
          · rw [hpdm, hpdm]
            simp only [hG']
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            simp only [if_false, if_true, Bool.false_eq_true]
            rw [K2, K3]
        have hstep : ∀ b n (G : Execution m → ℝ), average (publicRun r sel ν C b (n + 1)) G =
            average (publicRun r sel ν C b n) (fun ex => average (samplePrice r sel ν C (n + 1) ex.stock b)
              (fun ch => average (valueDraw (ν (n + 1))) (fun v =>
                G ⟨ex.observations ++ [⟨ch.failed, ch.price, v⟩], nextStock r ex.stock ch.price v,
                  ex.revenue + payment r ex.stock ch.price v,
                  ex.operations + ch.operations + 10 * (n + k + m + 1),
                  ex.simulatedTransitions + ch.transitions⟩))) := by
          intro b n G
          rw [publicRun]
          simp only [avg_branch, avg_single, one_mul]
        have hlen : ∀ b n, ∀ x ∈ publicRun r sel ν C b n, x.1.observations.length = n := by
          intro b n
          induction n with
          | zero => intro x hx; simp [publicRun] at hx; subst hx; rfl
          | succ n ih =>
            intro x hx
            rw [publicRun] at hx
            obtain ⟨y, hy, z, hz, rfl⟩ := mem_branch _ _ _ hx
            obtain ⟨y2, hy2, z2, hz2, rfl⟩ := mem_branch _ _ _ hz
            obtain ⟨y3, hy3, z3, hz3, rfl⟩ := mem_branch _ _ _ hz2
            simp only [List.mem_singleton] at hz3
            subst hz3
            simp [ih y hy]
        have hPL : ∀ b n N, n ≤ N → ∀ G : List (Observation m) → ℝ,
            average (publicRun r sel ν C b N) (fun ex => G (ex.observations.take n)) =
            average (publicRun r sel ν C b n) (fun ex => G (ex.observations.take n)) := by
          intro b n N hnN G
          induction N, hnN using Nat.le_induction with
          | base => rfl
          | succ N hN ih =>
            rw [hstep, ← ih]
            apply avg_congr
            intro x hx
            have hl := hlen b N x hx
            have e : ∀ o : Observation m, (x.1.observations ++ [o]).take n = x.1.observations.take n :=
              fun o => List.take_append_of_le_length (by omega)
            simp only [e]
            simp only [avg1 _ _ (hvdm _), avg1 _ _ (hsp1 _ _ _)]
        have hCL : ∀ n (g : Execution m → ℝ),
            average (publicRun r sel ν C false n)
              (fun ex => if (∀ o ∈ ex.observations, o.failed = false) then g ex else 0) =
            average (publicRun r sel ν C true n)
              (fun ex => if (∀ o ∈ ex.observations, o.failed = false) then g ex else 0) := by
          intro n
          induction n with
          | zero => intro g; rfl
          | succ n ih =>
            intro g
            rw [hstep, hstep]
            set H : Execution m → ℝ := fun ex => average (samplePrice r sel ν C (n + 1) ex.stock false)
              (fun ch => if ch.failed = false then average (valueDraw (ν (n + 1))) (fun v =>
                g ⟨ex.observations ++ [⟨ch.failed, ch.price, v⟩], nextStock r ex.stock ch.price v,
                  ex.revenue + payment r ex.stock ch.price v,
                  ex.operations + ch.operations + 10 * (n + k + m + 1),
                  ex.simulatedTransitions + ch.transitions⟩) else 0) with hH
            have key : ∀ b (ex : Execution m),
                average (samplePrice r sel ν C (n + 1) ex.stock b)
                (fun ch => average (valueDraw (ν (n + 1))) (fun v =>
                  if (∀ o ∈ ex.observations ++ [⟨ch.failed, ch.price, v⟩], o.failed = false) then
                  g ⟨ex.observations ++ [⟨ch.failed, ch.price, v⟩], nextStock r ex.stock ch.price v,
                  ex.revenue + payment r ex.stock ch.price v,
                  ex.operations + ch.operations + 10 * (n + k + m + 1),
                  ex.simulatedTransitions + ch.transitions⟩ else 0)) =
                if (∀ o ∈ ex.observations, o.failed = false) then H ex else 0 := by
              intro b ex
              by_cases hc : ∀ o ∈ ex.observations, o.failed = false
              · rw [if_pos hc]
                have e2 : average (samplePrice r sel ν C (n + 1) ex.stock b)
                    (fun ch => average (valueDraw (ν (n + 1))) (fun v =>
                      if (∀ o ∈ ex.observations ++ [⟨ch.failed, ch.price, v⟩], o.failed = false) then
                      g ⟨ex.observations ++ [⟨ch.failed, ch.price, v⟩], nextStock r ex.stock ch.price v,
                      ex.revenue + payment r ex.stock ch.price v,
                      ex.operations + ch.operations + 10 * (n + k + m + 1),
                      ex.simulatedTransitions + ch.transitions⟩ else 0)) =
                    average (samplePrice r sel ν C (n + 1) ex.stock b)
                    (fun ch => if ch.failed = false then average (valueDraw (ν (n + 1))) (fun v =>
                      g ⟨ex.observations ++ [⟨ch.failed, ch.price, v⟩], nextStock r ex.stock ch.price v,
                      ex.revenue + payment r ex.stock ch.price v,
                      ex.operations + ch.operations + 10 * (n + k + m + 1),
                      ex.simulatedTransitions + ch.transitions⟩) else 0) := by
                  congr 1; funext ch
                  by_cases hf : ch.failed = false
                  · rw [if_pos hf]; congr 1; funext v
                    rw [if_pos]
                    intro o ho
                    rcases List.mem_append.1 ho with ho | ho
                    · exact hc o ho
                    · rw [List.mem_singleton] at ho; subst ho; exact hf
                  · rw [if_neg hf]
                    have : ∀ v : Fin (m + 1), ¬ (∀ o ∈ ex.observations ++ [(⟨ch.failed, ch.price, v⟩ : Observation m)],
                        o.failed = false) := fun v h => hf (h ⟨ch.failed, ch.price, v⟩ (by simp))
                    simp only [this, if_false]
                    exact avg1 _ _ (hvdm _)
                rw [e2, hH]
                cases b
                · rfl
                · symm
                  apply hsp2 _ _ _ 0
                  intro ch hch; simp [hch]
              · rw [if_neg hc]
                have e1 : ∀ (ch : RoundChoice m) (v : Fin (m + 1)),
                    ¬ (∀ o ∈ ex.observations ++ [(⟨ch.failed, ch.price, v⟩ : Observation m)],
                      o.failed = false) := by
                  intro ch v h; exact hc (fun o ho => h o (List.mem_append_left _ ho))
                simp only [e1, if_false]
                simp only [avg1 _ _ (hvdm _), avg1 _ _ (hsp1 _ _ _)]
            refine (avg_congr _ _ (fun ex => if (∀ o ∈ ex.observations, o.failed = false) then H ex else 0) ?_).trans
              ((ih H).trans (avg_congr _ _ _ ?_))
            · intro x _; exact key false x.1
            · intro x _; exact (key true x.1).symm
        have hpart : ∀ b, firstPartition (publicRun r sel ν C b T) T := by
          intro b x hx
          have hl := hlen b T x hx
          have huniq : ∀ (t1 t2 : ℕ) (h1 : FirstHistory m (t1 + 1)) (h2 : FirstHistory m (t2 + 1)),
              matchesFirst x.1 (t1 + 1) h1 → matchesFirst x.1 (t2 + 1) h2 → t1 < t2 → False := by
            intro t1 t2 h1 h2 m1 m2 hlt
            obtain ⟨_, hle1, htk1, hf1⟩ := m1
            obtain ⟨_, hle2, htk2, _⟩ := m2
            have ht1 : t1 + 1 ≤ x.1.observations.length := by omega
            rw [if_pos ht1] at hf1
            have h3 := congrArg (fun l => l[t1]?) htk2
            simp only [List.getElem?_take] at h3
            rw [if_pos (by omega)] at h3
            simp only [show t1 + 1 - 1 = t1 by omega] at hf1
            rw [h3] at hf1
            rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_ofFn] at hf1
            simp at hf1
          have hsame : ∀ (t : ℕ) (h1 h2 : FirstHistory m (t + 1)),
              matchesFirst x.1 (t + 1) h1 → matchesFirst x.1 (t + 1) h2 → h1 = h2 := by
            intro t h1 h2 m1 m2
            have := List.ofFn_injective (m1.2.2.1.symm.trans m2.2.2.1)
            funext i
            have hi := congrFun this i
            simp only [Observation.mk.injEq] at hi
            exact Prod.ext hi.2.1 hi.2.2
          obtain ⟨t0, ht0⟩ : ∃ t0, t0 = x.1.observations.findIdx (fun o => o.failed) := ⟨_, rfl⟩
          have ht0le : t0 ≤ x.1.observations.length := by rw [ht0]; exact List.findIdx_le_length
          have hobs : ∀ o : Observation m, o.failed = false → o = ⟨false, o.price, o.value⟩ := by
            rintro ⟨f, p, v⟩ h; simp only at h; subst h; rfl
          let h0 : FirstHistory m (t0 + 1) := fun i =>
            ((x.1.observations[i.val]'(by have := i.isLt; omega)).price,
             (x.1.observations[i.val]'(by have := i.isLt; omega)).value)
          have hm0 : matchesFirst x.1 (t0 + 1) h0 := by
            refine ⟨by omega, by omega, ?_, ?_⟩
            · apply List.ext_getElem
              · simp; omega
              · intro i hi1 hi2
                simp only [List.getElem_take, List.getElem_ofFn]
                apply hobs
                have : i < t0 := by simp at hi2; omega
                rw [ht0] at this
                exact List.not_of_lt_findIdx this
            · split_ifs with hc
              · simp only [show t0 + 1 - 1 = t0 by omega]
                rw [List.getElem?_eq_getElem (by omega)]
                simp only [Option.map_some, Option.getD_some]
                have hlt : x.1.observations.findIdx (fun o => o.failed) < x.1.observations.length := by
                  rw [← ht0]; omega
                have := List.findIdx_getElem (w := hlt)
                simp only [← ht0] at this
                try exact this
          have hlt0 : t0 < T + 1 := by omega
          refine ⟨⟨⟨t0, hlt0⟩, h0⟩, hm0, ?_⟩
          rintro ⟨t, h⟩ hm
          have htt : t.val = t0 := by
            rcases lt_trichotomy t.val t0 with hlt | heq | hgt
            · exact (huniq _ _ _ _ hm hm0 hlt).elim
            · exact heq
            · exact (huniq _ _ _ _ hm0 hm hgt).elim
          have ht' : t = ⟨t0, hlt0⟩ := Fin.ext htt
          subst ht'
          exact congrArg (Sigma.mk _) (hsame t0 h h0 hm hm0)
        refine ⟨hpart false, hpart true, ?_⟩
        intro t ht1 ht2 h
        obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        set L : List (Observation m) := List.ofFn (fun i => (⟨false, (h i).1, (h i).2⟩ : Observation m)) with hL
        have hLc : ∀ o ∈ L, o.failed = false := by
          intro o ho; rw [hL, List.mem_ofFn] at ho; obtain ⟨i, rfl⟩ := ho; rfl
        have hLlen : L.length = s := by rw [hL, List.length_ofFn]; omega
        unfold firstMass
        by_cases hsT : s = T
        · subst hsT
          have e : ∀ b, ∀ x ∈ publicRun r sel ν C b s,
              (if matchesFirst x.1 (s + 1) h then (1 : ℝ) else 0) =
              (if (∀ o ∈ x.1.observations, o.failed = false) then
                (if x.1.observations = L then 1 else 0) else 0) := by
            intro b x hx
            have hl := hlen b s x hx
            have hiff : matchesFirst x.1 (s + 1) h ↔ x.1.observations = L := by
              unfold matchesFirst
              constructor
              · rintro ⟨_, _, htk, _⟩
                rw [List.take_of_length_le (by omega)] at htk; exact htk
              · intro heq
                refine ⟨by omega, by omega, ?_, ?_⟩
                · rw [List.take_of_length_le (by omega)]; exact heq
                · rw [if_neg (by omega)]; trivial
            by_cases hm : x.1.observations = L
            · rw [if_pos (hiff.2 hm), if_pos hm, if_pos]; rw [hm]; exact hLc
            · rw [if_neg (fun h' => hm (hiff.1 h')), if_neg hm]; split_ifs <;> rfl
          refine (avg_congr _ _ _ ?_).trans ((hCL s (fun ex => if ex.observations = L then 1 else 0)).trans
            (avg_congr _ _ _ ?_))
          · intro x hx; exact e false x hx
          · intro x hx; exact (e true x hx).symm
        · have hsT' : s < T := by omega
          set G : List (Observation m) → ℝ := fun l =>
            if l.take s = L ∧ (l[s]?.map Observation.failed).getD false = true then 1 else 0 with hG
          set F : Execution m → ℝ := fun ex => average (samplePrice r sel ν C (s + 1) ex.stock false)
            (fun ch => if ch.failed = true then 1 else 0) with hF
          have red : ∀ b, average (publicRun r sel ν C b T) (fun ex => if matchesFirst ex (s + 1) h then 1 else 0)
              = average (publicRun r sel ν C b s) (fun ex => if (∀ o ∈ ex.observations, o.failed = false) then
                (if ex.observations = L then F ex else 0) else 0) := by
            intro b
            have stepA : average (publicRun r sel ν C b T) (fun ex => if matchesFirst ex (s + 1) h then 1 else 0)
                = average (publicRun r sel ν C b T) (fun ex => G (ex.observations.take (s + 1))) := by
              apply avg_congr
              intro x hx
              have hl := hlen b T x hx
              have hiff : matchesFirst x.1 (s + 1) h ↔ (x.1.observations.take (s + 1)).take s = L ∧
                  ((x.1.observations.take (s + 1))[s]?.map Observation.failed).getD false = true := by
                rw [List.take_take, List.getElem?_take, if_pos (by omega),
                  show min s (s + 1) = s by omega]
                unfold matchesFirst
                rw [if_pos (by omega)]
                simp only [show s + 1 - 1 = s by omega]
                constructor
                · rintro ⟨_, _, a, b⟩; exact ⟨a, b⟩
                · rintro ⟨a, b⟩; exact ⟨by omega, by omega, a, b⟩
              rw [hG]
              simp only
              by_cases hmm : matchesFirst x.1 (s + 1) h
              · rw [if_pos hmm, if_pos (hiff.1 hmm)]
              · rw [if_neg hmm, if_neg (fun h' => hmm (hiff.2 h'))]
            rw [stepA, hPL b (s + 1) T (by omega) G, hstep]
            apply avg_congr
            intro x hx
            have hl := hlen b s x hx
            have eG : ∀ o : Observation m, G ((x.1.observations ++ [o]).take (s + 1)) =
                if x.1.observations = L ∧ o.failed = true then 1 else 0 := by
              intro o
              rw [List.take_of_length_le (by simp; omega), hG]
              simp only
              rw [List.take_left' hl, List.getElem?_append_right (by omega), hl]
              simp
            simp only [eG]
            by_cases hm : x.1.observations = L
            · have hc : ∀ o ∈ x.1.observations, o.failed = false := by rw [hm]; exact hLc
              rw [if_pos hc, if_pos hm, hF]
              simp only [hm, true_and]
              simp only [avg1 _ _ (hvdm _)]
              cases b
              · rfl
              · symm; apply hsp2 _ _ _ 1; intro ch hch; simp [hch]
            · simp only [hm, false_and, if_false]
              simp only [avg1 _ _ (hvdm _), avg1 _ _ (hsp1 _ _ _)]
              split_ifs <;> rfl
          rw [red false, red true]
          exact hCL s _
