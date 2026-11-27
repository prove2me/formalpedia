-- Prove2me | solution 1 for TreeOrient.RecGreedy.Supplement.theorem_2_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:42.977002+00:00
-- url     : https://prove2.me/submissions/c9401fd0-508e-4853-b6f9-3f40548367c6

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Supplement_TopLevel

open TreeOrient
open TreeOrient.RecGreedy
open TreeOrient.RecGreedy.Supplement

/-- Theorem 2.9, p. 8 (PDF 9): Algorithm 2 with `U = n ^ a` is an `O(log k)`-approximation
running in `(n log B)^{O(log k)}` steps when `f ≤ n ^ a`. -/
theorem solution : ∀ a : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (I : Inst n) (k : ℕ),
      IsMonotone I.f →
      NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)) →
      (∀ S, I.f S ≤ n ^ a) → 2 ≤ k → k ≤ n →
      (∃ T, (alg29 I a k).1 = some T ∧ Feasible I.c I.root ∅ I.B T ∧
        (∃ A' : Edges n, A' ⊆ T ∧ IsArbo I.root A' ∧ verts I.root A' = verts I.root T) ∧
        ∀ A : Edges n, IsArbo I.root A → cost I.c A ≤ I.B → A.card + 1 ≤ k →
          (I.f (verts I.root A) : ℝ) ≤ C * Real.log k * (I.f (verts I.root T) : ℝ)) ∧
      ((alg29 I a k).2 : ℝ) ≤
        ((n : ℝ) * Real.logb 2 ((I.B : ℝ) + 2)) ^ (C * Real.log k) := by
          intro a
          have hbs : ∀ (probe : ℕ → Bool × ℕ) (fuel lo hi b : ℕ),
                (bsearchAux probe fuel lo hi).1 = some b → b ≤ hi := by
            intro probe fuel
            induction fuel with
            | zero => intro lo hi b h; simp [bsearchAux] at h
            | succ fuel ih =>
              intro lo hi b h
              rw [bsearchAux] at h
              split_ifs at h with h1
              simp at h
              split_ifs at h with h2 h3
              · simp at h; omega
              · simp only [Option.some.injEq] at h
                rcases hb' : (bsearchAux probe fuel lo (lo + (hi - lo) / 2 - 1)).1 with _ | b'
                · rw [hb'] at h; simp at h; omega
                · rw [hb'] at h; simp at h
                  have := ih _ _ _ hb'
                  omega
              · exact ih _ _ _ h
          have hTime : ∃ C2 : ℝ, 0 < C2 ∧ ∀ (n : ℕ) (I : Inst n) (k : ℕ), 2 ≤ k → k ≤ n →
              ((alg29 I a k).2 : ℝ) ≤
                ((n : ℝ) * Real.logb 2 ((I.B : ℝ) + 2)) ^ (C2 * Real.log k) := by
            refine ⟨4 * (a + 10) / Real.log 2, div_pos (by have := (Nat.cast_nonneg a : (0:ℝ) ≤ a); linarith) (Real.log_pos (by norm_num)), ?_⟩
            intro n I k hk hkn
            have hn : 1 ≤ n := by omega
            have hlogstep : ∀ x y : ℕ, 2 * x ≤ y → 1 ≤ y → 1 + Nat.log 2 (2 * x) ≤ Nat.log 2 (2 * y) := by
              intro x y hxy hy
              rcases Nat.eq_zero_or_pos x with rfl | hx
              · simp
                calc 1 = Nat.log 2 2 := by have := Nat.log_mul_base (b := 2) (n := 1) (by norm_num) (by norm_num); simpa using this.symm
                  _ ≤ Nat.log 2 (2 * y) := Nat.log_mono_right (by omega)
              · have h1 : Nat.log 2 (2 * x * 2) = Nat.log 2 (2 * x) + 1 := Nat.log_mul_base (by norm_num) (by omega)
                have h2 : Nat.log 2 (2 * x * 2) ≤ Nat.log 2 (2 * y) := Nat.log_mono_right (by omega)
                omega
            have hbsT : ∀ (probe : ℕ → Bool × ℕ) (P fuel lo hi : ℕ), (∀ b, b ≤ hi → (probe b).2 ≤ P) →
                (bsearchAux probe fuel lo hi).2 ≤ P * Nat.log 2 (2 * (hi + 1 - lo)) := by
              intro probe P fuel
              induction fuel with
              | zero => intro lo hi _; exact Nat.zero_le _
              | succ fuel ih =>
                intro lo hi hP
                rw [bsearchAux]
                split_ifs with h1
                · exact Nat.zero_le _
                · rcases hp : probe (lo + (hi - lo) / 2) with ⟨ok, t⟩
                  have ht : t ≤ P := by have := hP (lo + (hi - lo) / 2) (by omega); rw [hp] at this; exact this
                  simp only [hp]
                  cases ok
                  · simp only [Bool.false_eq_true, if_false]
                    have := ih (lo + (hi - lo) / 2 + 1) hi hP
                    have hs := hlogstep (hi + 1 - (lo + (hi - lo) / 2 + 1)) (hi + 1 - lo) (by omega) (by omega)
                    have : P * (1 + Nat.log 2 (2 * (hi + 1 - (lo + (hi - lo) / 2 + 1)))) ≤ P * Nat.log 2 (2 * (hi + 1 - lo)) :=
                      Nat.mul_le_mul_left _ hs
                    rw [Nat.mul_add, Nat.mul_one] at this; omega
                  · simp only [if_true]
                    split_ifs with h2
                    · simp only
                      have : 1 ≤ Nat.log 2 (2 * (hi + 1 - lo)) := by
                        have := hlogstep 0 (hi + 1 - lo) (by omega) (by omega); omega
                      calc t ≤ P * 1 := by omega
                        _ ≤ _ := Nat.mul_le_mul_left _ this
                    · simp only
                      have := ih lo (lo + (hi - lo) / 2 - 1) (fun b hb => hP b (by omega))
                      have hs := hlogstep (lo + (hi - lo) / 2 - 1 + 1 - lo) (hi + 1 - lo) (by omega) (by omega)
                      have : P * (1 + Nat.log 2 (2 * (lo + (hi - lo) / 2 - 1 + 1 - lo))) ≤ P * Nat.log 2 (2 * (hi + 1 - lo)) :=
                        Nat.mul_le_mul_left _ hs
                      rw [Nat.mul_add, Nat.mul_one] at this; omega
            have hflT : ∀ {β : Type} (l : List β) (g : (List (Edges n) × ℕ) → β → List (Edges n) × ℕ) (D : ℕ),
                (∀ x u, (g x u).2 ≤ x.2 + D ∧ (g x u).1.length ≤ x.1.length + 1) → ∀ init : List (Edges n) × ℕ,
                (l.foldl g init).2 ≤ init.2 + l.length * D ∧ (l.foldl g init).1.length ≤ init.1.length + l.length := by
              intro β l g D hg
              induction l with
              | nil => intro init; simp
              | cons u l ih =>
                intro init
                simp only [List.foldl_cons, List.length_cons]
                obtain ⟨h1, h2⟩ := ih (g init u)
                obtain ⟨h3, h4⟩ := hg init u
                constructor
                · linarith
                · omega
            have hRPT : ∀ (U : ℕ) (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
                (r v : Fin n) (Y1 Y2 X : Finset (Fin n)) (B F L : ℕ),
                (∀ b ≤ B, ∀ X', (sub r Y1 b X').2 ≤ F) → (∀ b ≤ B, ∀ X', (sub v Y2 b X').2 ≤ F) →
                (∀ (probe : ℕ → Bool × ℕ), (∀ b, b ≤ B → (probe b).2 ≤ F + 1) → (bsearch probe 0 B).2 ≤ (F + 1) * L) →
                (∀ (probe : ℕ → Bool × ℕ) b, (bsearch probe 0 B).1 = some b → b ≤ B) →
                (runPlan I (.bsearch U) sub [(r, Y1), (v, Y2)] X B ∅).2 ≤ (U + 1) * ((F + 1) * L + 2 * F) ∧
                (runPlan I (.bsearch U) sub [(r, Y1), (v, Y2)] X B ∅).1.length ≤ U + 1 := by
              intro U sub r v Y1 Y2 X B F L h1 h2 hbsT hbs
              rw [runPlan]
              · simp only [runPlan]
                have hlen : (do let a ← List.range (U + 1); pure (a : ℝ) : List ℝ).length = U + 1 := by simp
                refine ⟨le_trans (hflT _ _ ((F + 1) * L + 2 * F) ?_ _).1 ?_, le_trans (hflT _ _ ((F + 1) * L + 2 * F) ?_ _).2 ?_⟩
                rotate_left
                · rw [hlen]; exact le_of_eq (Nat.zero_add _)
                rotate_left
                · rw [hlen]; exact le_of_eq (Nat.zero_add _)
                all_goals
                  intro x u
                  split
                  · rename_i hob
                    dsimp only
                    refine ⟨?_, by omega⟩
                    refine le_trans (Nat.add_le_add_left (hbsT _ ?_) _) (by omega)
                    intro b hb; (try dsimp only); split <;> (have := h1 b hb X; (try dsimp only); omega)
                  · rename_i b hb
                    have hbB := hbs _ b hb
                    split
                    · dsimp only
                      have := h1 b hbB X
                      refine ⟨?_, by omega⟩
                      refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (hbsT _ ?_) _) _) (by omega)
                      intro b hb; (try dsimp only); split <;> (have := h1 b hb X; (try dsimp only); omega)
                    · rename_i T hT
                      dsimp only
                      have := h1 b hbB X
                      have := h2 (B - b) (by omega) (X ∪ verts r T)
                      refine ⟨?_, ?_⟩
                      · refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left (hbsT _ ?_) _) _) _) (by omega)
                        intro b hb; (try dsimp only); split <;> (have := h1 b hb X; (try dsimp only); omega)
                      · rw [List.length_append, List.length_map]
                        rcases (sub v Y2 (B - b) (X ∪ verts r T)).1 with _ | _ <;> simp
              · simp
            obtain ⟨U, hU⟩ : ∃ U, U = n ^ a := ⟨_, rfl⟩
            have hMain : ∀ i m (r : Fin n) (Y₀ : Finset (Fin n)) (B' : ℕ) (X : Finset (Fin n)), B' ≤ I.B → (Y₀.erase r).card ≤ m →
                (rg I 1 (.bsearch U) i r Y₀ B' X).2 ≤ (4 * n * (U + 1) * (Nat.log 2 (2 * (I.B + 1)) + 2) * 2 ^ (m + i)) ^ i := by
              have hCBT : ∀ (X : Finset (Fin n)) (r : Fin n) (init : Option (Edges n)) (L : List (Edges n)),
                  (chooseBest I.f X r init L).2 = L.length := by
                have gen : ∀ {α : Type} (g : α × ℕ → Edges n → α × ℕ), (∀ x T, (g x T).2 = x.2 + 1) →
                    ∀ (L : List (Edges n)) (init : α × ℕ), (L.foldl g init).2 = init.2 + L.length := by
                  intro α g hg L
                  induction L with
                  | nil => intro init; rfl
                  | cons x xs ih => intro init; simp only [List.foldl_cons, List.length_cons]; rw [ih, hg]; omega
                intro X r init L
                unfold chooseBest
                exact (gen _ (fun _ _ => rfl) L (init, 0)).trans (by simp)
              have hPFT : ∀ (X : Finset (Fin n)) (r : Fin n)
                  (plans : List (List (Fin n × Finset (Fin n))))
                  (g : List (Fin n × Finset (Fin n)) → List (Edges n) × ℕ) (D : ℕ),
                  (∀ p ∈ plans, (g p).2 + (g p).1.length ≤ D) → ∀ (init : Option (Edges n)) (s : ℕ),
                  (plans.foldl (fun x plan => ((chooseBest I.f X r x.1 (g plan).1).1,
                      x.2 + (g plan).2 + (chooseBest I.f X r x.1 (g plan).1).2)) (init, s)).2 ≤ s + plans.length * D := by
                intro X r plans g D hD
                induction plans with
                | nil => intro init s; simp
                | cons p ps ih =>
                  intro init s
                  simp only [List.foldl_cons, List.length_cons]
                  have h1 := ih (fun q hq => hD q (List.mem_cons_of_mem _ hq)) (chooseBest I.f X r init (g p).1).1
                    (s + (g p).2 + (chooseBest I.f X r init (g p).1).2)
                  have h2 := hD p (by simp)
                  rw [hCBT] at h1 ⊢
                  linarith
              have hLP : ∀ (r : Fin n) (Y : Finset (Fin n)), (leafPlans 1 r Y).length = n * 2 ^ Y.card := by
                intro r Y; simp [leafPlans, List.length_flatMap]
              have hLPm : ∀ (r : Fin n) (Y : Finset (Fin n)), ∀ p ∈ leafPlans 1 r Y, ∃ v S, S ⊆ Y ∧ p = [(r, (S ∪ {v}) \ {r}), (v, Y \ (S ∪ {v}))] := by
                intro r Y p hp
                simp only [leafPlans, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
                          List.append_nil, List.mem_flatMap, List.mem_finRange, Finset.mem_toList,
                          Finset.mem_powerset, true_and, List.mem_cons, List.not_mem_nil, or_false] at hp
                obtain ⟨v, S, hS, rfl⟩ := hp
                exact ⟨v, S, hS, rfl⟩
              have hBT : ∀ (r : Fin n) (Y : Finset (Fin n)) (B : ℕ) (X : Finset (Fin n)),
                  (rgBasic I (.bsearch U) 1 r Y B X).2 ≤ 1 + n := by
                intro r Y B X
                rw [rgBasic]
                split_ifs with h1 h2 h3 <;> first | exact absurd rfl h2 | exact Nat.le_add_right 1 n | exact le_refl _
              set L := Nat.log 2 (2 * (I.B + 1)) with hL
              set W := 4 * n * (U + 1) * (L + 2) with hW
              have hW1 : 1 ≤ W := by
                have : 1 ≤ 4 * n * (U + 1) * (L + 2) := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hn) (Nat.succ_pos _)) (Nat.succ_pos _)
                exact this
              intro i
              induction i with
              | zero => intro m r Y₀ B' X _ _; rw [rg, pow_zero]
              | succ i ih =>
                intro m r Y₀ B' X hB' hY
                rw [rg]
                split_ifs with h1 h2 h3
                · exact Nat.one_le_pow _ _ (Nat.mul_pos hW1 (Nat.two_pow_pos _))
                · subst h2
                  refine le_trans (hBT _ _ _ _) ?_
                  simp only [zero_add, pow_one]
                  have h2p : 2 ≤ 2 ^ (m + 1) := by
                    calc 2 = 2 ^ 1 := by norm_num
                      _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
                  have hnW : n ≤ W := by
                    rw [hW]; exact le_trans (le_trans (by omega : n ≤ 4 * n) (Nat.le_mul_of_pos_right _ (Nat.succ_pos U))) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
                  calc 1 + n ≤ W * 2 := by omega
                    _ ≤ W * 2 ^ (m + 1) := Nat.mul_le_mul_left _ h2p
                all_goals try exact absurd rfl h3
                all_goals
                  dsimp only
                  set F := (W * 2 ^ (m + 1 + i)) ^ i with hF
                  have hF1 : 1 ≤ F := Nat.one_le_pow _ _ (Nat.mul_pos hW1 (Nat.two_pow_pos _))
                  refine le_trans (hPFT X r _ _ ((U + 1) * ((F + 1) * L + 2 * F) + (U + 1)) ?_ _ _) ?_
                  · intro p hp
                    obtain ⟨v, S, hS, rfl⟩ := hLPm r _ p hp
                    have hbsT' : ∀ (probe : ℕ → Bool × ℕ), (∀ b, b ≤ B' → (probe b).2 ≤ F + 1) →
                        (bsearch probe 0 B').2 ≤ (F + 1) * L := by
                      intro probe hp
                      refine le_trans (hbsT probe (F + 1) _ 0 B' hp) (Nat.mul_le_mul_left _ ?_)
                      exact Nat.log_mono_right (by omega)
                    have hbs' : ∀ (probe : ℕ → Bool × ℕ) b, (bsearch probe 0 B').1 = some b → b ≤ B' :=
                      fun probe b h => hbs probe _ 0 B' b h
                    have hc1 : (((S ∪ {v}) \ {r}).erase r).card ≤ m + 1 := by
                      calc (((S ∪ {v}) \ {r}).erase r).card ≤ ((S ∪ {v}) \ {r}).card := Finset.card_erase_le
                        _ ≤ (S ∪ {v}).card := Finset.card_le_card Finset.sdiff_subset
                        _ ≤ S.card + 1 := by simpa using Finset.card_union_le S {v}
                        _ ≤ (Y₀.erase r).card + 1 := by have := Finset.card_le_card hS; omega
                        _ ≤ m + 1 := by omega
                    have hc2 : (((Y₀.erase r) \ (S ∪ {v})).erase v).card ≤ m + 1 := by
                      calc (((Y₀.erase r) \ (S ∪ {v})).erase v).card ≤ ((Y₀.erase r) \ (S ∪ {v})).card := Finset.card_erase_le
                        _ ≤ (Y₀.erase r).card := Finset.card_le_card Finset.sdiff_subset
                        _ ≤ m + 1 := by omega
                    obtain ⟨hR1, hR2⟩ := hRPT U (rg I 1 (.bsearch U) i) r v ((S ∪ {v}) \ {r}) (Y₀.erase r \ (S ∪ {v})) X B' F L
                      (fun b hb X' => ih (m + 1) r _ b X' (by omega) hc1)
                      (fun b hb X' => ih (m + 1) v _ b X' (by omega) hc2)
                      hbsT' hbs'
                    omega
                  · rw [hLP]
                    have hYc : 2 ^ (Y₀.erase r).card ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hY
                    have hD : (U + 1) * ((F + 1) * L + 2 * F) + (U + 1) ≤ 2 * (U + 1) * (L + 2) * F := by
                      clear * - hF1
                      have i0 : L ≤ F * L := Nat.le_mul_of_pos_left L hF1
                      have e1 : (F + 1) * L = F * L + L := Nat.succ_mul F L
                      have e2 : 2 * (L + 2) * F = 2 * (F * L) + 4 * F := by ring
                      have i2 : (F + 1) * L + 2 * F + 1 ≤ 2 * (L + 2) * F := by omega
                      have e4 : (U + 1) * (2 * (L + 2) * F) = 2 * (U + 1) * (L + 2) * F := by ring
                      have := Nat.mul_le_mul_left (U + 1) i2
                      rw [Nat.mul_add_one] at this
                      omega
                    have h2m' : 2 ^ (m + 1 + i) = 2 ^ (m + (i + 1)) := by rw [show m + 1 + i = m + (i + 1) by omega]
                    rw [h2m'] at hF
                    have hP : n * 2 ^ (Y₀.erase r).card * ((U + 1) * ((F + 1) * L + 2 * F) + (U + 1)) ≤
                        n * 2 ^ m * (2 * (U + 1) * (L + 2) * F) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hYc) hD
                    have hm2 : 2 ^ m ≤ 2 ^ (m + (i + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
                    have hWF : W * 2 ^ (m + (i + 1)) * F = (W * 2 ^ (m + (i + 1))) ^ (i + 1) := by
                      rw [hF]; exact (pow_succ' _ _).symm
                    rw [← hWF]
                    have e1 : n * 2 ^ m * (2 * (U + 1) * (L + 2) * F) * 2 = W * 2 ^ m * F := by clear * - hW; rw [hW]; ring
                    have e2 : W * 2 ^ m * F ≤ W * 2 ^ (m + (i + 1)) * F :=
                      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm2)
                    have e3 : 1 ≤ n * 2 ^ m * (2 * (U + 1) * (L + 2) * F) := Nat.mul_pos (Nat.mul_pos hn (Nat.two_pow_pos _)) (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.succ_pos _)) (Nat.succ_pos _)) hF1)
                    omega
            have hM : (alg29 I a k).2 ≤ (4 * n * (n ^ a + 1) * (Nat.log 2 (2 * (I.B + 1)) + 2) * 2 ^ (0 + dOf k)) ^ dOf k := by
              have := hMain (dOf k) 0 I.root ∅ I.B ∅ le_rfl (by simp)
              rw [hU] at this; exact this
            clear hMain hRPT hflT hbs hbsT hlogstep hU
            set L := Nat.log 2 (2 * (I.B + 1)) with hL
            set c := Nat.clog 2 k with hc
            have hc1 : 1 ≤ c := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) (by omega))
            have hpc : 2 ^ (c - 1) < k := by
              have := Nat.pow_pred_clog_lt_self (b := 2) (x := k) (by norm_num) (by omega)
              simpa [Nat.pred_eq_sub_one] using this
            have hn2 : 2 ≤ n := by omega
            have h4 : 4 ≤ n ^ 2 := Nat.pow_le_pow_left hn2 2
            have h2c : 2 ^ c ≤ 2 * n := by
              have : 2 ^ c = 2 * 2 ^ (c - 1) := by
                rw [← pow_succ']; congr 1; omega
              omega
            have h2d : 2 ^ (0 + dOf k) ≤ n ^ 4 := by
              have e : 2 ^ (0 + dOf k) = (2 ^ c) ^ 2 := by
                show 2 ^ (0 + 2 * Nat.clog 2 k) = _
                rw [← hc, ← pow_mul, zero_add, mul_comm]
              rw [e]
              calc (2 ^ c) ^ 2 ≤ (2 * n) ^ 2 := Nat.pow_le_pow_left h2c 2
                _ ≤ n ^ 4 := by
                  have e1 : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
                  have e2 : n ^ 4 = n ^ 2 * n ^ 2 := by ring
                  rw [e1, e2]; exact Nat.mul_le_mul_right _ h4
            have hna : n ^ a + 1 ≤ n ^ (a + 1) := by
              rw [pow_succ]; have : 1 ≤ n ^ a := Nat.one_le_pow _ _ (by omega)
              have := Nat.mul_le_mul_left (n ^ a) hn2
              omega
            have hWn : 4 * n * (n ^ a + 1) * (L + 2) * 2 ^ (0 + dOf k) ≤ n ^ (a + 8) * (L + 2) := by
              have : n ^ (a + 8) = n ^ 2 * n * n ^ (a + 1) * n ^ 4 := by ring
              rw [this]
              have h1 : 4 * n ≤ n ^ 2 * n := Nat.mul_le_mul_right _ h4
              have h2 : 4 * n * (n ^ a + 1) ≤ n ^ 2 * n * n ^ (a + 1) := Nat.mul_le_mul h1 hna
              calc 4 * n * (n ^ a + 1) * (L + 2) * 2 ^ (0 + dOf k) = 4 * n * (n ^ a + 1) * 2 ^ (0 + dOf k) * (L + 2) := by ring
                _ ≤ n ^ 2 * n * n ^ (a + 1) * n ^ 4 * (L + 2) :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h2d)
            -- real part
            set ℓ := Real.logb 2 ((I.B : ℝ) + 2) with hℓ
            have hB0 : (0 : ℝ) ≤ I.B := Nat.cast_nonneg _
            have hB2 : (0 : ℝ) < (I.B : ℝ) + 2 := by linarith
            have hℓ1 : 1 ≤ ℓ := by
              rw [hℓ, Real.le_logb_iff_rpow_le (by norm_num) hB2, Real.rpow_one]; linarith
            have hLr : (L : ℝ) ≤ 1 + ℓ := by
              have h1 : 2 ^ L ≤ 2 * (I.B + 1) := Nat.pow_log_le_self 2 (by omega)
              have h2 : (L : ℝ) ≤ Real.logb 2 (2 * ((I.B : ℝ) + 2)) := by
                clear * - h1 hB0
                rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_natCast]
                have : ((2 ^ L : ℕ) : ℝ) ≤ ((2 * (I.B + 1) : ℕ) : ℝ) := by exact_mod_cast h1
                push_cast at this; linarith
              rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)] at h2
              exact h2
            have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn2
            have hX : ((4 * n * (n ^ a + 1) * (L + 2) * 2 ^ (0 + dOf k) : ℕ) : ℝ) ≤ ((n : ℝ) * ℓ) ^ (a + 10) := by
              have e1 : ((4 * n * (n ^ a + 1) * (L + 2) * 2 ^ (0 + dOf k) : ℕ) : ℝ) ≤ (n : ℝ) ^ (a + 8) * ((L : ℝ) + 2) := by
                exact_mod_cast hWn
              have hℓ0 : (0:ℝ) ≤ ℓ := le_trans zero_le_one hℓ1
              have h4r : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h4
              have e2 : (L : ℝ) + 2 ≤ (n : ℝ) ^ 2 * ℓ := by
                have := mul_le_mul_of_nonneg_right h4r hℓ0
                clear * - this hLr hℓ1
                linarith
              have e3 : ℓ ≤ ℓ ^ (a + 10) := le_self_pow₀ hℓ1 (by omega)
              have hn0 : (0:ℝ) ≤ (n:ℝ) ^ (a + 8) := pow_nonneg (Nat.cast_nonneg _) _
              have hn0' : (0:ℝ) ≤ (n:ℝ) ^ (a + 10) := pow_nonneg (Nat.cast_nonneg _) _
              calc _ ≤ _ := e1
                _ ≤ (n : ℝ) ^ (a + 8) * ((n : ℝ) ^ 2 * ℓ) := mul_le_mul_of_nonneg_left e2 hn0
                _ = (n : ℝ) ^ (a + 10) * ℓ := by ring
                _ ≤ (n : ℝ) ^ (a + 10) * ℓ ^ (a + 10) := mul_le_mul_of_nonneg_left e3 hn0'
                _ = _ := (mul_pow _ _ _).symm
            have hstep : ((alg29 I a k).2 : ℝ) ≤ (((n : ℝ) * ℓ) ^ (a + 10)) ^ dOf k := by
              have : ((alg29 I a k).2 : ℝ) ≤ (((4 * n * (n ^ a + 1) * (L + 2) * 2 ^ (0 + dOf k) : ℕ) : ℝ)) ^ dOf k := by
                exact_mod_cast hM
              exact this.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hX _)
            have hbase : (1 : ℝ) ≤ (n : ℝ) * ℓ := one_le_mul_of_one_le_of_one_le (by linarith) hℓ1
            rw [← pow_mul, ← Real.rpow_natCast] at hstep
            refine hstep.trans (Real.rpow_le_rpow_of_exponent_le hbase ?_)
            -- exponent
            have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
            have hcl : ((c : ℝ) - 1) < Real.logb 2 k := by
              rw [Real.lt_logb_iff_rpow_lt (by norm_num) (lt_of_lt_of_le two_pos hk2)]
              have : ((2 ^ (c - 1) : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast hpc
              rw [show ((c : ℝ) - 1) = ((c - 1 : ℕ) : ℝ) by push_cast [hc1]; ring, Real.rpow_natCast]
              exact_mod_cast this
            have hlk : 1 ≤ Real.logb 2 k := by
              rw [Real.le_logb_iff_rpow_le (by norm_num) (lt_of_lt_of_le two_pos hk2), Real.rpow_one]; exact hk2
            have hlogb : Real.logb 2 k = Real.log k / Real.log 2 := rfl
            have hd : ((dOf k : ℕ) : ℝ) = 2 * (c : ℝ) := by unfold dOf; push_cast; rfl
            push_cast
            rw [hd]
            have : 4 * ((a : ℝ) + 10) / Real.log 2 * Real.log k = (4 * ((a : ℝ) + 10)) * Real.logb 2 k := by
              rw [hlogb]; ring
            rw [this]
            have ha : (0 : ℝ) ≤ (a : ℝ) + 10 := by have := (Nat.cast_nonneg a : (0:ℝ) ≤ a); linarith
            have hc2 : 2 * (c : ℝ) ≤ 4 * Real.logb 2 k := by linarith
            have := mul_le_mul_of_nonneg_left hc2 ha
            linarith
          -- (1) the top-level call always returns a tree
          have hSome : ∀ {n : ℕ} (I : Inst n) (k : ℕ), 2 ≤ k → ∃ T, (alg29 I a k).1 = some T := by
            intro n I k hk
            have hcb : ∀ (X : Finset (Fin n)) (r : Fin n) (L : List (Edges n)) (T0 : Edges n),
                ∃ T, (chooseBest I.f X r (some T0) L).1 = some T := by
              intro X r L
              unfold chooseBest
              suffices h : ∀ (L : List (Edges n)) (T0 : Edges n) (s : ℕ), ∃ T,
                  (L.foldl (fun (incumbent, steps) T =>
                    let next := match incumbent with
                      | none => some T
                      | some old => if fX I.f X r old < fX I.f X r T then some T else incumbent
                    (next, steps + 1)) (some T0, s)).1 = some T by
                intro T0; exact h L T0 0
              intro L
              induction L with
              | nil => intro T0 s; exact ⟨T0, rfl⟩
              | cons x xs ih =>
                intro T0 s
                simp only [List.foldl_cons]
                split_ifs with h
                · exact ih x _
                · exact ih T0 _
            have hd : ∃ i, dOf k = i + 1 + 1 := by
              have : 1 ≤ Nat.clog 2 k := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) hk)
              exact ⟨2 * Nat.clog 2 k - 2, by unfold dOf; omega⟩
            obtain ⟨i, hi⟩ := hd
            unfold alg29
            rw [hi, rg]
            simp only [Finset.erase_empty, Finset.card_empty, Nat.cast_zero, add_eq_zero, one_ne_zero, and_false, if_false, if_true]
            have hcap : ¬ capImp 1 (i + 1 + 1) < 0 := by unfold capImp; push Not; positivity
            rw [if_neg hcap]
            have hfold : ∀ (P : List (List (Fin n × Finset (Fin n))))
                (g : List (Fin n × Finset (Fin n)) → List (Edges n) × ℕ) (T0 : Edges n) (s : ℕ),
                ∃ T, (P.foldl (fun x plan => ((chooseBest I.f ∅ I.root x.1 (g plan).1).1,
                    x.2 + (g plan).2 + (chooseBest I.f ∅ I.root x.1 (g plan).1).2)) (some T0, s)).1 = some T := by
              intro P g
              induction P with
              | nil => intro T0 s; exact ⟨T0, rfl⟩
              | cons p ps ih =>
                intro T0 s
                simp only [List.foldl_cons]
                obtain ⟨T1, hT1⟩ := hcb ∅ I.root (g p).1 T0
                rw [hT1]
                exact ih T1 _
            exact hfold _ _ ∅ 1
          -- (2) every returned tree is feasible
          have hFeasG : ∀ {n : ℕ} (I : Inst n), ∀ i (r : Fin n) (Y₀ : Finset (Fin n)) (B : ℕ) (X : Finset (Fin n)) T,
              (rg I 1 (.bsearch (n ^ a)) i r Y₀ B X).1 = some T →
              ((∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧ Y₀.erase r ⊆ verts r T) := by
            intro n I
            classical
            have hfl : ∀ (Q : Edges n → Prop) {β : Type} (l : List β) (g : (List (Edges n) × ℕ) → β → List (Edges n) × ℕ),
                  (∀ x u, ∃ e, (g x u).1 = x.1 ++ e ∧ ∀ c ∈ e, Q c) → ∀ init : List (Edges n) × ℕ, (∀ c ∈ init.1, Q c) →
                  ∀ c ∈ (l.foldl g init).1, Q c := by
              intro Q β l g hg
              induction l with
              | nil => intro init h; simpa using h
              | cons u l ih =>
                intro init h
                simp only [List.foldl_cons]
                apply ih
                obtain ⟨e, he, hQ⟩ := hg init u
                rw [he]
                intro c hc
                rcases List.mem_append.1 hc with hc | hc
                · exact h c hc
                · exact hQ c hc
            have hRP : ∀ (U : ℕ) (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
            (r v : Fin n) (Y1 Y2 X : Finset (Fin n)) (B : ℕ) (Q : Edges n → Prop),
            (∀ b T1 T2 X', b ≤ B → (sub r Y1 b X).1 = some T1 → (sub v Y2 (B - b) X').1 = some T2 →
              Q (T1 ∪ T2)) →
            ∀ c ∈ (runPlan I (.bsearch U) sub [(r, Y1), (v, Y2)] X B ∅).1, Q c := by
              intro U sub r v Y1 Y2 X B Q hQ
              rw [runPlan]
              · simp only [runPlan]
                refine hfl Q _ _ ?_ _ ?_
                swap
                · intro c hc; nomatch hc
                intro x u
                split
                · exact ⟨[], (List.append_nil _).symm, fun c hc => nomatch hc⟩
                · rename_i b hb
                  split
                  · exact ⟨[], (List.append_nil _).symm, fun c hc => nomatch hc⟩
                  · rename_i T1 hT1
                    refine ⟨_, rfl, ?_⟩
                    intro c hc
                    rcases hT2 : (sub v Y2 (B - b) (X ∪ verts r T1)).1 with _ | T2
                    · rw [hT2] at hc; nomatch hc
                    · rw [hT2] at hc
                      rw [Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton, Finset.empty_union] at hc
                      subst hc
                      exact hQ b T1 T2 _ (hbs _ _ _ _ _ hb) hT1 hT2
              · simp
            have hComp : ∀ (r v : Fin n) (Y S : Finset (Fin n)) (B b : ℕ) (T1 T2 : Edges n),
            b ≤ B →
            ((∀ w ∈ verts r T1, Reaches T1 r w) ∧ cost I.c T1 ≤ b ∧ (insert v S \ {r}).erase r ⊆ verts r T1) →
            ((∀ w ∈ verts v T2, Reaches T2 v w) ∧ cost I.c T2 ≤ B - b ∧ (Y \ insert v S).erase v ⊆ verts v T2) →
            ((∀ w ∈ verts r (T1 ∪ T2), Reaches (T1 ∪ T2) r w) ∧ cost I.c (T1 ∪ T2) ≤ B ∧
              Y.erase r ⊆ verts r (T1 ∪ T2)) := by
              intro r v Y S B b T1 T2 hb ⟨h1R, h1c, h1Y⟩ ⟨h2R, h2c, h2Y⟩
              have hv : v ∈ verts r T1 := by
                by_cases hvr : v = r
                · subst hvr; exact Finset.mem_insert_self _ _
                · exact h1Y (Finset.mem_erase.2 ⟨hvr, Finset.mem_sdiff.2 ⟨Finset.mem_insert_self _ _, by rwa [Finset.mem_singleton]⟩⟩)
              have hsub1 : verts r T1 ⊆ verts r (T1 ∪ T2) := by
                intro x hx
                simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx ⊢
                rcases hx with h | ⟨e, he, h⟩ | ⟨e, he, h⟩
                · exact Or.inl h
                · exact Or.inr (Or.inl ⟨e, Or.inl he, h⟩)
                · exact Or.inr (Or.inr ⟨e, Or.inl he, h⟩)
              have hsub2 : verts v T2 ⊆ verts r (T1 ∪ T2) := by
                intro x hx
                simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
                rcases hx with h | ⟨e, he, h⟩ | ⟨e, he, h⟩
                · subst h; exact hsub1 hv
                · simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
                  exact Or.inr (Or.inl ⟨e, Or.inr he, h⟩)
                · simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
                  exact Or.inr (Or.inr ⟨e, Or.inr he, h⟩)
              have hmono1 : ∀ x y, Reaches T1 x y → Reaches (T1 ∪ T2) x y := by
                intro x y h
                induction h with
                | refl => exact Relation.ReflTransGen.refl
                | tail _ hab ih => exact ih.tail (Finset.mem_union_left _ hab)
              have hmono2 : ∀ x y, Reaches T2 x y → Reaches (T1 ∪ T2) x y := by
                intro x y h
                induction h with
                | refl => exact Relation.ReflTransGen.refl
                | tail _ hab ih => exact ih.tail (Finset.mem_union_right _ hab)
              refine ⟨?_, ?_, ?_⟩
              · intro w hw
                simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hw
                rcases hw with h | ⟨e, he | he, h⟩ | ⟨e, he | he, h⟩
                · subst h; exact Relation.ReflTransGen.refl
                · apply hmono1; apply h1R
                  simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
                  exact Or.inr (Or.inl ⟨e, he, h⟩)
                · refine Relation.ReflTransGen.trans (hmono1 _ _ (h1R v hv)) (hmono2 _ _ (h2R w ?_))
                  simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
                  exact Or.inr (Or.inl ⟨e, he, h⟩)
                · apply hmono1; apply h1R
                  simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
                  exact Or.inr (Or.inr ⟨e, he, h⟩)
                · refine Relation.ReflTransGen.trans (hmono1 _ _ (h1R v hv)) (hmono2 _ _ (h2R w ?_))
                  simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
                  exact Or.inr (Or.inr ⟨e, he, h⟩)
              · have := Finset.sum_union_inter (s₁ := T1) (s₂ := T2) (f := fun e => I.c e.1 e.2)
                unfold cost at h1c h2c ⊢
                omega
              · intro x hx
                obtain ⟨hxr, hxY⟩ := Finset.mem_erase.1 hx
                by_cases hxS : x ∈ insert v S
                · exact hsub1 (h1Y (Finset.mem_erase.2 ⟨hxr, Finset.mem_sdiff.2 ⟨hxS, by rwa [Finset.mem_singleton]⟩⟩))
                · have hxv : x ≠ v := fun h => hxS (by rw [h]; exact Finset.mem_insert_self _ _)
                  exact hsub2 (h2Y (Finset.mem_erase.2 ⟨hxv, Finset.mem_sdiff.2 ⟨hxY, hxS⟩⟩))
            have hCB : ∀ (P : Edges n → Prop) (X : Finset (Fin n)) (r : Fin n)
            (L : List (Edges n)) (init : Option (Edges n)),
            (∀ T, init = some T → P T) → (∀ c ∈ L, P c) →
            ∀ T, (chooseBest I.f X r init L).1 = some T → P T := by
              intro P X r L
              unfold chooseBest
              suffices h : ∀ (L : List (Edges n)) (init : Option (Edges n)) (s : ℕ),
                  (∀ T, init = some T → P T) → (∀ c ∈ L, P c) →
                  ∀ T, (L.foldl (fun (incumbent, steps) T =>
                      let next := match incumbent with
                        | none => some T
                        | some old => if fX I.f X r old < fX I.f X r T then some T else incumbent
                      (next, steps + 1)) (init, s)).1 = some T → P T by
                intro init h1 h2; exact h L init 0 h1 h2
              intro L
              induction L with
              | nil => intro init s h1 _ T hT; exact h1 T hT
              | cons x xs ih =>
                intro init s h1 h2 T hT
                simp only [List.foldl_cons] at hT
                refine ih _ _ ?_ (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) T hT
                intro T' hT'
                rcases init with _ | old
                · obtain rfl := Option.some.inj hT'; exact h2 _ (List.mem_cons.2 (Or.inl rfl))
                · simp only at hT'
                  split_ifs at hT' with hlt
                  · obtain rfl := Option.some.inj hT'; exact h2 _ (List.mem_cons.2 (Or.inl rfl))
                  · exact h1 T' hT'
            have hBase : ∀ (r : Fin n) (Y : Finset (Fin n)) (B : ℕ) (X : Finset (Fin n)) T,
            (rgBasic I (.bsearch (n ^ a)) 1 r Y B X).1 = some T →
            ((∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧ Y.erase r ⊆ verts r T) := by
              intro r Y B X T hT
              rw [rgBasic] at hT
              have hedge : ∀ v, I.c r v ≤ B → ((∀ w ∈ verts r ({(r, v)} : Edges n), Reaches {(r, v)} r w) ∧
                  cost I.c ({(r, v)} : Edges n) ≤ B ∧ ({v} : Finset (Fin n)) ⊆ verts r {(r, v)}) := by
                intro v hv
                have hvv : verts r ({(r, v)} : Edges n) = insert r ({r} ∪ {v}) := by
                  simp only [verts, Finset.image_singleton]
                rw [hvv]
                refine ⟨?_, by rw [cost, Finset.sum_singleton]; exact hv, ?_⟩
                · intro w hw
                  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hw
                  rcases hw with rfl | rfl | rfl
                  · exact Relation.ReflTransGen.refl
                  · exact Relation.ReflTransGen.refl
                  · exact Relation.ReflTransGen.single (Finset.mem_singleton_self _)
                · intro x hx
                  rw [Finset.mem_singleton] at hx
                  rw [hx]
                  exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_singleton_self _))
              split_ifs at hT with h1 h2 h3
              · simp only at hT
                refine hCB (fun T => (∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧ Y.erase r ⊆ verts r T) X r _ _ ?_ ?_ T hT
                · intro T' hT'
                  obtain rfl := Option.some.inj hT'
                  refine ⟨?_, by rw [cost, Finset.sum_empty]; exact Nat.zero_le _, by rw [h3]; exact Finset.empty_subset _⟩
                  intro w hw
                  simp only [verts, Finset.image_empty, Finset.union_empty, Finset.mem_insert, Finset.notMem_empty, or_false] at hw
                  rw [hw]; exact Relation.ReflTransGen.refl
                · intro c hc
                  simp only [List.mem_filterMap, List.mem_finRange, true_and] at hc
                  obtain ⟨v, hv⟩ := hc
                  split_ifs at hv with hv'
                  obtain rfl := Option.some.inj hv
                  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hv'
                  obtain ⟨hA, hB, _⟩ := hedge v hv'.2
                  exact ⟨hA, hB, by rw [h3]; exact Finset.empty_subset _⟩
              · simp only at hT
                split at hT
                · rename_i v hv
                  split_ifs at hT with hc
                  obtain rfl := Option.some.inj hT
                  obtain ⟨hA, hB, hC⟩ := hedge v hc
                  refine ⟨hA, hB, ?_⟩
                  intro x hx
                  have : x ∈ (Y.erase r).toList := Finset.mem_toList.2 hx
                  rw [hv] at this
                  rw [List.mem_singleton.1 this]
                  exact hC (Finset.mem_singleton_self _)
                · cases hT
              all_goals omega
            have hMain : ∀ i (r : Fin n) (Y₀ : Finset (Fin n)) (B : ℕ) (X : Finset (Fin n)) T,
            (rg I 1 (.bsearch (n ^ a)) i r Y₀ B X).1 = some T →
            ((∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧ Y₀.erase r ⊆ verts r T) := by
              have hPF : ∀ (P : Edges n → Prop) (X : Finset (Fin n)) (r : Fin n)
                  (plans : List (List (Fin n × Finset (Fin n))))
                  (g : List (Fin n × Finset (Fin n)) → List (Edges n) × ℕ) (init : Option (Edges n)) (s : ℕ),
                  (∀ T, init = some T → P T) → (∀ p ∈ plans, ∀ c ∈ (g p).1, P c) →
                  ∀ T, (plans.foldl (fun x plan => ((chooseBest I.f X r x.1 (g plan).1).1,
                      x.2 + (g plan).2 + (chooseBest I.f X r x.1 (g plan).1).2)) (init, s)).1 = some T → P T := by
                intro P X r plans g
                induction plans with
                | nil => intro init s h1 _ T hT; exact h1 T hT
                | cons p ps ih =>
                  intro init s h1 h2 T hT
                  simp only [List.foldl_cons] at hT
                  refine ih _ _ ?_ (fun q hq => h2 q (List.mem_cons_of_mem _ hq)) T hT
                  exact hCB P X r _ init h1 (h2 p (List.mem_cons.2 (Or.inl rfl)))
              intro i
              induction i with
              | zero => intro r Y₀ B X T hT; rw [rg] at hT; cases hT
              | succ i ih =>
                intro r Y₀ B X T hT
                rw [rg] at hT
                split_ifs at hT with h1 h2 h3 h4
                · have := hBase r (Y₀.erase r) B X T hT
                  rwa [Finset.erase_idem] at this
                · exact absurd rfl h3
                · exact absurd rfl h3
                all_goals
                  have hplans : ∀ p ∈ leafPlans 1 r (Y₀.erase r), ∀ c ∈ (runPlan I (.bsearch (n ^ a))
                      (rg I 1 (.bsearch (n ^ a)) i) p X B ∅).1,
                      (fun T => (∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧
                        (Y₀.erase r).erase r ⊆ verts r T) c := by
                    intro p hp c hc
                    simp only [leafPlans, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
                      List.append_nil, List.mem_flatMap, List.mem_finRange, Finset.mem_toList,
                      Finset.mem_powerset, true_and, List.mem_cons, List.not_mem_nil, or_false] at hp
                    obtain ⟨v, S, hS, rfl⟩ := hp
                    refine hRP (n ^ a) _ r v _ _ X B (fun T => (∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧
                        (Y₀.erase r).erase r ⊆ verts r T) ?_ c hc
                    intro b T1 T2 X' hb hT1 hT2
                    have e : S ∪ {v} = insert v S := by rw [Finset.union_comm, ← Finset.insert_eq]
                    rw [e] at hT1 hT2
                    exact hComp r v _ S B b T1 T2 hb (ih _ _ _ _ _ hT1) (ih _ _ _ _ _ hT2)
                · rename_i hY
                  have key := hPF (fun T => (∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧
                    (Y₀.erase r).erase r ⊆ verts r T) X r _ _ _ _ ?_ hplans T hT
                  · rwa [Finset.erase_idem] at key
                  · intro T' hT'
                    obtain rfl := Option.some.inj hT'
                    refine ⟨?_, by rw [cost, Finset.sum_empty]; exact Nat.zero_le _, by rw [Finset.erase_idem, hY]; exact Finset.empty_subset _⟩
                    intro w hw
                    simp only [verts, Finset.image_empty, Finset.union_empty, Finset.mem_insert, Finset.notMem_empty, or_false] at hw
                    rw [hw]; exact Relation.ReflTransGen.refl
                · have key := hPF (fun T => (∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧
                    (Y₀.erase r).erase r ⊆ verts r T) X r _ _ _ _ ?_ hplans T hT
                  · rwa [Finset.erase_idem] at key
                  · intro T' hT'; cases hT'
            exact hMain
          have hFeas : ∀ {n : ℕ} (I : Inst n) (k : ℕ), 2 ≤ k → ∀ T, (alg29 I a k).1 = some T →
              Feasible I.c I.root ∅ I.B T := by
            intro n I k _ T hT
            obtain ⟨h1, h2, _⟩ := hFeasG I _ _ _ _ _ T hT
            exact ⟨h1, h2, Finset.empty_subset _⟩
          -- (3) a rooted reachable edge set contains a spanning arborescence
          have hArbo : ∀ {n : ℕ} (r : Fin n) (T : Edges n), (∀ w ∈ verts r T, Reaches T r w) →
              ∃ A' : Edges n, A' ⊆ T ∧ IsArbo r A' ∧ verts r A' = verts r T := by
            intro n r T hR
            classical
            obtain ⟨D, hD0, hDs⟩ : ∃ D : ℕ → Finset (Fin n), D 0 = {r} ∧
                ∀ m, D (m + 1) = D m ∪ (T.filter (fun e => e.1 ∈ D m)).image Prod.snd :=
              ⟨fun m => Nat.rec {r} (fun _ S => S ∪ (T.filter (fun e => e.1 ∈ S)).image Prod.snd) m,
                rfl, fun _ => rfl⟩
            set V := verts r T with hV
            have hrV : r ∈ V := by rw [hV]; exact Finset.mem_insert_self _ _
            have hfstV : ∀ e ∈ T, e.1 ∈ V := fun e he => by
              simp only [hV, verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
              exact Or.inr (Or.inl ⟨e, he, rfl⟩)
            have hsndV : ∀ e ∈ T, e.2 ∈ V := fun e he => by
              simp only [hV, verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
              exact Or.inr (Or.inr ⟨e, he, rfl⟩)
            have hDm : ∀ w, Reaches T r w → ∃ m, w ∈ D m := by
              intro w hw
              induction hw with
              | refl => exact ⟨0, by simp [hD0]⟩
              | tail _ hbc ih =>
                obtain ⟨m, hm⟩ := ih
                refine ⟨m + 1, ?_⟩
                rw [hDs]
                exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨hbc, hm⟩, rfl⟩)
            let dist : Fin n → ℕ := fun w => if h : ∃ m, w ∈ D m then Nat.find h else 0
            have hpar : ∀ w ∈ V, w ≠ r → ∃ u, (u, w) ∈ T ∧ u ∈ V ∧ dist u < dist w := by
              intro w hw hwr
              have h : ∃ m, w ∈ D m := hDm w (hR w hw)
              have hdw : dist w = Nat.find h := dif_pos h
              have hspec := Nat.find_spec h
              obtain ⟨j, hj⟩ : ∃ j, Nat.find h = j + 1 := by
                rcases hk : Nat.find h with _ | j
                · rw [hk, hD0] at hspec; simp at hspec; exact absurd hspec hwr
                · exact ⟨j, rfl⟩
              have hnot : w ∉ D j := Nat.find_min h (by omega)
              rw [hj, hDs] at hspec
              rcases Finset.mem_union.1 hspec with h1 | h1
              · exact absurd h1 hnot
              obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h1
              obtain ⟨heT, heD⟩ := Finset.mem_filter.1 he
              refine ⟨e.1, by simpa using heT, hfstV e heT, ?_⟩
              have h' : ∃ m, e.1 ∈ D m := ⟨j, heD⟩
              have hdu : dist e.1 = Nat.find h' := dif_pos h'
              rw [hdu, hdw, hj]
              have := Nat.find_min' h' heD
              omega
            choose! par hpar1 hpar2 hpar3 using hpar
            refine ⟨(V.erase r).image (fun w => (par w, w)), ?_, ⟨?_, ?_, ?_⟩, ?_⟩
            · intro e he
              obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
              obtain ⟨hwr, hwV⟩ := Finset.mem_erase.1 hw
              exact hpar1 w hwV hwr
            · intro e he
              obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
              exact (Finset.mem_erase.1 hw).1
            · intro e he e' he' h
              obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
              obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 he'
              simp only at h
              rw [h]
            · have hverts : verts r ((V.erase r).image (fun w => (par w, w))) ⊆ V := by
                intro x hx
                simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
                rcases hx with rfl | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
                · exact hrV
                · obtain ⟨w, hw, rfl⟩ := he
                  obtain ⟨hwr, hwV⟩ := Finset.mem_erase.1 hw
                  exact hpar2 w hwV hwr
                · obtain ⟨w, hw, rfl⟩ := he
                  exact (Finset.mem_erase.1 hw).2
              have key : ∀ m, ∀ w ∈ V, dist w = m →
                  Reaches ((V.erase r).image (fun w => (par w, w))) r w := by
                intro m
                induction m using Nat.strong_induction_on with
                | _ m ih =>
                  intro w hw hdm
                  by_cases hwr : w = r
                  · subst hwr; exact Relation.ReflTransGen.refl
                  · have h1 := ih (dist (par w)) (by rw [← hdm]; exact hpar3 w hw hwr) (par w)
                      (hpar2 w hw hwr) rfl
                    exact Relation.ReflTransGen.tail h1
                      (Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨hwr, hw⟩, rfl⟩)
              intro w hw
              exact key _ w (hverts hw) rfl
            · apply Finset.Subset.antisymm
              · intro x hx
                simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
                rcases hx with rfl | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
                · exact hrV
                · obtain ⟨w, hw, rfl⟩ := he
                  obtain ⟨hwr, hwV⟩ := Finset.mem_erase.1 hw
                  exact hpar2 w hwV hwr
                · obtain ⟨w, hw, rfl⟩ := he
                  exact (Finset.mem_erase.1 hw).2
              · intro x hx
                by_cases hxr : x = r
                · subst hxr; exact Finset.mem_insert_self _ _
                · simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
                  exact Or.inr (Or.inr ⟨(par x, x), ⟨x, Finset.mem_erase.2 ⟨hxr, hx⟩, rfl⟩, rfl⟩)
          -- (4) the O(log k) approximation guarantee
          have hApprox : ∃ C1 : ℝ, 0 < C1 ∧ ∀ (n : ℕ) (I : Inst n) (k : ℕ),
              IsMonotone I.f →
              NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)) →
              (∀ S, I.f S ≤ n ^ a) → 2 ≤ k → k ≤ n → ∀ T, (alg29 I a k).1 = some T →
                ∀ A : Edges n, IsArbo I.root A → cost I.c A ≤ I.B → A.card + 1 ≤ k →
                  (I.f (verts I.root A) : ℝ) ≤ C1 * Real.log k * (I.f (verts I.root T) : ℝ) := by
            refine ⟨4 / Real.log 2, div_pos (by norm_num) (Real.log_pos (by norm_num)), ?_⟩
            intro n I k hmono hsub hbd
            have hFeasG := hFeasG I
            clear hTime hSome hFeas hArbo
            classical
            have hSep : ∀ (r : Fin n) (A : Edges n), IsArbo r A → ∀ t : ℕ, 1 ≤ t → t ≤ A.card →
                  ∃ (v : Fin n) (A1 A2 : Edges n), Disjoint A1 A2 ∧ A1 ∪ A2 = A ∧ IsArbo r A1 ∧ IsArbo v A2 ∧
                    v ∈ verts r A1 ∧ t ≤ A2.card ∧ A2.card + 1 ≤ 2 * t := by
              clear hFeasG
              classical
              intro r A ⟨hA0, hU, hR⟩ t ht1 htA
              -- unique parent
              have hpar : ∀ x p y, (x, y) ∈ A → (p, y) ∈ A → x = p := fun x p y h1 h2 =>
                congrArg Prod.fst (hU _ h1 _ h2 rfl)
              have hsnd : ∀ e ∈ A, e.2 ∈ verts r A := fun e he => by
                unfold verts
                exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he))
              have hfst : ∀ e ∈ A, e.1 ∈ verts r A := fun e he => by
                unfold verts
                exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he))
              -- no cycles
              have hNC0 : ∀ y, Reaches A r y → ∀ x, (x, y) ∈ A → Reaches A y x → False := by
                intro y hy
                induction hy with
                | refl => intro x hx _; exact hA0 _ hx rfl
                | @tail p y _ hpy ih =>
                  intro x hx hyx
                  have hxp : x = p := hpar _ _ _ hx hpy
                  subst hxp
                  rcases Relation.ReflTransGen.cases_tail hyx with h | ⟨q, hq1, hq2⟩
                  · subst h; exact ih _ hpy Relation.ReflTransGen.refl
                  · exact ih q hq2 (Relation.ReflTransGen.head hpy hq1)
              have hNC : ∀ x y, (x, y) ∈ A → Reaches A y x → False := fun x y h1 h2 =>
                hNC0 y (hR _ (hsnd _ h1)) x h1 h2
              -- comparability
              have hCMP : ∀ a x, Reaches A a x → ∀ b, Reaches A b x → Reaches A a b ∨ Reaches A b a := by
                intro a x hax
                induction hax with
                | refl => intro b hb; exact Or.inr hb
                | @tail y x hay hyx ih =>
                  intro b hbx
                  rcases Relation.ReflTransGen.cases_tail hbx with h | ⟨q, hq1, hq2⟩
                  · subst h; exact Or.inl (Relation.ReflTransGen.tail hay hyx)
                  · have : q = y := hpar _ _ _ hq2 hyx
                    subst this
                    exact ih b hq1
              -- down sets
              let D : Fin n → Edges n := fun x => A.filter (fun e => Reaches A x e.2 ∧ e.2 ≠ x)
              let Dn : Fin n → Edges n := fun x => A.filter (fun e => Reaches A x e.2)
              have hDr : D r = A := by
                apply Finset.filter_true_of_mem
                intro e he
                exact ⟨hR _ (hsnd _ he), hA0 e he⟩
              -- choose v
              obtain ⟨v, hvC, hvmin⟩ := Finset.exists_min_image
                (Finset.univ.filter (fun x => Reaches A r x ∧ t ≤ (D x).card)) (fun x => (D x).card)
                ⟨r, Finset.mem_filter.2 ⟨Finset.mem_univ _, Relation.ReflTransGen.refl, by rw [hDr]; exact htA⟩⟩
              obtain ⟨hrv, htv⟩ := (Finset.mem_filter.1 hvC).2
              let E : Edges n := A.filter (fun e => e.1 = v)
              have hEA : ∀ f ∈ E, f ∈ A := fun f hf => (Finset.mem_filter.1 hf).1
              have hE1 : ∀ f ∈ E, f.1 = v := fun f hf => (Finset.mem_filter.1 hf).2
              have hEv : ∀ f ∈ E, (v, f.2) ∈ A := fun f hf => by
                have h := hEA f hf; rw [← hE1 f hf]; exact h
              -- branch weights bounded by t
              have hwt : ∀ f ∈ E, (Dn f.2).card ≤ t := by
                intro f hf
                have hvw := hEv f hf
                have hsub : Dn f.2 ⊆ insert (v, f.2) (D f.2) := by
                  intro e he
                  obtain ⟨heA, hre⟩ := Finset.mem_filter.1 he
                  by_cases h : e.2 = f.2
                  · have : e = (v, f.2) := hU _ heA _ hvw h
                    rw [this]; exact Finset.mem_insert_self _ _
                  · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨heA, hre, h⟩)
                have hlt : (D f.2).card < (D v).card := by
                  apply Finset.card_lt_card
                  refine ⟨?_, ?_⟩
                  · intro e he
                    obtain ⟨heA, hre, hne⟩ := Finset.mem_filter.1 he
                    refine Finset.mem_filter.2 ⟨heA, Relation.ReflTransGen.head hvw hre, ?_⟩
                    intro hev
                    rw [hev] at hre
                    exact hNC _ _ hvw hre
                  · intro hsub2
                    have := hsub2 (Finset.mem_filter.2 ⟨hvw, Relation.ReflTransGen.single hvw,
                      fun h => hNC _ _ hvw (by have h' : f.2 = v := h; rw [h']; exact Relation.ReflTransGen.refl)⟩)
                    exact (Finset.mem_filter.1 this).2.2 rfl
                have hct : (D f.2).card < t := by
                  by_contra hc
                  have := hvmin f.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _,
                    Relation.ReflTransGen.tail hrv hvw, by omega⟩)
                  omega
                have := Finset.card_le_card hsub
                have := Finset.card_insert_le (v, f.2) (D f.2)
                omega
              -- total weight ≥ t
              have hDvE : D v ⊆ E.biUnion (fun f => Dn f.2) := by
                intro e he
                obtain ⟨heA, hre, hne⟩ := Finset.mem_filter.1 he
                rcases Relation.ReflTransGen.cases_head hre with h | ⟨w, hvw, hw⟩
                · exact absurd h.symm hne
                · exact Finset.mem_biUnion.2 ⟨(v, w), Finset.mem_filter.2 ⟨hvw, rfl⟩,
                    Finset.mem_filter.2 ⟨heA, hw⟩⟩
              have hsumE : t ≤ ∑ f ∈ E, (Dn f.2).card :=
                le_trans htv (le_trans (Finset.card_le_card hDvE) Finset.card_biUnion_le)
              -- greedy selection
              have hGR : ∀ (S : Edges n), (∀ f ∈ S, (Dn f.2).card ≤ t) → t ≤ ∑ f ∈ S, (Dn f.2).card →
                  ∃ F ⊆ S, t ≤ ∑ f ∈ F, (Dn f.2).card ∧ ∑ f ∈ F, (Dn f.2).card + 1 ≤ 2 * t := by
                intro S
                induction S using Finset.induction_on with
                | empty => intro _ h; rw [Finset.sum_empty] at h; omega
                | @insert e S he ih =>
                  intro hw hs
                  by_cases hS : t ≤ ∑ f ∈ S, (Dn f.2).card
                  · obtain ⟨F, hF, h1, h2⟩ := ih (fun f hf => hw f (Finset.mem_insert_of_mem hf)) hS
                    exact ⟨F, hF.trans (Finset.subset_insert _ _), h1, h2⟩
                  · refine ⟨insert e S, Finset.Subset.refl _, hs, ?_⟩
                    rw [Finset.sum_insert he]
                    have := hw e (Finset.mem_insert_self _ _)
                    omega
              obtain ⟨F, hFE, hF1, hF2⟩ := hGR E hwt hsumE
              -- separation of distinct children
              have hsep : ∀ f ∈ E, ∀ f' ∈ E, f.2 ≠ f'.2 → ¬ Reaches A f.2 f'.2 := by
                intro f hf f' hf' hne h
                rcases Relation.ReflTransGen.cases_tail h with h' | ⟨q, hq1, hq2⟩
                · exact hne h'.symm
                · have : q = v := hpar _ _ _ hq2 (hEv f' hf')
                  subst this
                  exact hNC _ _ (hEv f hf) hq1
              let A2 : Edges n := F.biUnion (fun f => Dn f.2)
              let A1 : Edges n := A \ A2
              have hA2A : A2 ⊆ A := by
                intro e he
                obtain ⟨f, _, hef⟩ := Finset.mem_biUnion.1 he
                exact (Finset.mem_filter.1 hef).1
              have hcard : A2.card = ∑ f ∈ F, (Dn f.2).card := by
                apply Finset.card_biUnion
                intro f hf f' hf' hff
                have hfE := hFE hf
                have hfE' := hFE hf'
                have hne : f.2 ≠ f'.2 := by
                  intro h
                  apply hff
                  have e1 := hE1 f hfE
                  have e2 := hE1 f' hfE'
                  exact Prod.ext (by rw [e1, e2]) h
                rw [Function.onFun, Finset.disjoint_left]
                intro e he he'
                have h1 := (Finset.mem_filter.1 he).2
                have h2 := (Finset.mem_filter.1 he').2
                rcases hCMP _ _ h1 _ h2 with h | h
                · exact hsep f hfE f' hfE' hne h
                · exact hsep f' hfE' f hfE (Ne.symm hne) h
              -- Bad predicate
              have hmemA1 : ∀ e ∈ A, (¬ ∃ f ∈ F, Reaches A f.2 e.2) → e ∈ A1 := by
                intro e he hb
                refine Finset.mem_sdiff.2 ⟨he, ?_⟩
                intro he2
                obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.1 he2
                exact hb ⟨f, hf, (Finset.mem_filter.1 hef).2⟩
              have hA1R : ∀ x, Reaches A r x → (¬ ∃ f ∈ F, Reaches A f.2 x) → Reaches A1 r x := by
                intro x hx
                induction hx with
                | refl => intro _; exact Relation.ReflTransGen.refl
                | @tail y x _ hyx ih =>
                  intro hb
                  have hby : ¬ ∃ f ∈ F, Reaches A f.2 y := fun ⟨f, hf, h⟩ =>
                    hb ⟨f, hf, Relation.ReflTransGen.tail h hyx⟩
                  exact Relation.ReflTransGen.tail (ih hby) (hmemA1 _ hyx hb)
              have hnotA2 : ∀ e ∈ A1, ∀ f ∈ F, ¬ Reaches A f.2 e.2 := by
                intro e he f hf h
                exact (Finset.mem_sdiff.1 he).2 (Finset.mem_biUnion.2 ⟨f, hf, Finset.mem_filter.2
                  ⟨(Finset.mem_sdiff.1 he).1, h⟩⟩)
              have hA1A : A1 ⊆ A := Finset.sdiff_subset
              have hgood : ∀ x ∈ verts r A1, (¬ ∃ f ∈ F, Reaches A f.2 x) := by
                intro x hx ⟨f, hf, h⟩
                unfold verts at hx
                rcases Finset.mem_insert.1 hx with hx | hx
                · subst hx
                  rcases Relation.ReflTransGen.cases_tail h with h' | ⟨q, _, hq2⟩
                  · exact hA0 f (hEA f (hFE hf)) h'.symm
                  · exact hA0 _ hq2 rfl
                rcases Finset.mem_union.1 hx with hx | hx
                · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
                  exact hnotA2 e he f hf (Relation.ReflTransGen.tail h (hA1A he))
                · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
                  exact hnotA2 e he f hf h
              have hvertsA1 : verts r A1 ⊆ verts r A := by
                intro x hx
                unfold verts at hx ⊢
                rcases Finset.mem_insert.1 hx with hx | hx
                · rw [hx]; exact Finset.mem_insert_self _ _
                refine Finset.mem_insert_of_mem ?_
                rcases Finset.mem_union.1 hx with hx | hx
                · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
                  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hA1A he))
                · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
                  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hA1A he))
              -- path inside a branch
              have hDnR : ∀ f ∈ F, ∀ y, Reaches A f.2 y → Reaches A2 f.2 y := by
                intro f hf y hy
                induction hy with
                | refl => exact Relation.ReflTransGen.refl
                | @tail y z hy hyz ih =>
                  exact Relation.ReflTransGen.tail ih (Finset.mem_biUnion.2 ⟨f, hf,
                    Finset.mem_filter.2 ⟨hyz, Relation.ReflTransGen.tail hy hyz⟩⟩)
              have hfA2 : ∀ f ∈ F, (v, f.2) ∈ A2 := fun f hf => Finset.mem_biUnion.2 ⟨f, hf,
                Finset.mem_filter.2 ⟨hEv f (hFE hf), Relation.ReflTransGen.refl⟩⟩
              have hvA1 : Reaches A1 r v := hA1R v hrv (fun ⟨f, hf, h⟩ => hNC _ _ (hEv f (hFE hf)) h)
              refine ⟨v, A1, A2, Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hA2A, ⟨?_, ?_, ?_⟩,
                ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
              · exact fun e he => hA0 e (hA1A he)
              · exact fun e he e' he' h => hU e (hA1A he) e' (hA1A he') h
              · intro w hw
                exact hA1R w (hR w (hvertsA1 hw)) (hgood w hw)
              · intro e he hev
                obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.1 he
                have h := (Finset.mem_filter.1 hef).2
                rw [hev] at h
                exact hNC _ _ (hEv f (hFE hf)) h
              · exact fun e he e' he' h => hU e (hA2A he) e' (hA2A he') h
              · intro w hw
                unfold verts at hw
                rcases Finset.mem_insert.1 hw with hw | hw
                · rw [hw]; exact Relation.ReflTransGen.refl
                -- every endpoint of a branch edge is reachable from v inside A2
                have key : ∀ e ∈ A2, Reaches A2 v e.1 ∧ Reaches A2 v e.2 := by
                  intro e he
                  obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.1 he
                  obtain ⟨heA, h⟩ := Finset.mem_filter.1 hef
                  have hv2 : Reaches A2 v f.2 := Relation.ReflTransGen.single (hfA2 f hf)
                  refine ⟨?_, Relation.ReflTransGen.trans hv2 (hDnR f hf _ h)⟩
                  rcases Relation.ReflTransGen.cases_tail h with h' | ⟨q, hq1, hq2⟩
                  · have : e = (v, f.2) := hU _ heA _ (hEv f (hFE hf)) h'
                    rw [this]; exact Relation.ReflTransGen.refl
                  · have : q = e.1 := hpar _ _ _ hq2 heA
                    rw [← this]
                    exact Relation.ReflTransGen.trans hv2 (hDnR f hf _ hq1)
                rcases Finset.mem_union.1 hw with hw | hw
                · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hw
                  exact (key e he).1
                · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hw
                  exact (key e he).2
              · rcases Relation.ReflTransGen.cases_tail hvA1 with h | ⟨q, _, hq2⟩
                · rw [h]; unfold verts; exact Finset.mem_insert_self _ _
                · unfold verts
                  exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd hq2))
              · rw [hcard]; exact hF1
              · rw [hcard]; exact hF2
            have hCBD : ∀ (X : Finset (Fin n)) (r : Fin n) (init : Option (Edges n)) (L : List (Edges n)),
                  (∀ T0, init = some T0 → ∃ T, (chooseBest I.f X r init L).1 = some T ∧ fX I.f X r T0 ≤ fX I.f X r T) ∧
                  (∀ c ∈ L, ∃ T, (chooseBest I.f X r init L).1 = some T ∧ fX I.f X r c ≤ fX I.f X r T) := by
              clear hFeasG hSep
              intro X r init L
              clear hsub hbd hmono
              have gen : ∀ (g : Option (Edges n) × ℕ → Edges n → Option (Edges n) × ℕ),
                  (∀ x T, ∃ T1, (g x T).1 = some T1 ∧ fX I.f X r T ≤ fX I.f X r T1 ∧
                      ∀ T0, x.1 = some T0 → fX I.f X r T0 ≤ fX I.f X r T1) →
                  ∀ (L : List (Edges n)) (x : Option (Edges n) × ℕ),
                  (∀ T0, x.1 = some T0 → ∃ T, (L.foldl g x).1 = some T ∧ fX I.f X r T0 ≤ fX I.f X r T) ∧
                  (∀ c ∈ L, ∃ T, (L.foldl g x).1 = some T ∧ fX I.f X r c ≤ fX I.f X r T) := by
                intro g hg L
                induction L with
                | nil => intro x; exact ⟨fun T0 h => ⟨T0, h, le_refl _⟩, fun c hc => absurd hc List.not_mem_nil⟩
                | cons y ys ih =>
                  intro x
                  rw [List.foldl_cons]
                  obtain ⟨T1, hT1, hy, hi⟩ := hg x y
                  obtain ⟨ih1, ih2⟩ := ih (g x y)
                  obtain ⟨T, hT, hle⟩ := ih1 T1 hT1
                  refine ⟨fun T0 h => ⟨T, hT, le_trans (hi T0 h) hle⟩, fun c hc => ?_⟩
                  rcases List.mem_cons.1 hc with rfl | hc
                  · exact ⟨T, hT, le_trans hy hle⟩
                  · exact ih2 c hc
              unfold chooseBest
              refine gen _ ?_ L (init, 0)
              rintro ⟨o, s⟩ T
              rcases o with _ | old
              · exact ⟨T, rfl, le_refl _, fun T0 h => by cases h⟩
              · by_cases hlt : fX I.f X r old < fX I.f X r T
                · refine ⟨T, if_pos hlt, le_refl _, fun T0 h => ?_⟩
                  cases h; exact le_of_lt hlt
                · refine ⟨old, if_neg hlt, le_of_not_gt hlt, fun T0 h => ?_⟩
                  cases h; exact le_refl _
            have hPFD : ∀ (X : Finset (Fin n)) (r : Fin n) (plans : List (List (Fin n × Finset (Fin n))))
                  (g : List (Fin n × Finset (Fin n)) → List (Edges n) × ℕ) (init : Option (Edges n)) (s : ℕ),
                  (∀ T0, init = some T0 → ∃ T, (plans.foldl (fun x plan => ((chooseBest I.f X r x.1 (g plan).1).1,
                      x.2 + (g plan).2 + (chooseBest I.f X r x.1 (g plan).1).2)) (init, s)).1 = some T ∧
                      fX I.f X r T0 ≤ fX I.f X r T) ∧
                  (∀ p ∈ plans, ∀ c ∈ (g p).1, ∃ T, (plans.foldl (fun x plan => ((chooseBest I.f X r x.1 (g plan).1).1,
                      x.2 + (g plan).2 + (chooseBest I.f X r x.1 (g plan).1).2)) (init, s)).1 = some T ∧
                      fX I.f X r c ≤ fX I.f X r T) := by
              clear hFeasG hSep
              intro X r plans g
              clear hsub hbd hmono
              induction plans with
              | nil => intro init s; exact ⟨fun T0 h => ⟨T0, h, le_refl _⟩, fun p hp => absurd hp List.not_mem_nil⟩
              | cons p ps ih =>
                intro init s
                rw [List.foldl_cons]
                obtain ⟨ih1, ih2⟩ := ih (chooseBest I.f X r init (g p).1).1
                  (s + (g p).2 + (chooseBest I.f X r init (g p).1).2)
                obtain ⟨c1, c2⟩ := hCBD X r init (g p).1
                refine ⟨fun T0 h => ?_, fun q hq c hc => ?_⟩
                · obtain ⟨T1, hT1, h1⟩ := c1 T0 h
                  obtain ⟨T, hT, h2⟩ := ih1 T1 hT1
                  exact ⟨T, hT, le_trans h1 h2⟩
                · rcases List.mem_cons.1 hq with rfl | hq
                  · obtain ⟨T1, hT1, h1⟩ := c2 c hc
                    obtain ⟨T, hT, h2⟩ := ih1 T1 hT1
                    exact ⟨T, hT, le_trans h1 h2⟩
                  · exact ih2 q hq c hc
            have hVal : ∀ (X : Finset (Fin n)) (r v : Fin n) (T1 T2 : Edges n), v ∈ verts r T1 →
                  fX I.f X r (T1 ∪ T2) = fX I.f X r T1 + fX I.f (X ∪ verts r T1) v T2 := by
              clear hFeasG hSep hCBD hPFD
              intro X r v T1 T2 hv
              clear hsub hbd hmono
              have e : verts r (T1 ∪ T2) ∪ X = verts v T2 ∪ (X ∪ verts r T1) := by
                ext x
                unfold verts at hv ⊢
                simp only [Finset.mem_union, Finset.mem_insert, Finset.image_union] at hv ⊢
                constructor
                · rintro ((h | (h | h) | (h | h)) | h)
                  · exact Or.inr (Or.inr (Or.inl h))
                  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
                  · exact Or.inl (Or.inr (Or.inl h))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
                  · exact Or.inl (Or.inr (Or.inr h))
                  · exact Or.inr (Or.inl h)
                · rintro ((h | h | h) | h | h | h | h)
                  · subst h
                    rcases hv with h | h | h
                    · exact Or.inl (Or.inl h)
                    · exact Or.inl (Or.inr (Or.inl (Or.inl h)))
                    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
                  · exact Or.inl (Or.inr (Or.inl (Or.inr h)))
                  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
                  · exact Or.inr h
                  · exact Or.inl (Or.inl h)
                  · exact Or.inl (Or.inr (Or.inl (Or.inl h)))
                  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
              unfold fX
              rw [e, Finset.union_comm (verts r T1) X]
              ring
            have hBaseG : ∀ (r : Fin n) (Y₀ X : Finset (Fin n)) (B : ℕ) (A : Edges n), IsArbo r A → Y₀.erase r ⊆ verts r A →
                  A.card ≤ 1 → cost I.c A ≤ B →
                  ∃ T, (rg I 1 (.bsearch (n ^ a)) 1 r Y₀ B X).1 = some T ∧ fX I.f X r A ≤ fX I.f X r T := by
              clear hFeasG hSep hPFD hVal
              intro r Y₀ X B A hA hY hc hB
              clear hsub hbd hmono
              rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h0 | h1
              · have hA0 : A = ∅ := Finset.card_eq_zero.1 h0
                subst hA0
                have hYe : Y₀.erase r = ∅ := by
                  apply Finset.eq_empty_of_forall_notMem
                  intro x hx
                  have h := hY hx
                  simp only [verts, Finset.image_empty, Finset.union_empty, Finset.mem_insert,
                    Finset.notMem_empty, or_false] at h
                  exact (Finset.mem_erase.1 hx).1 h
                have hcap : ¬ capImp 1 (0 + 1) < ((Y₀.erase r).card : ℝ) := by
                  rw [hYe, Finset.card_empty]; unfold capImp; norm_num
                rw [rg, if_neg hcap, if_pos rfl, if_pos rfl, rgBasic, Finset.erase_idem, if_neg hcap, if_pos rfl,
                  if_pos hYe]
                obtain ⟨T, hT, hle⟩ := (hCBD X r (some ∅) _).1 ∅ rfl
                exact ⟨T, hT, hle⟩
              · obtain ⟨⟨p, w⟩, rfl⟩ := Finset.card_eq_one.1 h1
                have hw : w ≠ r := hA.1 (p, w) (Finset.mem_singleton_self _)
                have inv : ∀ x, Reaches ({(p, w)} : Edges n) r x → x = r ∨ p = r := by
                  intro x h
                  induction h with
                  | refl => exact Or.inl rfl
                  | tail _ hab ih =>
                    rcases Prod.mk.inj (Finset.mem_singleton.1 hab) with ⟨h1, _⟩
                    rcases ih with h | h
                    · exact Or.inr (h1 ▸ h)
                    · exact Or.inr h
                have hwv : w ∈ verts r ({(p, w)} : Edges n) := by
                  simp only [verts, Finset.image_singleton, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
                  exact Or.inr (Or.inr trivial)
                have hp : p = r := (inv w (hA.2.2 w hwv)).resolve_left hw
                subst hp
                have hcw : I.c p w ≤ B := by
                  unfold cost at hB; rwa [Finset.sum_singleton] at hB
                have hYw : Y₀.erase p ⊆ {w} := by
                  intro x hx
                  have h := hY hx
                  simp only [verts, Finset.image_singleton, Finset.mem_insert, Finset.mem_union,
                    Finset.mem_singleton] at h
                  rcases h with h | h | h
                  · exact absurd h (Finset.mem_erase.1 hx).1
                  · exact absurd h (Finset.mem_erase.1 hx).1
                  · exact Finset.mem_singleton.2 h
                have hcap : ¬ capImp 1 (0 + 1) < ((Y₀.erase p).card : ℝ) := by
                  have : (Y₀.erase p).card ≤ 1 := by
                    have := Finset.card_le_card hYw; rwa [Finset.card_singleton] at this
                  have h' : ((Y₀.erase p).card : ℝ) ≤ 1 := by exact_mod_cast this
                  unfold capImp; norm_num; linarith
                rw [rg, if_neg hcap, if_pos rfl, if_pos rfl, rgBasic, Finset.erase_idem, if_neg hcap, if_pos rfl]
                by_cases hYe : Y₀.erase p = ∅
                · rw [if_pos hYe]
                  have hmem : ({(p, w)} : Edges n) ∈ List.filterMap
                      (fun v => if (decide (v = p) || decide (B < I.c p v)) = true then none else some {(p, v)})
                      (List.finRange n) := by
                    rw [List.mem_filterMap]
                    refine ⟨w, List.mem_finRange w, ?_⟩
                    rw [if_neg]
                    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt]
                    exact ⟨hw, hcw⟩
                  obtain ⟨T, hT, hle⟩ := (hCBD X p (some ∅) _).2 _ hmem
                  exact ⟨T, hT, hle⟩
                · rw [if_neg hYe]
                  have hYw' : Y₀.erase p = {w} :=
                    Finset.Subset.antisymm hYw (by
                      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hYe
                      have := Finset.mem_singleton.1 (hYw hx)
                      subst this
                      exact Finset.singleton_subset_iff.2 hx)
                  rw [hYw', Finset.toList_singleton]
                  exact ⟨_, if_pos hcw, le_refl _⟩
            have hBS : ∀ (probe : ℕ → Bool × ℕ), (∀ b b', b ≤ b' → (probe b).1 = true → (probe b').1 = true) → ∀ hi : ℕ,
                  (∀ b, (bsearch probe 0 hi).1 = some b → (probe b).1 = true ∧ b ≤ hi ∧
                      ∀ b0, b0 ≤ hi → (probe b0).1 = true → b ≤ b0) ∧
                  (∀ b0, b0 ≤ hi → (probe b0).1 = true → ∃ b, (bsearch probe 0 hi).1 = some b) := by
              clear hFeasG hSep hCBD hPFD hVal hBaseG
              intro probe hmon
              have key : ∀ fuel lo hi, hi + 1 - lo ≤ fuel →
                  (∀ b, (bsearchAux probe fuel lo hi).1 = some b → (probe b).1 = true ∧ lo ≤ b ∧ b ≤ hi ∧
                    ∀ b0, lo ≤ b0 → b0 ≤ hi → (probe b0).1 = true → b ≤ b0) ∧
                  (∀ b0, lo ≤ b0 → b0 ≤ hi → (probe b0).1 = true → ∃ b, (bsearchAux probe fuel lo hi).1 = some b) := by
                intro fuel
                induction fuel with
                | zero =>
                  intro lo hi h
                  refine ⟨fun b hb => by simp [bsearchAux] at hb, fun b0 h1 h2 _ => by omega⟩
                | succ fuel ih =>
                  intro lo hi hf
                  rw [bsearchAux]
                  by_cases hlt : hi < lo
                  · rw [if_pos hlt]
                    exact ⟨fun b hb => by simp at hb, fun b0 h1 h2 _ => by omega⟩
                  · rw [if_neg hlt]
                    by_cases hmid' : (probe (lo + (hi - lo) / 2)).1 = true
                    swap
                    · have hmid : (probe (lo + (hi - lo) / 2)).1 = false := by simpa using hmid'
                      obtain ⟨ih1, ih2⟩ := ih (lo + (hi - lo) / 2 + 1) hi (by omega)
                      simp only; rw [if_neg hmid']
                      refine ⟨fun b hb => ?_, fun b0 h1 h2 h3 => ?_⟩
                      · obtain ⟨q1, q2, q3, q4⟩ := ih1 b hb
                        refine ⟨q1, by omega, q3, fun b0 h1 h2 h3 => ?_⟩
                        by_cases hb0 : b0 ≤ lo + (hi - lo) / 2
                        · have := hmon _ _ hb0 h3; rw [hmid] at this; exact absurd this (by simp)
                        · exact q4 b0 (by omega) h2 h3
                      · by_cases hb0 : b0 ≤ lo + (hi - lo) / 2
                        · have := hmon _ _ hb0 h3; rw [hmid] at this; exact absurd this (by simp)
                        · exact ih2 b0 (by omega) h2 h3
                    · have hmid := hmid'
                      simp only; rw [if_pos hmid']
                      by_cases he : lo + (hi - lo) / 2 = lo
                      · rw [if_pos he]
                        refine ⟨fun b hb => ?_, fun b0 _ _ _ => ⟨_, rfl⟩⟩
                        simp only [Option.some.injEq] at hb
                        subst hb
                        refine ⟨hmid, by omega, by omega, fun b0 h1 _ _ => by omega⟩
                      · rw [if_neg he]
                        obtain ⟨ih1, ih2⟩ := ih lo (lo + (hi - lo) / 2 - 1) (by omega)
                        rcases hr : (bsearchAux probe fuel lo (lo + (hi - lo) / 2 - 1)).1 with _ | b'
                        all_goals rw [hr] at ih1 ih2; simp only
                        · refine ⟨fun b hb => ?_, fun b0 _ _ _ => ⟨_, rfl⟩⟩
                          simp only [Option.orElse, Option.some.injEq] at hb
                          subst hb
                          refine ⟨hmid, by omega, by omega, fun b0 h1 h2 h3 => ?_⟩
                          by_contra hc
                          obtain ⟨_, hh⟩ := ih2 b0 h1 (by omega) h3
                          exact absurd hh (by simp)
                        · refine ⟨fun b hb => ?_, fun b0 _ _ _ => ⟨_, rfl⟩⟩
                          simp only [Option.orElse, Option.some.injEq] at hb
                          subst hb
                          obtain ⟨q1, q2, q3, q4⟩ := ih1 b' rfl
                          refine ⟨q1, q2, by omega, fun b0 h1 h2 h3 => ?_⟩
                          by_cases hb0 : b0 ≤ lo + (hi - lo) / 2 - 1
                          · exact q4 b0 h1 hb0 h3
                          · omega
              intro hi
              obtain ⟨k1, k2⟩ := key (hi + 1 - 0) 0 hi le_rfl
              exact ⟨fun b hb => by obtain ⟨q1, _, q3, q4⟩ := k1 b hb; exact ⟨q1, q3, fun b0 h2 h3 => q4 b0 (Nat.zero_le _) h2 h3⟩,
                fun b0 h2 h3 => k2 b0 (Nat.zero_le _) h2 h3⟩
            have hS : ∀ (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
                  (r v : Fin n) (Y1 Y2 X : Finset (Fin n)) (B : ℕ), ∃ P : ℝ → ℕ → Bool × ℕ,
                 (∀ u b, (P u b).1 = true ↔ ∃ T, (sub r Y1 b X).1 = some T ∧ u ≤ fX I.f X r T) ∧
                 ∀ c, c ∈ (runPlan I (.bsearch (n ^ a)) sub [(r, Y1), (v, Y2)] X B ∅).1 ↔
                   ∃ u : ℝ, (∃ m : ℕ, m ≤ n ^ a ∧ (m : ℝ) = u) ∧ ∃ b T1 T2, (bsearch (P u) 0 B).1 = some b ∧
                     (sub r Y1 b X).1 = some T1 ∧ (sub v Y2 (B - b) (X ∪ verts r T1)).1 = some T2 ∧ c = T1 ∪ T2 := by
              clear hFeasG hSep hCBD hPFD hVal hBaseG hBS
              have hfm : ∀ {β : Type} (g : List (Edges n) × ℕ → β → List (Edges n) × ℕ),
                  (∀ x u, (g x u).1 = x.1 ++ (g ([], 0) u).1) → ∀ (l : List β) (init : List (Edges n) × ℕ) c,
                  c ∈ (l.foldl g init).1 ↔ c ∈ init.1 ∨ ∃ u ∈ l, c ∈ (g ([], 0) u).1 := by
                intro β g hg l
                induction l with
                | nil => intro init c; simp
                | cons x xs ih =>
                  intro init c
                  rw [List.foldl_cons, ih, hg, List.mem_append]
                  simp only [List.mem_cons, exists_eq_or_imp]
                  tauto
              intro sub r v Y1 Y2 X B
              rw [runPlan]
              swap
              · simp
              simp only [runPlan]
              apply Exists.intro
              constructor
              swap
              · intro c
                rw [hfm]
                · constructor
                  · rintro (hc | ⟨u, hu, hc⟩)
                    · simp at hc
                    refine ⟨u, ?_, ?_⟩
                    · simp only [List.pure_def, List.bind_eq_flatMap, List.mem_flatMap, List.mem_range,
                        List.mem_singleton] at hu
                      obtain ⟨m, hm, rfl⟩ := hu
                      exact ⟨m, by omega, rfl⟩
                    dsimp only at hc
                    split at hc
                    · simp at hc
                    rename_i b heq
                    split at hc
                    · simp at hc
                    rename_i T1 heq1
                    rcases h2 : (sub v Y2 (B - b) (X ∪ verts r T1)).1 with _ | T2
                    · rw [h2] at hc; simp at hc
                    rw [h2] at hc
                    simp only [Option.toList_some, List.map_cons, List.map_nil, Finset.empty_union] at hc
                    exact ⟨b, T1, T2, heq, heq1, h2, by simpa using hc⟩
                  · rintro ⟨u, ⟨m, hm, rfl⟩, b, T1, T2, hb, h1, h2, rfl⟩
                    right
                    refine ⟨(m : ℝ), ?_, ?_⟩
                    · simp only [List.pure_def, List.bind_eq_flatMap, List.mem_flatMap, List.mem_range,
                        List.mem_singleton]
                      exact ⟨m, by omega, rfl⟩
                    simp only [hb, h1, h2]
                    simp
                · intro x u
                  dsimp only
                  split
                  · simp
                  · split
                    · simp
                    · simp
              · intro u b
                split
                · rename_i h; simp [h]
                · rename_i T h; simp [h]
            have hCandF : ∀ (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
                  (r v : Fin n) (Y1 Y2 X : Finset (Fin n)) (B : ℕ),
                  (∀ b b' T, b ≤ b' → (sub r Y1 b X).1 = some T →
                      ∃ T', (sub r Y1 b' X).1 = some T' ∧ fX I.f X r T ≤ fX I.f X r T') →
                  ∀ u : ℕ, u ≤ n ^ a → ∀ b T1, b ≤ B → (sub r Y1 b X).1 = some T1 → (u : ℝ) ≤ fX I.f X r T1 →
                  ∃ b' T1', b' ≤ b ∧ (sub r Y1 b' X).1 = some T1' ∧ (u : ℝ) ≤ fX I.f X r T1' ∧
                    (∀ b'' T'', (sub r Y1 b'' X).1 = some T'' → (u : ℝ) ≤ fX I.f X r T'' → b' ≤ b'') ∧
                    ∀ T2, (sub v Y2 (B - b') (X ∪ verts r T1')).1 = some T2 →
                      T1' ∪ T2 ∈ (runPlan I (.bsearch (n ^ a)) sub [(r, Y1), (v, Y2)] X B ∅).1 := by
              clear hFeasG hSep hCBD hPFD hVal hBaseG
              intro sub r v Y1 Y2 X B hmonoS u hu b T1 hb hT1 hu1
              obtain ⟨P, hP, hmem⟩ := hS sub r v Y1 Y2 X B
              have hPm : ∀ b1 b2, b1 ≤ b2 → (P (u : ℝ) b1).1 = true → (P (u : ℝ) b2).1 = true := by
                intro b1 b2 h12 h1
                obtain ⟨T, hT, hTu⟩ := (hP _ _).1 h1
                obtain ⟨T', hT', hle⟩ := hmonoS b1 b2 T h12 hT
                exact (hP _ _).2 ⟨T', hT', le_trans hTu hle⟩
              obtain ⟨hB1, hB2⟩ := hBS (P (u : ℝ)) hPm B
              have hpb : (P (u : ℝ) b).1 = true := (hP _ _).2 ⟨T1, hT1, hu1⟩
              obtain ⟨b', hb'⟩ := hB2 b hb hpb
              obtain ⟨q1, q2, q3⟩ := hB1 b' hb'
              obtain ⟨T1', hT1', hu1'⟩ := (hP _ _).1 q1
              refine ⟨b', T1', q3 b hb hpb, hT1', hu1', ?_, ?_⟩
              · intro b'' T'' h1 h2
                by_cases hbB : b'' ≤ B
                · exact q3 b'' hbB ((hP _ _).2 ⟨T'', h1, h2⟩)
                · omega
              · intro T2 hT2
                exact (hmem _).2 ⟨u, ⟨u, hu, rfl⟩, b', T1', T2, hb', hT1', hT2, rfl⟩
            have hCandI : ∀ (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
                  (r v : Fin n) (Y1 Y2 X : Finset (Fin n)) (B : ℕ),
                  (∀ b b' T, b ≤ b' → (sub r Y1 b X).1 = some T →
                      ∃ T', (sub r Y1 b' X).1 = some T' ∧ fX I.f X r T ≤ fX I.f X r T') →
                  ∀ c ∈ (runPlan I (.bsearch (n ^ a)) sub [(r, Y1), (v, Y2)] X B ∅).1,
                  ∃ (u b : ℕ) (T1 T2 : Edges n), b ≤ B ∧ (sub r Y1 b X).1 = some T1 ∧ (u : ℝ) ≤ fX I.f X r T1 ∧
                    (∀ b'' T'', (sub r Y1 b'' X).1 = some T'' → (u : ℝ) ≤ fX I.f X r T'' → b ≤ b'') ∧
                    (sub v Y2 (B - b) (X ∪ verts r T1)).1 = some T2 ∧ c = T1 ∪ T2 := by
              clear hFeasG hSep hCBD hPFD hVal hBaseG hCandF
              intro sub r v Y1 Y2 X B hmonoS c hc
              obtain ⟨P, hP, hmem⟩ := hS sub r v Y1 Y2 X B
              obtain ⟨u, ⟨m, hm, rfl⟩, b, T1, T2, hb, hT1, hT2, rfl⟩ := (hmem c).1 hc
              have hPm : ∀ b1 b2, b1 ≤ b2 → (P (m : ℝ) b1).1 = true → (P (m : ℝ) b2).1 = true := by
                intro b1 b2 h12 h1
                obtain ⟨T, hT, hTu⟩ := (hP _ _).1 h1
                obtain ⟨T', hT', hle⟩ := hmonoS b1 b2 T h12 hT
                exact (hP _ _).2 ⟨T', hT', le_trans hTu hle⟩
              obtain ⟨hB1, _⟩ := hBS (P (m : ℝ)) hPm B
              obtain ⟨q1, q2, q3⟩ := hB1 b hb
              obtain ⟨T, hT, hTu⟩ := (hP _ _).1 q1
              rw [hT1, Option.some.injEq] at hT
              subst hT
              refine ⟨m, b, T1, T2, q2, hT1, hTu, ?_, hT2, rfl⟩
              intro b'' T'' h1 h2
              by_cases hbB : b'' ≤ B
              · exact q3 b'' hbB ((hP _ _).2 ⟨T'', h1, h2⟩)
              · omega
            have hMono : ∀ i (r : Fin n) (Y₀ X : Finset (Fin n)) (B B' : ℕ) (T : Edges n), B ≤ B' →
                  (rg I 1 (.bsearch (n ^ a)) i r Y₀ B X).1 = some T →
                  ∃ T', (rg I 1 (.bsearch (n ^ a)) i r Y₀ B' X).1 = some T' ∧ fX I.f X r T ≤ fX I.f X r T' := by
              clear hSep hBaseG hBS hS
              classical
              have hCB : ∀ (P : Edges n → Prop) (X : Finset (Fin n)) (r : Fin n)
                  (L : List (Edges n)) (init : Option (Edges n)),
                  (∀ T, init = some T → P T) → (∀ c ∈ L, P c) →
                  ∀ T, (chooseBest I.f X r init L).1 = some T → P T := by
                intro P X r L
                unfold chooseBest
                suffices h : ∀ (L : List (Edges n)) (init : Option (Edges n)) (s : ℕ),
                    (∀ T, init = some T → P T) → (∀ c ∈ L, P c) →
                    ∀ T, (L.foldl (fun (incumbent, steps) T =>
                        let next := match incumbent with
                          | none => some T
                          | some old => if fX I.f X r old < fX I.f X r T then some T else incumbent
                        (next, steps + 1)) (init, s)).1 = some T → P T by
                  intro init h1 h2; exact h L init 0 h1 h2
                intro L
                induction L with
                | nil => intro init s h1 _ T hT; exact h1 T hT
                | cons x xs ih =>
                  intro init s h1 h2 T hT
                  simp only [List.foldl_cons] at hT
                  refine ih _ _ ?_ (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) T hT
                  intro T' hT'
                  rcases init with _ | old
                  · simp only [Option.some.injEq] at hT'; subst hT'; exact h2 _ List.mem_cons_self
                  · simp only at hT'
                    split_ifs at hT' with hlt
                    · simp only [Option.some.injEq] at hT'; subst hT'; exact h2 _ List.mem_cons_self
                    · exact h1 T' hT'
              have hPF : ∀ (P : Edges n → Prop) (X : Finset (Fin n)) (r : Fin n)
                  (plans : List (List (Fin n × Finset (Fin n))))
                  (g : List (Fin n × Finset (Fin n)) → List (Edges n) × ℕ) (init : Option (Edges n)) (s : ℕ),
                  (∀ T, init = some T → P T) → (∀ p ∈ plans, ∀ c ∈ (g p).1, P c) →
                  ∀ T, (plans.foldl (fun x plan => ((chooseBest I.f X r x.1 (g plan).1).1,
                      x.2 + (g plan).2 + (chooseBest I.f X r x.1 (g plan).1).2)) (init, s)).1 = some T → P T := by
                intro P X r plans g
                induction plans with
                | nil => intro init s h1 _ T hT; exact h1 T hT
                | cons p ps ih =>
                  intro init s h1 h2 T hT
                  simp only [List.foldl_cons] at hT
                  refine ih _ _ ?_ (fun q hq => h2 q (List.mem_cons_of_mem _ hq)) T hT
                  exact hCB P X r _ init h1 (h2 p List.mem_cons_self)
              have hFD : ∀ (X : Finset (Fin n)) (r : Fin n) (plans : List (List (Fin n × Finset (Fin n))))
                  (g g' : List (Fin n × Finset (Fin n)) → List (Edges n) × ℕ) (init : Option (Edges n)) (s : ℕ) T,
                  (plans.foldl (fun x plan => ((chooseBest I.f X r x.1 (g plan).1).1,
                      x.2 + (g plan).2 + (chooseBest I.f X r x.1 (g plan).1).2)) (init, s)).1 = some T →
                  (∀ p ∈ plans, ∀ c ∈ (g p).1, ∃ c' ∈ (g' p).1, fX I.f X r c ≤ fX I.f X r c') →
                  ∃ T', (plans.foldl (fun x plan => ((chooseBest I.f X r x.1 (g' plan).1).1,
                      x.2 + (g' plan).2 + (chooseBest I.f X r x.1 (g' plan).1).2)) (init, s)).1 = some T' ∧
                      fX I.f X r T ≤ fX I.f X r T' := by
                intro X r plans g g' init s T hT hdom
                refine hPF (fun T => ∃ T', (plans.foldl (fun x plan => ((chooseBest I.f X r x.1 (g' plan).1).1,
                      x.2 + (g' plan).2 + (chooseBest I.f X r x.1 (g' plan).1).2)) (init, s)).1 = some T' ∧
                      fX I.f X r T ≤ fX I.f X r T') X r plans g init s ?_ ?_ T hT
                · exact (hPFD X r plans g' init s).1
                · intro p hp c hc
                  obtain ⟨c', hc', hle⟩ := hdom p hp c hc
                  obtain ⟨T', h1, h2⟩ := (hPFD X r plans g' init s).2 p hp c' hc'
                  exact ⟨T', h1, hle.trans h2⟩
              intro i
              induction i with
              | zero => intro r Y₀ X B B' T _ hT; rw [rg] at hT; exact absurd hT (by simp)
              | succ i ih =>
                intro r Y₀ X B B' T hBB hT
                rw [rg] at hT ⊢
                by_cases h1 : capImp 1 (i + 1) < ((Y₀.erase r).card : ℝ)
                · rw [if_pos h1] at hT; exact absurd hT (by simp only [reduceCtorEq, not_false_eq_true])
                rw [if_neg h1] at hT ⊢
                rcases Nat.eq_zero_or_pos i with rfl | hi
                · rw [if_pos rfl, if_pos rfl] at hT ⊢
                  clear hCandF hCandI hPFD hVal hFeasG hPF hFD ih
                  rw [rgBasic] at hT ⊢
                  by_cases g1 : capImp 1 (0 + 1) < (((Y₀.erase r).erase r).card : ℝ)
                  · rw [if_pos g1] at hT; exact absurd hT (by simp only [reduceCtorEq, not_false_eq_true])
                  rw [if_neg g1, if_pos rfl] at hT ⊢
                  by_cases g3 : (Y₀.erase r).erase r = ∅
                  · rw [if_pos g3] at hT ⊢
                    obtain ⟨hA, hBc⟩ := hCBD X r (some ∅) (List.filterMap (fun v => if (decide (v = r) || decide (B' < I.c r v)) = true then none else some ({(r, v)} : Edges n)) (List.finRange n))
                    refine hCB (fun T => ∃ T', (chooseBest I.f X r (some ∅) (List.filterMap (fun v => if (decide (v = r) || decide (B' < I.c r v)) = true then none else some ({(r, v)} : Edges n)) (List.finRange n))).1 = some T' ∧ fX I.f X r T ≤ fX I.f X r T') X r _ _ (fun T0 h0 => hA T0 h0) ?_ T hT
                    intro c hc
                    apply hBc
                    simp only [List.mem_filterMap, List.mem_finRange, true_and] at hc ⊢
                    obtain ⟨v, hv⟩ := hc
                    refine ⟨v, ?_⟩
                    by_cases hvr : v = r
                    · simp [hvr] at hv
                    · by_cases hc' : B < I.c r v
                      · simp [hvr, hc'] at hv
                      · have : ¬ B' < I.c r v := by omega
                        simp [hvr, hc'] at hv; simp [hvr, this, hv]
                  · rw [if_neg g3] at hT ⊢
                    revert hT
                    dsimp only
                    split
                    · intro hT
                      split_ifs at hT ⊢ with hc hc'
                      · exact ⟨T, hT, le_refl _⟩
                      · omega
                    · intro hT; exact absurd hT (by simp)
                · rw [if_neg (by omega)] at hT ⊢
                  refine hFD X r (leafPlans 1 r (Y₀.erase r))
                    (fun p => runPlan I (.bsearch (n ^ a)) (rg I 1 (.bsearch (n ^ a)) i) p X B ∅)
                    (fun p => runPlan I (.bsearch (n ^ a)) (rg I 1 (.bsearch (n ^ a)) i) p X B' ∅) _ 1 T hT ?_
                  intro p hp c hc
                  simp only [leafPlans, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
                    List.append_nil, List.mem_flatMap, List.mem_finRange, Finset.mem_toList,
                    Finset.mem_powerset, true_and, List.mem_cons, List.not_mem_nil, or_false] at hp
                  obtain ⟨v, S, hS, rfl⟩ := hp
                  obtain ⟨u, b, T1, T2, hbB, hT1, hu, hleast, hT2, rfl⟩ :=
                    hCandI _ r v _ _ X B (fun b b' T hb hT => ih r _ X b b' T hb hT) c hc
                  have hun : u ≤ n ^ a := by
                    have e1 : (u : ℝ) ≤ (I.f (verts r T1 ∪ X) : ℝ) := by
                      have e0 := hu; unfold fX at e0; have : (0:ℝ) ≤ I.f X := Nat.cast_nonneg _; linarith
                    have e2 : ((I.f (verts r T1 ∪ X) : ℕ) : ℝ) ≤ ((n ^ a : ℕ) : ℝ) := by exact_mod_cast hbd _
                    exact_mod_cast e1.trans e2
                  obtain ⟨b', T1', hb'b, hT1', hu', hleast', hcand⟩ :=
                    hCandF _ r v _ _ X B' (fun b b' T hb hT => ih r _ X b b' T hb hT) u hun b T1 (hbB.trans hBB) hT1 hu
                  have hbb : b = b' := le_antisymm (hleast b' T1' hT1' hu') hb'b
                  subst hbb
                  rw [hT1] at hT1'
                  obtain rfl := Option.some.inj hT1'
                  obtain ⟨T2', hT2', hle⟩ := ih v _ (X ∪ verts r T1) (B - b) (B' - b) T2 (by omega) hT2
                  refine ⟨T1 ∪ T2', hcand T2' hT2', ?_⟩
                  have hv : v ∈ verts r T1 := by
                    by_cases hvr : v = r
                    · subst hvr; exact Finset.mem_insert_self _ _
                    · exact (hFeasG i r _ b X T1 hT1).2.2 (by simp [hvr])
                  rw [hVal X r v T1 T2 hv, hVal X r v T1 T2' hv]; linarith
            clear hCBD hBS hS hCandI
            intro hk hkn T hT A hA1 hA2 hA3
            classical
            -- the size schedule
            obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℕ, φ = fun j => if j % 2 = 0 then 2 ^ (j / 2) else 3 * 2 ^ (j / 2) / 2 :=
              ⟨_, rfl⟩
            have hφ1 : φ 1 = 1 := by rw [hφ]; rfl
            have hφeo : ∀ i, φ (2 * i) = 2 ^ i ∧ φ (2 * i + 1) = 3 * 2 ^ i / 2 := by
              intro i
              rw [hφ]
              refine ⟨?_, ?_⟩
              · simp only [Nat.mul_mod_right, if_true, Nat.mul_div_cancel_left i (by norm_num : 0 < 2)]
              · have h1 : (2 * i + 1) % 2 = 1 := by omega
                have h2 : (2 * i + 1) / 2 = i := by omega
                simp only [h1, h2, one_ne_zero, if_false]
            have hφstep : ∀ j, 2 * φ (j + 1) ≤ 3 * φ j + 1 := by
              intro j
              obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
              · rw [(hφeo i).2, (hφeo i).1]; omega
              · rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, (hφeo (i + 1)).1, (hφeo i).2, pow_succ]
                have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
                omega
            have hφcap : ∀ j, (φ j : ℝ) ≤ capImp 1 j := by
              intro j
              unfold capImp
              rw [one_mul]
              obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
              · rw [(hφeo i).1, pow_mul]
                push_cast
                exact pow_le_pow_left₀ (by norm_num) (by norm_num) i
              · rw [(hφeo i).2, pow_succ, pow_mul]
                have h1 : ((3 * 2 ^ i / 2 : ℕ) : ℝ) ≤ (3 * 2 ^ i : ℕ) / 2 := Nat.cast_div_le
                have h2 : (2 : ℝ) ^ i ≤ ((3 / 2 : ℝ) ^ 2) ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
                push_cast at h1
                linarith only [h1, h2]
            clear hφ
            -- basic facts about f
            have hfX0 : ∀ X r T, 0 ≤ fX I.f X r T := by
              intro X r T
              unfold fX
              have := hmono X (verts r T ∪ X) Finset.subset_union_right
              have : (I.f X : ℝ) ≤ I.f (verts r T ∪ X) := by exact_mod_cast this
              linarith only [this]
            -- arborescence: required vertices are bounded by the edge count
            have hYcard : ∀ (r : Fin n) (A : Edges n) (Y : Finset (Fin n)), IsArbo r A → Y.erase r ⊆ verts r A →
                (Y.erase r).card ≤ A.card := by
              intro r A Y hA hY
              have hs : Y.erase r ⊆ A.image Prod.snd := by
                intro x hx
                have hxr := Finset.ne_of_mem_erase hx
                have hR := hA.2.2 x (hY hx)
                rcases Relation.ReflTransGen.cases_tail hR with h | ⟨c, _, hc⟩
                · exact absurd h hxr
                · exact Finset.mem_image.2 ⟨(c, x), hc, rfl⟩
              exact (Finset.card_le_card hs).trans Finset.card_image_le
            -- the guarantee
            have hG : ∀ i, ∀ (r : Fin n) (Y₀ X : Finset (Fin n)) (B : ℕ) (A : Edges n), IsArbo r A →
                Y₀.erase r ⊆ verts r A → A.card ≤ φ (i + 1) → cost I.c A ≤ B →
                ∃ T, (rg I 1 (.bsearch (n ^ a)) (i + 1) r Y₀ B X).1 = some T ∧
                  fX I.f X r A ≤ ((i + 1 : ℕ) : ℝ) * fX I.f X r T := by
              intro i
              induction i with
              | zero =>
                intro r Y₀ X B A hA hY hc hB
                obtain ⟨T, hT, hle⟩ := hBaseG r Y₀ X B A hA hY (by rw [hφ1] at hc; exact hc) hB
                exact ⟨T, hT, by rw [zero_add, Nat.cast_one, one_mul]; exact hle⟩
              | succ i ih =>
                intro r Y₀ X B A hA hY hc hB
                -- split A
                obtain ⟨v, A1, A2, hdis, hun, hA1, hA2, hvA1, hc1, hc2⟩ :
                    ∃ (v : Fin n) (A1 A2 : Edges n), Disjoint A1 A2 ∧ A1 ∪ A2 = A ∧ IsArbo r A1 ∧ IsArbo v A2 ∧
                      v ∈ verts r A1 ∧ A1.card ≤ φ (i + 1) ∧ A2.card ≤ φ (i + 1) := by
                  by_cases hsmall : A.card ≤ φ (i + 1)
                  · refine ⟨r, A, ∅, Finset.disjoint_empty_right _, Finset.union_empty _, hA, ?_, ?_, hsmall, ?_⟩
                    · refine ⟨fun e he => absurd he (Finset.notMem_empty _),
                        fun e he => absurd he (Finset.notMem_empty _), ?_⟩
                      intro w hw
                      simp only [verts, Finset.image_empty, Finset.union_empty, Finset.mem_singleton,
                        Finset.insert_empty] at hw
                      rw [hw]; exact Relation.ReflTransGen.refl
                    · exact Finset.mem_insert_self _ _
                    · rw [Finset.card_empty]; exact Nat.zero_le _
                  · obtain ⟨v, A1, A2, hdis, hun, hA1, hA2, hvA1, hc1, hc2⟩ :=
                      hSep r A hA (A.card - φ (i + 1)) (by omega) (by omega)
                    have hcard : A1.card + A2.card = A.card := by
                      rw [← hun, Finset.card_union_of_disjoint hdis]
                    have := hφstep (i + 1)
                    exact ⟨v, A1, A2, hdis, hun, hA1, hA2, hvA1, by omega, by omega⟩
                have hcost : cost I.c A1 + cost I.c A2 = cost I.c A := by
                  unfold cost; rw [← hun, Finset.sum_union hdis]
                have hvertsA : verts r A ⊆ verts r A1 ∪ verts v A2 := by
                  rw [← hun]
                  intro x hx
                  simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx ⊢
                  rcases hx with h | ⟨e, he | he, h⟩ | ⟨e, he | he, h⟩
                  · exact Or.inl (Or.inl h)
                  · exact Or.inl (Or.inr (Or.inl ⟨e, he, h⟩))
                  · exact Or.inr (Or.inr (Or.inl ⟨e, he, h⟩))
                  · exact Or.inl (Or.inr (Or.inr ⟨e, he, h⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨e, he, h⟩))
                obtain ⟨Y, hYdef⟩ : ∃ Y, Y = Y₀.erase r := ⟨_, rfl⟩
                rw [← hYdef] at hY
                obtain ⟨S, hS⟩ : ∃ S, S = Y ∩ verts r A1 := ⟨_, rfl⟩
                obtain ⟨Y1, hY1⟩ : ∃ Y1, Y1 = (S ∪ {v}) \ {r} := ⟨_, rfl⟩
                obtain ⟨Y2, hY2⟩ : ∃ Y2, Y2 = Y \ (S ∪ {v}) := ⟨_, rfl⟩
                have hY1s : Y1.erase r ⊆ verts r A1 := by
                  intro x hx
                  have hx' := Finset.mem_of_mem_erase hx
                  rw [hY1, Finset.mem_sdiff, Finset.mem_union] at hx'
                  rcases hx'.1 with h | h
                  · rw [hS] at h; exact (Finset.mem_inter.1 h).2
                  · rw [Finset.mem_singleton.1 h]; exact hvA1
                have hY2s : Y2.erase v ⊆ verts v A2 := by
                  intro x hx
                  have hxv := Finset.ne_of_mem_erase hx
                  have hx' := Finset.mem_of_mem_erase hx
                  rw [hY2, Finset.mem_sdiff, Finset.mem_union] at hx'
                  obtain ⟨hxY, hxS⟩ := hx'
                  rcases Finset.mem_union.1 (hvertsA (hY hxY)) with h | h
                  · exact absurd (Or.inl (hS ▸ Finset.mem_inter.2 ⟨hxY, h⟩)) hxS
                  · exact h
                have hp : [(r, Y1), (v, Y2)] ∈ leafPlans 1 r Y := by
                  simp only [leafPlans, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
                            List.append_nil, List.mem_flatMap, List.mem_finRange, Finset.mem_toList,
                            Finset.mem_powerset, true_and, List.mem_cons, List.not_mem_nil, or_false]
                  exact ⟨v, S, hS ▸ Finset.inter_subset_left, by rw [hY1, hY2]; rfl⟩
                -- first leaf with the budget of A1
                obtain ⟨T1o, hT1o, hle1⟩ := ih r Y1 X (cost I.c A1) A1 hA1 hY1s hc1 le_rfl
                have hu : ∃ u : ℕ, (u : ℝ) = fX I.f X r T1o ∧ u ≤ n ^ a := by
                  refine ⟨I.f (verts r T1o ∪ X) - I.f X, ?_, ?_⟩
                  · unfold fX
                    rw [Nat.cast_sub (hmono _ _ Finset.subset_union_right)]
                  · exact (Nat.sub_le _ _).trans (hbd _)
                obtain ⟨u, hu1, hu2⟩ := hu
                obtain ⟨b', T1, hb', hT1, huT1, -, hcand⟩ :=
                  hCandF (rg I 1 (.bsearch (n ^ a)) (i + 1)) r v Y1 Y2 X B
                    (fun b b' T hbb hT => hMono (i + 1) r Y1 X b b' T hbb hT) u hu2 (cost I.c A1) T1o
                    (by omega) hT1o (le_of_eq hu1)
                -- second leaf
                obtain ⟨T2, hT2, hle2⟩ := ih v Y2 (X ∪ verts r T1) (B - b') A2 hA2 hY2s hc2 (by omega)
                have hmem := hcand T2 hT2
                have hv1 : v ∈ verts r T1 := by
                  by_cases hvr : v = r
                  · rw [hvr]; exact Finset.mem_insert_self _ _
                  · refine (hFeasG (i + 1) r Y1 b' X T1 hT1).2.2 (Finset.mem_erase.2 ⟨hvr, ?_⟩)
                    rw [hY1, Finset.mem_sdiff, Finset.mem_union]
                    exact ⟨Or.inr (Finset.mem_singleton_self v), fun h => hvr (Finset.mem_singleton.1 h)⟩
                have hval := hVal X r v T1 T2 hv1
                -- value inequalities
                have hsubadd : fX I.f X r A ≤ fX I.f X r A1 + fX I.f X v A2 := by
                  unfold fX
                  have h1 := hsub (verts r A1 ∪ X) (verts v A2 ∪ X)
                  have h2 : (I.f X : ℝ) ≤ I.f ((verts r A1 ∪ X) ∩ (verts v A2 ∪ X)) := by
                    exact_mod_cast hmono _ _ (Finset.subset_inter Finset.subset_union_right Finset.subset_union_right)
                  have h3 : (I.f (verts r A ∪ X) : ℝ) ≤ I.f (verts r A1 ∪ X ∪ (verts v A2 ∪ X)) := by
                    refine Nat.cast_le.2 (hmono _ _ ?_)
                    intro x hx
                    rcases Finset.mem_union.1 hx with h | h
                    · rcases Finset.mem_union.1 (hvertsA h) with h' | h'
                      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h')
                      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h')
                    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
                  simp only at h1
                  linarith only [h1, h2, h3]
                have hshift : fX I.f X v A2 - fX I.f X r T1 ≤ fX I.f (X ∪ verts r T1) v A2 := by
                  unfold fX
                  have h1 : (I.f (verts v A2 ∪ X) : ℝ) ≤ I.f (verts v A2 ∪ (X ∪ verts r T1)) := by
                    refine Nat.cast_le.2 (hmono _ _ ?_)
                    exact Finset.union_subset_union le_rfl Finset.subset_union_left
                  rw [Finset.union_comm X (verts r T1)] at h1 ⊢
                  linarith only [h1]
                obtain ⟨Tf, hTf, hleTf⟩ :=
                  (hPFD X r (leafPlans 1 r Y)
                    (fun plan => runPlan I (.bsearch (n ^ a)) (rg I 1 (.bsearch (n ^ a)) (i + 1)) plan X B ∅)
                    (if Y = ∅ then some ∅ else none) 1).2 _ hp _ hmem
                have hcapY : ¬ capImp 1 (i + 1 + 1) < ((Y₀.erase r).card : ℝ) := by
                  push Not
                  have h1 : ((Y₀.erase r).card : ℝ) ≤ A.card := by exact_mod_cast hYcard r A Y₀ hA (hYdef ▸ hY)
                  have h2 : (A.card : ℝ) ≤ φ (i + 1 + 1) := by exact_mod_cast hc
                  exact h1.trans (h2.trans (hφcap (i + 1 + 1)))
                refine ⟨Tf, ?_, ?_⟩
                · rw [rg, if_neg hcapY, if_neg (Nat.succ_ne_zero i), ← hYdef]
                  exact hTf
                · have e1 := hfX0 (X ∪ verts r T1) v T2
                  have e2 : fX I.f X r A1 ≤ ((i + 1 : ℕ) : ℝ) * fX I.f X r T1 := by
                    refine hle1.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
                    rw [← hu1]; exact huT1
                  rw [hval] at hleTf
                  push_cast at e2 hle2 ⊢
                  have e3 : ((i : ℝ) + 1) * fX I.f (X ∪ verts r T1) v T2 ≤ ((i : ℝ) + 1 + 1) * fX I.f (X ∪ verts r T1) v T2 := by
                    linarith only [e1]
                  have e4 : ((i : ℝ) + 1 + 1) * (fX I.f X r T1 + fX I.f (X ∪ verts r T1) v T2) ≤
                      ((i : ℝ) + 1 + 1) * fX I.f X r Tf :=
                    mul_le_mul_of_nonneg_left hleTf (by positivity)
                  linarith only [hsubadd, e2, hshift, hle2, e3, e4]
            -- top level
            have hc1 : 1 ≤ Nat.clog 2 k := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) (by omega))
            obtain ⟨T', hT', hle⟩ := hG (dOf k - 1) I.root ∅ ∅ I.B A hA1 (by intro x hx; simp at hx)
              (by
                have h1 := (hφeo (Nat.clog 2 k)).1
                have h2 : k ≤ 2 ^ Nat.clog 2 k := Nat.le_pow_clog (by norm_num) k
                have h3 : dOf k - 1 + 1 = 2 * Nat.clog 2 k := by unfold dOf; omega
                rw [h3, h1]; omega) hA2
            have h3 : dOf k - 1 + 1 = dOf k := by unfold dOf; omega
            rw [h3] at hT' hle
            unfold alg29 at hT
            rw [hT] at hT'
            cases hT'
            unfold fX at hle
            rw [Finset.union_empty, Finset.union_empty] at hle
            obtain ⟨c, hc⟩ : ∃ c, c = Nat.clog 2 k := ⟨_, rfl⟩
            rw [← hc] at hc1
            have hpc : 2 ^ (c - 1) < k := by
              have := Nat.pow_pred_clog_lt_self (b := 2) (x := k) (by norm_num) (by omega)
              rwa [Nat.pred_eq_sub_one, ← hc] at this
            have hck : 2 ^ c ≤ k ^ 2 := by
              calc 2 ^ c = 2 * 2 ^ (c - 1) := by rw [← pow_succ']; congr 1; omega
                _ ≤ 2 * k := by omega
                _ ≤ k * k := Nat.mul_le_mul_right k hk
                _ = k ^ 2 := (sq k).symm
            have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have hlog : (c : ℝ) * Real.log 2 ≤ 2 * Real.log k := by
              have h := Real.log_le_log (pow_pos (by norm_num) c) (show ((2 : ℝ) ^ c) ≤ (k : ℝ) ^ 2 by exact_mod_cast hck)
              rwa [Real.log_pow, Real.log_pow, Nat.cast_ofNat] at h
            have hd : ((dOf k : ℕ) : ℝ) = 2 * (c : ℝ) := by rw [dOf, Nat.cast_mul, Nat.cast_ofNat, hc]
            have hdk : ((dOf k : ℕ) : ℝ) ≤ 4 / Real.log 2 * Real.log k := by
              rw [hd, div_mul_eq_mul_div, le_div_iff₀ hlog2]; linarith only [hlog]
            have hd1 : (1 : ℝ) ≤ ((dOf k : ℕ) : ℝ) := by rw [hd]; linarith [(by exact_mod_cast hc1 : (1:ℝ) ≤ c)]
            have hf0 : (0 : ℝ) ≤ I.f ∅ := Nat.cast_nonneg _
            have hfT : (0 : ℝ) ≤ I.f (verts I.root T) := Nat.cast_nonneg _
            have h0 : 0 ≤ (((dOf k : ℕ) : ℝ) - 1) * I.f ∅ := mul_nonneg (by linarith only [hd1]) hf0
            have h5 : ((dOf k : ℕ) : ℝ) * I.f (verts I.root T) ≤ 4 / Real.log 2 * Real.log k * I.f (verts I.root T) :=
              mul_le_mul_of_nonneg_right hdk hfT
            linarith only [hle, h0, h5]
          -- (5) the quasi-polynomial step bound
          obtain ⟨C1, hC1, hA⟩ := hApprox
          obtain ⟨C2, hC2, hT⟩ := hTime
          refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
          intro n I k hmono hsub hbd hk hkn
          obtain ⟨T, hTeq⟩ := hSome I k hk
          have hF := hFeas I k hk T hTeq
          refine ⟨⟨T, hTeq, hF, hArbo I.root T hF.1, ?_⟩, ?_⟩
          · intro A hA1 hA2 hA3
            refine le_trans (hA n I k hmono hsub hbd hk hkn T hTeq A hA1 hA2 hA3) ?_
            have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
            have hf : (0 : ℝ) ≤ (I.f (verts I.root T) : ℝ) := Nat.cast_nonneg _
            apply mul_le_mul_of_nonneg_right _ hf
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlog
          · refine le_trans (hT n I k hk hkn) ?_
            have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
            have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
            have hb : (1 : ℝ) ≤ Real.logb 2 ((I.B : ℝ) + 2) := by
              rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
              have : (0:ℝ) ≤ I.B := Nat.cast_nonneg _
              norm_num
            apply Real.rpow_le_rpow_of_exponent_le (by nlinarith)
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) hlog
