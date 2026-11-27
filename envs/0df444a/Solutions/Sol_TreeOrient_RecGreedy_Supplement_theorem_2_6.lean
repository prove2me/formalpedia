-- Prove2me | solution 1 for TreeOrient.RecGreedy.Supplement.theorem_2_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:08.678985+00:00
-- url     : https://prove2.me/submissions/aa836b9e-acbb-4c28-811f-fd789a53c739

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Supplement_TopLevel

open TreeOrient
open TreeOrient.RecGreedy
open TreeOrient.RecGreedy.Supplement

/-- Theorem 2.6, p. 7 (PDF 8): Algorithm 1 at Remark 2.1's depth is a
`⌈log_{3/2} k⌉`-approximation running in `(n(B + 2))^{O(log k)}` steps. -/
theorem solution : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (I : Inst n) (k : ℕ),
      IsMonotone I.f →
      NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)) →
      2 ≤ k → k ≤ n →
      (∃ T, (alg26 I k).1 = some T ∧ Feasible I.c I.root ∅ I.B T ∧
        (∃ A' : Edges n, A' ⊆ T ∧ IsArbo I.root A' ∧ verts I.root A' = verts I.root T) ∧
        ∀ A : Edges n, IsArbo I.root A → cost I.c A ≤ I.B → A.card + 1 ≤ k →
          (I.f (verts I.root A) : ℝ) ≤ (d26 k : ℝ) * (I.f (verts I.root T) : ℝ)) ∧
      ((alg26 I k).2 : ℝ) ≤ ((n : ℝ) * ((I.B : ℝ) + 2)) ^ (C * Real.log k) := by
        have hd2 : ∀ k : ℕ, 2 ≤ k → 2 ≤ d26 k := by
          intro k hk
          have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
          have h1 : (1 : ℝ) < Real.logb (3/2) k := by
            rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by linarith), Real.rpow_one]; linarith
          have := Nat.lt_ceil.2 (show ((1 : ℕ) : ℝ) < Real.logb (3/2) k by exact_mod_cast h1)
          unfold d26; omega
        have hdk : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ (3/2 : ℝ) ^ (d26 k) := by
          intro k hk
          have hk' : (0 : ℝ) < k := by exact_mod_cast hk
          have h := Nat.le_ceil (Real.logb (3/2) (k : ℝ))
          rw [Real.logb_le_iff_le_rpow (by norm_num) hk', Real.rpow_natCast] at h
          exact h
        have hRPE : ∀ {n : ℕ} (I : Inst n) (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
            (r v : Fin n) (Y1 Y2 X : Finset (Fin n)) (B : ℕ) (c : Edges n),
            c ∈ (runPlan I .enum sub [(r, Y1), (v, Y2)] X B ∅).1 ↔
              ∃ b T1 T2, b ≤ B ∧ (sub r Y1 b X).1 = some T1 ∧
                (sub v Y2 (B - b) (X ∪ verts r T1)).1 = some T2 ∧ c = T1 ∪ T2 := by
          intro n I sub r v Y1 Y2 X B c
          have hfold : ∀ (l : List ℕ) (e : ℕ → List (Edges n))
              (g : List (Edges n) × ℕ → ℕ → List (Edges n) × ℕ), (∀ x u, (g x u).1 = x.1 ++ e u) →
              ∀ init, (l.foldl g init).1 = init.1 ++ l.flatMap e := by
            intro l e g hg
            induction l with
            | nil => intro init; simp only [List.foldl_nil, List.flatMap_nil, List.append_nil]
            | cons u l ih =>
              intro init
              rw [List.foldl_cons, ih, hg, List.flatMap_cons, List.append_assoc]
          simp only [runPlan]
          rw [hfold (List.range (B + 1)) (fun b => match (sub r Y1 b X).1 with
              | none => []
              | some T => List.map (fun T_1 => ∅ ∪ T ∪ T_1) (sub v Y2 (B - b) (X ∪ verts r T)).1.toList)]
          · rw [List.nil_append, List.mem_flatMap]
            constructor
            · rintro ⟨b, hb, hc⟩
              rcases h1 : (sub r Y1 b X).1 with _ | T1
              · rw [h1] at hc; nomatch hc
              · rw [h1] at hc
                dsimp only at hc
                rcases h2 : (sub v Y2 (B - b) (X ∪ verts r T1)).1 with _ | T2
                · rw [h2] at hc; nomatch hc
                · rw [h2, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton,
                    Finset.empty_union] at hc
                  exact ⟨b, T1, T2, Nat.lt_succ_iff.1 (List.mem_range.1 hb), h1, h2, hc⟩
            · rintro ⟨b, T1, T2, hb, h1, h2, rfl⟩
              refine ⟨b, List.mem_range.2 (Nat.lt_succ_of_le hb), ?_⟩
              simp only [h1, h2, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton,
                Finset.empty_union]
          · intro x u
            split <;> rename_i h <;> simp only [h, List.append_nil]
        have hTime : ∃ C2 : ℝ, 0 < C2 ∧ ∀ (n : ℕ) (I : Inst n) (k : ℕ), 2 ≤ k → k ≤ n →
            ((alg26 I k).2 : ℝ) ≤ ((n : ℝ) * ((I.B : ℝ) + 2)) ^ (C2 * Real.log k) := by
            have hl15 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
            refine ⟨8 / Real.log (3 / 2), div_pos (by norm_num) hl15, ?_⟩
            intro n I k hk hkn
            have hn : 1 ≤ n := by omega
            have hflT : ∀ (l : List ℕ) (g : (List (Edges n) × ℕ) → ℕ → List (Edges n) × ℕ) (D Bm : ℕ),
                (∀ b ∈ l, b ≤ Bm) →
                (∀ x u, u ≤ Bm → (g x u).2 ≤ x.2 + D ∧ (g x u).1.length ≤ x.1.length + 1) → ∀ init : List (Edges n) × ℕ,
                (l.foldl g init).2 ≤ init.2 + l.length * D ∧ (l.foldl g init).1.length ≤ init.1.length + l.length := by
              intro l g D Bm hl hg
              induction l with
              | nil => intro init; simp
              | cons u l ih =>
                intro init
                simp only [List.foldl_cons, List.length_cons]
                obtain ⟨h1, h2⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)) (g init u)
                obtain ⟨h3, h4⟩ := hg init u (hl u List.mem_cons_self)
                constructor
                · rw [Nat.add_mul, Nat.one_mul]; omega
                · omega
            have hRPT : ∀ (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
                (r v : Fin n) (Y1 Y2 X : Finset (Fin n)) (B F : ℕ),
                (∀ b ≤ B, ∀ X', (sub r Y1 b X').2 ≤ F) → (∀ b ≤ B, ∀ X', (sub v Y2 b X').2 ≤ F) →
                (runPlan I .enum sub [(r, Y1), (v, Y2)] X B ∅).2 ≤ (B + 1) * (2 * F) ∧
                (runPlan I .enum sub [(r, Y1), (v, Y2)] X B ∅).1.length ≤ B + 1 := by
              intro sub r v Y1 Y2 X B F h1 h2
              rw [runPlan]
              · simp only [runPlan]
                have hr : ∀ b ∈ List.range (B + 1), b ≤ B := fun b hb => by rw [List.mem_range] at hb; omega
                refine ⟨le_trans (hflT _ _ (2 * F) B hr ?_ _).1 ?_, le_trans (hflT _ _ (2 * F) B hr ?_ _).2 ?_⟩
                rotate_left
                · rw [List.length_range]; exact le_of_eq (Nat.zero_add _)
                rotate_left
                · rw [List.length_range]; exact le_of_eq (Nat.zero_add _)
                all_goals
                  intro x u hu
                  have ha := h1 u hu X
                  split
                  · dsimp only; constructor <;> omega
                  · rename_i T _
                    dsimp only
                    have hb := h2 (B - u) (by omega) (X ∪ verts r T)
                    rw [List.length_append, List.length_map]
                    have hlen : (sub v Y2 (B - u) (X ∪ verts r T)).1.toList.length ≤ 1 := by
                      rcases (sub v Y2 (B - u) (X ∪ verts r T)).1 with _ | _ <;> simp
                    constructor <;> omega
              · simp
            have hMain : ∀ i m (r : Fin n) (Y₀ : Finset (Fin n)) (B' : ℕ) (X : Finset (Fin n)), B' ≤ I.B → (Y₀.erase r).card ≤ m →
                (rg I 1 .enum i r Y₀ B' X).2 ≤ (4 * n * (I.B + 1) * 2 ^ (m + i)) ^ i := by
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
                  rw [Nat.add_mul, Nat.one_mul]
                  omega
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
                  (rgBasic I .enum 1 r Y B X).2 ≤ 1 + n := by
                intro r Y B X
                rw [rgBasic]
                split_ifs with h1 h2 h3 <;> first | exact absurd rfl h2 | exact Nat.le_add_right 1 n | exact le_refl _
              set W := 4 * n * (I.B + 1) with hW
              have hW1 : 1 ≤ W := Nat.mul_pos (Nat.mul_pos (by norm_num) hn) (Nat.succ_pos _)
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
                    rw [hW]; exact le_trans (by omega : n ≤ 4 * n) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
                  calc 1 + n ≤ W * 2 := by omega
                    _ ≤ W * 2 ^ (m + 1) := Nat.mul_le_mul_left _ h2p
                all_goals try exact absurd rfl h3
                all_goals
                  dsimp only
                  set F := (W * 2 ^ (m + 1 + i)) ^ i with hF
                  have hF1 : 1 ≤ F := Nat.one_le_pow _ _ (Nat.mul_pos hW1 (Nat.two_pow_pos _))
                  refine le_trans (hPFT X r _ _ ((B' + 1) * (2 * F) + (B' + 1)) ?_ _ _) ?_
                  · intro p hp
                    obtain ⟨v, S, hS, rfl⟩ := hLPm r _ p hp
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
                    obtain ⟨hR1, hR2⟩ := hRPT (rg I 1 .enum i) r v ((S ∪ {v}) \ {r}) (Y₀.erase r \ (S ∪ {v})) X B' F
                      (fun b hb X' => ih (m + 1) r _ b X' (by omega) hc1)
                      (fun b hb X' => ih (m + 1) v _ b X' (by omega) hc2)
                    omega
                  · rw [hLP]
                    have hYc : 2 ^ (Y₀.erase r).card ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hY
                    have hD : (B' + 1) * (2 * F) + (B' + 1) ≤ 3 * (I.B + 1) * F := by
                      have e1 : (B' + 1) * (2 * F) + (B' + 1) ≤ (B' + 1) * (3 * F) := by
                        rw [show (B' + 1) * (3 * F) = (B' + 1) * (2 * F) + (B' + 1) * F by ring]
                        have := Nat.mul_le_mul_left (B' + 1) hF1
                        omega
                      have e2 : (B' + 1) * (3 * F) ≤ (I.B + 1) * (3 * F) := Nat.mul_le_mul_right _ (by omega)
                      have e3 : (I.B + 1) * (3 * F) = 3 * (I.B + 1) * F := by ring
                      omega
                    have h2m' : 2 ^ (m + 1 + i) = 2 ^ (m + (i + 1)) := by rw [show m + 1 + i = m + (i + 1) by omega]
                    rw [h2m'] at hF
                    have hP : n * 2 ^ (Y₀.erase r).card * ((B' + 1) * (2 * F) + (B' + 1)) ≤
                        n * 2 ^ m * (3 * (I.B + 1) * F) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hYc) hD
                    have hm2 : 2 ^ m ≤ 2 ^ (m + (i + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
                    have hWF : W * 2 ^ (m + (i + 1)) * F = (W * 2 ^ (m + (i + 1))) ^ (i + 1) := by
                      rw [hF]; exact (pow_succ' _ _).symm
                    rw [← hWF]
                    have e1 : n * 2 ^ m * (3 * (I.B + 1) * F) * 4 = W * 2 ^ m * F * 3 := by clear * - hW; rw [hW]; ring
                    have e2 : W * 2 ^ m * F ≤ W * 2 ^ (m + (i + 1)) * F :=
                      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm2)
                    have e3 : 1 ≤ n * 2 ^ m * (3 * (I.B + 1) * F) := Nat.mul_pos (Nat.mul_pos hn (Nat.two_pow_pos _)) (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.succ_pos _)) hF1)
                    omega
            set d := d26 k with hd
            have hM : (alg26 I k).2 ≤ (4 * n * (I.B + 1) * 2 ^ (0 + d)) ^ d := by
              have := hMain d 0 I.root ∅ I.B ∅ le_rfl (by simp)
              exact this
            clear hMain hRPT hflT
            -- real part
            have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
            have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
            have hk0 : (0 : ℝ) < k := by linarith
            have hlb : 0 < Real.logb (3 / 2) k := Real.logb_pos (by norm_num) (by linarith)
            have hdd : d = ⌈Real.logb (3 / 2) (k : ℝ)⌉₊ := rfl
            have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by rw [hdd]; exact (Nat.ceil_pos.2 hlb).ne')
            have hdlt : ((d - 1 : ℕ) : ℝ) < Real.logb (3 / 2) k := by
              rw [hdd]; exact Nat.lt_ceil.1 (by rw [← hdd]; omega)
            have hdup : (d : ℝ) < Real.logb (3 / 2) k + 1 := by
              rw [hdd]; exact Nat.ceil_lt_add_one hlb.le
            have hpow : ((3 / 2 : ℝ)) ^ (d - 1) < k := by
              have := (Real.lt_logb_iff_rpow_lt (by norm_num) hk0).1 hdlt
              rwa [Real.rpow_natCast] at this
            have h2pow : (2 : ℝ) ^ d ≤ 2 * (n : ℝ) ^ 2 := by
              have e1 : (2 : ℝ) ^ d = 2 * 2 ^ (d - 1) := by
                rw [← pow_succ']; congr 1; omega
              have e2 : (2 : ℝ) ^ (d - 1) ≤ (((3 / 2 : ℝ)) ^ (d - 1)) ^ 2 := by
                rw [← pow_mul, mul_comm, pow_mul]
                exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
              have e3 : (((3 / 2 : ℝ)) ^ (d - 1)) ^ 2 ≤ (n : ℝ) ^ 2 :=
                pow_le_pow_left₀ (by positivity) (hpow.le.trans hkn') 2
              rw [e1]; linarith
            have hB0 : (0 : ℝ) ≤ I.B := Nat.cast_nonneg _
            have hN : (2 : ℝ) ≤ n := by linarith
            set x : ℝ := (n : ℝ) * ((I.B : ℝ) + 2) with hx
            have hx1 : (1 : ℝ) ≤ x := by
              rw [hx]; nlinarith
            have hX : ((4 * n * (I.B + 1) * 2 ^ (0 + d) : ℕ) : ℝ) ≤ x ^ 4 := by
              push_cast
              rw [zero_add]
              have hn0 : (0 : ℝ) ≤ n := by linarith
              have a1 : 4 * (n : ℝ) * ((I.B : ℝ) + 1) * 2 ^ d ≤ 4 * (n : ℝ) * ((I.B : ℝ) + 2) * (2 * (n : ℝ) ^ 2) :=
                mul_le_mul (by nlinarith) h2pow (by positivity) (by positivity)
              have a2 : (8 : ℝ) ≤ ((I.B : ℝ) + 2) ^ 3 := by
                have : (2 : ℝ) ^ 3 ≤ ((I.B : ℝ) + 2) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
                norm_num at this; linarith
              have a3 : 4 * (n : ℝ) * ((I.B : ℝ) + 2) * (2 * (n : ℝ) ^ 2) = 8 * (n : ℝ) ^ 3 * ((I.B : ℝ) + 2) := by ring
              have a4 : x ^ 4 = ((I.B : ℝ) + 2) ^ 3 * ((n : ℝ) * (n : ℝ) ^ 3 * ((I.B : ℝ) + 2)) := by rw [hx]; ring
              have a5 : 0 ≤ (n : ℝ) ^ 3 * ((I.B : ℝ) + 2) := by positivity
              have a6 : 8 * (n : ℝ) ^ 3 * ((I.B : ℝ) + 2) ≤ ((I.B : ℝ) + 2) ^ 3 * ((n : ℝ) * (n : ℝ) ^ 3 * ((I.B : ℝ) + 2)) := by
                have : (n : ℝ) ^ 3 * ((I.B : ℝ) + 2) ≤ (n : ℝ) * ((n : ℝ) ^ 3 * ((I.B : ℝ) + 2)) := by nlinarith
                nlinarith
              linarith
            have hstep : ((alg26 I k).2 : ℝ) ≤ (x ^ 4) ^ d := by
              have : ((alg26 I k).2 : ℝ) ≤ (((4 * n * (I.B + 1) * 2 ^ (0 + d) : ℕ) : ℝ)) ^ d := by
                exact_mod_cast hM
              exact this.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hX _)
            rw [← pow_mul, ← Real.rpow_natCast] at hstep
            refine hstep.trans (Real.rpow_le_rpow_of_exponent_le hx1 ?_)
            -- exponent: 4 d ≤ 8 / log(3/2) * log k
            have hlogk : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk2
            have hl32 : Real.log (3 / 2) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
            have hlb' : Real.logb (3 / 2) k = Real.log k / Real.log (3 / 2) := rfl
            have h1 : 1 ≤ Real.log k / Real.log (3 / 2) := by
              rw [le_div_iff₀ hl15]; linarith
            push_cast
            have : 8 / Real.log (3 / 2) * Real.log k = 8 * (Real.log k / Real.log (3 / 2)) := by ring
            rw [this]
            rw [hlb'] at hdup
            linarith
        -- (1) the top-level call always returns a tree
        have hSome : ∀ {n : ℕ} (I : Inst n) (k : ℕ), 2 ≤ k → ∃ T, (alg26 I k).1 = some T := by
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
          have hd : ∃ i, d26 k = i + 1 + 1 := ⟨d26 k - 2, by have := hd2 k hk; omega⟩
          obtain ⟨i, hi⟩ := hd
          unfold alg26
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
            (rg I 1 .enum i r Y₀ B X).1 = some T →
            ((∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧ Y₀.erase r ⊆ verts r T) := by
          intro n I
          classical
          have hRP : ∀ (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
          (r v : Fin n) (Y1 Y2 X : Finset (Fin n)) (B : ℕ) (Q : Edges n → Prop),
          (∀ b T1 T2 X', b ≤ B → (sub r Y1 b X).1 = some T1 → (sub v Y2 (B - b) X').1 = some T2 →
            Q (T1 ∪ T2)) →
          ∀ c ∈ (runPlan I .enum sub [(r, Y1), (v, Y2)] X B ∅).1, Q c := by
            intro sub r v Y1 Y2 X B Q hQ c hc
            obtain ⟨b, T1, T2, hb, h1, h2, rfl⟩ := (hRPE I sub r v Y1 Y2 X B c).1 hc
            exact hQ b T1 T2 _ hb h1 h2
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
          (rgBasic I .enum 1 r Y B X).1 = some T →
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
          (rg I 1 .enum i r Y₀ B X).1 = some T →
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
                have hplans : ∀ p ∈ leafPlans 1 r (Y₀.erase r), ∀ c ∈ (runPlan I .enum
                    (rg I 1 .enum i) p X B ∅).1,
                    (fun T => (∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧
                      (Y₀.erase r).erase r ⊆ verts r T) c := by
                  intro p hp c hc
                  simp only [leafPlans, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
                    List.append_nil, List.mem_flatMap, List.mem_finRange, Finset.mem_toList,
                    Finset.mem_powerset, true_and, List.mem_cons, List.not_mem_nil, or_false] at hp
                  obtain ⟨v, S, hS, rfl⟩ := hp
                  refine hRP _ r v _ _ X B (fun T => (∀ w ∈ verts r T, Reaches T r w) ∧ cost I.c T ≤ B ∧
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
        have hFeas : ∀ {n : ℕ} (I : Inst n) (k : ℕ), 2 ≤ k → ∀ T, (alg26 I k).1 = some T →
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
        -- (4) the approximation guarantee
        have hApprox : ∀ (n : ℕ) (I : Inst n) (k : ℕ),
            IsMonotone I.f →
            NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)) →
            2 ≤ k → k ≤ n → ∀ T, (alg26 I k).1 = some T →
              ∀ A : Edges n, IsArbo I.root A → cost I.c A ≤ I.B → A.card + 1 ≤ k →
                (I.f (verts I.root A) : ℝ) ≤ (d26 k : ℝ) * (I.f (verts I.root T) : ℝ) := by
          intro n I k hmono hsub
          have hFeasG := hFeasG I
          clear hTime hSome hFeas hArbo
          classical
          have hSep : ∀ (r : Fin n) (A : Edges n), IsArbo r A → ∀ t : ℕ, 1 ≤ t → t ≤ A.card →
                ∃ (v : Fin n) (A1 A2 : Edges n), Disjoint A1 A2 ∧ A1 ∪ A2 = A ∧ IsArbo r A1 ∧ IsArbo v A2 ∧
                  v ∈ verts r A1 ∧ t ≤ A2.card ∧ (A2.card = t ∨ A2.card + 2 ≤ 2 * t) := by
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
            obtain ⟨F, hFE, hF1, hF2⟩ : ∃ F ⊆ E, t ≤ ∑ f ∈ F, (Dn f.2).card ∧
                (∑ f ∈ F, (Dn f.2).card = t ∨ ∑ f ∈ F, (Dn f.2).card + 2 ≤ 2 * t) := by
              by_cases hbig : ∃ f ∈ E, t ≤ (Dn f.2).card
              · obtain ⟨f, hf, hft⟩ := hbig
                refine ⟨{f}, Finset.singleton_subset_iff.2 hf, ?_, Or.inl ?_⟩
                · rw [Finset.sum_singleton]; exact hft
                · rw [Finset.sum_singleton]; exact le_antisymm (hwt f hf) hft
              · push Not at hbig
                have hGR : ∀ (S : Edges n), (∀ f ∈ S, (Dn f.2).card + 1 ≤ t) → t ≤ ∑ f ∈ S, (Dn f.2).card →
                    ∃ F ⊆ S, t ≤ ∑ f ∈ F, (Dn f.2).card ∧ ∑ f ∈ F, (Dn f.2).card + 2 ≤ 2 * t := by
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
                obtain ⟨F, hF, h1, h2⟩ := hGR E (fun f hf => hbig f hf) hsumE
                exact ⟨F, hF, h1, Or.inr h2⟩
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
            clear hsub hmono
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
            clear hsub hmono
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
            clear hsub hmono
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
                ∃ T, (rg I 1 .enum 1 r Y₀ B X).1 = some T ∧ fX I.f X r A ≤ fX I.f X r T := by
            clear hFeasG hSep hPFD hVal
            intro r Y₀ X B A hA hY hc hB
            clear hsub hmono
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
          clear hCBD
          intro hk hkn T hT A hA1 hA2 hA3
          -- basic facts about f
          have hfX0 : ∀ X r T, 0 ≤ fX I.f X r T := by
            intro X r T
            unfold fX
            have := hmono X (verts r T ∪ X) Finset.subset_union_right
            have : (I.f X : ℝ) ≤ I.f (verts r T ∪ X) := by exact_mod_cast this
            linarith only [this]
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
          have hG : ∀ i, ∀ (r : Fin n) (Y₀ X : Finset (Fin n)) (B : ℕ) (A : Edges n), IsArbo r A →
              Y₀.erase r ⊆ verts r A → (A.card : ℝ) ≤ (3/2 : ℝ) ^ (i + 1) → cost I.c A ≤ B →
              ∃ T, (rg I 1 .enum (i + 1) r Y₀ B X).1 = some T ∧
                fX I.f X r A ≤ ((i + 1 : ℕ) : ℝ) * fX I.f X r T := by
            intro i
            induction i with
            | zero =>
              intro r Y₀ X B A hA hY hc hB
              have hc' : A.card ≤ 1 := by
                have h2 : (A.card : ℝ) < 2 := by norm_num at hc; linarith only [hc]
                have h3 : A.card < 2 := by exact_mod_cast h2
                omega
              obtain ⟨T, hT, hle⟩ := hBaseG r Y₀ X B A hA hY hc' hB
              exact ⟨T, hT, by rw [zero_add, Nat.cast_one, one_mul]; exact hle⟩
            | succ i ih =>
              intro r Y₀ X B A hA hY hc hB
              have hpow : (3/2 : ℝ) ^ (i + 1 + 1) = (3/2) * (3/2 : ℝ) ^ (i + 1) := pow_succ' _ _
              have hpos1 : (1 : ℝ) ≤ (3/2 : ℝ) ^ (i + 1) := one_le_pow₀ (by norm_num)
              -- split A
              obtain ⟨v, A1, A2, hdis, hun, hA1, hA2, hvA1, hc1, hc2⟩ :
                  ∃ (v : Fin n) (A1 A2 : Edges n), Disjoint A1 A2 ∧ A1 ∪ A2 = A ∧ IsArbo r A1 ∧ IsArbo v A2 ∧
                    v ∈ verts r A1 ∧ (A1.card : ℝ) ≤ (3/2 : ℝ) ^ (i + 1) ∧
                    (A2.card : ℝ) ≤ (3/2 : ℝ) ^ (i + 1) := by
                by_cases hsmall : A.card ≤ 1
                · refine ⟨r, A, ∅, Finset.disjoint_empty_right _, Finset.union_empty _, hA, ?_, ?_, ?_, ?_⟩
                  · refine ⟨fun e he => absurd he (Finset.notMem_empty _),
                      fun e he => absurd he (Finset.notMem_empty _), ?_⟩
                    intro w hw
                    simp only [verts, Finset.image_empty, Finset.union_empty, Finset.mem_singleton,
                      Finset.insert_empty] at hw
                    rw [hw]; exact Relation.ReflTransGen.refl
                  · exact Finset.mem_insert_self _ _
                  · have : (A.card : ℝ) ≤ 1 := by exact_mod_cast hsmall
                    linarith only [this, hpos1]
                  · rw [Finset.card_empty, Nat.cast_zero]; linarith only [hpos1]
                · obtain ⟨v, A1, A2, hdis, hun, hA1, hA2, hvA1, hc1, hc2⟩ :=
                    hSep r A hA ((A.card + 2) / 3) (by omega) (by omega)
                  have hcard : A1.card + A2.card = A.card := by
                    rw [← hun, Finset.card_union_of_disjoint hdis]
                  have h1 : 3 * A1.card ≤ 2 * A.card := by omega
                  have h2 : 3 * A2.card ≤ 2 * A.card := by omega
                  have h1' : (3 : ℝ) * A1.card ≤ 2 * A.card := by exact_mod_cast h1
                  have h2' : (3 : ℝ) * A2.card ≤ 2 * A.card := by exact_mod_cast h2
                  refine ⟨v, A1, A2, hdis, hun, hA1, hA2, hvA1, ?_, ?_⟩
                  · linarith only [h1', hc, hpow]
                  · linarith only [h2', hc, hpow]
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
              -- the two leaves
              obtain ⟨T1, hT1, hle1⟩ := ih r Y1 X (cost I.c A1) A1 hA1 hY1s hc1 le_rfl
              obtain ⟨T2, hT2, hle2⟩ := ih v Y2 (X ∪ verts r T1) (B - cost I.c A1) A2 hA2 hY2s hc2 (by omega)
              have hmem : T1 ∪ T2 ∈ (runPlan I .enum (rg I 1 .enum (i + 1)) [(r, Y1), (v, Y2)] X B ∅).1 :=
                (hRPE I _ r v Y1 Y2 X B _).2 ⟨cost I.c A1, T1, T2, by omega, hT1, hT2, rfl⟩
              have hv1 : v ∈ verts r T1 := by
                by_cases hvr : v = r
                · rw [hvr]; exact Finset.mem_insert_self _ _
                · refine (hFeasG (i + 1) r Y1 (cost I.c A1) X T1 hT1).2.2 (Finset.mem_erase.2 ⟨hvr, ?_⟩)
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
                  (fun plan => runPlan I .enum (rg I 1 .enum (i + 1)) plan X B ∅)
                  (if Y = ∅ then some ∅ else none) 1).2 _ hp _ hmem
              have hcapY : ¬ capImp 1 (i + 1 + 1) < ((Y₀.erase r).card : ℝ) := by
                rw [not_lt]
                have h1 : ((Y₀.erase r).card : ℝ) ≤ A.card := by exact_mod_cast hYcard r A Y₀ hA (hYdef ▸ hY)
                unfold capImp
                rw [one_mul]
                exact h1.trans hc
              refine ⟨Tf, ?_, ?_⟩
              · rw [rg, if_neg hcapY, if_neg (Nat.succ_ne_zero i), ← hYdef]
                exact hTf
              · have e1 := hfX0 (X ∪ verts r T1) v T2
                rw [hval] at hleTf
                push_cast at hle1 hle2 ⊢
                have e3 : ((i : ℝ) + 1) * fX I.f (X ∪ verts r T1) v T2 ≤ ((i : ℝ) + 1 + 1) * fX I.f (X ∪ verts r T1) v T2 := by
                  linarith only [e1]
                have e4 : ((i : ℝ) + 1 + 1) * (fX I.f X r T1 + fX I.f (X ∪ verts r T1) v T2) ≤
                    ((i : ℝ) + 1 + 1) * fX I.f X r Tf :=
                  mul_le_mul_of_nonneg_left hleTf (by positivity)
                have e5 : ((i : ℝ) + 1) * fX I.f X r T1 ≤ ((i : ℝ) + 1) * fX I.f X r T1 := le_rfl
                linarith only [hsubadd, hle1, hshift, hle2, e3, e4]
          -- top level
          have hd := hd2 k hk
          have h3 : d26 k - 1 + 1 = d26 k := by omega
          obtain ⟨T', hT', hle⟩ := hG (d26 k - 1) I.root ∅ ∅ I.B A hA1 (by intro x hx; simp at hx)
            (by
              rw [h3]
              have h4 := hdk k (by omega)
              have h5 : (A.card : ℝ) + 1 ≤ k := by exact_mod_cast hA3
              linarith only [h4, h5]) hA2
          rw [h3] at hT' hle
          unfold alg26 at hT
          rw [hT] at hT'
          cases hT'
          unfold fX at hle
          rw [Finset.union_empty, Finset.union_empty] at hle
          have hd1 : (1 : ℝ) ≤ ((d26 k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d26 k)
          have hf0 : (0 : ℝ) ≤ I.f ∅ := Nat.cast_nonneg _
          have h0 : 0 ≤ (((d26 k : ℕ) : ℝ) - 1) * I.f ∅ := mul_nonneg (by linarith only [hd1]) hf0
          linarith only [hle, h0]
        obtain ⟨C2, hC2, hTm⟩ := hTime
        refine ⟨C2, hC2, ?_⟩
        intro n I k hmono hsub hk hkn
        obtain ⟨T, hTeq⟩ := hSome I k hk
        have hF := hFeas I k hk T hTeq
        exact ⟨⟨T, hTeq, hF, hArbo I.root T hF.1, fun A hA1 hA2 hA3 =>
          hApprox n I k hmono hsub hk hkn T hTeq A hA1 hA2 hA3⟩, hTm n I k hk hkn⟩
