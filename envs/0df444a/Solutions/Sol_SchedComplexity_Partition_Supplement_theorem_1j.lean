-- Prove2me | solution 1 for SchedComplexity.Partition.Supplement.theorem_1j
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:38:59.521988+00:00
-- url     : https://prove2.me/submissions/172981d8-d081-45f0-913e-3c84a6fb652e

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

open SchedComplexity
open SchedComplexity.Partition
open SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem solution (M : MachineCount) (hM : M.Valid) (ell : ShopKind)
    (lam : Parameters) (hadm : Admissible lam .sumWT) :
    PolyReducible (language M ell lam .sumWC) (language M ell lam .sumWT) := by
      have partA1 : ∀ k : ℕ, BSym.sep ∉ (Nat.bits k).map (fun b => if b then BSym.one else BSym.zero) := by
        intro k h
        simp only [List.mem_map] at h
        obtain ⟨b, -, hb⟩ := h
        cases b <;> simp at hb

      have partA2 : ∀ (ds x : List BSym) (xs : List ℕ), BSym.sep ∉ ds → ds ++ BSym.sep :: x = encNats xs →
          ∃ k xs', xs = k :: xs' ∧ ds = (Nat.bits k).map (fun b => if b then BSym.one else BSym.zero) ∧ x = encNats xs' := by
        have partA1 := partA1
        intro ds x xs hds h
        cases xs with
        | nil => simp [encNats] at h
        | cons k xs' =>
          refine ⟨k, xs', rfl, ?_⟩
          have h2 : encNats (k :: xs') = (Nat.bits k).map (fun b => if b then BSym.one else BSym.zero) ++ BSym.sep :: encNats xs' := by
            simp [encNats, encNat]
          rw [h2] at h
          have aux : ∀ a b x y : List BSym, BSym.sep ∉ a → BSym.sep ∉ b → a ++ BSym.sep :: x = b ++ BSym.sep :: y → a = b ∧ x = y := by
            intro a
            induction a with
            | nil =>
              intro b x y _ hb h
              cases b with
              | nil => simpa using h
              | cons c b => simp at h; simp [← h.1] at hb
            | cons c a ih =>
              intro b x y ha hb h
              cases b with
              | nil => simp at h; simp [h.1] at ha
              | cons d b =>
                simp at h ha hb
                obtain ⟨h1, h2⟩ := ih b x y ha.2 hb.2 h.2
                exact ⟨by rw [h.1, h1], h2⟩
          exact aux _ _ _ _ hds (partA1 k) h

      have partA3 : ∀ (k k' : ℕ), (Nat.bits k).map (fun b => if b then BSym.one else BSym.zero) = (Nat.bits k').map (fun b => if b then BSym.one else BSym.zero) → k = k' := by
        intro k k' h
        have hinj : Function.Injective (fun b : Bool => if b then BSym.one else BSym.zero) := by
          intro a b; cases a <;> cases b <;> simp
        have h2 := List.map_injective_iff.2 hinj h
        have : ∀ k, (Nat.bits k).foldr (fun b a => b.toNat + 2 * a) 0 = k := by
          intro k
          induction k using Nat.binaryRec' with
          | zero => simp
          | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp only [List.foldr_cons, ih, Nat.bit_val]; omega
        rw [← this k, ← this k', h2]

      have partA4 : ∀ xs ys : List ℕ, encNats xs = encNats ys → xs = ys := by
        have partA1 := partA1
        have partA2 := partA2
        have partA3 := partA3
        intro xs
        induction xs with
        | nil =>
          intro ys h
          cases ys with
          | nil => rfl
          | cons k ys => simp [encNats, encNat] at h
        | cons k xs ih =>
          intro ys h
          have h2 : encNats (k :: xs) = (Nat.bits k).map (fun b => if b then BSym.one else BSym.zero) ++ BSym.sep :: encNats xs := by
            simp [encNats, encNat]
          rw [h2] at h
          obtain ⟨k', ys', rfl, h3, h4⟩ := partA2 _ _ _ (partA1 k) h
          rw [partA3 _ _ h3, ih _ h4]

      have partA5 : ∀ ds : List Bool, ds.getLast? ≠ some false → ∃ k, Nat.bits k = ds := by
        intro ds
        induction ds with
        | nil => intro _; exact ⟨0, by simp⟩
        | cons b ds ih =>
          intro h
          cases ds with
          | nil =>
            cases b
            · simp at h
            · exact ⟨1, by simp⟩
          | cons c ds =>
            obtain ⟨k, hk⟩ := ih (by simpa [List.getLast?_cons_cons] using h)
            refine ⟨Nat.bit b k, ?_⟩
            rw [Nat.bits_append_bit, hk]
            rintro rfl
            simp at hk

      have partA6 : ∀ k, (Nat.bits k).getLast? ≠ some false := by
        intro k
        induction k using Nat.binaryRec' with
        | zero => simp
        | bit b n hn ih =>
          rw [Nat.bits_append_bit _ _ hn]
          rw [List.getLast?_cons]
          cases h : (Nat.bits n).getLast? with
          | none =>
            have : Nat.bits n = [] := by simpa using h
            have h0 : n = 0 := by
              by_contra h0
              have := congrArg (fun l => l.foldr (fun b a => b.toNat + 2 * a) 0) this
              have h3 : ∀ k, (Nat.bits k).foldr (fun b a => b.toNat + 2 * a) 0 = k := by
                intro k
                induction k using Nat.binaryRec' with
                | zero => simp
                | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp only [List.foldr_cons, ih, Nat.bit_val]; omega
              simp [h3] at this
              exact h0 this
            simp [hn h0]
          | some c =>
            rw [h] at ih
            simpa using ih

      have partB1 : ∀ (act : Fin 6 → (BSym × Option Bool) → Option (Option BSym × Bool × Fin 6 × Bool)),
        ∃ (M : TM (BSym × Option Bool)) (VR : Bool → Option Bool → M.Q) (WL : Fin 6 → Option BSym → Bool → Bool → M.Q)
          (WR : Fin 6 → Bool → M.Q) (POP : Fin 6 → M.Q) (BAD FIN : M.Q),
          M.q₀ = VR true none ∧
          (∀ f st, VR f st ≠ M.qaccept ∧ VR f st ≠ M.qreject) ∧
          (∀ a b c d, WL a b c d ≠ M.qaccept ∧ WL a b c d ≠ M.qreject) ∧
          (∀ a b, WR a b ≠ M.qaccept ∧ WR a b ≠ M.qreject) ∧
          (∀ a, POP a ≠ M.qaccept ∧ POP a ≠ M.qreject) ∧
          (BAD ≠ M.qaccept ∧ BAD ≠ M.qreject) ∧
          (FIN ≠ M.qaccept ∧ FIN ≠ M.qreject) ∧
          (∀ f st s c, M.δ (VR f st) (some (s, c)) = if s = BSym.minus ∨ (s = BSym.sep ∧ st = some false) then (BAD, some (s, none), Move.right)
             else (VR (f && decide (s ≠ BSym.sep)) (if s = BSym.sep then none else some (decide (s = BSym.one))),
                some (s, if f then some (decide (s = BSym.one)) else none), Move.right)) ∧
          (∀ f st, M.δ (VR f st) none = if st = none ∧ f = false then (POP 0, none, Move.left) else (M.qaccept, none, Move.right)) ∧
          (∀ g, M.δ BAD (some g) = (BAD, some g, Move.right)) ∧
          (M.δ BAD none = (M.qaccept, none, Move.right)) ∧
          (∀ g, M.δ FIN (some g) = (FIN, some g, Move.left)) ∧
          (M.δ FIN none = (M.qaccept, none, Move.right)) ∧
          (∀ a b c d g, M.δ (WL a b c d) (some g) = (WL a b c d, some g, Move.left)) ∧
          (∀ a b d, M.δ (WL a b true d) none = (WL a b false d, b.map (fun s => (s, none)), Move.left)) ∧
          (∀ a b d, M.δ (WL a b false d) none = (WR a d, b.map (fun s => (s, none)), Move.right)) ∧
          (∀ a p s, M.δ (WR a p) (some (s, none)) = (WR a p, some (s, none), Move.right)) ∧
          (∀ a p s c, M.δ (WR a p) (some (s, some c)) = (WR a (p && !c), some (s, some (xor c p)), Move.right)) ∧
          (∀ a p, M.δ (WR a p) none = (POP (if p then 4 else a), none, Move.left)) ∧
          (∀ s, M.δ (POP 5) (some (s, none)) = (FIN, some (s, none), Move.left)) ∧
          (∀ a g t e b p, act a g = some (t, e, b, p) → ¬ (a = 5 ∧ g.2 = none) → M.δ (POP a) (some g) = (WL b t e p, none, Move.left)) ∧
          (∀ a g, act a g = none → ¬ (a = 5 ∧ g.2 = none) → M.δ (POP a) (some g) = (M.qaccept, none, Move.right)) := by
        clear * -
        intro act
        let Q := (Bool × Option Bool) ⊕ (Fin 6 × Option BSym × Bool × Bool) ⊕ (Fin 6 × Bool) ⊕ Fin 6 ⊕ Fin 4
        let VR : Bool → Option Bool → Q := fun f st => Sum.inl (f, st)
        let WL : Fin 6 → Option BSym → Bool → Bool → Q := fun a b c d => Sum.inr (Sum.inl (a, b, c, d))
        let WR : Fin 6 → Bool → Q := fun a b => Sum.inr (Sum.inr (Sum.inl (a, b)))
        let POP : Fin 6 → Q := fun a => Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))
        let BAD : Q := Sum.inr (Sum.inr (Sum.inr (Sum.inr 0)))
        let FIN : Q := Sum.inr (Sum.inr (Sum.inr (Sum.inr 1)))
        let ACC : Q := Sum.inr (Sum.inr (Sum.inr (Sum.inr 2)))
        let REJ : Q := Sum.inr (Sum.inr (Sum.inr (Sum.inr 3)))
        let δ : Q → Option (BSym × Option Bool) → Q × Option (BSym × Option Bool) × Move := fun q h =>
          match q with
          | Sum.inl (f, st) =>
            match h with
            | some (s, c) => if s = BSym.minus ∨ (s = BSym.sep ∧ st = some false) then (BAD, some (s, none), Move.right)
               else (VR (f && decide (s ≠ BSym.sep)) (if s = BSym.sep then none else some (decide (s = BSym.one))),
                some (s, if f then some (decide (s = BSym.one)) else none), Move.right)
            | none => if st = none ∧ f = false then (POP 0, none, Move.left) else (ACC, none, Move.right)
          | Sum.inr (Sum.inl (a, b, c, d)) =>
            match h with
            | some g => (WL a b c d, some g, Move.left)
            | none => if c then (WL a b false d, b.map (fun s => (s, none)), Move.left) else (WR a d, b.map (fun s => (s, none)), Move.right)
          | Sum.inr (Sum.inr (Sum.inl (a, p))) =>
            match h with
            | some (s, none) => (WR a p, some (s, none), Move.right)
            | some (s, some c) => (WR a (p && !c), some (s, some (xor c p)), Move.right)
            | none => (POP (if p then 4 else a), none, Move.left)
          | Sum.inr (Sum.inr (Sum.inr (Sum.inl a))) =>
            match h with
            | some g => if a = 5 ∧ g.2 = none then (FIN, some g, Move.left) else
                match act a g with
                | some (t, e, b, p) => (WL b t e p, none, Move.left)
                | none => (ACC, none, Move.right)
            | none => (ACC, none, Move.right)
          | Sum.inr (Sum.inr (Sum.inr (Sum.inr a))) =>
            match h with
            | some g => if a = 0 then (BAD, some g, Move.right) else (FIN, some g, Move.left)
            | none => (ACC, none, Move.right)
        let M : TM (BSym × Option Bool) := { Q := Q, finQ := (inferInstance : Fintype ((Bool × Option Bool) ⊕ (Fin 6 × Option BSym × Bool × Bool) ⊕ (Fin 6 × Bool) ⊕ Fin 6 ⊕ Fin 4)), decQ := Classical.decEq _, q₀ := VR true none, qaccept := ACC, qreject := REJ, accept_ne_reject := fun h => absurd (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h)))) (by decide), δ := δ }
        refine ⟨M, VR, WL, WR, POP, BAD, FIN, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro f st; exact ⟨Sum.inl_ne_inr, Sum.inl_ne_inr⟩
        · intro a b c d; constructor <;> (intro h; cases h)
        · intro a b; constructor <;> (intro h; cases h)
        · intro a; constructor <;> (intro h; cases h)
        · constructor <;> exact fun h => absurd (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h)))) (by decide)
        · constructor <;> exact fun h => absurd (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h)))) (by decide)
        · intros; rfl
        · intros; rfl
        · intros; rfl
        · rfl
        · intros; rfl
        · rfl
        · intros; rfl
        · intros; rfl
        · intros; rfl
        · intros; rfl
        · intros; rfl
        · intros; rfl
        · intros; rfl
        · intro a g t e b p h hn
          simp only [M, δ, POP, if_neg hn, h]
        · intro a g h hn
          simp only [M, δ, POP, if_neg hn, h]

      have partB2
        (partB1 : ∀ (act : Fin 6 → (BSym × Option Bool) → Option (Option BSym × Bool × Fin 6 × Bool)),
        ∃ (M : TM (BSym × Option Bool)) (VR : Bool → Option Bool → M.Q) (WL : Fin 6 → Option BSym → Bool → Bool → M.Q)
          (WR : Fin 6 → Bool → M.Q) (POP : Fin 6 → M.Q) (BAD FIN : M.Q),
          M.q₀ = VR true none ∧
          (∀ f st, VR f st ≠ M.qaccept ∧ VR f st ≠ M.qreject) ∧
          (∀ a b c d, WL a b c d ≠ M.qaccept ∧ WL a b c d ≠ M.qreject) ∧
          (∀ a b, WR a b ≠ M.qaccept ∧ WR a b ≠ M.qreject) ∧
          (∀ a, POP a ≠ M.qaccept ∧ POP a ≠ M.qreject) ∧
          (BAD ≠ M.qaccept ∧ BAD ≠ M.qreject) ∧
          (FIN ≠ M.qaccept ∧ FIN ≠ M.qreject) ∧
          (∀ f st s c, M.δ (VR f st) (some (s, c)) = if s = BSym.minus ∨ (s = BSym.sep ∧ st = some false) then (BAD, some (s, none), Move.right)
             else (VR (f && decide (s ≠ BSym.sep)) (if s = BSym.sep then none else some (decide (s = BSym.one))),
                some (s, if f then some (decide (s = BSym.one)) else none), Move.right)) ∧
          (∀ f st, M.δ (VR f st) none = if st = none ∧ f = false then (POP 0, none, Move.left) else (M.qaccept, none, Move.right)) ∧
          (∀ g, M.δ BAD (some g) = (BAD, some g, Move.right)) ∧
          (M.δ BAD none = (M.qaccept, none, Move.right)) ∧
          (∀ g, M.δ FIN (some g) = (FIN, some g, Move.left)) ∧
          (M.δ FIN none = (M.qaccept, none, Move.right)) ∧
          (∀ a b c d g, M.δ (WL a b c d) (some g) = (WL a b c d, some g, Move.left)) ∧
          (∀ a b d, M.δ (WL a b true d) none = (WL a b false d, b.map (fun s => (s, none)), Move.left)) ∧
          (∀ a b d, M.δ (WL a b false d) none = (WR a d, b.map (fun s => (s, none)), Move.right)) ∧
          (∀ a p s, M.δ (WR a p) (some (s, none)) = (WR a p, some (s, none), Move.right)) ∧
          (∀ a p s c, M.δ (WR a p) (some (s, some c)) = (WR a (p && !c), some (s, some (xor c p)), Move.right)) ∧
          (∀ a p, M.δ (WR a p) none = (POP (if p then 4 else a), none, Move.left)) ∧
          (∀ s, M.δ (POP 5) (some (s, none)) = (FIN, some (s, none), Move.left)) ∧
          (∀ a g t e b p, act a g = some (t, e, b, p) → ¬ (a = 5 ∧ g.2 = none) → M.δ (POP a) (some g) = (WL b t e p, none, Move.left)) ∧
          (∀ a g, act a g = none → ¬ (a = 5 ∧ g.2 = none) → M.δ (POP a) (some g) = (M.qaccept, none, Move.right))) :
        ∀ (act : Fin 6 → (BSym × Option Bool) → Option (Option BSym × Bool × Fin 6 × Bool))
          (V : List BSym → List (BSym × Option Bool)) (hV : V = List.map (fun s => (s, none)))
          (RS : Bool → List (BSym × Option Bool) → Bool × List (BSym × Option Bool))
          (hRSnil : ∀ p, RS p [] = (p, []))
          (hRSp : ∀ p s l, RS p ((s, none) :: l) = ((RS p l).1, (s, none) :: (RS p l).2))
          (hRSm : ∀ p s c l, RS p ((s, some c) :: l) = ((RS (p && !c) l).1, (s, some (xor c p)) :: (RS (p && !c) l).2))
          (mark : Bool → List BSym → List (BSym × Option Bool))
          (hmknil : ∀ f, mark f [] = [])
          (hmk : ∀ f s l, mark f (s :: l) = (s, if f then some (decide (s = BSym.one)) else none) :: mark (f && decide (s ≠ BSym.sep)) l)
          (vs : Option Bool → List BSym → Option (Option Bool))
          (hvsnil : ∀ st, vs st [] = some st)
          (hvs : ∀ st s l, vs st (s :: l) = if s = BSym.minus ∨ (s = BSym.sep ∧ st = some false) then none else vs (if s = BSym.sep then none else some (decide (s = BSym.one))) l),
        ∃ (M : TM (BSym × Option Bool)) (At : Fin 6 → List (BSym × Option Bool) → Cfg (BSym × Option Bool) M.Q → Prop),
          -- non-finishing steps
          (∀ ph s t e ph' p w, act ph s = some (t, e, ph', p) → ¬ (ph = 5 ∧ s.2 = none) → (e = true → ∃ b, t = some b) →
            ∀ c, At ph (w ++ [s]) c → ∃ k ≤ 2 * w.length + 7,
              At (if (RS p w).1 then 4 else ph') (V (t.toList ++ if e then t.toList else []) ++ (RS p w).2) (M.run k c)) ∧
          -- reject
          (∀ ph s w, act ph s = none → ¬ (ph = 5 ∧ s.2 = none) →
            ∀ c, At ph (w ++ [s]) c → ∃ k ≤ 2 * w.length + 7, (M.run k c).state = M.qaccept ∧ M.output (M.run k c) = []) ∧
          -- finish
          (∀ s w, ∀ c, At 5 (w ++ [(s, none)]) c → ∃ k ≤ 2 * w.length + 7, (M.run k c).state = M.qaccept ∧ M.output (M.run k c) = (w ++ [(s, none)]).map some) ∧
          -- init
          (∀ x, vs none x = some none → (∃ a b, x = a ++ BSym.sep :: b ) → ∃ k ≤ x.length + 1, At 0 (mark true x) (M.run k (M.init (x.map (fun s => (s, none)))))) ∧
          (∀ x, (vs none x ≠ some none ∨ BSym.sep ∉ x) → ∃ k ≤ x.length + 1, (M.run k (M.init (x.map (fun s => (s, none))))).state = M.qaccept ∧
             M.output (M.run k (M.init (x.map (fun s => (s, none))))) = []) := by
        clear * - partB1
        intro act V hV RS hRSnil hRSp hRSm mark hmknil hmk vs hvsnil hvs
        obtain ⟨M, VR, WL, WR, POP, BAD, FIN, hq0, nVR, nWL, nWR, nPOP, nBAD, nFIN, dVR, dVR0, dBAD, dBAD0, dFIN, dFIN0, dWL, dWL1, dWL0, dWRp, dWRm, dWR0, dPOP5, dPOP, dPOPr⟩ := partB1 act
        clear partB1
        have stepR : ∀ q h q' s' L R, (q ≠ M.qaccept ∧ q ≠ M.qreject) → M.δ q h = (q', s', Move.right) →
            M.step ⟨q, L, h, R⟩ = ⟨q', s' :: L, R.headD none, R.tail⟩ := by
          intro q h q' s' L R hq hd
          have : ¬ M.IsHalting ⟨q, L, h, R⟩ := by rintro (h | h); exacts [hq.1 h, hq.2 h]
          simp only [TM.step, if_neg this, hd]
        have stepL : ∀ q h q' s' L R, (q ≠ M.qaccept ∧ q ≠ M.qreject) → M.δ q h = (q', s', Move.left) →
            M.step ⟨q, L, h, R⟩ = ⟨q', L.tail, L.headD none, s' :: R⟩ := by
          intro q h q' s' L R hq hd
          have : ¬ M.IsHalting ⟨q, L, h, R⟩ := by rintro (h | h); exacts [hq.1 h, hq.2 h]
          cases L <;> simp only [TM.step, if_neg this, hd] <;> rfl
        have run1 : ∀ k c, M.run (k + 1) c = M.run k (M.step c) := fun k c => rfl
        have run0 : ∀ c, M.run 0 c = c := fun c => rfl
        have runone : ∀ c, M.run 1 c = M.step c := fun c => rfl
        have runadd : ∀ a b c, M.run (a + b) c = M.run b (M.run a c) := by
          intro a b c
          simp only [TM.run]
          rw [add_comm, Function.iterate_add_apply]
        -- walking left in state q
        have walkL : ∀ q, (q ≠ M.qaccept ∧ q ≠ M.qreject) → (∀ g, M.δ q (some g) = (q, some g, Move.left)) →
            ∀ (l : List (BSym × Option Bool)) (Z R), M.run l.length ⟨q, (l.map some ++ Z).tail, (l.map some ++ Z).headD none, R⟩ =
              ⟨q, Z.tail, Z.headD none, l.reverse.map some ++ R⟩ := by
          intro q hq hd l
          induction l with
          | nil => intro Z R; rfl
          | cons s l ih =>
            intro Z R
            rw [List.length_cons, run1]
            simp only [List.map_cons, List.cons_append, List.tail_cons, List.headD_cons]
            rw [stepL q _ q (some s) _ _ hq (hd s), ih]
            simp
        have walkR : ∀ ph (w : List (BSym × Option Bool)) (p L Z), M.run w.length ⟨WR ph p, L, (w.map some ++ Z).headD none, (w.map some ++ Z).tail⟩ =
              ⟨WR ph (RS p w).1, (RS p w).2.reverse.map some ++ L, Z.headD none, Z.tail⟩ := by
          intro ph w
          induction w with
          | nil => intro p L Z; rw [hRSnil]; rfl
          | cons s w ih =>
            intro p L Z
            rw [List.length_cons, run1]
            simp only [List.map_cons, List.cons_append, List.tail_cons, List.headD_cons]
            obtain ⟨s, c⟩ := s
            cases c with
            | none =>
              rw [stepR _ _ _ _ _ _ (nWR _ _) (dWRp ph p s), ih, hRSp]
              simp
            | some c =>
              rw [stepR _ _ _ _ _ _ (nWR _ _) (dWRm ph p s c), ih, hRSm]
              simp
        have repH : ∀ i, (List.replicate i (none : Option (BSym × Option Bool))).headD none = none := by
          intro i; cases i <;> simp [List.replicate_succ]
        have outrep : ∀ q L (w : List (BSym × Option Bool)) j, M.output ⟨q, L, (w.map some ++ List.replicate j none).headD none, (w.map some ++ List.replicate j none).tail⟩ = w.map some := by
          intro q L w j
          have h1 : ∀ i, M.output ⟨q, L, none, List.replicate i none⟩ = [] := by
            intro i
            simp only [TM.output]
            rw [← List.replicate_succ, List.reverse_replicate]
            simp
          cases w with
          | nil =>
            simp only [List.map_nil, List.nil_append]
            rw [repH, List.tail_replicate, h1]
          | cons s w =>
            simp only [List.map_cons, List.cons_append, List.tail_cons, List.headD_cons, TM.output]
            have h2 : (some s :: (List.map some w ++ List.replicate j none)).reverse = List.replicate j none ++ (some s :: w.map some).reverse := by
              simp
            rw [h2, List.dropWhile_append]
            have h3 : List.dropWhile Option.isNone (List.replicate j (none : Option (BSym × Option Bool))) = [] := by simp
            rw [h3]
            have h4 : (some s :: w.map some).reverse = (s :: w).reverse.map some := by simp
            rw [h4]
            have h5 : ∀ l : List (BSym × Option Bool), List.dropWhile Option.isNone (l.map some) = l.map some := by
              intro l; cases l <;> simp
            rw [List.isEmpty_nil, if_pos rfl, h5]
            simp
        refine ⟨M, fun ph w c => ∃ i j, c = ⟨POP ph, (w.reverse.map some ++ List.replicate i none).tail, (w.reverse.map some ++ List.replicate i none).headD none, List.replicate j none⟩, ?_, ?_, ?_, ?_, ?_⟩
        · intro ph s t e ph' p w ha hn he c ⟨i, j, hc⟩
          have tailL : ∀ (t : Option BSym) (W : List (BSym × Option Bool)) i j, ∃ k ≤ W.length + 2, ∃ i' j',
             M.run k ⟨WL ph' t false p, List.replicate i none, none, W.map some ++ List.replicate j none⟩ =
               ⟨POP (if (RS p W).1 then 4 else ph'), (((V t.toList) ++ (RS p W).2).reverse.map some ++ List.replicate i' none).tail,
                 (((V t.toList) ++ (RS p W).2).reverse.map some ++ List.replicate i' none).headD none, List.replicate j' none⟩ := by
            intro t W i j
            refine ⟨1 + (W.length + 1), by omega, ?_⟩
            rw [runadd, runone, stepR _ _ _ _ _ _ (nWL _ _ _ _) (dWL0 ph' t p), runadd, walkR, runone, repH,
              stepL _ _ _ _ _ _ (nWR _ _) (dWR0 _ _)]
            cases t with
            | none =>
              refine ⟨i + 1, (j - 1) + 1, ?_⟩
              simp [hV, List.replicate_succ]
            | some b =>
              refine ⟨i, (j - 1) + 1, ?_⟩
              simp [hV, List.replicate_succ]
          have hmain : ∀ i' j' : ℕ, M.run (1 + w.length) c = ⟨WL ph' t e p, List.replicate (i-1) none, none, w.map some ++ List.replicate (j+1) none⟩ := by
            intro _ _
            rw [hc, runadd, runone]
            simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, List.tail_cons, List.headD_cons]
            rw [stepL _ _ _ _ _ _ (nPOP _) (dPOP _ _ _ _ _ _ ha hn)]
            have := walkL _ (nWL ph' t e p) (dWL ph' t e p) w.reverse (List.replicate i none) (none :: List.replicate j none)
            rw [List.length_reverse] at this
            rw [this, repH, List.tail_replicate, List.reverse_reverse, List.replicate_succ]
          have hmain := hmain 0 0
          cases e with
          | false =>
            obtain ⟨k, hk, i', j', h⟩ := tailL t w (i-1) (j+1)
            refine ⟨1 + w.length + k, by omega, i', j', ?_⟩
            rw [runadd, hmain, h]
            simp
          | true =>
            obtain ⟨b, rfl⟩ := he rfl
            obtain ⟨k, hk, i', j', h⟩ := tailL (some b) ((b, none) :: w) (i-1-1) (j+1)
            simp only [List.length_cons] at hk
            refine ⟨1 + w.length + (1 + k), by omega, i', j', ?_⟩
            rw [runadd, hmain, runadd, runone, stepL _ _ _ _ _ _ (nWL _ _ _ _) (dWL1 _ _ _), repH, List.tail_replicate]
            have h' := h
            simp only [List.map_cons, List.cons_append] at h'
            rw [show (Option.map (fun s => (s, (none : Option Bool))) (some b)) = some (b, none) from rfl, h']
            simp [hRSp, hV]
        · intro ph s w ha hn c ⟨i, j, hc⟩
          refine ⟨1, by omega, ?_⟩
          rw [hc, runone]
          simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, List.tail_cons, List.headD_cons]
          rw [stepR _ _ _ _ _ _ (nPOP _) (dPOPr _ _ ha hn)]
          exact ⟨rfl, by simpa using outrep M.qaccept _ [] j⟩
        · intro s w c ⟨i, j, hc⟩
          refine ⟨1 + (w.length + 1), by omega, ?_⟩
          have hmain : M.run (1 + (w.length + 1)) c = ⟨M.qaccept, none :: List.replicate (i-1) none, (((w ++ [(s, none)]).map some) ++ List.replicate j none).headD none, (((w ++ [(s, none)]).map some) ++ List.replicate j none).tail⟩ := by
            rw [hc, runadd, runone]
            simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, List.tail_cons, List.headD_cons]
            rw [stepL _ _ _ _ _ _ (nPOP _) (dPOP5 _)]
            have := walkL _ nFIN dFIN w.reverse (List.replicate i none) (some (s, none) :: List.replicate j none)
            rw [List.length_reverse] at this
            rw [runadd, this, repH, List.tail_replicate, List.reverse_reverse, runone, stepR _ _ _ _ _ _ nFIN dFIN0]
            simp
          rw [hmain]
          exact ⟨rfl, outrep _ _ _ _⟩
        · have walkV : ∀ (x : List BSym) f st L, (∀ st', vs st x = some st' → M.run x.length ⟨VR f st, L, ((x.map (fun s => (s, none))).map some).headD none, ((x.map (fun s => (s, none))).map some).tail⟩ =
              ⟨VR (f && decide (BSym.sep ∉ x)) st', (mark f x).reverse.map some ++ L, none, []⟩) := by
            intro x
            induction x with
            | nil => intro f st L st' h; rw [hvsnil] at h; cases h; rw [hmknil]; simp [run0]
            | cons s x ih =>
              intro f st L st' h
              rw [hvs] at h
              by_cases hb : s = BSym.minus ∨ (s = BSym.sep ∧ st = some false)
              · rw [if_pos hb] at h; cases h
              · rw [if_neg hb] at h
                rw [List.length_cons, run1]
                simp only [List.map_cons, List.tail_cons, List.headD_cons]
                have hd := dVR f st s none
                rw [if_neg hb] at hd
                rw [stepR _ _ _ _ _ _ (nVR _ _) hd, ih _ _ _ _ h, hmk]
                cases f <;> cases s <;> simp
          intro x hx ⟨a, b, hab⟩
          refine ⟨x.length + 1, le_refl _, ?_⟩
          have h1 := walkV x true none [] none hx
          have h2 : M.init (x.map (fun s => (s, none))) = ⟨VR true none, [], ((x.map (fun s => (s, none))).map some).headD none, ((x.map (fun s => (s, none))).map some).tail⟩ := by
            simp only [TM.init, hq0]
          have h3 : (true && decide (BSym.sep ∉ x)) = false := by simp [hab]
          rw [h2, runadd, h1, runone, h3]
          have hd := dVR0 false none
          rw [if_pos ⟨rfl, rfl⟩] at hd
          rw [stepL _ _ _ _ _ _ (nVR _ _) hd]
          exact ⟨0, 1, by simp⟩
        · have walkB : ∀ (x : List BSym) L, M.run (x.length + 1) ⟨BAD, L, ((x.map (fun s => (s, none))).map some).headD none, ((x.map (fun s => (s, none))).map some).tail⟩ =
              ⟨M.qaccept, none :: ((x.map (fun s => (s, none))).map some).reverse ++ L, none, []⟩ := by
            intro x
            induction x with
            | nil => intro L; simp [runone, stepR _ _ _ _ _ _ nBAD dBAD0]
            | cons s x ih =>
              intro L
              rw [List.length_cons, run1]
              simp only [List.map_cons, List.tail_cons, List.headD_cons]
              rw [stepR _ _ _ _ _ _ nBAD (dBAD _), ih]
              simp
          have walkV : ∀ (x : List BSym) f st L, (vs st x ≠ some none ∨ (f = true ∧ BSym.sep ∉ x)) → ∃ L', M.run (x.length + 1) ⟨VR f st, L, ((x.map (fun s => (s, none))).map some).headD none, ((x.map (fun s => (s, none))).map some).tail⟩ =
              ⟨M.qaccept, L', none, []⟩ := by
            intro x
            induction x with
            | nil =>
              intro f st L h
              have hd := dVR0 f st
              rw [hvsnil] at h
              rw [if_neg (by rintro ⟨rfl, rfl⟩; simp at h)] at hd
              exact ⟨none :: L, by simp [runone, stepR _ _ _ _ _ _ (nVR _ _) hd]⟩
            | cons s x ih =>
              intro f st L h
              rw [hvs] at h
              have hd := dVR f st s none
              rw [List.length_cons, run1]
              simp only [List.map_cons, List.tail_cons, List.headD_cons]
              by_cases hb : s = BSym.minus ∨ (s = BSym.sep ∧ st = some false)
              · rw [if_pos hb] at hd
                rw [stepR _ _ _ _ _ _ (nVR _ _) hd, walkB]
                exact ⟨_, rfl⟩
              · rw [if_neg hb] at hd h
                rw [stepR _ _ _ _ _ _ (nVR _ _) hd]
                apply ih
                rcases h with h | ⟨h1, h2⟩
                · exact Or.inl h
                · right
                  simp at h2
                  refine ⟨?_, h2.2⟩
                  have := Ne.symm h2.1
                  simp [h1, this]
          intro x hx
          refine ⟨x.length + 1, le_refl _, ?_⟩
          have h2 : M.init (x.map (fun s => (s, none))) = ⟨VR true none, [], ((x.map (fun s => (s, none))).map some).headD none, ((x.map (fun s => (s, none))).map some).tail⟩ := by
            simp only [TM.init, hq0]
          obtain ⟨L', h⟩ := walkV x true none [] (by rcases hx with h | h; exacts [Or.inl h, Or.inr ⟨rfl, h⟩])
          rw [h2, h]
          exact ⟨rfl, by simp [TM.output]⟩

      have partB : ∃ f : List BSym → List BSym, PolyTimeComputable f ∧ 
         (∀ x, (∃ n pre, ∃ wd : List (ℕ × ℕ), ∃ y, wd.length = n ∧ pre ≠ [] ∧ x = encNats ((n :: pre) ++ (wd.flatMap fun p => [p.1,p.2]) ++ [y]) ∧ f x = encNats ((n :: pre) ++ (wd.flatMap fun p => [p.1,0]) ++ [y])) ∨ ((¬ ∃ n pre, ∃ wd : List (ℕ × ℕ), ∃ y, wd.length = n ∧ pre ≠ [] ∧ x = encNats ((n :: pre) ++ (wd.flatMap fun p => [p.1,p.2]) ++ [y])) ∧ f x = [])) := by
        clear * - partA1 partA2 partA4 partA5 partA6 partB1 partB2
        obtain ⟨act, hact⟩ : ∃ act : Fin 6 → (BSym × Option Bool) → Option (Option BSym × Bool × Fin 6 × Bool), act = fun ph g =>
          if ph = 0 then (if g.2 = none ∧ g.1 = BSym.sep then some (some BSym.sep,false,1,false) else none)
          else if ph = 1 then (if g.2 = none then (if g.1 = BSym.sep then some (some BSym.sep,false,2,true) else some (some g.1,false,1,false)) else none)
          else if ph = 2 then (if g.2 = none then (if g.1 = BSym.sep then some (some BSym.sep,false,3,false) else some (none,false,2,false)) else none)
          else if ph = 3 then (if g.2 = none then (if g.1 = BSym.sep then some (some BSym.sep,false,2,true) else some (some g.1,false,3,false)) else none)
          else if ph = 4 then (if g.2 = none then some (some g.1,false,4,false) else some (some g.1,false,5,false))
          else some (some g.1,false,5,false) := ⟨_, rfl⟩
        have a0 : act 0 (BSym.sep, none) = some (some BSym.sep,false,1,false) := by subst hact; simp
        have a0m : ∀ s c, act 0 (s, some c) = none := by subst hact; simp
        have a1 : ∀ s, s ≠ BSym.sep → act 1 (s, none) = some (some s,false,1,false) := by subst hact; intro s h; simp [h]
        have a1s : act 1 (BSym.sep, none) = some (some BSym.sep,false,2,true) := by subst hact; simp
        have a1m : ∀ s c, act 1 (s, some c) = none := by subst hact; simp
        have a2 : ∀ s, s ≠ BSym.sep → act 2 (s, none) = some (none,false,2,false) := by subst hact; intro s h; simp [h]
        have a2s : act 2 (BSym.sep, none) = some (some BSym.sep,false,3,false) := by subst hact; simp
        have a2m : ∀ s c, act 2 (s, some c) = none := by subst hact; simp
        have a3 : ∀ s, s ≠ BSym.sep → act 3 (s, none) = some (some s,false,3,false) := by subst hact; intro s h; simp [h]
        have a3s : act 3 (BSym.sep, none) = some (some BSym.sep,false,2,true) := by subst hact; simp
        have a3m : ∀ s c, act 3 (s, some c) = none := by subst hact; simp
        have a4 : ∀ s, act 4 (s, none) = some (some s,false,4,false) := by subst hact; simp
        have a4m : ∀ s c, act 4 (s, some c) = some (some s,false,5,false) := by subst hact; simp
        have a5m : ∀ s c, act 5 (s, some c) = some (some s,false,5,false) := by subst hact; simp
        clear hact
        obtain ⟨V, hV⟩ : ∃ V : List BSym → List (BSym × Option Bool), V = List.map (fun s => (s, none)) := ⟨_, rfl⟩
        obtain ⟨RS, hRSnil, hRSp, hRSm⟩ : ∃ RS : Bool → List (BSym × Option Bool) → Bool × List (BSym × Option Bool),
          (∀ p, RS p [] = (p, [])) ∧
          (∀ p s l, RS p ((s, none) :: l) = ((RS p l).1, (s, none) :: (RS p l).2)) ∧
          (∀ p s c l, RS p ((s, some c) :: l) = ((RS (p && !c) l).1, (s, some (xor c p)) :: (RS (p && !c) l).2)) :=
          ⟨fun p l => (l.foldr (fun (g : BSym × Option Bool) (k : Bool → Bool × List (BSym × Option Bool)) (p : Bool) =>
            match g.2 with
            | none => ((k p).1, (g.1, none) :: (k p).2)
            | some c => ((k (p && !c)).1, (g.1, some (xor c p)) :: (k (p && !c)).2)) (fun p => (p, []))) p,
            fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
        obtain ⟨mark, hmknil, hmk⟩ : ∃ mark : Bool → List BSym → List (BSym × Option Bool),
          (∀ f, mark f [] = []) ∧
          (∀ f s l, mark f (s :: l) = (s, if f then some (decide (s = BSym.one)) else none) :: mark (f && decide (s ≠ BSym.sep)) l) :=
          ⟨fun f l => (l.foldr (fun (s : BSym) (k : Bool → List (BSym × Option Bool)) (f : Bool) =>
            (s, if f then some (decide (s = BSym.one)) else none) :: k (f && decide (s ≠ BSym.sep))) (fun _ => [])) f,
            fun _ => rfl, fun _ _ _ => rfl⟩
        obtain ⟨vs, hvsnil, hvs⟩ : ∃ vs : Option Bool → List BSym → Option (Option Bool),
          (∀ st, vs st [] = some st) ∧
          (∀ st s l, vs st (s :: l) = if s = BSym.minus ∨ (s = BSym.sep ∧ st = some false) then none else vs (if s = BSym.sep then none else some (decide (s = BSym.one))) l) :=
          ⟨fun st l => (l.foldr (fun (s : BSym) (k : Option Bool → Option (Option Bool)) (st : Option Bool) =>
            if s = BSym.minus ∨ (s = BSym.sep ∧ st = some false) then none else k (if s = BSym.sep then none else some (decide (s = BSym.one)))) (fun st => some st)) st,
            fun _ => rfl, fun _ _ _ => rfl⟩
        obtain ⟨M, At, hstep, hrej, hfin, hinit, hbad⟩ := partB2 partB1 act V hV RS hRSnil hRSp hRSm mark hmknil hmk vs hvsnil hvs
        clear partB1 partB2
        have runadd : ∀ a b c, M.run (a + b) c = M.run b (M.run a c) := by
          intro a b c
          simp only [TM.run]
          rw [add_comm, Function.iterate_add_apply]
        have Vnil : V [] = [] := by rw [hV]; rfl
        have Vapp : ∀ a b, V (a ++ b) = V a ++ V b := by intro a b; rw [hV, List.map_append]
        have Vlen : ∀ a, (V a).length = a.length := by intro a; rw [hV, List.length_map]
        have Vcons : ∀ s a, V (s :: a) = (s, none) :: V a := by intro s a; rw [hV]; rfl
        obtain ⟨Mk, hMk⟩ : ∃ Mk : List (BSym × Bool) → List (BSym × Option Bool), Mk = List.map (fun s => (s.1, some s.2)) := ⟨_, rfl⟩
        have Mnil : Mk [] = [] := by rw [hMk]; rfl
        have Mapp : ∀ a b, Mk (a ++ b) = Mk a ++ Mk b := by intro a b; rw [hMk, List.map_append]
        have Mlen : ∀ a, (Mk a).length = a.length := by intro a; rw [hMk, List.length_map]
        have Mcons : ∀ s a, Mk (s :: a) = (s.1, some s.2) :: Mk a := by intro s a; rw [hMk]; rfl
        obtain ⟨val, hvalnil, hvalcons⟩ : ∃ val : List (BSym × Bool) → ℕ, val [] = 0 ∧ ∀ s c l, val ((s, c) :: l) = c.toNat + 2 * val l :=
          ⟨fun l => l.foldr (fun g a => g.2.toNat + 2 * a) 0, rfl, fun _ _ _ => rfl⟩
        have RSf : ∀ w, RS false w = (false, w) := by
          intro w
          induction w with
          | nil => rw [hRSnil]
          | cons g w ih =>
            obtain ⟨s, c⟩ := g
            cases c with
            | none => rw [hRSp, ih]
            | some c => rw [hRSm]; simp [ih]
        have RSV : ∀ p v r, RS p (V v ++ r) = ((RS p r).1, V v ++ (RS p r).2) := by
          intro p v r
          induction v with
          | nil => simp [Vnil]
          | cons s v ih => rw [Vcons, List.cons_append, hRSp, ih]; rfl
        have RSVt : ∀ p v, RS p (V v) = (p, V v) := by
          intro p v
          have := RSV p v []
          simpa [hRSnil] using this
        have decM : ∀ mk : List (BSym × Bool), ∃ mk' : List (BSym × Bool), mk'.map Prod.fst = mk.map Prod.fst ∧ (val mk ≠ 0 → val mk' + 1 = val mk) ∧
            ∀ p, RS true (Mk mk ++ V p) = (decide (val mk = 0), Mk mk' ++ V p) := by
          intro mk
          induction mk with
          | nil => exact ⟨[], rfl, fun h => absurd hvalnil h, fun p => by simp [Mnil, RSVt, hvalnil]⟩
          | cons g mk ih =>
            obtain ⟨s, c⟩ := g
            cases c with
            | true =>
              refine ⟨(s, false) :: mk, rfl, ?_, ?_⟩
              · intro _; rw [hvalcons, hvalcons]; simp; omega
              · intro p
                rw [Mcons, Mcons, List.cons_append, hRSm, hvalcons]
                simp [RSf]
            | false =>
              obtain ⟨mk', h1, h2, h3⟩ := ih
              refine ⟨(s, true) :: mk', by simp [h1], ?_, ?_⟩
              · rw [hvalcons, hvalcons]; simp; intro h; have := h2 h; omega
              · intro p
                rw [Mcons, Mcons, List.cons_append, hRSm, hvalcons]
                simp [h3]
        obtain ⟨Go, hGo⟩ : ∃ Go : ℕ → ℕ → Fin 6 → List (BSym × Option Bool) → Fin 6 → List (BSym × Option Bool) → Prop,
          ∀ X m ph w ph' w', Go X m ph w ph' w' ↔ ∀ c, At ph w c → ∃ k ≤ m*(2*X+7), At ph' w' (M.run k c) := ⟨_, fun _ _ _ _ _ _ => Iff.rfl⟩
        obtain ⟨En, hEn⟩ : ∃ En : ℕ → ℕ → Fin 6 → List (BSym × Option Bool) → List BSym → Prop,
          ∀ X m ph w out, En X m ph w out ↔ ∀ c, At ph w c → ∃ k ≤ m*(2*X+7), (M.run k c).state = M.qaccept ∧ M.output (M.run k c) = (V out).map some := ⟨_, fun _ _ _ _ _ => Iff.rfl⟩
        have goRefl : ∀ X ph w, Go X 0 ph w ph w := by
          intro X ph w; rw [hGo]; intro c hc; exact ⟨0, by omega, hc⟩
        have goTrans : ∀ X m1 m2 p1 w1 p2 w2 p3 w3, Go X m1 p1 w1 p2 w2 → Go X m2 p2 w2 p3 w3 → Go X (m1 + m2) p1 w1 p3 w3 := by
          intro X m1 m2 p1 w1 p2 w2 p3 w3 h1 h2
          rw [hGo] at *
          intro c hc
          obtain ⟨k1, hk1, h1⟩ := h1 c hc
          obtain ⟨k2, hk2, h2⟩ := h2 _ h1
          exact ⟨k1 + k2, by rw [add_mul]; omega, by rw [runadd]; exact h2⟩
        have goEnd : ∀ X m1 m2 p1 w1 p2 w2 out, Go X m1 p1 w1 p2 w2 → En X m2 p2 w2 out → En X (m1 + m2) p1 w1 out := by
          intro X m1 m2 p1 w1 p2 w2 out h1 h2
          rw [hGo] at h1
          rw [hEn] at *
          intro c hc
          obtain ⟨k1, hk1, h1⟩ := h1 c hc
          obtain ⟨k2, hk2, h2⟩ := h2 _ h1
          exact ⟨k1 + k2, by rw [add_mul]; omega, by rw [runadd]; exact h2⟩
        have popP : ∀ X ph s t e ph' v mk p, act ph (s, none) = some (t, e, ph', false) → ph ≠ 5 → (e = true → ∃ b, t = some b) →
            v.length + mk.length + p.length ≤ X →
            Go X 1 ph (V v ++ (Mk mk ++ V (p ++ [s]))) ph' (V ((t.toList ++ if e then t.toList else []) ++ v) ++ (Mk mk ++ V p)) := by
          intro X ph s t e ph' v mk p ha hph he hX
          rw [hGo]
          intro c hc
          have hw : V v ++ (Mk mk ++ V (p ++ [s])) = (V v ++ (Mk mk ++ V p)) ++ [(s, none)] := by
            rw [Vapp, Vcons, Vnil]; simp
          rw [hw] at hc
          obtain ⟨k, hk, h⟩ := hstep ph (s, none) t e ph' false _ ha (fun h => hph h.1) he c hc
          refine ⟨k, ?_, ?_⟩
          · simp [Vlen, Mlen] at hk; omega
          · rw [RSf] at h
            rw [Vapp]
            simpa using h
        have popD : ∀ X ph s t e ph' v mk p, act ph (s, none) = some (t, e, ph', true) → ph ≠ 5 → (e = true → ∃ b, t = some b) →
            v.length + mk.length + p.length ≤ X →
            ∃ mk' : List (BSym × Bool), mk'.map Prod.fst = mk.map Prod.fst ∧ (val mk ≠ 0 → val mk' + 1 = val mk) ∧
            Go X 1 ph (V v ++ (Mk mk ++ V (p ++ [s]))) (if val mk = 0 then 4 else ph') (V ((t.toList ++ if e then t.toList else []) ++ v) ++ (Mk mk' ++ V p)) := by
          intro X ph s t e ph' v mk p ha hph he hX
          obtain ⟨mk', h1, h2, h3⟩ := decM mk
          refine ⟨mk', h1, h2, ?_⟩
          rw [hGo]
          intro c hc
          have hw : V v ++ (Mk mk ++ V (p ++ [s])) = (V v ++ (Mk mk ++ V p)) ++ [(s, none)] := by
            rw [Vapp, Vcons, Vnil]; simp
          rw [hw] at hc
          obtain ⟨k, hk, h⟩ := hstep ph (s, none) t e ph' true _ ha (fun h => hph h.1) he c hc
          refine ⟨k, ?_, ?_⟩
          · simp [Vlen, Mlen] at hk; omega
          · rw [RSV, h3] at h
            rw [Vapp]
            simpa using h
        have popM : ∀ X ph s c ph' v mk, act ph (s, some c) = some (some s, false, ph', false) → v.length + mk.length ≤ X →
            Go X 1 ph (V v ++ Mk (mk ++ [(s, c)])) ph' (V (s :: v) ++ Mk mk) := by
          intro X ph s c ph' v mk ha hX
          rw [hGo]
          intro c' hc
          have hw : V v ++ Mk (mk ++ [(s, c)]) = (V v ++ Mk mk) ++ [(s, some c)] := by
            rw [Mapp, Mcons, Mnil]; simp
          rw [hw] at hc
          obtain ⟨k, hk, h⟩ := hstep ph (s, some c) (some s) false ph' false _ ha (by simp) (by simp) c' hc
          refine ⟨k, ?_, ?_⟩
          · simp [Vlen, Mlen] at hk; omega
          · rw [RSf] at h
            rw [Vcons]
            simpa [Vcons, Vnil] using h
        have rejM : ∀ X ph v mk, (∀ s c, act ph (s, some c) = none) → mk ≠ [] → v.length + mk.length ≤ X →
            En X 1 ph (V v ++ Mk mk) [] := by
          intro X ph v mk ha hmk' hX
          rw [hEn]
          intro c' hc
          obtain ⟨mk, g, rfl⟩ := List.eq_nil_or_concat mk |>.resolve_left hmk'
          obtain ⟨s, c⟩ := g
          have hw : V v ++ Mk (mk.concat (s, c)) = (V v ++ Mk mk) ++ [(s, some c)] := by
            rw [List.concat_eq_append, Mapp, Mcons, Mnil]; simp
          rw [hw] at hc
          obtain ⟨k, hk, h1, h2⟩ := hrej ph (s, some c) _ (ha s c) (by simp) c' hc
          refine ⟨k, ?_, h1, by rw [h2, Vnil]; rfl⟩
          simp [Vlen, Mlen] at hk hX; omega
        have finV : ∀ X v, v ≠ [] → v.length ≤ X → En X 1 5 (V v) v := by
          intro X v hv hX
          rw [hEn]
          intro c' hc
          obtain ⟨v, s, rfl⟩ := List.eq_nil_or_concat v |>.resolve_left hv
          have hw : V (v.concat s) = V v ++ [(s, none)] := by
            rw [List.concat_eq_append, Vapp, Vcons, Vnil]
          rw [hw] at hc
          obtain ⟨k, hk, h1, h2⟩ := hfin s _ c' hc
          refine ⟨k, ?_, h1, by rw [h2, hw]⟩
          simp [Vlen] at hk hX; omega
        have copy : ∀ X ph mk p ds v, (∀ s ∈ ds, act ph (s, none) = some (some s, false, ph, false)) → ph ≠ 5 →
            v.length + mk.length + p.length + ds.length ≤ X →
            Go X ds.length ph (V v ++ (Mk mk ++ V (p ++ ds))) ph (V (ds ++ v) ++ (Mk mk ++ V p)) := by
          intro X ph mk p ds
          induction ds using List.reverseRecOn with
          | nil => intro v _ _ _; simpa using goRefl _ _ _
          | append_singleton ds s ih =>
            intro v ha hph hX
            simp only [List.length_append, List.length_singleton] at hX
            have h1 := popP X ph s (some s) false ph v mk (p ++ ds) (ha s (by simp)) hph (by simp) (by simp; omega)
            have h2 := ih (s :: v) (fun s hs => ha s (by simp [hs])) hph (by simp; omega)
            have h3 := goTrans _ _ _ _ _ _ _ _ _ h1 (by simpa using h2)
            rw [add_comm] at h3
            simpa using h3
        have drop : ∀ X mk p ds v, (∀ s ∈ ds, s ≠ BSym.sep) → 
            v.length + mk.length + p.length + ds.length ≤ X →
            Go X ds.length 2 (V v ++ (Mk mk ++ V (p ++ ds))) 2 (V v ++ (Mk mk ++ V p)) := by
          intro X mk p ds
          induction ds using List.reverseRecOn with
          | nil => intro v _ _; simpa using goRefl _ _ _
          | append_singleton ds s ih =>
            intro v ha hX
            simp only [List.length_append, List.length_singleton] at hX
            have h1 := popP X 2 s none false 2 v mk (p ++ ds) (a2 s (ha s (by simp))) (by decide) (by simp) (by simp; omega)
            have h2 := ih v (fun s hs => ha s (by simp [hs])) (by omega)
            have h3 := goTrans _ _ _ _ _ _ _ _ _ h1 (by simpa using h2)
            rw [add_comm] at h3
            simpa using h3
        have copyM5 : ∀ X mk v, v.length + mk.length ≤ X → Go X mk.length 5 (V v ++ Mk mk) 5 (V (mk.map Prod.fst ++ v)) := by
          intro X mk
          induction mk using List.reverseRecOn with
          | nil => intro v _; simpa [Mnil] using goRefl _ _ _
          | append_singleton mk g ih =>
            intro v hX
            obtain ⟨s, c⟩ := g
            simp only [List.length_append, List.length_singleton] at hX
            have h1 := popM X 5 s c 5 v mk (a5m s c) (by omega)
            have h2 := ih (s :: v) (by simp; omega)
            have h3 := goTrans _ _ _ _ _ _ _ _ _ h1 h2
            rw [add_comm] at h3
            simpa using h3
        have copyM4 : ∀ X mk v, mk ≠ [] → v.length + mk.length ≤ X → En X (mk.length + 1) 4 (V v ++ Mk mk) (mk.map Prod.fst ++ v) := by
          intro X mk v hmk' hX
          obtain ⟨mk, g, rfl⟩ := List.eq_nil_or_concat mk |>.resolve_left hmk'
          obtain ⟨s, c⟩ := g
          rw [List.concat_eq_append] at *
          simp only [List.length_append, List.length_singleton] at hX
          have h1 := popM X 4 s c 5 v mk (a4m s c) (by omega)
          have h2 := copyM5 X mk (s :: v) (by simp; omega)
          have h3 := goTrans _ _ _ _ _ _ _ _ _ h1 h2
          have h4 := goEnd _ _ _ _ _ _ _ _ h3 (finV X _ (by simp) (by simp; omega))
          have e1 : (mk ++ [(s, c)]).length + 1 = 1 + mk.length + 1 := by simp; omega
          rw [e1]
          simpa using h4
        obtain ⟨bs, hbs⟩ : ∃ bs : ℕ → List BSym, bs = fun k => (Nat.bits k).map (fun b => if b then BSym.one else BSym.zero) := ⟨_, rfl⟩
        have bssep : ∀ k, ∀ s ∈ bs k, s ≠ BSym.sep := by
          intro k s hs h; subst h; subst hbs; exact partA1 k hs
        have enil : encNats [] = [] := rfl
        have econs : ∀ k xs, encNats (k :: xs) = bs k ++ BSym.sep :: encNats xs := by
          intro k xs; subst hbs; simp [encNats, encNat]
        have eapp : ∀ xs ys, encNats (xs ++ ys) = encNats xs ++ encNats ys := by
          intro xs ys; simp [encNats]
        have bs0 : bs 0 = [] := by subst hbs; simp
        have loop : ∀ X k ts e v mk, (k ≠ 0 → val mk + 1 = k) → mk ≠ [] →
            1 + v.length + mk.length + (encNats ts).length + (bs e).length ≤ X →
            ∃ out m, m ≤ mk.length + (encNats ts).length + (bs e).length + 1 ∧
              En X m (if k = 0 then 4 else 2) (V (BSym.sep :: v) ++ (Mk mk ++ V (encNats ts ++ bs e))) out ∧
              ((∃ pre, ∃ wd : List (ℕ × ℕ), wd.length = k ∧ pre ≠ [] ∧ ts ++ [e] = pre ++ (wd.flatMap fun p => [p.1,p.2]) ∧
                  out = mk.map Prod.fst ++ encNats (pre ++ (wd.flatMap fun p => [p.1,0])) ++ v) ∨
               ((¬ ∃ pre, ∃ wd : List (ℕ × ℕ), wd.length = k ∧ pre ≠ [] ∧ ts ++ [e] = pre ++ (wd.flatMap fun p => [p.1,p.2])) ∧ out = [])) := by
          intro X k
          induction k with
          | zero =>
            intro ts e v mk _ hmk' hX
            refine ⟨mk.map Prod.fst ++ ((encNats ts ++ bs e) ++ BSym.sep :: v), (encNats ts ++ bs e).length + (mk.length + 1), by simp; omega, ?_, Or.inl ⟨ts ++ [e], [], rfl, by simp, by simp, ?_⟩⟩
            · rw [if_pos rfl]
              have h1 := copy X 4 mk [] (encNats ts ++ bs e) (BSym.sep :: v) (fun s _ => a4 s) (by decide) (by simp; omega)
              have h2 := copyM4 X mk ((encNats ts ++ bs e) ++ BSym.sep :: v) hmk' (by simp; omega)
              refine goEnd _ _ _ _ _ _ _ _ ?_ h2
              simpa [Vnil] using h1
            · simp [eapp, econs, enil]
          | succ k ih =>
            intro ts e v mk hval hmk' hX
            have hval := hval (by omega)
            rw [if_neg (by omega)]
            have h1 := drop X mk (encNats ts) (bs e) (BSym.sep :: v) (bssep e) (by simp; omega)
            rcases List.eq_nil_or_concat ts with rfl | ⟨ts1, w, rfl⟩
            · refine ⟨[], (bs e).length + 1, by simp [enil], ?_, Or.inr ⟨?_, rfl⟩⟩
              · refine goEnd _ _ _ _ _ _ _ _ h1 ?_
                simpa [enil, Vnil] using rejM X 2 (BSym.sep :: v) mk a2m hmk' (by simp; omega)
              · rintro ⟨pre, wd, hl, hp, heq⟩
                have := congrArg List.length heq
                have h3 : 0 < pre.length := List.length_pos_iff.2 hp
                cases wd with
                | nil => simp at hl
                | cons a wd => simp [List.flatMap_cons] at this; omega
            · rw [List.concat_eq_append] at *
              have hE : encNats (ts1 ++ [w]) = (encNats ts1 ++ bs w) ++ [BSym.sep] := by simp [eapp, econs, enil]
              rw [hE] at h1 hX
              simp only [List.length_append, List.length_singleton] at hX
              have h2 := popP X 2 BSym.sep (some BSym.sep) false 3 (BSym.sep :: v) mk (encNats ts1 ++ bs w) a2s (by decide) (by simp) (by simp; omega)
              have h3 := copy X 3 mk (encNats ts1) (bs w) (BSym.sep :: BSym.sep :: v) (fun s hs => a3 s (bssep w s hs)) (by decide) (by simp; omega)
              have h4 := goTrans _ _ _ _ _ _ _ _ _ (goTrans _ _ _ _ _ _ _ _ _ h1 h2) (by simpa using h3)
              rcases List.eq_nil_or_concat ts1 with rfl | ⟨ts2, e', rfl⟩
              · refine ⟨[], (bs e).length + 1 + (bs w).length + 1, by simp [econs, enil]; omega, ?_, Or.inr ⟨?_, rfl⟩⟩
                · rw [hE]
                  refine goEnd _ _ _ _ _ _ _ _ h4 ?_
                  simpa [enil, Vnil] using rejM X 3 (bs w ++ BSym.sep :: BSym.sep :: v) mk a3m hmk' (by simp; omega)
                · rintro ⟨pre, wd, hl, hp, heq⟩
                  have := congrArg List.length heq
                  have h3 : 0 < pre.length := List.length_pos_iff.2 hp
                  cases wd with
                  | nil => simp at hl
                  | cons a wd => simp [List.flatMap_cons] at this; omega
              · rw [List.concat_eq_append] at *
                have hE2 : encNats (ts2 ++ [e']) = (encNats ts2 ++ bs e') ++ [BSym.sep] := by simp [eapp, econs, enil]
                rw [hE2] at h4 hX
                simp only [List.length_append, List.length_singleton] at hX
                obtain ⟨mk', hf1, hf2, h5⟩ := popD X 3 BSym.sep (some BSym.sep) false 2 (bs w ++ BSym.sep :: BSym.sep :: v) mk (encNats ts2 ++ bs e') a3s (by decide) (by simp) (by simp; omega)
                have hlen : mk'.length = mk.length := by simpa using congrArg List.length hf1
                have hvk : val mk = k := by omega
                rw [hvk] at h5 hf2
                obtain ⟨out, m, hm, hEnd, hout⟩ := ih ts2 e' (bs w ++ BSym.sep :: BSym.sep :: v) mk' hf2 (by rintro rfl; simp at hlen; exact hmk' (List.length_eq_zero_iff.1 hlen.symm)) (by simp; omega)
                refine ⟨out, (bs e).length + 1 + (bs w).length + 1 + m, ?_, ?_, ?_⟩
                · rw [hE, hE2]; simp; omega
                · rw [hE, hE2]
                  refine goEnd _ _ _ _ _ _ _ _ (goTrans _ _ _ _ _ _ _ _ _ h4 h5) ?_
                  simpa using hEnd
                · rcases hout with ⟨pre, wd, hl, hp, heq, ho⟩ | ⟨hno, ho⟩
                  · left
                    refine ⟨pre, wd ++ [(w, e)], by simp [hl], hp, ?_, ?_⟩
                    · rw [heq]; simp
                    · rw [ho, hf1]; simp [eapp, econs, enil, bs0]
                  · right
                    refine ⟨?_, ho⟩
                    rintro ⟨pre, wd, hl, hp, heq⟩
                    apply hno
                    rcases List.eq_nil_or_concat wd with rfl | ⟨wd1, ab, rfl⟩
                    · simp at hl
                    · refine ⟨pre, wd1, by simpa using hl, hp, ?_⟩
                      have h9 : (ts2 ++ [e']) ++ [w, e] = (pre ++ (wd1.flatMap fun p => [p.1,p.2])) ++ [ab.1, ab.2] := by
                        simpa using heq
                      exact (List.append_inj' h9 rfl).1
        have chk : ∀ (x : List BSym) (ds : List Bool), vs ds.getLast? x = some none ↔ ∃ xs, ds.map (fun b => if b then BSym.one else BSym.zero) ++ x = encNats xs := by
          have nosep : ∀ ds : List Bool, BSym.sep ∉ ds.map (fun b => if b then BSym.one else BSym.zero) := by
            intro ds h
            simp only [List.mem_map] at h
            obtain ⟨b, -, hb⟩ := h
            cases b <;> simp at hb
          intro x
          induction x with
          | nil =>
            intro ds
            rw [hvsnil]
            constructor
            · intro h
              have : ds = [] := by simpa using h
              subst this
              exact ⟨[], rfl⟩
            · rintro ⟨xs, h⟩
              cases xs with
              | nil => simp [enil] at h; simp [h]
              | cons k xs =>
                exfalso
                apply nosep ds
                rw [List.append_nil] at h
                rw [h, econs]; simp
          | cons s x ih =>
            intro ds
            rw [hvs]
            cases s with
            | minus =>
              simp only [true_or, if_true]
              constructor
              · intro h; cases h
              · rintro ⟨xs, h⟩
                exfalso
                have nomin : ∀ xs, BSym.minus ∉ encNats xs := by
                  intro xs
                  induction xs with
                  | nil => simp [enil]
                  | cons k xs ih =>
                    rw [econs]
                    simp only [List.mem_append, List.mem_cons, not_or]
                    refine ⟨?_, by simp, ih⟩
                    rw [hbs]
                    simp only [List.mem_map]
                    rintro ⟨b, -, hb⟩
                    cases b <;> simp at hb
                apply nomin xs
                rw [← h]; simp
            | zero =>
              have := ih (ds ++ [false])
              simpa using this
            | one =>
              have := ih (ds ++ [true])
              simpa using this
            | sep =>
              have h0 := ih []
              by_cases hl : ds.getLast? = some false
              · simp only [hl, and_self, or_true, if_true]
                constructor
                · intro h; cases h
                · rintro ⟨xs, h⟩
                  exfalso
                  obtain ⟨k, xs', -, hk, -⟩ := partA2 _ _ _ (nosep ds) h
                  have hinj : Function.Injective (fun b : Bool => if b then BSym.one else BSym.zero) := by
                    intro a b; cases a <;> cases b <;> simp
                  have h2 := List.map_injective_iff.2 hinj hk
                  exact partA6 k (h2 ▸ hl)
              · simp only [hl, and_false, or_false, if_true, reduceCtorEq, if_false]
                simp only [List.getLast?_nil, List.map_nil, List.nil_append] at h0
                rw [h0]
                constructor
                · rintro ⟨xs, h⟩
                  obtain ⟨k, hk⟩ := partA5 ds hl
                  refine ⟨k :: xs, ?_⟩
                  rw [econs, ← h, hbs, ← hk]
                · rintro ⟨xs, h⟩
                  obtain ⟨k, xs', -, -, hk⟩ := partA2 _ _ _ (nosep ds) h
                  exact ⟨xs', hk⟩
        have markf : ∀ y, mark false y = V y := by
          intro y
          induction y with
          | nil => rw [hmknil, Vnil]
          | cons s y ih => rw [hmk, Vcons, Bool.false_and, ih]; simp
        have markt : ∀ (ds : List Bool) y, mark true (ds.map (fun b => if b then BSym.one else BSym.zero) ++ BSym.sep :: y) =
            Mk (ds.map (fun b => (if b then BSym.one else BSym.zero, b)) ++ [(BSym.sep, false)]) ++ V y := by
          intro ds y
          induction ds with
          | nil => simp [hmk, Mcons, Mnil, markf]
          | cons b ds ih =>
            simp only [List.map_cons, List.cons_append]
            rw [hmk, Mcons, List.cons_append]
            cases b <;> simp at ih ⊢ <;> exact ih
        have valbits : ∀ n : ℕ, val ((Nat.bits n).map (fun b => (if b then BSym.one else BSym.zero, b)) ++ [(BSym.sep, false)]) = n := by
          intro k
          induction k using Nat.binaryRec' with
          | zero => simp [hvalcons, hvalnil]
          | bit b n hn ih =>
            rw [Nat.bits_append_bit _ _ hn, List.map_cons, List.cons_append, hvalcons, ih, Nat.bit_val]
            omega
        have main : ∀ x, ∃ out, (∃ k ≤ (x.length + 1) + (x.length + 4) * (2 * (x.length + 4) + 7), (M.run k (M.init (x.map (fun s => (s, none))))).state = M.qaccept ∧ M.output (M.run k (M.init (x.map (fun s => (s, none))))) = (V out).map some) ∧
           ((∃ n pre, ∃ wd : List (ℕ × ℕ), ∃ y, wd.length = n ∧ pre ≠ [] ∧ x = encNats ((n :: pre) ++ (wd.flatMap fun p => [p.1,p.2]) ++ [y]) ∧ out = encNats ((n :: pre) ++ (wd.flatMap fun p => [p.1,0]) ++ [y])) ∨ ((¬ ∃ n pre, ∃ wd : List (ℕ × ℕ), ∃ y, wd.length = n ∧ pre ≠ [] ∧ x = encNats ((n :: pre) ++ (wd.flatMap fun p => [p.1,p.2]) ++ [y])) ∧ out = [])) := by
          intro x
          by_cases hb : vs none x ≠ some none ∨ BSym.sep ∉ x
          · obtain ⟨k, hk, h1, h2⟩ := hbad x hb
            refine ⟨[], ⟨k, by omega, h1, by rw [h2, Vnil]; rfl⟩, Or.inr ⟨?_, rfl⟩⟩
            rintro ⟨n, pre, wd, y, -, -, hx⟩
            rcases hb with hb | hb
            · exact hb ((chk x []).2 ⟨_, hx⟩)
            · apply hb; rw [hx]; simp [econs]
          · push Not at hb
            obtain ⟨hb1, hb2⟩ := hb
            obtain ⟨xs, hxs⟩ := (chk x []).1 hb1
            rw [List.map_nil, List.nil_append] at hxs
            cases xs with
            | nil => rw [hxs] at hb2; simp [enil] at hb2
            | cons n rest =>
            obtain ⟨k0, hk0, hAt⟩ := hinit x hb1 (List.append_of_mem hb2)
            have hmark : mark true x = Mk ((Nat.bits n).map (fun b => (if b then BSym.one else BSym.zero, b)) ++ [(BSym.sep, false)]) ++ V (encNats rest) := by
              rw [hxs, econs, hbs, markt]
            obtain ⟨mk, hmkdef⟩ : ∃ mk, mk = ((Nat.bits n).map (fun b => (if b then BSym.one else BSym.zero, b)) ++ [(BSym.sep, false)]) := ⟨_, rfl⟩
            have hvalmk : val mk = n := by rw [hmkdef]; exact valbits n
            have hmkne : mk ≠ [] := by rw [hmkdef]; simp
            have hmkfst : mk.map Prod.fst = bs n ++ [BSym.sep] := by rw [hmkdef, hbs]; simp
            rw [← hmkdef] at hmark
            have hmklen : mk.length = (bs n).length + 1 := by simpa using congrArg List.length hmkfst
            rw [hmark] at hAt
            have hxlen : x.length = mk.length + (encNats rest).length := by
              rw [hxs, econs, hmklen]; simp; omega
            -- it suffices to give En
            suffices H : ∃ out m, m ≤ x.length + 4 ∧ En (x.length + 4) m 0 (V [] ++ (Mk mk ++ V (encNats rest))) out ∧
               ((∃ pre, ∃ wd : List (ℕ × ℕ), ∃ y, wd.length = n ∧ pre ≠ [] ∧ rest = pre ++ (wd.flatMap fun p => [p.1,p.2]) ++ [y] ∧ out = encNats ((n :: pre) ++ (wd.flatMap fun p => [p.1,0]) ++ [y])) ∨
                ((¬ ∃ pre, ∃ wd : List (ℕ × ℕ), ∃ y, wd.length = n ∧ pre ≠ [] ∧ rest = pre ++ (wd.flatMap fun p => [p.1,p.2]) ++ [y]) ∧ out = [])) by
              obtain ⟨out, m, hm, hE, ho⟩ := H
              rw [hEn] at hE
              obtain ⟨k1, hk1, h1, h2⟩ := hE _ (by rw [Vnil, List.nil_append]; exact hAt)
              rw [← runadd] at h1 h2
              refine ⟨out, ⟨k0 + k1, ?_, h1, h2⟩, ?_⟩
              · have := Nat.mul_le_mul_right (2 * (x.length + 4) + 7) hm
                omega
              · rcases ho with ⟨pre, wd, y, hl, hp, hr, ho⟩ | ⟨hno, ho⟩
                · left
                  exact ⟨n, pre, wd, y, hl, hp, by rw [hxs, hr]; simp, ho⟩
                · right
                  refine ⟨?_, ho⟩
                  rintro ⟨n', pre, wd, y, hl, hp, hx⟩
                  have := partA4 _ _ (hxs.symm.trans hx)
                  simp only [List.cons_append, List.cons.injEq] at this
                  obtain ⟨rfl, h3⟩ := this
                  exact hno ⟨pre, wd, y, hl, hp, h3⟩
            rcases List.eq_nil_or_concat rest with rfl | ⟨r', y, rfl⟩
            · refine ⟨[], 1, by omega, ?_, Or.inr ⟨?_, rfl⟩⟩
              · simpa [enil, Vnil] using rejM (x.length + 4) 0 [] mk a0m hmkne (by simp; omega)
              · rintro ⟨pre, wd, y, -, -, h⟩
                simp at h
            · rw [List.concat_eq_append] at *
              have hE : encNats (r' ++ [y]) = (encNats r' ++ bs y) ++ [BSym.sep] := by simp [eapp, econs, enil]
              rw [hE] at hxlen ⊢
              simp only [List.length_append, List.length_singleton] at hxlen
              have h1 := popP (x.length + 4) 0 BSym.sep (some BSym.sep) false 1 [] mk (encNats r' ++ bs y) a0 (by decide) (by simp) (by simp; omega)
              have h2 := copy (x.length + 4) 1 mk (encNats r') (bs y) [BSym.sep] (fun s hs => a1 s (bssep y s hs)) (by decide) (by simp; omega)
              have h3 := goTrans _ _ _ _ _ _ _ _ _ h1 (by simpa using h2)
              rcases List.eq_nil_or_concat r' with rfl | ⟨ts, e, rfl⟩
              · refine ⟨[], 1 + (bs y).length + 1, by omega, ?_, Or.inr ⟨?_, rfl⟩⟩
                · refine goEnd _ _ _ _ _ _ _ _ h3 ?_
                  simpa [enil, Vnil] using rejM (x.length + 4) 1 (bs y ++ [BSym.sep]) mk a1m hmkne (by simp; omega)
                · rintro ⟨pre, wd, y', -, hp, h⟩
                  have := congrArg List.length h
                  have h3 : 0 < pre.length := List.length_pos_iff.2 hp
                  simp at this
                  omega
              · rw [List.concat_eq_append] at *
                have hE2 : encNats (ts ++ [e]) = (encNats ts ++ bs e) ++ [BSym.sep] := by simp [eapp, econs, enil]
                rw [hE2] at h3 hxlen ⊢
                simp only [List.length_append, List.length_singleton] at hxlen
                obtain ⟨mk', hf1, hf2, h5⟩ := popD (x.length + 4) 1 BSym.sep (some BSym.sep) false 2 (bs y ++ [BSym.sep]) mk (encNats ts ++ bs e) a1s (by decide) (by simp) (by simp; omega)
                have hlen : mk'.length = mk.length := by simpa using congrArg List.length hf1
                rw [hvalmk] at h5 hf2
                obtain ⟨out, m, hm, hEnd, hout⟩ := loop (x.length + 4) n ts e (bs y ++ [BSym.sep]) mk' hf2 (by rintro rfl; simp at hlen; exact hmkne (List.length_eq_zero_iff.1 hlen.symm)) (by simp; omega)
                refine ⟨out, 1 + (bs y).length + 1 + m, by omega, ?_, ?_⟩
                · refine goEnd _ _ _ _ _ _ _ _ (goTrans _ _ _ _ _ _ _ _ _ h3 h5) ?_
                  simpa using hEnd
                · rcases hout with ⟨pre, wd, hl, hp, heq, ho⟩ | ⟨hno, ho⟩
                  · left
                    refine ⟨pre, wd, y, hl, hp, by rw [heq], ?_⟩
                    rw [ho, hf1, hmkfst]; simp [eapp, econs, enil, bs0]
                  · right
                    refine ⟨?_, ho⟩
                    rintro ⟨pre, wd, y', hl, hp, heq⟩
                    exact hno ⟨pre, wd, hl, hp, (List.append_inj' heq rfl).1⟩
        choose f hf1 hf2 using main
        refine ⟨f, ⟨BSym × Option Bool, inferInstance, ⟨fun s => (s, none), fun a b h => (Prod.ext_iff.1 h).1⟩, ⟨fun s => (s, none), fun a b h => (Prod.ext_iff.1 h).1⟩, M, 200, ?_⟩, hf2⟩
        intro x
        obtain ⟨k, hk, h1, h2⟩ := hf1 x
        have hkle : k ≤ x.length ^ 200 + 200 := by
          refine hk.trans ?_
          generalize x.length = n
          rcases Nat.lt_or_ge n 2 with h | h
          · interval_cases n <;> norm_num
          · have h4 : n ^ 200 = n ^ 2 * n ^ 198 := by rw [← pow_add]
            have h5 : 2 ^ 198 ≤ n ^ 198 := Nat.pow_le_pow_left h 198
            have h6 : n ^ 2 * 100 ≤ n ^ 200 := by
              rw [h4]
              exact Nat.mul_le_mul_left _ (le_trans (by norm_num) h5)
            nlinarith
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hkle
        have hfix : M.run (x.length ^ 200 + 200) (M.init (x.map (fun s => (s, none)))) = M.run k (M.init (x.map (fun s => (s, none)))) := by
          rw [hj, runadd]
          apply Function.iterate_fixed
          unfold TM.step
          exact if_pos (Or.inl h1)
        have e1 : x.map (⟨fun s => (s, none), fun a b h => (Prod.ext_iff.1 h).1⟩ : BSym ↪ (BSym × Option Bool)) = x.map (fun s => (s, none)) := rfl
        refine ⟨?_, ?_⟩
        · unfold TM.HaltsWithin
          rw [e1, hfix]
          exact Or.inl h1
        · rw [e1, hfix, h2, hV, List.map_map]
          rfl

      have partC (partA4 : ∀ xs ys : List ℕ, encNats xs = encNats ys → xs = ys)
         (M : MachineCount) (hM : M.Valid) (ell : ShopKind)
          (lam : Parameters) (hadm : Admissible lam .sumWT) (f : List BSym → List BSym)
         (hf : ∀ x, (∃ n pre, ∃ wd : List (ℕ × ℕ), ∃ y, wd.length = n ∧ pre ≠ [] ∧ x = encNats ((n :: pre) ++ (wd.flatMap fun p => [p.1,p.2]) ++ [y]) ∧ f x = encNats ((n :: pre) ++ (wd.flatMap fun p => [p.1,0]) ++ [y])) ∨ ((¬ ∃ n pre, ∃ wd : List (ℕ × ℕ), ∃ y, wd.length = n ∧ pre ≠ [] ∧ x = encNats ((n :: pre) ++ (wd.flatMap fun p => [p.1,p.2]) ++ [y])) ∧ f x = [])) :
         ∀ x, x ∈ language M ell lam .sumWC ↔ f x ∈ language M ell lam .sumWT := by
        clear * - partA4 hM hadm f hf
        have hnd : Feature.deadlines ∉ lam := by
          intro h; rcases hadm.2.2 h with h | h <;> simp at h
        have hadm' : Admissible lam .sumWC := ⟨hadm.1, hadm.2.1, fun h => absurd h hnd⟩
        -- code shape
        have hcode : ∀ {n m : ℕ} (I : Instance n m), ∃ pre, pre ≠ [] ∧ (I.shop.code 0).dropLast = n :: pre ∧
            ∀ (w d : Fin n → ℕ), (({shop := I.shop, weight := w, due := d} : Instance n m).shop.code 0).dropLast = n :: pre := by
          intro n m I
          obtain ⟨pre, h⟩ : ∃ pre, (I.shop.code 0).dropLast = n :: m :: pre := by
            unfold SchedComplexity.Shops.ShopInstance.code
            rw [List.dropLast_concat]
            simp only [List.cons_append, List.nil_append]
            exact ⟨_, rfl⟩
          exact ⟨m :: pre, by simp, h, fun _ _ => h⟩
        have hwd : ∀ {n : ℕ} (w d : Fin n → ℕ), (List.ofFn fun j : Fin n => [w j, d j]).flatten =
            (List.ofFn fun j : Fin n => (w j, d j)).flatMap fun p => [p.1, p.2] := by
          intro n w d
          rw [List.flatMap_def, List.map_ofFn]; rfl
        have hlen2 : ∀ (wd : List (ℕ × ℕ)) (g : ℕ × ℕ → ℕ), (wd.flatMap fun p => [p.1, g p]).length = 2 * wd.length := by
          intro wd g
          induction wd with
          | nil => rfl
          | cons a t ih => simp [List.flatMap_cons, ih]; omega
        have hinj2 : ∀ (wd wd' : List (ℕ × ℕ)), (wd.flatMap fun p => [p.1, p.2]) = (wd'.flatMap fun p => [p.1, p.2]) → wd = wd' := by
          intro wd
          induction wd with
          | nil => intro wd' h; cases wd' <;> simp_all
          | cons a t ih =>
            intro wd' h
            cases wd' with
            | nil => simp at h
            | cons b t' =>
              simp [List.flatMap_cons] at h
              obtain ⟨h1, h2, h3⟩ := h
              rw [ih t' h3, Prod.ext h1 h2]
        have hmeets : ∀ {n m : ℕ} (I : Instance n m) (y z : ℕ) (_ : z = y) (d : Fin n → ℕ) (_ : d = fun _ => 0),
            Meets ell lam .sumWC I y ↔ Meets ell lam .sumWT ({shop := I.shop, weight := I.weight, due := d} : Instance n m) z := by
          rintro n m I y _ rfl _ rfl
          have ht : ∀ (Q : SchedComplexity.Shops.ShopInstance n m) (S : Q.Op → ℕ) (j : Fin n),
              tardiness ({shop := I.shop, weight := I.weight, due := fun _ => 0} : Instance n m) Q S j = (Q.completion S j : ℤ) := by
            intro Q S j
            simp [tardiness, lateness]
          have key : ∀ (Q : SchedComplexity.Shops.ShopInstance n m) (S : Q.Op → ℕ),
              (∑ j, (I.weight j : ℤ) * tardiness ({shop := I.shop, weight := I.weight, due := fun _ => 0} : Instance n m) Q S j)
                = ∑ j, (I.weight j : ℤ) * (Q.completion S j : ℤ) := fun Q S =>
            Finset.sum_congr rfl (fun j _ => congrArg (fun t => (I.weight j : ℤ) * t) (ht Q S j))
          constructor
          · rintro ⟨a, S, h1, h2, h3, h4, h5⟩
            refine ⟨a, S, h1, h2, h3, fun h => absurd h hnd, ?_⟩
            exact (key (realize ell I a) S).trans_le h5
          · rintro ⟨a, S, h1, h2, h3, h4, h5⟩
            refine ⟨a, S, h1, h2, h3, fun h => absurd h hnd, ?_⟩
            exact (key (realize ell I a) S).symm.trans_le h5
        have hdata : ∀ {n m : ℕ} (I : Instance n m) (d : Fin n → ℕ),
           DataRestrictions lam I ↔ DataRestrictions lam ({shop := I.shop, weight := I.weight, due := d} : Instance n m) :=
          fun I d => Iff.rfl
        have hshape : ∀ {n m : ℕ} (I : Instance n m) (w d : Fin n → ℕ),
           HasShape ell I ↔ HasShape ell ({shop := I.shop, weight := w, due := d} : Instance n m) :=
          fun I w d => Iff.rfl
        intro x
        constructor
        · rintro ⟨hv, n, m, I, y, hA, hH, hD, hMe, hx⟩
          obtain ⟨pre, hpre, hc, hc'⟩ := hcode I
          have hx' : x = encNats ((n :: pre) ++ ((List.ofFn fun j : Fin n => (I.weight j, I.due j)).flatMap fun p => [p.1, p.2]) ++ [y]) := by
            rw [hx, instanceNumbers, hc, hwd]; rfl
          rcases hf x with ⟨n', pre', wd, y', hl, hp, hx2, hfx⟩ | ⟨hno, -⟩
          · have he := partA4 _ _ (hx'.symm.trans hx2)
            obtain ⟨hee, hy⟩ := List.append_inj' he rfl
            clear he
            simp only [List.cons_append, List.cons.injEq] at hee
            obtain ⟨hn, hee2⟩ := hee
            subst hn
            obtain ⟨he1, he2⟩ := List.append_inj' hee2 (by
              rw [hlen2 _ (fun p => p.2), hlen2 _ (fun p => p.2), hl]; simp)
            have he3 := hinj2 _ _ he2
            subst he3 he1
            have hy' : y = y' := by simpa using hy
            subst hy'
            refine ⟨⟨hv.1, hadm⟩, n, m, {shop := I.shop, weight := I.weight, due := fun _ => 0}, y, hA, hH, hD, ?_, ?_⟩
            · exact (hmeets I y y rfl _ rfl).1 hMe
            · rw [hfx, instanceNumbers, hc', hwd]
              congr 1
              simp only [thresholdNumbers]
              congr 2
              rw [List.flatMap_def, List.flatMap_def, List.map_ofFn, List.map_ofFn]
              rfl
          · exact absurd ⟨n, pre, _, y, by simp, hpre, hx'⟩ hno
        · rintro ⟨hv, n, m, I, (z : ℕ), hA, hH, hD, hMe, hx⟩
          obtain ⟨pre, hpre, hc, hc'⟩ := hcode I
          have hx' : f x = encNats ((n :: pre) ++ ((List.ofFn fun j : Fin n => (I.weight j, I.due j)).flatMap fun p => [p.1, p.2]) ++ [z]) := by
            rw [hx, instanceNumbers, hc, hwd]; rfl
          rcases hf x with ⟨n', pre', wd, y', hl, hp, hx2, hfx⟩ | ⟨hno, hfx⟩
          · have he := partA4 _ _ (hx'.symm.trans hfx)
            obtain ⟨hee, hy⟩ := List.append_inj' he rfl
            clear he
            simp only [List.cons_append, List.cons.injEq] at hee
            obtain ⟨hn, hee2⟩ := hee
            subst hn
            obtain ⟨he1, he2⟩ := List.append_inj' hee2 (by
              rw [hlen2 _ (fun p => p.2), hlen2 _ (fun p => 0), hl]; simp)
            have he2' : ((List.ofFn fun j : Fin n => (I.weight j, I.due j)).flatMap fun p => [p.1, p.2]) = (wd.map (fun p => (p.1, 0))).flatMap fun p => [p.1, p.2] := by
              rw [he2, List.flatMap_map]
            have he3 := hinj2 _ _ he2'
            subst he1
            have hz : z = y' := (List.cons.inj hy).1
            have hwt : ∀ j : Fin n, I.weight j = (wd[j.val]'(by omega)).1 ∧ I.due j = 0 := by
              intro j
              have := congrArg (fun l => l[j.val]?) he3
              simp [hl] at this
              exact this
            refine ⟨⟨hv.1, hadm'⟩, n, m, {shop := I.shop, weight := I.weight, due := fun j => (wd[j.val]'(by omega)).2}, y', hA, hH, hD, ?_, ?_⟩
            · refine (hmeets {shop := I.shop, weight := I.weight, due := fun j => (wd[j.val]'(by omega)).2} y' z hz I.due ?_).2 hMe
              funext j; exact (hwt j).2
            · rw [hx2, instanceNumbers, hc', hwd]
              have : (List.ofFn fun j : Fin n => (I.weight j, (wd[j.val]'(by omega)).2)) = wd := by
                apply List.ext_getElem
                · simp [hl]
                · intro i h1 h2
                  simp only [List.getElem_ofFn]
                  rw [(hwt ⟨i, by omega⟩).1]
              rw [this]; rfl
          · exfalso
            rw [hx'] at hfx
            simp [encNats, encNat] at hfx
      obtain ⟨f, hf, hspec⟩ := partB
      exact ⟨f, hf, partC partA4 M hM ell lam hadm f hspec⟩
