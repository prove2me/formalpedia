-- Prove2me | solution 1 for WeightedMajority.Shifting.Supplement.theorem_7_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:06.977187+00:00
-- url     : https://prove2.me/submissions/dee740b3-009d-49c7-8081-003fb82f3362

import Definitions.Def_WeightedMajority_Shifting_Supplement_EffectiveBudgets

open WeightedMajority
open WeightedMajority.Shifting
open WeightedMajority.Shifting.Supplement

theorem solution :
    ∃ (X : Type) (_ : Primcodable X) (φ : ℕ → X → Bool),
      Computable (Function.uncurry φ) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : UnderstandingML.OnlineAlg X Bool,
        ∃ (T : ℕ) (S : Fin T → X × Bool) (i : ℕ), i < n ∧
          (∀ t, (S t).2 = φ i (S t).1) ∧
          Nat.log 2 n ≤ UnderstandingML.mistakes A S := by
            refine ⟨ℕ, inferInstance, fun i x => Nat.testBit i x, ?_, ?_⟩
            · have hit : ∀ k m : ℕ, (fun y : ℕ => y / 2)^[k] m = m / 2 ^ k := by
                intro k
                induction k with
                | zero => intro m; simp
                | succ k ih =>
                  intro m
                  rw [Function.iterate_succ_apply', ih, Nat.div_div_eq_div_mul, pow_succ]
              have heq : Function.uncurry (fun i x : ℕ => Nat.testBit i x)
                  = fun p : ℕ × ℕ => decide ((fun y : ℕ => y / 2)^[p.2] p.1 % 2 = 1) := by
                funext p
                simp only [Function.uncurry, hit]
                exact Nat.testBit_eq_decide_div_mod_eq
              rw [heq]
              have h1 : Primrec (fun p : ℕ × ℕ => (fun y => y/2)^[p.2] p.1) :=
                Primrec.nat_iterate Primrec.snd Primrec.fst
                  ((Primrec.nat_div.comp Primrec.snd (Primrec.const 2)).to₂)
              have h2 : Primrec (fun p : ℕ × ℕ => (fun y => y/2)^[p.2] p.1 % 2) :=
                Primrec.nat_mod.comp h1 (Primrec.const 2)
              exact (Primrec.eq.comp h2 (Primrec.const 1)).decide.to_comp
            · intro n hn A
              let L : ℕ → List (ℕ × Bool) := fun m =>
                Nat.rec (motive := fun _ => List (ℕ × Bool)) [] (fun j l => l ++ [(j, !A l j)]) m
              have hL0 : L 0 = [] := rfl
              have hLs : ∀ m, L (m + 1) = L m ++ [(m, !A (L m) m)] := fun m => rfl
              let b : ℕ → Bool := fun m => !A (L m) m
              let I : ℕ → ℕ := fun m =>
                Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => if b j then 2 ^ j + acc else acc) m
              have hI0 : I 0 = 0 := rfl
              have hIs : ∀ m, I (m + 1) = if b m then 2 ^ m + I m else I m := fun m => rfl
              have hlen : ∀ m, (L m).length = m := by
                intro m
                induction m with
                | zero => rw [hL0]; rfl
                | succ m ih => rw [hLs]; simp [ih]
              have hpre : ∀ m j, j ≤ m → (L m).take j = L j := by
                intro m
                induction m with
                | zero => intro j hj; rw [Nat.le_zero.mp hj]; simp [hL0]
                | succ m ih =>
                  intro j hj
                  rcases Nat.lt_or_ge j (m + 1) with h | h
                  · rw [hLs, List.take_append_of_le_length (by rw [hlen]; omega)]
                    exact ih j (by omega)
                  · have : j = m + 1 := by omega
                    subst this
                    rw [List.take_of_length_le (hlen (m + 1)).le]
              have hget : ∀ m t (h : t < (L m).length), (L m)[t] = (t, b t) := by
                intro m t h
                have hm : t + 1 ≤ m := by rw [hlen] at h; omega
                have h2 : t < ((L m).take (t + 1)).length := by simp [hlen]; omega
                rw [← List.getElem_take (j := t + 1) (h := h2)]
                simp only [hpre m (t + 1) hm, hLs]
                rw [List.getElem_append_right (by rw [hlen])]
                simp [hlen, b]
              have hIlt : ∀ m, I m < 2 ^ m := by
                intro m
                induction m with
                | zero => rw [hI0]; norm_num
                | succ m ih =>
                  rw [hIs, pow_succ]
                  split <;> omega
              have hIbit : ∀ m t, t < m → Nat.testBit (I m) t = b t := by
                intro m
                induction m with
                | zero => intro t ht; omega
                | succ m ih =>
                  intro t ht
                  rw [hIs]
                  rcases Nat.lt_or_ge t m with h | h
                  · split
                    · rw [Nat.testBit_two_pow_add_gt h]; exact ih t h
                    · exact ih t h
                  · have : t = m := by omega
                    subst this
                    have hf := Nat.testBit_lt_two_pow (hIlt t)
                    split
                    · rename_i hb
                      rw [Nat.testBit_two_pow_add_eq, hf, hb]; rfl
                    · rename_i hb
                      rw [hf]; simpa using hb
              set k := Nat.log 2 n with hk
              let S : Fin k → ℕ × Bool := fun t => (L k)[t.1]'(by rw [hlen]; exact t.2)
              have hS : ∀ t : Fin k, S t = (t.1, b t.1) := fun t => hget k t.1 _
              have hofFn : List.ofFn S = L k := by
                apply List.ext_getElem
                · simp [hlen]
                · intro j h1 h2
                  simp [S]
              have hhist : ∀ t : Fin k, UnderstandingML.history S t = L t := by
                intro t
                simp only [UnderstandingML.history, hofFn]
                exact hpre k t.1 (le_of_lt t.2)
              refine ⟨k, S, I k, ?_, ?_, ?_⟩
              · exact lt_of_lt_of_le (hIlt k) (Nat.pow_log_le_self 2 (by omega))
              · intro t
                rw [hS t]
                exact (hIbit k t.1 t.2).symm
              · apply le_of_eq
                unfold UnderstandingML.mistakes
                rw [Finset.filter_true_of_mem]
                · simp
                · intro t _
                  rw [hhist t, hS t]
                  simp [b]
