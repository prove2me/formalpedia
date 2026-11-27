-- Prove2me | solution 1 for WeightedMajority.Shifting.Supplement.theorem_7_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:38.036062+00:00
-- url     : https://prove2.me/submissions/229be755-2bd5-46f9-8161-b1a11ea1b70c

import Definitions.Def_WeightedMajority_Shifting_Supplement_EffectiveBudgets

open WeightedMajority
open WeightedMajority.Shifting
open WeightedMajority.Shifting.Supplement

theorem solution (M : ℕ → ℕ) (hM : Computable M) :
    (BudgetA M → BudgetB M) ∧ (BudgetB M → BudgetC M) ∧ (BudgetC M → BudgetD M) := by
      classical
      have hBC : BudgetB M → BudgetC M := by
        rintro ⟨c, hc⟩ X inst φ hφ
        obtain ⟨A, hA, hb⟩ := hc X inst φ hφ
        exact ⟨c, 0, A, hA, fun i _ => hb i⟩
      have hcoin : ∀ (N : ℕ) (F : Finset ℕ) (e : ℕ → ℕ),
          (∀ i ∈ F, e i ≤ N) → 2 ^ N ≤ ∑ i ∈ F, 2 ^ e i →
          ∃ G ⊆ F, ∑ i ∈ G, 2 ^ e i = 2 ^ N := by
        intro N
        induction N with
        | zero =>
          intro F e he hs
          have hne : F.Nonempty := by
            by_contra h
            simp [Finset.not_nonempty_iff_eq_empty.mp h] at hs
          obtain ⟨i, hi⟩ := hne
          refine ⟨{i}, Finset.singleton_subset_iff.mpr hi, ?_⟩
          simp [Nat.eq_zero_of_le_zero (he i hi)]
        | succ N ih =>
          intro F e he hs
          by_cases hex : ∃ i ∈ F, e i = N + 1
          · obtain ⟨i, hi, hei⟩ := hex
            exact ⟨{i}, Finset.singleton_subset_iff.mpr hi, by simp [hei]⟩
          · have he' : ∀ i ∈ F, e i ≤ N := by
              intro i hi
              have := he i hi
              have : e i ≠ N + 1 := fun h => hex ⟨i, hi, h⟩
              omega
            have hpow : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by omega
            have hs' : 2 ^ N ≤ ∑ i ∈ F, 2 ^ e i := by omega
            obtain ⟨G, hGF, hG⟩ := ih F e he' hs'
            have hdisj : Disjoint G (F \ G) := by
              exact Finset.disjoint_left.mpr (fun i hi hi' => (Finset.mem_sdiff.mp hi').2 hi)
            have hsum : (∑ i ∈ G, 2 ^ e i) + ∑ i ∈ F \ G, 2 ^ e i =
                ∑ i ∈ F, 2 ^ e i := by
              rw [← Finset.sum_union hdisj, Finset.union_sdiff_of_subset hGF]
            have hs'' : 2 ^ N ≤ ∑ i ∈ F \ G, 2 ^ e i := by omega
            obtain ⟨H, hH, heH⟩ := ih (F \ G) e
              (fun i hi => he' i ((Finset.mem_sdiff.mp hi).1)) hs''
            refine ⟨G ∪ H, Finset.union_subset hGF (hH.trans Finset.sdiff_subset), ?_⟩
            have hd : Disjoint G H := hdisj.mono_right hH
            rw [Finset.sum_union hd, hG, heH, hpow]
      have hcons : ∀ {X : Type} (A : UnderstandingML.OnlineAlg X Bool)
          (e : X × Bool) (T : ℕ) (S : Fin T → X × Bool),
          UnderstandingML.mistakes A (Fin.cons e S) =
            (if A [] e.1 ≠ e.2 then 1 else 0) +
              UnderstandingML.mistakes (fun h x => A (e :: h) x) S := by
        clear M hM hBC hcoin
        intro X A e T S
        unfold UnderstandingML.mistakes
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Fin.sum_univ_succ]
        simp only [UnderstandingML.history, List.ofFn_succ, List.take_succ_cons]
        simp only [Fin.cons_zero, Fin.cons_succ, List.take_zero, Fin.val_zero,
          Fin.val_succ, Prod.fst, Prod.snd, List.take_succ_cons, add_left_cancel_iff]
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> simp_all
      have hcap : ∀ {X : Type} (φ : ℕ → X → Bool),
          (∀ (F : Finset ℕ) (g : ℕ → Bool), ∃ x, ∀ i ∈ F, φ i x = g i) →
          ∀ (F : Finset ℕ) (b : ℕ → ℕ) (N : ℕ) (A : UnderstandingML.OnlineAlg X Bool),
          (∀ i ∈ F, b i ≤ N) → (∀ i ∈ F, HasBudget A (φ i) (b i : ℝ)) →
          (∑ i ∈ F, 2 ^ (N - b i)) < 2 ^ (N + 1) := by
        intro X φ hsplit F b N A hb hA
        generalize hm : (∑ i ∈ F, (b i + 1)) = m
        induction m using Nat.strong_induction_on generalizing F b N A with
        | h m ih =>
          by_contra hbad
          have hbad' : 2 ^ (N + 1) ≤ ∑ i ∈ F, 2 ^ (N - b i) := by omega
          have hp : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by omega
          obtain ⟨G, hGF, hG⟩ := hcoin N F (fun i => N - b i)
            (fun i _ => Nat.sub_le N (b i)) (by omega)
          have hsum : (∑ i ∈ G, 2 ^ (N - b i)) + ∑ i ∈ F \ G, 2 ^ (N - b i) =
              ∑ i ∈ F, 2 ^ (N - b i) := by
            rw [← Finset.sum_union (show Disjoint G (F \ G) from
              Finset.disjoint_left.mpr (fun i hi hi' => (Finset.mem_sdiff.mp hi').2 hi)),
              Finset.union_sdiff_of_subset hGF]
          obtain ⟨x, hx⟩ := hsplit F (fun i => decide (i ∈ G))
          let P := if A [] x then F \ G else G
          have hPF : P ⊆ F := by
            cases ha : A [] x
            · simpa only [P, ha, Bool.false_eq_true, if_false] using hGF
            · simpa only [P, ha, if_true] using (Finset.sdiff_subset : F \ G ⊆ F)
          have hmass : 2 ^ N ≤ ∑ i ∈ P, 2 ^ (N - b i) := by
            dsimp [P]
            split <;> omega
          have hne : P.Nonempty := by
            by_contra hn
            have he := Finset.not_nonempty_iff_eq_empty.mp hn
            simp [he] at hmass
          have hlabel : ∀ i ∈ P, φ i x = !(A [] x) := by
            intro i hi
            rw [hx i (hPF hi)]
            cases ha : A [] x
            · have hiG : i ∈ G := by simpa only [P, ha, Bool.false_eq_true, if_false] using hi
              simp only [hiG, decide_true, Bool.not_false]
            · have hiG : i ∉ G := (Finset.mem_sdiff.mp (show i ∈ F \ G by
                simpa only [P, ha, if_true] using hi)).2
              simp only [hiG, decide_false, Bool.not_true]
          have hpos : ∀ i ∈ P, 1 ≤ b i := by
            intro i hi
            have hh := hA i (hPF hi) 1 (fun _ => (x, φ i x)) (by simp)
            have hcount : UnderstandingML.mistakes A (fun _ : Fin 1 => (x, φ i x)) = 1 := by
              simp [UnderstandingML.mistakes, UnderstandingML.history, hlabel i hi]
            rw [hcount] at hh
            exact_mod_cast hh
          let A' : UnderstandingML.OnlineAlg X Bool := fun h z => A ((x, !(A [] x)) :: h) z
          have hA' : ∀ i ∈ P, HasBudget A' (φ i) ((b i - 1 : ℕ) : ℝ) := by
            intro i hi T S hS
            have hh := hA i (hPF hi) (T + 1) (Fin.cons (x, !(A [] x)) S) (by
              intro t
              refine Fin.cases ?_ (fun t => ?_) t
              · simpa using (hlabel i hi).symm
              · exact hS t)
            rw [hcons] at hh
            have hnot : A [] x ≠ !(A [] x) := by cases A [] x <;> decide
            have hone : (if A [] x ≠ !(A [] x) then 1 else 0 : ℕ) = 1 := if_pos hnot
            rw [hone] at hh
            push_cast at hh
            dsimp [A']
            rw [Nat.cast_sub (hpos i hi)]
            push_cast
            linarith
          have hmeasure : (∑ i ∈ P, (b i - 1 + 1)) < m := by
            have heq : (∑ i ∈ P, (b i - 1 + 1)) = ∑ i ∈ P, b i := by
              apply Finset.sum_congr rfl
              intro i hi
              have := hpos i hi
              omega
            rw [heq]
            have hlt : (∑ i ∈ P, b i) < ∑ i ∈ P, (b i + 1) := by
              exact Finset.sum_lt_sum (by intros; omega) (by
                obtain ⟨i, hi⟩ := hne
                exact ⟨i, hi, by omega⟩)
            have hle : (∑ i ∈ P, (b i + 1)) ≤ ∑ i ∈ F, (b i + 1) :=
              Finset.sum_le_sum_of_subset hPF
            omega
          have hh := ih (∑ i ∈ P, (b i - 1 + 1)) hmeasure P (fun i => b i - 1) N A'
            (fun i hi => le_trans (Nat.sub_le _ _) (hb i (hPF hi))) hA' rfl
          have hdouble : (∑ i ∈ P, 2 ^ (N - (b i - 1))) =
              (∑ i ∈ P, 2 ^ (N - b i)) * 2 := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            have he : N - (b i - 1) = (N - b i) + 1 := by
              have := hpos i hi
              have := hb i (hPF hi)
              omega
            rw [he, pow_succ]
          rw [hdouble] at hh
          omega
      have hCD : BudgetC M → BudgetD M := by
        intro hC
        let φ : ℕ → List Bool → Bool := fun i x => x.getD i false
        have hφ : Computable (Function.uncurry φ) :=
          (Primrec₂.comp (Primrec.list_getD false) Primrec.snd Primrec.fst).to_comp
        obtain ⟨c, j, A, hAc, hAb⟩ := hC (List Bool) inferInstance φ hφ
        obtain ⟨k, hk⟩ := exists_nat_ge c
        have hsplit : ∀ (F : Finset ℕ) (g : ℕ → Bool), ∃ x, ∀ i ∈ F, φ i x = g i := by
          intro F g
          refine ⟨List.ofFn (fun i : Fin (F.sup id + 1) => g i), ?_⟩
          intro i hi
          have hil : i < F.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
          dsimp [φ]
          rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hil)]
          simp only [List.getElem_ofFn]
        have hfinite : ∀ F : Finset ℕ, (∀ i ∈ F, j ≤ i) →
            (∑ i ∈ F, budgetWeight M i) ≤ (2 : ℝ) ^ (k + 1) := by
          intro F hF
          let b : ℕ → ℕ := fun i => M i + k
          let N := F.sup b
          have hb : ∀ i ∈ F, b i ≤ N := fun i hi => Finset.le_sup hi
          have hbud : ∀ i ∈ F, HasBudget A (φ i) (b i : ℝ) := by
            intro i hi T S hS
            have hh := hAb i (hF i hi) T S hS
            dsimp [b]
            push_cast
            linarith
          have hh := hcap φ hsplit F b N A hb hbud
          have hhR : (∑ i ∈ F, (2 : ℝ) ^ (N - b i)) < (2 : ℝ) ^ (N + 1) := by
            exact_mod_cast hh
          have heq : (∑ i ∈ F, budgetWeight M i) * (2 : ℝ) ^ N =
              (2 : ℝ) ^ k * ∑ i ∈ F, (2 : ℝ) ^ (N - b i) := by
            rw [Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            have hNi : M i + k ≤ N := hb i hi
            have hexp : N = M i + k + (N - b i) := by dsimp [b]; omega
            have hpN : (2 : ℝ) ^ N = (2 : ℝ) ^ M i * (2 : ℝ) ^ k * (2 : ℝ) ^ (N - b i) := by
              conv_lhs => rw [hexp]
              rw [pow_add, pow_add]
            rw [budgetWeight, hpN]
            field_simp
          have hNpos : 0 < (2 : ℝ) ^ N := by positivity
          have hKpos : 0 < (2 : ℝ) ^ k := by positivity
          have hlt : (∑ i ∈ F, budgetWeight M i) * (2 : ℝ) ^ N <
              (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ N := by
            rw [heq]
            calc
              _ < (2 : ℝ) ^ k * (2 : ℝ) ^ (N + 1) := mul_lt_mul_of_pos_left hhR hKpos
              _ = _ := by simp only [pow_succ]; ring
          exact le_of_lt ((mul_lt_mul_iff_left₀ hNpos).mp hlt)
        apply summable_of_sum_le (c := (∑ i ∈ Finset.range j, budgetWeight M i) + (2 : ℝ) ^ (k + 1))
        · intro i
          dsimp [budgetWeight]
          positivity
        · intro F
          let G := F.filter (fun i => j ≤ i)
          have hG : ∑ i ∈ G, budgetWeight M i ≤ (2 : ℝ) ^ (k + 1) :=
            hfinite G (by intro i hi; exact (Finset.mem_filter.mp hi).2)
          have hs : F \ G ⊆ Finset.range j := by
            intro i hi
            obtain ⟨hiF, hiG⟩ := Finset.mem_sdiff.mp hi
            simp only [Finset.mem_range]
            have : ¬j ≤ i := by intro h; exact hiG (Finset.mem_filter.mpr ⟨hiF, h⟩)
            omega
          have hsmall : (∑ i ∈ F \ G, budgetWeight M i) ≤ ∑ i ∈ Finset.range j, budgetWeight M i := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; dsimp [budgetWeight]; positivity)
          have hdecomp := Finset.sum_sdiff (f := budgetWeight M) (show G ⊆ F from Finset.filter_subset _ _)
          linarith
      have hAB : BudgetA M → BudgetB M := by
        classical
        have csum : ∀ {α : Type} [Primcodable α] (f : α → ℕ → ℕ),
            Computable₂ f →
            Computable (fun p : α × ℕ => ∑ i ∈ Finset.range p.2, f p.1 i) := by
          intro α inst f hf
          have hc := Computable.nat_rec (σ := ℕ)
            (Computable.snd : Computable (fun p : α × ℕ => p.2)) (Computable.const 0)
            (Computable.to₂ (Computable₂.comp Primrec.nat_add.to_comp (Computable.snd.comp Computable.snd)
              (Computable.comp (f := fun z : α × ℕ => f z.1 z.2) hf
                ((Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd)))))
          apply hc.of_eq
          intro p
          dsimp
          induction p.2 with
          | zero => simp
          | succ n ih => simpa [Finset.sum_range_succ] using congrArg (fun z => z + f p.1 n) ih
        have cpow : Computable₂ (fun a n : ℕ => a ^ n) := by
          have hc := Computable.nat_rec (σ := ℕ)
            (Computable.snd : Computable (fun p : ℕ × ℕ => p.2)) (Computable.const 1)
            (Computable.to₂ (Computable₂.comp Primrec.nat_mul.to_comp (Computable.snd.comp Computable.snd)
              (Computable.fst.comp Computable.fst)))
          apply hc.of_eq
          intro p
          change Nat.rec 1 (fun _ z => z * p.1) p.2 = p.1 ^ p.2
          induction p.2 with
          | zero => rfl
          | succ n ih => simpa [pow_succ] using congrArg (fun z => z * p.1) ih
        have cInt : Computable Int.toNat := by
          have hc : Computable (fun z : ℤ => bif (Encodable.encode z).bodd then 0 else Encodable.encode z / 2) :=
            (Computable.comp Primrec.nat_bodd.to_comp Computable.encode).cond (Computable.const 0)
              (Computable₂.comp Primrec.nat_div.to_comp Computable.encode (Computable.const 2))
          apply hc.of_eq
          intro z
          cases z with
          | ofNat v =>
            change (bif (Nat.bit false v).bodd then 0 else Nat.bit false v / 2) = v
            rw [Nat.bodd_bit]
            simp [Nat.bit_false]
          | negSucc v =>
            change (bif (Nat.bit true v).bodd then 0 else Nat.bit true v / 2) = 0
            rw [Nat.bodd_bit]
            rfl
        have cadd : ∀ {α : Type} [Primcodable α] {f g : α → ℕ},
            Computable f → Computable g → Computable (fun x => f x + g x) := by
          intro α inst f g hf hg
          exact Computable₂.comp Primrec.nat_add.to_comp hf hg
        have cmul : ∀ {α : Type} [Primcodable α] {f g : α → ℕ},
            Computable f → Computable g → Computable (fun x => f x * g x) := by
          intro α inst f g hf hg
          exact Computable₂.comp Primrec.nat_mul.to_comp hf hg
        have csub : ∀ {α : Type} [Primcodable α] {f g : α → ℕ},
            Computable f → Computable g → Computable (fun x => f x - g x) := by
          intro α inst f g hf hg
          exact Computable₂.comp Primrec.nat_sub.to_comp hf hg
        have cle : ∀ {α : Type} [Primcodable α] {f g : α → ℕ},
            Computable f → Computable g → ComputablePred (fun x => f x ≤ g x) := by
          intro α inst f g hf hg
          obtain ⟨d, hd⟩ := Primrec.nat_le
          exact ⟨fun x => d (f x, g x), Computable.comp hd.to_comp (hf.pair hg)⟩
        have ceq : ∀ {α β : Type} [Primcodable α] [Primcodable β] {f g : α → β},
            Computable f → Computable g → ComputablePred (fun x => f x = g x) := by
          intro α β inst inst' f g hf hg
          obtain ⟨d, hd⟩ := (Primrec.eq : PrimrecRel (α := β) Eq)
          exact ⟨fun x => d (f x, g x), Computable.comp hd.to_comp (hf.pair hg)⟩
        have cite : ∀ {α β : Type} [Primcodable α] [Primcodable β]
            (P : α → Prop) [DecidablePred P] {f g : α → β},
            ComputablePred P → Computable f → Computable g →
            Computable (fun x => if P x then f x else g x) := by
          intro α β inst inst' P dec f g hP hf hg
          obtain ⟨d, hd⟩ := hP
          apply (hd.cond hf hg).of_eq
          intro x
          simp
        have hpotential : ∀ {X : Type} (A : UnderstandingML.OnlineAlg X Bool)
            (V : List (X × Bool) → ℝ),
            (∀ h e, V (h ++ [e]) ≤ V h) →
            (∀ h e, A h e.1 ≠ e.2 → V (h ++ [e]) ≤ V h / 2 + 1 / (2 * (4 : ℝ) ^ h.length)) →
            ∀ (T : ℕ) (S : Fin T → X × Bool),
            (2 : ℝ) ^ UnderstandingML.mistakes A S * V (List.ofFn S) +
              2 / (2 : ℝ) ^ T ≤ V [] + 2 := by
          intro X A V hmono hwrong
          classical
          have hsnoc : ∀ (T : ℕ) (S : Fin (T + 1) → X × Bool),
              UnderstandingML.mistakes A S = UnderstandingML.mistakes A (fun i => S i.castSucc) +
              (if A (List.ofFn (fun i => S i.castSucc)) (S (Fin.last T)).1 ≠ (S (Fin.last T)).2 then 1 else 0) := by
            intro T S
            have hhist : ∀ k, k ≤ T → UnderstandingML.history S k =
                UnderstandingML.history (fun i => S i.castSucc) k := by
              intro k hk
              unfold UnderstandingML.history
              rw [List.ofFn_succ', List.concat_eq_append, List.take_append_of_le_length (by simpa using hk)]
            have hlast : UnderstandingML.history S T = List.ofFn (fun i => S i.castSucc) := by
              rw [hhist T le_rfl]
              simp [UnderstandingML.history]
            unfold UnderstandingML.mistakes
            simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
            rw [Fin.sum_univ_castSucc]
            simp only [Fin.val_last, hlast]
            congr 1
            apply Finset.sum_congr rfl
            intro t _
            rw [show UnderstandingML.history S (t.castSucc : ℕ) =
                UnderstandingML.history (fun i => S i.castSucc) (t : ℕ) from hhist t (Nat.le_of_lt t.isLt)]
          intro T
          induction T with
          | zero => intro S; simp [UnderstandingML.mistakes]
          | succ T ih =>
            intro S
            let S' : Fin T → X × Bool := fun i => S i.castSucc
            let H := List.ofFn S'
            let e := S (Fin.last T)
            let m := UnderstandingML.mistakes A S'
            have ih' := ih S'
            have hlen : H.length = T := List.length_ofFn
            have hlist : List.ofFn S = H ++ [e] := by
              rw [List.ofFn_succ', List.concat_eq_append]
            have hc := hsnoc T S
            change UnderstandingML.mistakes A S = m + (if A H e.1 ≠ e.2 then 1 else 0) at hc
            have hpT : 0 < (2 : ℝ) ^ T := by positivity
            have hhalf : 2 / (2 : ℝ) ^ (T + 1) = 1 / (2 : ℝ) ^ T := by
              rw [pow_succ]
              field_simp
            rw [hlist, hc]
            by_cases he : A H e.1 ≠ e.2
            · rw [if_pos he, pow_succ, hhalf]
              have hw := hwrong H e he
              rw [hlen] at hw
              have hm : m ≤ T := by
                dsimp [m, UnderstandingML.mistakes]
                exact le_trans (Finset.card_filter_le _ _) (by simp)
              have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ T := (pow_le_pow_iff_right₀ (by norm_num)).mpr hm
              have h4 : (4 : ℝ) ^ T = ((2 : ℝ) ^ T) ^ 2 := by
                calc
                  (4 : ℝ) ^ T = ((2 : ℝ) ^ 2) ^ T := by norm_num
                  _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]
              have herr : (2 : ℝ) ^ m / (4 : ℝ) ^ T ≤ 1 / (2 : ℝ) ^ T := by
                calc
                  _ ≤ (2 : ℝ) ^ T / (4 : ℝ) ^ T := div_le_div_of_nonneg_right hpow (by positivity)
                  _ = _ := by rw [h4]; field_simp
              have hw' : (2 : ℝ) ^ m * 2 * V (H ++ [e]) ≤
                  (2 : ℝ) ^ m * V H + (2 : ℝ) ^ m / (4 : ℝ) ^ T := by
                calc
                  _ ≤ (2 : ℝ) ^ m * 2 * (V H / 2 + 1 / (2 * (4 : ℝ) ^ T)) :=
                    mul_le_mul_of_nonneg_left hw (by positivity)
                  _ = _ := by field_simp <;> ring
              change (2 : ℝ) ^ m * V H + 2 / (2 : ℝ) ^ T ≤ V [] + 2 at ih'
              simp only [div_eq_mul_inv] at *
              linarith
            · rw [if_neg he, add_zero, hhalf]
              have hw := mul_le_mul_of_nonneg_left (hmono H e) (show 0 ≤ (2 : ℝ) ^ m by positivity)
              change (2 : ℝ) ^ m * V H + 2 / (2 : ℝ) ^ T ≤ V [] + 2 at ih'
              have hz : 0 ≤ 1 / (2 : ℝ) ^ T := by positivity
              simp only [div_eq_mul_inv] at *
              linarith
        intro hAM
        obtain ⟨hs, a, hac, haerr⟩ := hAM
        let K : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, M i
        have hK : Computable K := by
          have hc := Computable.comp (csum (fun (_ : Unit) i => M i)
            (Computable.comp (f := M) hM Computable.snd)) ((Computable.const ()).pair Computable.id)
          exact hc
        have hKi : ∀ n i, i < n → M i ≤ K n := by
          intro n i hi
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
        let U : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, 2 ^ (K n - M i)
        have hU : Computable U := by
          have hc := Computable.comp (csum (fun n i => 2 ^ (K n - M i))
            (Computable₂.comp (f := fun a n : ℕ => a ^ n) cpow (Computable.const 2)
              (csub (Computable.comp hK Computable.fst) (Computable.comp (f := M) hM Computable.snd))))
            (Computable.id.pair Computable.id)
          exact hc
        have hUR : ∀ n, (U n : ℝ) = (∑ i ∈ Finset.range n, budgetWeight M i) * (2 : ℝ) ^ K n := by
          intro n
          dsimp [U]
          push_cast
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          have hp : (2 : ℝ) ^ K n = (2 : ℝ) ^ (K n - M i) * (2 : ℝ) ^ M i := by
            rw [← pow_add, Nat.sub_add_cancel (hKi n i (Finset.mem_range.mp hi))]
          rw [budgetWeight, hp]
          field_simp
        let p : ℕ → ℕ := fun r => (a r).1.toNat
        let d : ℕ → ℕ := fun r => (a r).2 + 1
        let q : ℕ → ℝ := fun r => (p r : ℝ) / (d r : ℝ)
        let W : ℝ := ∑' i, budgetWeight M i
        have hW : 0 ≤ W := tsum_nonneg (fun i => by dsimp [budgetWeight]; positivity)
        have hp : Computable p := Computable.comp cInt (Computable.comp Computable.fst hac)
        have hd : Computable d := cadd (Computable.comp Computable.snd hac) (Computable.const 1)
        have hdpos : ∀ r, 0 < (d r : ℝ) := by intro r; dsimp [d]; positivity
        have hq : ∀ r, 1 ≤ r → |q r - W| ≤ 1 / (2 : ℝ) ^ r := by
          intro r hr
          have he := haerr r hr
          by_cases hn : 0 ≤ (a r).1
          · have heq : (p r : ℝ) = ((a r).1 : ℝ) := by
              dsimp [p]
              exact_mod_cast Int.toNat_of_nonneg hn
            simpa only [q, W, d, heq, Nat.cast_add, Nat.cast_one] using he
          · have hpz : p r = 0 := Int.toNat_eq_zero.mpr (by omega)
            have hnum : ((a r).1 : ℝ) ≤ 0 := by exact_mod_cast (show (a r).1 ≤ 0 by omega)
            have hdiv : ((a r).1 : ℝ) / (((a r).2 : ℝ) + 1) ≤ 0 :=
              div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
            have he' := (abs_le.mp he).1
            dsimp [q]
            rw [hpz]
            simp only [Nat.cast_zero, zero_div, zero_sub, abs_neg, abs_of_nonneg hW]
            dsimp [W] at hW ⊢
            linarith
        let r : ℕ → ℕ := fun t => 2 * t + 4
        let L : ℕ → ℕ → ℕ := fun t n => p (r t) * 2 ^ K n * 2 ^ r t
        let R : ℕ → ℕ → ℕ := fun t n => U n * d (r t) * 2 ^ r t + 2 * d (r t) * 2 ^ K n
        let P : ℕ → ℕ → Prop := fun t n => L t n + 1 ≤ R t n
        have hrc : Computable r := cadd (cmul (Computable.const 2) Computable.id) (Computable.const 4)
        have hLc : Computable (Function.uncurry L) :=
          cmul (cmul (Computable.comp hp (Computable.comp hrc Computable.fst))
            (Computable₂.comp (f := fun a n : ℕ => a ^ n) cpow (Computable.const 2) (Computable.comp hK Computable.snd)))
            (Computable₂.comp (f := fun a n : ℕ => a ^ n) cpow (Computable.const 2) (Computable.comp hrc Computable.fst))
        have hRc : Computable (Function.uncurry R) :=
          cadd (cmul (cmul (Computable.comp hU Computable.snd)
            (Computable.comp hd (Computable.comp hrc Computable.fst)))
            (Computable₂.comp (f := fun a n : ℕ => a ^ n) cpow (Computable.const 2) (Computable.comp hrc Computable.fst)))
            (cmul (cmul (Computable.const 2) (Computable.comp hd (Computable.comp hrc Computable.fst)))
              (Computable₂.comp (f := fun a n : ℕ => a ^ n) cpow (Computable.const 2) (Computable.comp hK Computable.snd)))
        have hPc : ComputablePred (fun z : ℕ × ℕ => P z.1 z.2) :=
          cle (cadd hLc (Computable.const 1)) hRc
        have hPiff : ∀ t n, P t n ↔ q (r t) - (∑ i ∈ Finset.range n, budgetWeight M i) < 2 / (2 : ℝ) ^ r t := by
          intro t n
          let Z : ℝ := (d (r t) : ℝ) * (2 : ℝ) ^ K n * (2 : ℝ) ^ r t
          have hZ : 0 < Z := by dsimp [Z]; positivity
          have heq : (q (r t) - (∑ i ∈ Finset.range n, budgetWeight M i) - 2 / (2 : ℝ) ^ r t) * Z =
              (L t n : ℝ) - (R t n : ℝ) := by
            dsimp [q, Z, L, R]
            push_cast
            rw [hUR]
            field_simp [ne_of_gt (hdpos (r t))]
            <;> ring
          constructor
          · intro h
            have hh : (L t n : ℝ) < (R t n : ℝ) := by exact_mod_cast (Nat.lt_of_add_one_le h)
            have hz : (q (r t) - (∑ i ∈ Finset.range n, budgetWeight M i) - 2 / (2 : ℝ) ^ r t) * Z < 0 := by
              rw [heq]; linarith
            nlinarith
          · intro h
            have hz : (q (r t) - (∑ i ∈ Finset.range n, budgetWeight M i) - 2 / (2 : ℝ) ^ r t) * Z < 0 :=
              mul_neg_of_neg_of_pos (by linarith) hZ
            rw [heq] at hz
            have hh : L t n < R t n := by exact_mod_cast (show (L t n : ℝ) < R t n by linarith)
            exact Nat.add_one_le_of_lt hh
        have hPex : ∀ t, ∃ n, P t n := by
          intro t
          have he := (abs_le.mp (hq (r t) (by dsimp [r]; omega))).2
          have heps : (0 : ℝ) < 1 / 2 ^ r t := by positivity
          have hlow : q (r t) - 2 / (2 : ℝ) ^ r t < W := by
            simp only [div_eq_mul_inv] at he heps ⊢
            linarith
          obtain ⟨n, hn⟩ := (hs.hasSum.tendsto_sum_nat.eventually_const_lt hlow).exists
          exact ⟨n, (hPiff t n).mpr (by linarith)⟩
        let n : ℕ → ℕ := fun t => Nat.find (hPex t)
        have hnc : Computable n := Computable.find hPc hPex
        have htail : ∀ t, (∑' i, budgetWeight M (i + n t)) ≤ 1 / (2 * (4 : ℝ) ^ t) := by
          intro t
          have hh := (hPiff t (n t)).mp (Nat.find_spec (hPex t))
          have he := (abs_le.mp (hq (r t) (by dsimp [r]; omega))).1
          have hsum := hs.sum_add_tsum_nat_add (n t)
          have hbound : (∑' i, budgetWeight M (i + n t)) < 3 / (2 : ℝ) ^ r t := by
            dsimp [W] at he
            simp only [div_eq_mul_inv] at hh he ⊢
            linarith
          have hpow : (2 : ℝ) ^ r t = 16 * (4 : ℝ) ^ t := by
            dsimp [r]
            rw [pow_add, pow_mul]
            norm_num
            ring
          apply le_trans (le_of_lt hbound)
          rw [hpow]
          have h4 : 0 < (4 : ℝ) ^ t := by positivity
          field_simp
          nlinarith
        obtain ⟨k, hk⟩ := exists_nat_ge (W + 2)
        have hkpow : W + 2 ≤ (2 : ℝ) ^ k := by
          have hkp : ∀ v : ℕ, (v : ℝ) ≤ (2 : ℝ) ^ v := by
            intro v
            induction v with
            | zero => norm_num
            | succ v ih =>
              push_cast
              rw [pow_succ]
              have hge : (1 : ℝ) ≤ 2 ^ v := one_le_pow₀ (by norm_num)
              linarith
          exact hk.trans (hkp k)
        refine ⟨(k : ℝ), ?_⟩
        intro X inst φ hφ
        change Computable₂ φ at hφ
        by_cases hX : Nonempty X
        swap
        · refine ⟨fun _ _ => false, Computable.const false, ?_⟩
          intro i T S hS
          have hT : T = 0 := by
            by_contra ht
            exact hX ⟨(S ⟨0, Nat.pos_of_ne_zero ht⟩).1⟩
          subst T
          simp only [UnderstandingML.mistakes, Finset.univ_eq_empty, Finset.filter_empty,
            Finset.card_empty, Nat.cast_zero]
          positivity
        obtain ⟨x0⟩ := hX
        let bad : List (X × Bool) → ℕ → ℕ := fun h i =>
          ∑ t ∈ Finset.range h.length,
            if φ i (h.getD t (x0, false)).1 = (h.getD t (x0, false)).2 then 0 else 1
        have hbadc : Computable₂ bad := by
          let E : ((List (X × Bool) × ℕ) × ℕ) → X × Bool := fun z => z.1.1.getD z.2 (x0, false)
          have hE : Computable E := Computable₂.comp (f := fun (l : List (X × Bool)) (t : ℕ) => l.getD t (x0, false)) (Primrec.list_getD (x0, false)).to_comp
            (Computable.fst.comp Computable.fst) Computable.snd
          have hF : Computable (fun z : ((List (X × Bool) × ℕ) × ℕ) => φ z.1.2 (E z).1) :=
            Computable₂.comp (f := φ) hφ (Computable.snd.comp Computable.fst) (Computable.fst.comp hE)
          have hterm : Computable (fun z : ((List (X × Bool) × ℕ) × ℕ) =>
              if φ z.1.2 (E z).1 = (E z).2 then 0 else 1) :=
            cite _ (ceq hF (Computable.snd.comp hE)) (Computable.const 0) (Computable.const 1)
          have hc := Computable.comp (csum (fun (z : List (X × Bool) × ℕ) t => if φ z.2 (z.1.getD t (x0, false)).1 =
            (z.1.getD t (x0, false)).2 then 0 else 1) hterm)
            (Computable.id.pair (Computable.list_length.comp Computable.fst))
          exact hc
        have hgood : ∀ h i, bad h i = 0 ↔ ∀ e ∈ h, φ i e.1 = e.2 := by
          intro h i
          dsimp [bad]
          rw [Finset.sum_eq_zero_iff]
          constructor
          · intro hh e he
            obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp he
            have hz := hh t (Finset.mem_range.mpr ht)
            rw [List.getD_eq_getElem _ _ ht] at hz
            by_cases hc : φ i h[t].1 = h[t].2
            · exact hc
            · simp only [hc, if_false, one_ne_zero] at hz
          · intro hh t ht
            have ht' := Finset.mem_range.mp ht
            have hz := hh h[t] (List.getElem_mem ht')
            rw [List.getD_eq_getElem _ _ ht']
            simp only [hz, if_true]
        have hgappend : ∀ h e i, bad (h ++ [e]) i = 0 ↔ bad h i = 0 ∧ φ i e.1 = e.2 := by
          intro h e i
          simp only [hgood, List.forall_mem_append, List.forall_mem_singleton]
        let vote : (List (X × Bool) × X) → Bool → ℕ := fun z y =>
          ∑ i ∈ Finset.range (n z.1.length),
            if bad z.1 i = 0 then
              if φ i z.2 = y then 2 ^ (K (n z.1.length) - M i) else 0 else 0
        have hvotec : ∀ y, Computable (fun z => vote z y) := by
          intro y
          have hb : Computable (fun z : (List (X × Bool) × X) × ℕ => bad z.1.1 z.2) :=
            Computable₂.comp (f := bad) hbadc (Computable.fst.comp Computable.fst) Computable.snd
          have hF : Computable (fun z : (List (X × Bool) × X) × ℕ => φ z.2 z.1.2) :=
            Computable₂.comp (f := φ) hφ Computable.snd (Computable.snd.comp Computable.fst)
          have hN : Computable (fun z : (List (X × Bool) × X) × ℕ => n z.1.1.length) :=
            Computable.comp hnc (Computable.list_length.comp (Computable.fst.comp Computable.fst))
          have hpow : Computable (fun z : (List (X × Bool) × X) × ℕ => 2 ^ (K (n z.1.1.length) - M z.2)) :=
            Computable₂.comp (f := fun a n : ℕ => a ^ n) cpow (Computable.const 2)
              (csub (Computable.comp hK hN) (Computable.comp hM Computable.snd))
          have hlabelterm : Computable (fun z : (List (X × Bool) × X) × ℕ =>
              if φ z.2 z.1.2 = y then 2 ^ (K (n z.1.1.length) - M z.2) else 0) := by
            exact cite (fun z : (List (X × Bool) × X) × ℕ => φ z.2 z.1.2 = y)
              (f := fun z : (List (X × Bool) × X) × ℕ => 2 ^ (K (n z.1.1.length) - M z.2)) (g := fun _ => 0)
              (ceq (f := fun z : (List (X × Bool) × X) × ℕ => φ z.2 z.1.2) (g := fun _ => y) hF (Computable.const y)) hpow (Computable.const 0)
          have hterm : Computable (fun z : (List (X × Bool) × X) × ℕ =>
              if bad z.1.1 z.2 = 0 then
                if φ z.2 z.1.2 = y then 2 ^ (K (n z.1.1.length) - M z.2) else 0 else 0) := by
            exact cite (fun z : (List (X × Bool) × X) × ℕ => bad z.1.1 z.2 = 0)
              (f := fun z : (List (X × Bool) × X) × ℕ => if φ z.2 z.1.2 = y then 2 ^ (K (n z.1.1.length) - M z.2) else 0)
              (g := fun _ => 0)
              (ceq (f := fun z : (List (X × Bool) × X) × ℕ => bad z.1.1 z.2) (g := fun _ => 0) hb (Computable.const 0))
              hlabelterm (Computable.const 0)
          have hc := Computable.comp (csum (fun (z : List (X × Bool) × X) i => if bad z.1 i = 0 then
            if φ i z.2 = y then 2 ^ (K (n z.1.length) - M i) else 0 else 0) hterm)
            (Computable.id.pair (Computable.comp hnc (Computable.list_length.comp Computable.fst)))
          exact hc
        let A : UnderstandingML.OnlineAlg X Bool := fun h x => decide (vote (h, x) false ≤ vote (h, x) true)
        have hAc : Computable (Function.uncurry A) := by
          change Computable (fun z : List (X × Bool) × X => decide (vote z false ≤ vote z true))
          obtain ⟨dec, hc⟩ := cle (hvotec false) (hvotec true)
          apply hc.of_eq
          intro z
          exact congrArg (fun d : Decidable (vote z false ≤ vote z true) =>
            @decide (vote z false ≤ vote z true) d) (Subsingleton.elim _ _)
        let w : List (X × Bool) → ℕ → ℝ := fun h i => if bad h i = 0 then budgetWeight M i else 0
        let V : List (X × Bool) → ℝ := fun h => ∑' i, w h i
        have hwn : ∀ h i, 0 ≤ w h i := by
          intro h i
          dsimp only [w]
          split_ifs
          · dsimp [budgetWeight]; positivity
          · exact le_rfl
        have hwl : ∀ h i, w h i ≤ budgetWeight M i := by
          intro h i
          dsimp only [w]
          split_ifs
          · exact le_rfl
          · dsimp [budgetWeight]; positivity
        have hws : ∀ h, Summable (w h) := fun h => hs.of_nonneg_of_le (hwn h) (hwl h)
        have hwappend : ∀ h e i, w (h ++ [e]) i = if φ i e.1 = e.2 then w h i else 0 := by
          intro h e i
          simp only [w, hgappend]
          by_cases hb : bad h i = 0 <;> by_cases he : φ i e.1 = e.2 <;>
            simp only [hb, he, true_and, false_and, if_true, if_false]
        have hmono : ∀ h e, V (h ++ [e]) ≤ V h := by
          intro h e
          apply Summable.tsum_le_tsum _ (hws _) (hws _)
          intro i
          rw [hwappend]
          split_ifs
          · rfl
          · exact hwn h i
        have hvoteR : ∀ h x y, (vote (h, x) y : ℝ) =
            (∑ i ∈ Finset.range (n h.length), w (h ++ [(x, y)]) i) * (2 : ℝ) ^ K (n h.length) := by
          intro h x y
          dsimp [vote]
          push_cast
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hwappend]
          by_cases hb : bad h i = 0 <;> by_cases hf : φ i x = y
          all_goals simp only [hb, hf, if_true, if_false, w, mul_zero, zero_mul]
          have hp : (2 : ℝ) ^ K (n h.length) = (2 : ℝ) ^ (K (n h.length) - M i) * (2 : ℝ) ^ M i := by
            rw [← pow_add, Nat.sub_add_cancel (hKi _ _ (Finset.mem_range.mp hi))]
          rw [budgetWeight, hp]
          field_simp
        have hwrong : ∀ h e, A h e.1 ≠ e.2 →
            V (h ++ [e]) ≤ V h / 2 + 1 / (2 * (4 : ℝ) ^ h.length) := by
          intro h e he
          let J : Bool → ℝ := fun y => ∑ i ∈ Finset.range (n h.length), w (h ++ [(e.1, y)]) i
          have hbal : J e.2 ≤ J (!e.2) := by
            have hv : vote (h, e.1) e.2 ≤ vote (h, e.1) (!e.2) := by
              cases hy : e.2
              · have hc : vote (h, e.1) false ≤ vote (h, e.1) true := by
                  by_contra hn
                  exact he (by simp [A, hn, hy])
                simpa only [hy, Bool.not_false] using hc
              · have hc : ¬vote (h, e.1) false ≤ vote (h, e.1) true := by
                  intro hn
                  exact he (by simp [A, hn, hy])
                simpa only [hy, Bool.not_true] using (le_of_lt (Nat.lt_of_not_ge hc))
            have hvR : (vote (h, e.1) e.2 : ℝ) ≤ (vote (h, e.1) (!e.2) : ℝ) := by exact_mod_cast hv
            rw [hvoteR, hvoteR] at hvR
            exact (mul_le_mul_iff_left₀ (show 0 < (2 : ℝ) ^ K (n h.length) by positivity)).mp hvR
          have hJsum : J false + J true = ∑ i ∈ Finset.range (n h.length), w h i := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hwappend, hwappend]
            cases hf : φ i e.1 <;> simp [hf]
          have hsumle : (∑ i ∈ Finset.range (n h.length), w h i) ≤ V h :=
            (hws h).sum_le_tsum _ (fun i _ => hwn h i)
          have hJ : J e.2 ≤ V h / 2 := by
            cases hy : e.2 <;> simp only [hy, Bool.not_false, Bool.not_true] at hbal ⊢ <;> linarith
          have htaille : (∑' i, w (h ++ [e]) (i + n h.length)) ≤
              ∑' i, budgetWeight M (i + n h.length) :=
            Summable.tsum_le_tsum (fun i => hwl _ _) ((summable_nat_add_iff _).mpr (hws _))
              ((summable_nat_add_iff _).mpr hs)
          have hdecomp := (hws (h ++ [e])).sum_add_tsum_nat_add (n h.length)
          have hePair : (e.1, e.2) = e := Prod.eta e
          change (∑ i ∈ Finset.range (n h.length), w (h ++ [e]) i) +
            (∑' i, w (h ++ [e]) (i + n h.length)) = V (h ++ [e]) at hdecomp
          have hJ' : (∑ i ∈ Finset.range (n h.length), w (h ++ [e]) i) ≤ V h / 2 := by
            simpa only [J, hePair] using hJ
          linarith [htail h.length]
        refine ⟨A, hAc, ?_⟩
        intro i T S hS
        have hhist : bad (List.ofFn S) i = 0 := by
          apply (hgood _ _).mpr
          intro e he
          obtain ⟨t, rfl⟩ := List.mem_ofFn.mp he
          exact (hS t).symm
        have hweight : budgetWeight M i ≤ V (List.ofFn S) := by
          have hh := (hws (List.ofFn S)).le_tsum i (fun j _ => hwn _ j)
          simpa only [w, hhist, if_true, V] using hh
        have hpot := hpotential A V hmono hwrong T S
        have hVempty : V [] = W := by
          apply tsum_congr
          intro i
          simp only [w, bad, List.length_nil, Finset.range_zero, Finset.sum_empty, if_true]
        rw [hVempty] at hpot
        have hfinal : (2 : ℝ) ^ UnderstandingML.mistakes A S * budgetWeight M i ≤ (2 : ℝ) ^ k := by
          have hm := mul_le_mul_of_nonneg_left hweight
            (show 0 ≤ (2 : ℝ) ^ UnderstandingML.mistakes A S by positivity)
          have hpos : 0 ≤ 2 / (2 : ℝ) ^ T := by positivity
          linarith
        have hpow : (2 : ℝ) ^ UnderstandingML.mistakes A S ≤ (2 : ℝ) ^ (M i + k) := by
          dsimp [budgetWeight] at hfinal
          rw [mul_one_div] at hfinal
          have hh := (div_le_iff₀ (show 0 < (2 : ℝ) ^ M i by positivity)).mp hfinal
          simpa only [pow_add, mul_comm] using hh
        have hnat : UnderstandingML.mistakes A S ≤ M i + k :=
          (pow_le_pow_iff_right₀ (show (1 : ℝ) < 2 by norm_num)).mp hpow
        exact_mod_cast hnat
      exact ⟨hAB, hBC, hCD⟩
