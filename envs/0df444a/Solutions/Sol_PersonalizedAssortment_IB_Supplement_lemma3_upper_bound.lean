-- Prove2me | solution 1 for PersonalizedAssortment.IB.Supplement.lemma3_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:51.515071+00:00
-- url     : https://prove2.me/submissions/73b63d59-559a-4628-b396-ce17e9be509b

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_PrimalLP
import Definitions.Def_PersonalizedAssortment_IB_Supplement_OnlinePolicy
import Definitions.Def_PersonalizedAssortment_IB_Supplement_PhaseInstance

open PersonalizedAssortment
open PersonalizedAssortment.IB
open PersonalizedAssortment.IB.Supplement

open PersonalizedAssortment.IB

/-- Lemma 3 (Upper Bound on the Competitive Ratio), p. 1538, on the construction of p. 1539: `n`
products with unit revenues, initial inventories `k` each, horizon `T = n k`, customer types the
sets `Θ` of equally liked products (`phaseChoice`), every assortment feasible, and the arrival
sequences `z^σ` (`phaseSeq k σ`) for the `n!` permutations `σ`. The construction satisfies
Assumption 1, and for every deterministic online policy there is a permutation `σ` and a feasible
solution `y` of `Primal(z^σ)` with positive objective such that the policy's expected revenue on
`z^σ` is at most `ρ_n` times the objective of `y`. -/
theorem solution (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Substitutable (Finset.univ : Finset (Finset (Fin n))) (phaseChoice (n := n)) ∧
    ∀ π : OnlinePolicy n (Finset (Fin n)),
      ∃ σ : Equiv.Perm (Fin n), ∃ y : Fin (n * k) → Finset (Fin n) → ℝ,
        PrimalFeasible (fun _ => k) Finset.univ phaseChoice (phaseSeq k σ) y ∧
        0 < primalObj (fun _ => 1) Finset.univ phaseChoice (phaseSeq k σ) y ∧
        policyRevenue (fun _ => 1) (fun _ => k) phaseChoice π (phaseSeq k σ) ≤
          rhoN n * primalObj (fun _ => 1) Finset.univ phaseChoice (phaseSeq k σ) y := by
            constructor
            · intro Θ S _ i j hij
              simp only [phaseChoice]
              by_cases hi : i ∈ insert j S ∩ Θ
              · have hi' : i ∈ S ∩ Θ := by
                  simp only [Finset.mem_inter, Finset.mem_insert] at hi ⊢
                  rcases hi with ⟨h1 | h1, h2⟩
                  · exact absurd h1 hij
                  · exact ⟨h1, h2⟩
                rw [if_pos hi, if_pos hi']
                have hc : 0 < ((S ∩ Θ).card : ℝ) := by
                  exact_mod_cast Finset.card_pos.2 ⟨i, hi'⟩
                have hle : ((S ∩ Θ).card : ℝ) ≤ ((insert j S ∩ Θ).card : ℝ) := by
                  exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_right (Finset.subset_insert _ _))
                exact one_div_le_one_div_of_le hc hle
              · rw [if_neg hi]; split_ifs <;> positivity
            intro π
            let e : Fin n → Fin n → ℝ := fun x i => if i = x then 1 else 0
            have L2 : ∀ x (fut past : List (Finset (Fin n))) hist (I : Fin n → ℕ),
                revAux (e x) phaseChoice π past fut hist I ≤ I x := by
              intro x fut
              induction fut with
              | nil => intro past hist I; simp [revAux]
              | cons z fut ih =>
                intro past hist I
                rw [revAux]
                set S := π.offer (past ++ [z]) hist
                have hp1 := (phaseChoice z).sum_prob_le_one S
                have h1 : (1 - ∑ i ∈ S, (phaseChoice z).prob S i) *
                    revAux (e x) phaseChoice π (past ++ [z]) fut (hist ++ [none]) I ≤
                    (1 - ∑ i ∈ S, (phaseChoice z).prob S i) * I x :=
                  mul_le_mul_of_nonneg_left (ih _ _ _) (sub_nonneg.2 hp1)
                have h2 : ∀ i ∈ S, (phaseChoice z).prob S i * ((if 0 < I i then e x i else 0) +
                    revAux (e x) phaseChoice π (past ++ [z]) fut (hist ++ [some i]) (Function.update I i (I i - 1)))
                    ≤ (phaseChoice z).prob S i * I x := by
                  intro i _
                  apply mul_le_mul_of_nonneg_left _ ((phaseChoice z).prob_nonneg S i)
                  have := ih (past ++ [z]) (hist ++ [some i]) (Function.update I i (I i - 1))
                  by_cases hix : i = x
                  · subst hix
                    rw [Function.update_self] at this
                    by_cases hI : 0 < I i
                    · rw [if_pos hI]; simp only [e, if_true]
                      rw [Nat.cast_sub hI] at this; push_cast at this; linarith
                    · rw [if_neg hI]; have : I i = 0 := by omega
                      simp_all
                  · rw [Function.update_of_ne (Ne.symm hix)] at this
                    simp only [e, if_neg hix, ite_self]; linarith
                have h3 := Finset.sum_le_sum h2
                rw [← Finset.sum_mul] at h3
                nlinarith
            have L1 : ∀ (fut past : List (Finset (Fin n))) hist (I : Fin n → ℕ),
                revAux (fun _ => 1) phaseChoice π past fut hist I =
                  ∑ x, revAux (e x) phaseChoice π past fut hist I := by
              intro fut
              induction fut with
              | nil => intro past hist I; simp [revAux]
              | cons z fut ih =>
                intro past hist I
                simp only [revAux]
                rw [ih, Finset.sum_add_distrib, ← Finset.mul_sum]
                congr 1
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro i _
                rw [ih, ← Finset.mul_sum, Finset.sum_add_distrib]
                congr 2
                by_cases hI : 0 < I i
                · simp [hI, e]
                · simp [hI]
            let L : Equiv.Perm (Fin n) → List (Finset (Fin n)) := fun σ => List.ofFn (phaseSeq k σ)
            let a : ℕ → ℝ := fun j => ∑ t ∈ Finset.Icc 1 j, 1 / ((n : ℝ) - (t : ℝ) + 1)
            have hL : ∀ (σ σ' : Equiv.Perm (Fin n)) (t' : ℕ),
                (∀ s : Fin (n * k), s.val < t' → phaseSeq k σ s = phaseSeq k σ' s) →
                (L σ).take t' = (L σ').take t' := by
              intro σ σ' t' h
              apply List.ext_getElem
              · simp [L]
              · intro i h1 h2
                simp only [L, List.getElem_take, List.getElem_ofFn]
                apply h
                simp only [L, List.length_take, List.length_ofFn] at h1
                simp only; omega
            have hswapset : ∀ (A : Finset (Fin n)) (x x' : Fin n), x ∈ A → x' ∈ A →
                A.image (Equiv.swap x x') = A := by
              intro A x x' hx hx'
              ext y
              simp only [Finset.mem_image]
              constructor
              · rintro ⟨b, hb, rfl⟩
                rw [Equiv.swap_apply_def]; split_ifs <;> assumption
              · intro hy
                refine ⟨Equiv.swap x x' y, ?_, by simp⟩
                rw [Equiv.swap_apply_def]; split_ifs <;> assumption
            have L4 : ∀ m : Fin n, ∑ σ : Equiv.Perm (Fin n),
                revAux (e (σ m)) phaseChoice π [] (L σ) [] (fun _ => k) ≤
                  (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (k * a (m.val + 1)) := by
              intro m
              let C : ℕ → List (Finset (Fin n)) → Finset (Equiv.Perm (Fin n)) :=
                fun t past => Finset.univ.filter (fun σ => (L σ).take t = past)
              let β : ℕ → ℝ := fun s => if s / k ≤ m.val then 1 / ((n : ℝ) - ((s / k : ℕ) : ℝ)) else 0
              have hβ0 : ∀ s, 0 ≤ β s := by
                intro s; simp only [β]; split_ifs with h
                · have : s / k ≤ n := by have := m.2; omega
                  have : ((s / k : ℕ) : ℝ) < n := by exact_mod_cast (show s / k < n by have := m.2; omega)
                  apply le_of_lt; apply one_div_pos.2; linarith
                · exact le_refl _
              let B : ℕ → ℝ := fun t => ∑ s ∈ Finset.Ico t (n * k), β s
              have claim : ∀ d t, t + d = n * k → ∀ past hist (I : Fin n → ℕ),
                  ∑ σ ∈ C t past, revAux (e (σ m)) phaseChoice π past ((L σ).drop t) hist I ≤
                    ((C t past).card : ℝ) * B t := by
                intro d
                induction d with
                | zero =>
                  intro t ht past hist I
                  have : ∀ σ, (L σ).drop t = [] := by
                    intro σ; simp [L, ← ht]
                  simp [this, revAux, B, ← ht]
                | succ d ih =>
                  intro t ht past hist I
                  have htl : t < n * k := by omega
                  have ht' : (t + 1) + d = n * k := by omega
                  let g : Equiv.Perm (Fin n) → Finset (Fin n) := fun σ => phaseSeq k σ ⟨t, htl⟩
                  have hdrop : ∀ σ, (L σ).drop t = g σ :: (L σ).drop (t+1) := by
                    intro σ
                    rw [List.drop_eq_getElem_cons (by simp [L]; omega)]
                    simp [L, g]
                  have hF : ∀ z, (C t past).filter (fun σ => g σ = z) = C (t+1) (past ++ [z]) := by
                    intro z; ext σ
                    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
                    rw [List.take_succ, List.getElem?_eq_getElem (by simp [L]; omega)]
                    simp only [Option.toList_some]
                    constructor
                    · rintro ⟨h1, h2⟩; rw [h1, ← h2]; simp [L, g]
                    · intro h
                      have := List.append_inj' h (by simp)
                      refine ⟨this.1, ?_⟩
                      have h2 := this.2; simp only [List.cons.injEq, and_true] at h2
                      rw [← h2]; simp [L, g]
                  rw [← Finset.sum_fiberwise (C t past) g,
                    Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
                  push_cast
                  rw [Finset.sum_mul]
                  apply Finset.sum_le_sum
                  intro z _
                  rw [hF z]
                  have hgz : ∀ σ ∈ C (t+1) (past ++ [z]), g σ = z := by
                    intro σ hσ; rw [← hF z] at hσ; exact (Finset.mem_filter.1 hσ).2
                  have hBt : B t = β t + B (t+1) := Finset.sum_eq_sum_Ico_succ_bot htl _
                  set F := C (t+1) (past ++ [z]) with hFdef
                  set S := π.offer (past ++ [z]) hist with hS
                  set p : Fin n → ℝ := fun x => (phaseChoice z).prob S x with hp
                  have hp0 : ∀ x, 0 ≤ p x := fun x => (phaseChoice z).prob_nonneg S x
                  have hp1 : ∑ i ∈ S, p i ≤ 1 := (phaseChoice z).sum_prob_le_one S
                  have hstep : ∀ σ ∈ F, revAux (e (σ m)) phaseChoice π past ((L σ).drop t) hist I ≤
                      ((1 - ∑ i ∈ S, p i) * revAux (e (σ m)) phaseChoice π (past ++ [z]) ((L σ).drop (t+1))
                        (hist ++ [none]) I
                      + ∑ i ∈ S, p i * revAux (e (σ m)) phaseChoice π (past ++ [z]) ((L σ).drop (t+1))
                        (hist ++ [some i]) (Function.update I i (I i - 1)))
                      + p (σ m) := by
                    intro σ hσ
                    rw [hdrop σ, hgz σ hσ, revAux]
                    have hg : ∑ i ∈ S, p i * (if 0 < I i then e (σ m) i else 0) ≤ p (σ m) := by
                      calc ∑ i ∈ S, p i * (if 0 < I i then e (σ m) i else 0) ≤ ∑ i ∈ S, p i * e (σ m) i := by
                            apply Finset.sum_le_sum; intro i _
                            apply mul_le_mul_of_nonneg_left _ (hp0 i)
                            split_ifs
                            · exact le_rfl
                            · simp only [e]; split_ifs <;> norm_num
                        _ = if σ m ∈ S then p (σ m) else 0 := by
                            simp only [e, mul_ite, mul_one, mul_zero]; rw [Finset.sum_ite_eq']
                        _ ≤ p (σ m) := by split_ifs; exact le_rfl; exact hp0 _
                    simp only [mul_add, Finset.sum_add_distrib]
                    change (1 - ∑ i ∈ S, p i) * _ + (∑ i ∈ S, p i * (if 0 < I i then e (σ m) i else 0) + _) ≤ _
                    linarith
                  have hK : ∑ σ ∈ F, p (σ m) ≤ (F.card : ℝ) * β t := by
                    have hz : ∀ σ ∈ F, z = (Finset.univ.filter (fun j : Fin n => t / k ≤ j.val)).image σ := by
                      intro σ hσ; rw [← hgz σ hσ]; rfl
                    by_cases hlm : t / k ≤ m.val
                    · have hβt : β t = 1 / ((n:ℝ) - ((t/k : ℕ):ℝ)) := if_pos hlm
                      have hmz : ∀ σ ∈ F, σ m ∈ z := by
                        intro σ hσ; rw [hz σ hσ]; simp [hlm]
                      rcases F.eq_empty_or_nonempty with hFe | ⟨σ0, hσ0⟩
                      · simp [hFe]
                      have hlt' : t / k < n := (Nat.div_lt_iff_lt_mul hk).2 htl
                      have hzc : z.card = n - t / k := by
                        rw [hz σ0 hσ0, Finset.card_image_of_injective _ σ0.injective, ← Nat.card_Ico (t/k) n]
                        apply Finset.card_bij (fun j _ => j.val)
                        · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj; simp [hj, j.2]
                        · intro j1 _ j2 _ h; exact Fin.ext h
                        · intro v hv; simp only [Finset.mem_Ico] at hv
                          exact ⟨⟨v, hv.2⟩, by simp [hv.1], rfl⟩
                      have hswapF : ∀ x x', x ∈ z → x' ∈ z → ∀ σ ∈ F, Equiv.swap x x' * σ ∈ F := by
                        intro x x' hx hx' σ hσ
                        have hzσ := hz σ hσ
                        rw [hFdef, ← hF z] at hσ ⊢
                        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
                        have key : ∀ s : Fin (n*k), s.val ≤ t →
                            phaseSeq k (Equiv.swap x x' * σ) s = phaseSeq k σ s := by
                          intro s hs
                          simp only [phaseSeq, Equiv.Perm.coe_mul]
                          rw [← Finset.image_image]
                          have hsub : (Finset.univ.filter (fun j : Fin n => t / k ≤ j.val)).image σ ⊆
                              (Finset.univ.filter (fun j : Fin n => s.val / k ≤ j.val)).image σ := by
                            apply Finset.image_subset_image
                            intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                            intro h; exact le_trans (Nat.div_le_div_right hs) h
                          apply hswapset
                          · apply hsub; rw [← hzσ]; exact hx
                          · apply hsub; rw [← hzσ]; exact hx'
                        refine ⟨?_, ?_⟩
                        · rw [hL _ σ t (fun s hs => key s hs.le)]; exact hσ.1
                        · simp only [g]; rw [key ⟨t, htl⟩ le_rfl]; exact hσ.2
                      let N : Fin n → ℕ := fun x => (F.filter (fun σ => σ m = x)).card
                      have hN : ∀ x x', x ∈ z → x' ∈ z → N x ≤ N x' := by
                        intro x x' hx hx'
                        apply Finset.card_le_card_of_injOn (fun σ => Equiv.swap x x' * σ)
                        · intro σ hσ
                          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hσ ⊢
                          refine ⟨hswapF x x' hx hx' σ hσ.1, ?_⟩
                          simp [hσ.2]
                        · intro σ1 _ σ2 _ h; exact mul_left_cancel h
                      set x0 := σ0 m
                      have hx0 : x0 ∈ z := hmz σ0 hσ0
                      have hNeq : ∀ x ∈ z, N x = N x0 := fun x hx => le_antisymm (hN x x0 hx hx0) (hN x0 x hx0 hx)
                      have hcard : F.card = ∑ x ∈ z, N x := Finset.card_eq_sum_card_fiberwise (fun σ hσ => hmz σ hσ)
                      have hsumF : ∑ σ ∈ F, p (σ m) = ∑ x ∈ z, (N x : ℝ) * p x := by
                        rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ => σ m) hmz]
                        apply Finset.sum_congr rfl; intro x _
                        rw [Finset.sum_congr rfl (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]), Finset.sum_const,
                          nsmul_eq_mul]
                      have hpz : ∑ x ∈ z, p x ≤ 1 := by
                        calc ∑ x ∈ z, p x ≤ ∑ x ∈ Finset.univ, p x :=
                              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hp0 x)
                          _ = ∑ x ∈ S, p x := by
                              symm; apply Finset.sum_subset (Finset.subset_univ _)
                              intro x _ hx; exact (phaseChoice z).prob_eq_zero_of_not_mem S x hx
                          _ ≤ 1 := hp1
                      rw [hsumF, Finset.sum_congr rfl (fun x hx => by rw [hNeq x hx]), ← Finset.mul_sum, hcard,
                        Finset.sum_congr rfl (fun x hx => hNeq x hx), Finset.sum_const, hzc, hβt]
                      have hpos : (0:ℝ) < (n:ℝ) - ((t/k : ℕ):ℝ) := by
                        have : ((t/k : ℕ):ℝ) < n := by exact_mod_cast hlt'
                        linarith
                      rw [smul_eq_mul]; push_cast [Nat.cast_sub hlt'.le]
                      have hcancel : ((n:ℝ) - ((t/k : ℕ):ℝ)) * (N x0 : ℝ) * (1 / ((n:ℝ) - ((t/k : ℕ):ℝ))) = N x0 := by
                        field_simp
                      rw [hcancel]
                      have : (0:ℝ) ≤ N x0 := Nat.cast_nonneg _
                      nlinarith
                    · have h0 : ∀ σ ∈ F, p (σ m) = 0 := by
                        intro σ hσ
                        have hnot : σ m ∉ z := by
                          rw [hz σ hσ]; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
                          rintro ⟨j, hj, hjm⟩
                          have := σ.injective hjm; subst this; exact hlm hj
                        show (if σ m ∈ S ∩ z then _ else _) = 0
                        rw [if_neg (by simp [hnot])]
                      rw [Finset.sum_eq_zero h0]
                      exact mul_nonneg (Nat.cast_nonneg _) (hβ0 t)
                  calc ∑ σ ∈ F, revAux (e (σ m)) phaseChoice π past ((L σ).drop t) hist I
                      ≤ ∑ σ ∈ F, (((1 - ∑ i ∈ S, p i) * revAux (e (σ m)) phaseChoice π (past ++ [z]) ((L σ).drop (t+1))
                        (hist ++ [none]) I
                      + ∑ i ∈ S, p i * revAux (e (σ m)) phaseChoice π (past ++ [z]) ((L σ).drop (t+1))
                        (hist ++ [some i]) (Function.update I i (I i - 1)))
                      + p (σ m)) := Finset.sum_le_sum hstep
                    _ = (1 - ∑ i ∈ S, p i) * ∑ σ ∈ F, revAux (e (σ m)) phaseChoice π (past ++ [z]) ((L σ).drop (t+1))
                        (hist ++ [none]) I
                      + ∑ i ∈ S, p i * ∑ σ ∈ F, revAux (e (σ m)) phaseChoice π (past ++ [z]) ((L σ).drop (t+1))
                        (hist ++ [some i]) (Function.update I i (I i - 1))
                      + ∑ σ ∈ F, p (σ m) := by
                        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_comm (s := F)]
                        simp_rw [Finset.mul_sum]
                    _ ≤ (1 - ∑ i ∈ S, p i) * ((F.card : ℝ) * B (t+1)) + ∑ i ∈ S, p i * ((F.card : ℝ) * B (t+1))
                        + (F.card : ℝ) * β t := by
                        apply add_le_add (add_le_add _ _) hK
                        · exact mul_le_mul_of_nonneg_left (ih (t+1) ht' _ _ _) (sub_nonneg.2 hp1)
                        · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ih (t+1) ht' _ _ _) (hp0 i))
                    _ = (F.card : ℝ) * B t := by rw [hBt, ← Finset.sum_mul]; ring
              have h0 := claim (n * k) 0 (by simp) [] [] (fun _ => k)
              have hC : C 0 [] = Finset.univ := by ext σ; simp [C]
              have hB : B 0 = k * a (m.val + 1) := by
                have hγ : ∀ N, ∑ s ∈ Finset.range (N * k), β s =
                    k * ∑ l ∈ Finset.range N, (if l ≤ m.val then 1 / ((n:ℝ) - (l:ℝ)) else 0) := by
                  intro N
                  induction N with
                  | zero => simp
                  | succ N ih =>
                    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
                    have : ∀ x ∈ Finset.range k, β (N * k + x) =
                        (if N ≤ m.val then 1 / ((n:ℝ) - (N:ℝ)) else 0) := by
                      intro x hx
                      have hdiv : (N * k + x) / k = N := by
                        rw [add_comm, Nat.add_mul_div_right x N hk, Nat.div_eq_of_lt (Finset.mem_range.1 hx)]
                        simp
                      simp only [β, hdiv]
                    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                    ring
                have h1 : B 0 = ∑ s ∈ Finset.range (n * k), β s := by
                  simp only [B, Finset.range_eq_Ico]
                rw [h1, hγ n]
                congr 1
                rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
                have hf : (Finset.range n).filter (fun l => l ≤ m.val) = Finset.range (m.val + 1) := by
                  ext l; simp only [Finset.mem_filter, Finset.mem_range]; have := m.2; omega
                rw [hf]
                apply Finset.sum_nbij' (fun l => l + 1) (fun j => j - 1)
                · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at hj ⊢; omega
                · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at hj ⊢; omega
                · intro j hj; simp
                · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at hj ⊢; omega
                · intro j hj; push_cast; ring_nf
              simpa [hC, hB] using h0
            have hsum : ∑ σ, policyRevenue (fun _ => 1) (fun _ => k) phaseChoice π (phaseSeq k σ) ≤
                ∑ σ : Equiv.Perm (Fin n), (k : ℝ) * ∑ m : Fin n, min (a (m.val+1)) 1 := by
              have h1 : ∀ σ : Equiv.Perm (Fin n), policyRevenue (fun _ => 1) (fun _ => k) phaseChoice π (phaseSeq k σ)
                  = ∑ m : Fin n, revAux (e (σ m)) phaseChoice π [] (L σ) [] (fun _ => k) := by
                intro σ
                rw [policyRevenue, L1]
                exact (Equiv.sum_comp σ (fun x => revAux (e x) phaseChoice π [] (L σ) [] (fun _ => k))).symm
              simp_rw [h1]
              rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum,
                Finset.mul_sum]
              apply Finset.sum_le_sum
              intro m _
              have hA := L4 m
              have hB : ∑ σ : Equiv.Perm (Fin n),
                revAux (e (σ m)) phaseChoice π [] (L σ) [] (fun _ => k) ≤
                  (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * k := by
                calc _ ≤ ∑ σ : Equiv.Perm (Fin n), (k : ℝ) := Finset.sum_le_sum (fun σ _ => L2 _ _ _ _ _)
                  _ = _ := by simp
              have hk0 : (0 : ℝ) ≤ k := by positivity
              rcases le_total (a (m.val+1)) 1 with h | h
              · rw [min_eq_left h]; nlinarith
              · rw [min_eq_right h]; nlinarith
            obtain ⟨σ, -, hσ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
            have hlt : ∀ t : Fin (n * k), t.val / k < n := fun t => (Nat.div_lt_iff_lt_mul hk).2 t.2
            let f : Fin (n * k) → Fin n := fun t => σ ⟨t.val / k, hlt t⟩
            have hmem : ∀ t, f t ∈ phaseSeq k σ t := by
              intro t; simp [phaseSeq, f]
            have hprob : ∀ t i, (phaseChoice (phaseSeq k σ t)).prob {f t} i = if i = f t then 1 else 0 := by
              intro t i
              have : ({f t} : Finset (Fin n)) ∩ phaseSeq k σ t = {f t} := by
                rw [Finset.inter_eq_left, Finset.singleton_subset_iff]; exact hmem t
              simp only [phaseChoice, this, Finset.mem_singleton, Finset.card_singleton]
              simp
            have hobj : primalObj (fun _ => 1) Finset.univ phaseChoice (phaseSeq k σ)
                (fun t S => if S = {f t} then 1 else 0) = (n : ℝ) * k := by
              unfold primalObj
              have : ∀ t : Fin (n * k), ∑ S : Finset (Fin n), ∑ i : Fin n,
                  (1 : ℝ) * (phaseChoice (phaseSeq k σ t)).prob S i * (if S = {f t} then 1 else 0) = 1 := by
                intro t
                simp only [one_mul, mul_ite, mul_one, mul_zero]
                rw [Finset.sum_comm]
                simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hprob]
              rw [Finset.sum_congr rfl (fun t _ => this t)]
              simp
            have hrho : rhoN n * ((n : ℝ) * k) = k * ∑ m : Fin n, min (a (m.val+1)) 1 := by
              have hsw : ∑ j ∈ Finset.Icc 1 n, min (a j) 1 = ∑ m : Fin n, min (a (m.val+1)) 1 := by
                rw [Fin.sum_univ_eq_sum_range (fun m => min (a (m+1)) 1) n]
                apply Finset.sum_nbij' (fun j => j - 1) (fun m => m + 1)
                · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at hj ⊢; omega
                · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at hj ⊢; omega
                · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at hj ⊢; omega
                · intro j hj; simp
                · intro j hj; simp only [Finset.mem_Icc] at hj
                  congr 2; omega
              have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
              show (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n, min (a j) 1) * ((n : ℝ) * k) = _
              rw [hsw]; field_simp
            refine ⟨σ, fun t S => if S = {f t} then 1 else 0, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
            · intro t S _; dsimp only; split_ifs <;> norm_num
            · intro t; simp
            · intro i
              simp only [mul_ite, mul_one, mul_zero]
              have : ∀ t : Fin (n * k), ∑ S : Finset (Fin n),
                  (if S = {f t} then (phaseChoice (phaseSeq k σ t)).prob S i else 0) = if i = f t then 1 else 0 := by
                intro t; simp [hprob]
              rw [Finset.sum_congr rfl (fun t _ => this t), Finset.sum_boole]
              norm_cast
              calc (Finset.univ.filter (fun t : Fin (n * k) => i = f t)).card
                  ≤ (Finset.range k).card := by
                    apply Finset.card_le_card_of_injOn (fun t => t.val % k)
                    · intro t _; simp [Nat.mod_lt _ hk]
                    · intro t1 h1 t2 h2 h
                      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, f] at h1 h2
                      have h12 := h1.symm.trans h2
                      have hd : t1.val / k = t2.val / k := by
                        have := congrArg Fin.val (σ.injective h12); simpa using this
                      apply Fin.ext
                      rw [← Nat.div_add_mod t1.val k, ← Nat.div_add_mod t2.val k, hd]
                      simp only at h; rw [h]
                _ = k := Finset.card_range k
            · rw [hobj]; have : (0:ℝ) < n := by exact_mod_cast hn
              have : (0:ℝ) < k := by exact_mod_cast hk
              positivity
            · rw [hobj, hrho]; exact hσ
