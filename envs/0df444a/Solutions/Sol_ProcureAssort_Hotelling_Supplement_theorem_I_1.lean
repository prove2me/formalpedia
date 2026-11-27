-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.theorem_I_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:45:28.387728+00:00
-- url     : https://prove2.me/submissions/02d2d8f0-866c-4a25-9f3c-704f0ef2d45e

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Vertical

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 2 ≤ n) (alpha : Fin n → ℝ)
    (hAlpha : StrictMono alpha) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f)
    (hConditions : ∃ (θ : Profile Θ) (c : ℝ),
      (∀ (k : ℕ) (hk : k+2 < n),
        c + qualitySlope alpha (vvec Θ f θ) k (by omega) <
          qualitySlope alpha (vvec Θ f θ) (k+1) hk) ∧
      c < qualitySlope alpha (vvec Θ f θ) 0 (by omega) ∧
      qualitySlope alpha (vvec Θ f θ) (n-2) (by omega) < 1-c ∧
      (∀ i, 3 ≤ (Θ i).card) ∧
      (∀ i, ∀ a b : ℝ, Consecutive (Θ i) a b →
        virtualCost Θ f i b - virtualCost Θ f i a ≤ c * cstar alpha hn / 8)) :
    optDecLin Θ f (verticalGCS alpha) (simplex n) =
      optCent Θ f (verticalGCS alpha) (simplex n) ∧
    ValuesWellDefined Θ f (verticalGCS alpha) := by
      classical
      obtain ⟨hne, hpos, hfpos, hfsum⟩ := hTypes
      obtain ⟨θ0, c0, -, -, -, hcard, -⟩ := hConditions
      have hn0 : 0 < n := by omega
      -- linearity of interim
      have iadd : ∀ (g h : Profile Θ → ℝ) (i : Fin n) (c : ℝ),
          interim f (fun θ => g θ + h θ) i c = interim f g i c + interim f h i c := by
        intro g h i c
        unfold interim
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun θ _ => ?_
        split_ifs <;> ring
      have ismul : ∀ (k : ℝ) (g : Profile Θ → ℝ) (i : Fin n) (c : ℝ),
          interim f (fun θ => k * g θ) i c = k * interim f g i c := by
        intro k g i c
        unfold interim
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun θ _ => ?_
        split_ifs <;> ring
      have icongr : ∀ (g h : Profile Θ → ℝ) (i : Fin n) (c : ℝ),
          (∀ θ : Profile Θ, (θ i : ℝ) = c → g θ = h θ) → interim f g i c = interim f h i c := by
        intro g h i c H
        unfold interim
        refine Finset.sum_congr rfl fun θ _ => ?_
        split_ifs with hc
        · rw [H θ hc]
        · rfl
      have popos : ∀ (i : Fin n) (θ : Profile Θ), 0 < probOthers f i θ := by
        intro i θ
        unfold probOthers
        exact Finset.prod_pos fun j _ => hfpos j _ (θ j).2
      have inonneg : ∀ (g : Profile Θ → ℝ) (i : Fin n) (c : ℝ),
          (∀ θ : Profile Θ, (θ i : ℝ) = c → 0 ≤ g θ) → 0 ≤ interim f g i c := by
        intro g i c H
        unfold interim
        refine Finset.sum_nonneg fun θ _ => ?_
        split_ifs with hc
        · exact mul_nonneg (popos i θ).le (H θ hc)
        · exact le_rfl
      have ipos : ∀ (g : Profile Θ → ℝ) (i : Fin n) (c : ℝ), c ∈ Θ i →
          (∀ θ : Profile Θ, (θ i : ℝ) = c → 0 < g θ) → 0 < interim f g i c := by
        intro g i c hc H
        unfold interim
        refine Finset.sum_pos' (fun θ _ => ?_) ⟨Function.update θ0 i ⟨c, hc⟩, Finset.mem_univ _, ?_⟩
        · split_ifs with hc
          · exact mul_nonneg (popos i θ).le (H θ hc).le
          · exact le_rfl
        · have h1 : ((Function.update θ0 i ⟨c, hc⟩ i : ↥(Θ i)) : ℝ) = c := by simp
          rw [if_pos h1]
          exact mul_pos (popos i _) (H _ h1)
      have islice : ∀ (g : Profile Θ → ℝ) (i : Fin n) (a b : ℝ) (ha : a ∈ Θ i) (hb : b ∈ Θ i),
          interim f g i a = interim f (fun θ => g (Function.update θ i ⟨a, ha⟩)) i b := by
        intro g i a b ha hb
        unfold interim
        rw [← Finset.sum_filter, ← Finset.sum_filter]
        refine Finset.sum_nbij' (fun θ => Function.update θ i ⟨b, hb⟩)
          (fun θ => Function.update θ i ⟨a, ha⟩) ?_ ?_ ?_ ?_ ?_
        · intro θ _; simp
        · intro θ _; simp
        · intro θ hθ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
          have : (⟨a, ha⟩ : ↥(Θ i)) = θ i := Subtype.ext hθ.symm
          simp [this]
        · intro θ hθ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
          have : (⟨b, hb⟩ : ↥(Θ i)) = θ i := Subtype.ext hθ.symm
          simp [this]
        · intro θ hθ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
          have : (⟨a, ha⟩ : ↥(Θ i)) = θ i := Subtype.ext hθ.symm
          have h2 : probOthers f i (Function.update θ i ⟨b, hb⟩) = probOthers f i θ := by
            unfold probOthers
            refine Finset.prod_congr rfl fun j hj => ?_
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
          simp only [h2, Function.update_idem]
          simp [this]
      have iexp : ∀ (g : Profile Θ → ℝ) (i : Fin n),
          expect f g = ∑ c ∈ Θ i, f i c * interim f g i c := by
        intro g i
        unfold expect interim
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun θ _ => ?_
        rw [Finset.sum_eq_single (θ i : ℝ)]
        · rw [if_pos rfl]
          have : prob f θ = f i (θ i) * probOthers f i θ := by
            unfold prob probOthers
            rw [Finset.mul_prod_erase Finset.univ (fun j => f j (θ j)) (Finset.mem_univ i)]
          rw [this]; ring
        · intro b _ hb
          rw [if_neg (fun h => hb h.symm), mul_zero]
        · intro h; exact absurd (θ i).2 h
      have eadd : ∀ (g h : Profile Θ → ℝ), expect f (fun θ => g θ + h θ) = expect f g + expect f h := by
        intro g h
        unfold expect
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun θ _ => by ring
      have esub : ∀ (g h : Profile Θ → ℝ), expect f (fun θ => g θ - h θ) = expect f g - expect f h := by
        intro g h
        unfold expect
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun θ _ => by ring
      have esum : ∀ (g : Profile Θ → Fin n → ℝ),
          expect f (fun θ => ∑ i, g θ i) = ∑ i, expect f (fun θ => g θ i) := by
        intro g
        unfold expect
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun θ _ => by rw [Finset.mul_sum]
      have util : ∀ (x t : Profile Θ → Fin n → ℝ) (i : Fin n) (b a : ℝ),
          utility f x t i b a = interim f (fun θ => t θ i) i b
            - a * interim f (fun θ => x θ i) i b := by
        intro x t i b a
        unfold utility
        have := iadd (fun θ => t θ i) (fun θ => (-a) * x θ i) i b
        rw [ismul] at this
        rw [sub_eq_add_neg, ← neg_mul, ← this]
        congr 1; funext θ; ring
      -- closed form of GCS
      have hG : ∀ x : Fin n → ℝ, verticalGCS alpha x =
          ∑ i, alpha i * ((∑ j ∈ Finset.univ.filter (· ≤ i), x j)^2
            - (∑ j ∈ Finset.univ.filter (· < i), x j)^2) / 2 := by
        intro x
        unfold verticalGCS
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_mul_const, integral_id]
        ring
      -- Abel
      have abel : ∀ d : Fin n → ℝ, ∑ i, d i = 0 →
          ∑ i, alpha i * ((∑ j ∈ Finset.univ.filter (· ≤ i), d j)^2
            - (∑ j ∈ Finset.univ.filter (· < i), d j)^2) ≤ 0 := by
        intro d hd
        let e : ℕ → ℝ := fun k => ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), d j
        let a : ℕ → ℝ := fun k => alpha ⟨min k (n-1), by omega⟩
        have hmono : ∀ k, a k ≤ a (k+1) := by
          intro k
          apply hAlpha.monotone
          show min k (n-1) ≤ min (k+1) (n-1)
          omega
        have he0 : e 0 = 0 := by simp [e]
        have hen : e n = 0 := by
          rw [← hd]
          show ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < n), d j = _
          rw [Finset.filter_true_of_mem]
          intro j _; exact j.isLt
        have key : ∀ m, ∑ k ∈ Finset.range (m+1), a k * ((e (k+1))^2 - (e k)^2) ≤ a m * (e (m+1))^2 := by
          intro m
          induction m with
          | zero => simp [he0]
          | succ m ih =>
            rw [Finset.sum_range_succ]
            nlinarith [mul_nonneg (sub_nonneg.2 (hmono m)) (sq_nonneg (e (m+1)))]
        have h1 := key (n-1)
        have h2 : n - 1 + 1 = n := by omega
        rw [h2, hen, Finset.sum_range] at h1
        refine le_trans (le_of_eq ?_) (h1.trans (by simp))
        refine Finset.sum_congr rfl fun i _ => ?_
        have ha : a i.val = alpha i := by
          show alpha _ = alpha _
          congr 1
          apply Fin.ext
          show min i.val (n-1) = i.val
          have := i.isLt
          omega
        have hE : e i.val = ∑ j ∈ Finset.univ.filter (· < i), d j := by
          show ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), d j = _
          rfl
        have hD : e (i.val+1) = ∑ j ∈ Finset.univ.filter (· ≤ i), d j := by
          show ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val+1), d j = _
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
          omega
        rw [ha, hE, hD]
      -- every point of the simplex is a demand, at prices determined up to a shift
      have dem : ∀ x : Fin n → ℝ, x ∈ simplex n → ∃ π : Fin n → ℝ, ∀ s : ℝ,
          IsDemand (verticalGCS alpha) (simplex n) Finset.univ (fun i => π i + s) x := by
        intro x hx
        refine ⟨fun j => ∑ i, alpha i *
          ((∑ k ∈ Finset.univ.filter (· ≤ i), x k) * (if j ≤ i then 1 else 0)
            - (∑ k ∈ Finset.univ.filter (· < i), x k) * (if j < i then 1 else 0)), fun s => ?_⟩
        refine ⟨hx, fun i hi => absurd (Finset.mem_univ i) hi, fun z hz _ => ?_⟩
        have hd : ∑ i, (z i - x i) = 0 := by
          rw [Finset.sum_sub_distrib, hz.2, hx.2, sub_self]
        have hab := abel (fun i => z i - x i) hd
        have hle : ∀ i, ∑ k ∈ Finset.univ.filter (· ≤ i), (z k - x k) =
            ∑ k, (if k ≤ i then 1 else 0) * (z k - x k) := by
          intro i
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
        have hlt : ∀ i, ∑ k ∈ Finset.univ.filter (· < i), (z k - x k) =
            ∑ k, (if k < i then 1 else 0) * (z k - x k) := by
          intro i
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
        have hlin : ∑ j, (∑ i, alpha i *
          ((∑ k ∈ Finset.univ.filter (· ≤ i), x k) * (if j ≤ i then 1 else 0)
            - (∑ k ∈ Finset.univ.filter (· < i), x k) * (if j < i then 1 else 0))) * (z j - x j)
            = ∑ i, alpha i * ((∑ k ∈ Finset.univ.filter (· ≤ i), x k) *
                (∑ k ∈ Finset.univ.filter (· ≤ i), (z k - x k))
              - (∑ k ∈ Finset.univ.filter (· < i), x k) *
                (∑ k ∈ Finset.univ.filter (· < i), (z k - x k))) := by
          rw [Finset.sum_congr rfl (fun j _ => Finset.sum_mul _ _ _)]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hle, hlt, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        have hquad : verticalGCS alpha z - verticalGCS alpha x =
            ∑ i, alpha i * ((∑ k ∈ Finset.univ.filter (· ≤ i), x k) *
                (∑ k ∈ Finset.univ.filter (· ≤ i), (z k - x k))
              - (∑ k ∈ Finset.univ.filter (· < i), x k) *
                (∑ k ∈ Finset.univ.filter (· < i), (z k - x k)))
            + (∑ i, alpha i * ((∑ j ∈ Finset.univ.filter (· ≤ i), (z j - x j))^2
            - (∑ j ∈ Finset.univ.filter (· < i), (z j - x j))^2)) / 2 := by
          rw [hG, hG, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          ring
        rw [← hlin] at hquad
        unfold CS
        have e1 : ∀ (π : Fin n → ℝ), ∑ i, (π i + s) * z i - ∑ i, (π i + s) * x i =
            ∑ i, π i * (z i - x i) := by
          intro π
          have : ∑ i, s * z i - ∑ i, s * x i = 0 := by
            rw [← Finset.mul_sum, ← Finset.mul_sum, hz.2, hx.2, sub_self]
          rw [← Finset.sum_sub_distrib]
          rw [← Finset.sum_sub_distrib] at this
          rw [← add_zero (∑ i, π i * (z i - x i)), ← this, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        have e2 := e1 (fun j => ∑ i, alpha i *
          ((∑ k ∈ Finset.univ.filter (· ≤ i), x k) * (if j ≤ i then 1 else 0)
            - (∑ k ∈ Finset.univ.filter (· < i), x k) * (if j < i then 1 else 0)))
        linarith
      have hy : ∃ y ty : Profile Θ → Fin n → ℝ, (∀ θ, y θ ∈ simplex n) ∧
          (∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, a ≠ b → utility f y ty i b a < utility f y ty i a a) ∧
          (∀ i, ∀ a ∈ Θ i, 0 < utility f y ty i a a) := by
        obtain ⟨K, hK0, hK1, hK2⟩ : ∃ K : ℝ, 0 < K ∧ (∀ θ : Profile Θ, ∑ j, (θ j : ℝ) ≤ K) ∧
            (∀ i, ∀ c ∈ Θ i, c ≤ K) := by
          have hS : ∀ i, ∀ c ∈ Θ i, c ≤ ∑ c ∈ Θ i, c := fun i c hc =>
            Finset.single_le_sum (f := fun c : ℝ => c) (fun d hd => (hpos i d hd).le) hc
          have hS0 : ∀ i, 0 < ∑ c ∈ Θ i, c := fun i =>
            Finset.sum_pos (fun d hd => hpos i d hd) (hne i)
          have hS2 : ∀ i, ∑ c ∈ Θ i, c ≤ ∑ i, ∑ c ∈ Θ i, c := fun i =>
            Finset.single_le_sum (f := fun i => ∑ c ∈ Θ i, c) (fun j _ => (hS0 j).le)
              (Finset.mem_univ i)
          refine ⟨∑ i, ∑ c ∈ Θ i, c, (hS0 ⟨0, hn0⟩).trans_le (hS2 _), fun θ => ?_, fun i c hc =>
            (hS i c hc).trans (hS2 i)⟩
          exact Finset.sum_le_sum fun i _ => hS i _ (θ i).2
        have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
        obtain ⟨κ, hκ0, hκ⟩ : ∃ κ : ℝ, 0 < κ ∧ κ * (n * K) = 1 / n := by
          refine ⟨1 / n / (n * K), by positivity, ?_⟩
          field_simp
        have hyS : ∀ θ : Profile Θ,
            (fun i => 1 / (n:ℝ) + κ * (∑ j, (θ j : ℝ) - n * θ i)) ∈ simplex n := by
          intro θ
          constructor
          · intro i
            have h1 : 0 ≤ ∑ j, (θ j : ℝ) := Finset.sum_nonneg fun j _ => (hpos j _ (θ j).2).le
            have h2 := hK2 i _ (θ i).2
            have h3 : κ * (n * θ i) ≤ κ * (n * K) := by gcongr
            have h4 : 0 ≤ κ * ∑ j, (θ j : ℝ) := mul_nonneg hκ0.le h1
            show 0 ≤ 1 / (n:ℝ) + κ * (∑ j, (θ j : ℝ) - n * θ i)
            nlinarith
          · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [sub_self, mul_zero, add_zero]
            field_simp
        refine ⟨fun θ i => 1 / n + κ * (∑ j, (θ j : ℝ) - n * θ i),
          fun θ i => (K + κ * (n - 1) * K^2 + 1) - κ * (n - 1) * (θ i : ℝ)^2 / 2, hyS, ?_, ?_⟩
        · intro i a ha b hb hab
          unfold utility
          rw [islice _ i b a hb ha, ← sub_pos]
          have h1 := iadd (fun θ => ((K + κ * (n - 1) * K^2 + 1) - κ * (n - 1) * (θ i : ℝ)^2 / 2)
              - a * (1 / n + κ * (∑ j, (θ j : ℝ) - n * θ i)))
            (fun θ => (-1) * (((K + κ * (n - 1) * K^2 + 1)
              - κ * (n - 1) * ((Function.update θ i ⟨b, hb⟩ i : ↥(Θ i)) : ℝ)^2 / 2)
              - a * (1 / n + κ * (∑ j, ((Function.update θ i ⟨b, hb⟩ j : ↥(Θ j)) : ℝ)
                - n * ((Function.update θ i ⟨b, hb⟩ i : ↥(Θ i)) : ℝ))))) i a
          rw [ismul] at h1
          rw [sub_eq_add_neg, neg_eq_neg_one_mul, ← h1]
          apply ipos _ _ _ ha
          intro θ hθ
          have hsum : ∑ j, ((Function.update θ i ⟨b, hb⟩ j : ↥(Θ j)) : ℝ) =
              ∑ j, (θ j : ℝ) - a + b := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
              ← Finset.add_sum_erase Finset.univ (fun j => (θ j : ℝ)) (Finset.mem_univ i)]
            have : ∑ j ∈ Finset.univ.erase i, ((Function.update θ i ⟨b, hb⟩ j : ↥(Θ j)) : ℝ) =
                ∑ j ∈ Finset.univ.erase i, (θ j : ℝ) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
            rw [this]
            simp only [Function.update_self, hθ]
            ring
          rw [hsum]
          simp only [Function.update_self, hθ]
          have : 0 < κ * (n - 1) * (a - b)^2 / 2 := by
            have h1 : 0 < (a - b)^2 := by
              have := sub_ne_zero.2 hab
              positivity
            have h2 : (0:ℝ) < n - 1 := by linarith
            positivity
          refine this.trans_eq ?_
          ring
        · intro i a ha
          unfold utility
          apply ipos _ _ _ ha
          intro θ hθ
          have hs := hyS θ
          have hle1 : 1 / (n:ℝ) + κ * (∑ j, (θ j : ℝ) - n * θ i) ≤ 1 := by
            exact le_trans (Finset.single_le_sum
              (f := fun i => 1 / (n:ℝ) + κ * (∑ j, (θ j : ℝ) - n * θ i))
              (fun j _ => hs.1 j) (Finset.mem_univ i)) (le_of_eq hs.2)
          have ha0 := hpos i a ha
          have haK := hK2 i a ha
          have h1 : a * (1 / (n:ℝ) + κ * (∑ j, (θ j : ℝ) - n * θ i)) ≤ K := by
            calc _ ≤ a * 1 := by gcongr
              _ ≤ K := by linarith
          have h2 : κ * (n - 1) * (θ i : ℝ)^2 ≤ κ * (n - 1) * K^2 := by
            rw [hθ]
            have : (0:ℝ) < n - 1 := by linarith
            gcongr
          have h3 : 0 ≤ κ * (n - 1) * (θ i : ℝ)^2 := by
            have : (0:ℝ) < n - 1 := by linarith
            positivity
          show 0 < (K + κ * (n - 1) * K^2 + 1) - κ * (n - 1) * (θ i : ℝ)^2 / 2
              - a * (1 / n + κ * (∑ j, (θ j : ℝ) - n * θ i))
          linarith
      obtain ⟨y, ty, hyS, hyIC, hyIR⟩ := hy
      -- special profiles
      have hψ : ∃ ψ : (Σ i : Fin n, ↥(Θ i)) → Profile Θ, Function.Injective ψ ∧
          ∀ r, ψ r r.1 = r.2 := by
        have h2 : ∀ i, ∃ a b : ↥(Θ i), a ≠ b := by
          intro i
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < (Θ i).card by have := hcard i; omega)
          exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
        choose A B hAB using h2
        let i0 : Fin n := ⟨0, hn0⟩
        let W : (Σ i : Fin n, ↥(Θ i)) → Profile Θ := fun r j =>
          if r.2 = A r.1 then (if j = i0 then A j else B j) else (if j = i0 then B j else A j)
        refine ⟨fun r => Function.update (W r) r.1 r.2, ?_, fun r => by simp⟩
        rintro ⟨i, c⟩ ⟨j, d⟩ h
        by_cases hij : i = j
        · subst hij
          have := congrFun h i
          simp only [Function.update_self] at this
          rw [this]
        · exfalso
          have e1 := congrFun h i
          have e2 := congrFun h j
          have e3 : Function.update (W ⟨i, c⟩) i c i0 = Function.update (W ⟨j, d⟩) j d i0 := congrFun h i0
          simp only [Function.update_self] at e1 e2
          rw [Function.update_of_ne hij] at e1
          rw [Function.update_of_ne (Ne.symm hij)] at e2
          simp only [W] at e1 e2
          by_cases hc : c = A i <;> by_cases hd : d = A j
          · rw [if_pos hd] at e1
            rw [if_pos hc] at e2
            have hi : i = i0 := by
              by_contra hi; rw [if_neg hi, hc] at e1; exact hAB i e1
            have hj : j = i0 := by
              by_contra hj; rw [if_neg hj, hd] at e2; exact hAB j e2.symm
            exact hij (hi.trans hj.symm)
          · rw [if_neg hd] at e1
            rw [if_pos hc] at e2
            have hi : i ≠ i0 := by
              intro hi; rw [if_pos hi, hc] at e1; exact hAB i e1
            have hj : j ≠ i0 := by
              intro hj; rw [if_pos hj] at e2; exact hd e2.symm
            rw [Function.update_of_ne hi.symm, Function.update_of_ne hj.symm] at e3
            simp only [W, if_pos hc, if_neg hd, if_true] at e3
            exact hAB i0 e3
          · rw [if_pos hd] at e1
            rw [if_neg hc] at e2
            have hi : i ≠ i0 := by
              intro hi; rw [if_pos hi] at e1; exact hc e1
            have hj : j ≠ i0 := by
              intro hj; rw [if_pos hj, hd] at e2; exact hAB j e2.symm
            rw [Function.update_of_ne hi.symm, Function.update_of_ne hj.symm] at e3
            simp only [W, if_neg hc, if_pos hd, if_true] at e3
            exact hAB i0 e3.symm
          · rw [if_neg hd] at e1
            rw [if_neg hc] at e2
            have hi : i = i0 := by
              by_contra hi; rw [if_neg hi] at e1; exact hc e1
            have hj : j = i0 := by
              by_contra hj; rw [if_neg hj] at e2; exact hd e2.symm
            exact hij (hi.trans hj.symm)
      obtain ⟨ψ, hψinj, hψ⟩ := hψ
      have : Nonempty (Σ i : Fin n, ↥(Θ i)) := ⟨⟨⟨0, hn0⟩, θ0 _⟩⟩
      let z : Profile Θ → Fin n → ℝ := fun θ i => if i = (Function.invFun ψ θ).1 then 1 else 0
      have hzS : ∀ θ, z θ ∈ simplex n := by
        intro θ
        constructor
        · intro i
          simp only [z]
          split_ifs <;> norm_num
        · simp [z]
      -- the incidence matrix
      let N : (Profile Θ → Fin n → ℝ) →
          Matrix (Σ i : Fin n, ↥(Θ i)) (Σ i : Fin n, ↥(Θ i)) ℝ := fun x => Matrix.of fun r s =>
        if ((ψ s r.1 : ↥(Θ r.1)) : ℝ) = r.2 then probOthers f r.1 (ψ s) * x (ψ s) r.1 else 0
      have hNz : (N z).det ≠ 0 := by
        have hdiag : N z = Matrix.diagonal (fun r => probOthers f r.1 (ψ r)) := by
          ext r s
          simp only [N, Matrix.of_apply, z, Function.leftInverse_invFun hψinj s]
          by_cases hrs : r = s
          · subst hrs
            simp [hψ]
          · rw [Matrix.diagonal_apply_ne _ hrs]
            by_cases h1 : r.1 = s.1
            · rw [if_neg]
              intro h2
              apply hrs
              obtain ⟨i, c⟩ := r
              obtain ⟨j, d⟩ := s
              simp only at h1
              subst h1
              have := hψ ⟨i, d⟩
              simp only at this h2
              rw [this] at h2
              rw [Subtype.ext h2]
            · simp [h1]
        rw [hdiag, Matrix.det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun r _ => (popos _ _).ne'
      -- solvability
      have hsolve : ∀ x : Profile Θ → Fin n → ℝ, (N x).det ≠ 0 →
          ∀ R : (i : Fin n) → ℝ → ℝ, ∃ s : Profile Θ → ℝ, ∀ i, ∀ c ∈ Θ i,
            interim f (fun θ => s θ * x θ i) i c = R i c := by
        intro x hx R
        let w := (N x)⁻¹.mulVec (fun r => R r.1 r.2)
        have hw : (N x).mulVec w = fun r => R r.1 r.2 := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hx),
            Matrix.one_mulVec]
        refine ⟨fun θ => ∑ r, if θ = ψ r then w r else 0, fun i c hc => ?_⟩
        have := congrFun hw ⟨i, ⟨c, hc⟩⟩
        simp only at this
        rw [← this]
        unfold interim Matrix.mulVec dotProduct
        have e : ∀ θ : Profile Θ, (if (θ i : ℝ) = c then probOthers f i θ *
            ((∑ r, if θ = ψ r then w r else 0) * x θ i) else 0) =
            ∑ r, if θ = ψ r then (if (θ i : ℝ) = c then probOthers f i θ * x θ i else 0) * w r
              else 0 := by
          intro θ
          split_ifs with h
          · rw [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            split_ifs <;> ring
          · simp
        rw [Finset.sum_congr rfl fun θ _ => e θ, Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_ite_eq' Finset.univ (ψ r), if_pos (Finset.mem_univ _)]
        rfl
      have hGcont : Continuous (verticalGCS alpha) := by
        rw [show verticalGCS alpha = _ from funext hG]
        fun_prop
      have main : ∀ x t : Profile Θ → Fin n → ℝ, IsCentFeasible f (simplex n) x t → ∀ δ > 0,
          ∃ (q : Profile Θ → Finset (Fin n)) (p x' : Profile Θ → Fin n → ℝ),
            IsDecLinFeasible f (verticalGCS alpha) (simplex n) q p x' ∧
            centObj f (verticalGCS alpha) x t - δ < decLinObj f (verticalGCS alpha) p x' := by
        rintro x t ⟨hIC, hIR, hF⟩ δ hδ
        let X : ℝ → Profile Θ → Fin n → ℝ := fun e θ i =>
          (1 - e) * x θ i + (e * (1 - e) * y θ i + e^2 * z θ i)
        let T : ℝ → Profile Θ → Fin n → ℝ := fun e θ i =>
          (1 - e) * t θ i + e * (1 - e) * ty θ i
        have hutil : ∀ e i b a, utility f (X e) (T e) i b a =
            (1 - e) * utility f x t i b a + (e * (1 - e) * utility f y ty i b a
              + e^2 * utility f z (fun _ _ => 0) i b a) := by
          intro e i b a
          unfold utility
          rw [← ismul, ← ismul, ← ismul, ← iadd, ← iadd]
          congr 1
          funext θ
          simp only [X, T]
          ring
        have hXS : ∀ e, 0 < e → e < 1 → ∀ θ, X e θ ∈ simplex n := by
          intro e he0 he1 θ
          constructor
          · intro i
            have h1 := (hF θ).1 i
            have h2 := (hyS θ).1 i
            have h3 := (hzS θ).1 i
            have h4 : 0 < 1 - e := by linarith
            show 0 ≤ (1 - e) * x θ i + (e * (1 - e) * y θ i + e^2 * z θ i)
            positivity
          · show ∑ i, ((1 - e) * x θ i + (e * (1 - e) * y θ i + e^2 * z θ i)) = 1
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              ← Finset.mul_sum, (hF θ).2, (hyS θ).2, (hzS θ).2]
            ring
        -- small-ε facts
        have small : ∀ u v : ℝ, 0 < u → ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0),
            0 ≤ e * (1 - e) * u + e^2 * v := by
          intro u v hu
          have hc : Filter.Tendsto (fun e : ℝ => (1 - e) * u + e * v) (nhdsWithin 0 (Set.Ioi 0))
              (nhds u) := by
            have : Continuous (fun e : ℝ => (1 - e) * u + e * v) := by fun_prop
            have h := this.tendsto 0
            simp only [sub_zero, one_mul, zero_mul, add_zero] at h
            exact h.mono_left nhdsWithin_le_nhds
          filter_upwards [hc.eventually (lt_mem_nhds hu), self_mem_nhdsWithin] with e h1 h2
          have h2' : (0:ℝ) < e := h2
          have := mul_pos h2' h1
          nlinarith
        have hlt1 : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0), e < 1 :=
          nhdsWithin_le_nhds (gt_mem_nhds one_pos)
        have hICe : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i,
            utility f (X e) (T e) i b a ≤ utility f (X e) (T e) i a a := by
          rw [Filter.eventually_all]
          intro i
          rw [Filter.eventually_all_finset]
          intro a ha
          rw [Filter.eventually_all_finset]
          intro b hb
          by_cases hab : a = b
          · subst hab
            exact Filter.Eventually.of_forall fun _ => le_rfl
          · filter_upwards [small _ (utility f z (fun _ _ => 0) i a a - utility f z (fun _ _ => 0) i b a)
              (sub_pos.2 (hyIC i a ha b hb hab)), hlt1] with e h1 h2
            rw [hutil, hutil]
            have h3 := mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 (hIC i a ha b hb))
            nlinarith
        have hIRe : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ i, ∀ a ∈ Θ i,
            0 ≤ utility f (X e) (T e) i a a := by
          rw [Filter.eventually_all]
          intro i
          rw [Filter.eventually_all_finset]
          intro a ha
          filter_upwards [small _ (utility f z (fun _ _ => 0) i a a) (hyIR i a ha), hlt1] with e h1 h2
          rw [hutil]
          have h3 := mul_nonneg (sub_nonneg.2 h2.le) (hIR i a ha)
          linarith
        have hobj : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0),
            centObj f (verticalGCS alpha) x t - δ < centObj f (verticalGCS alpha) (X e) (T e) := by
          have hc : Continuous (fun e => centObj f (verticalGCS alpha) (X e) (T e)) := by
            unfold centObj expect
            refine continuous_finset_sum _ fun θ _ => ?_
            refine continuous_const.mul (Continuous.sub ?_ ?_)
            · refine hGcont.comp (continuous_pi fun i => ?_)
              simp only [X]
              fun_prop
            · refine continuous_finset_sum _ fun i _ => ?_
              simp only [T]
              fun_prop
          have h0 : centObj f (verticalGCS alpha) (X 0) (T 0) = centObj f (verticalGCS alpha) x t := by
            congr 1 <;> (funext θ i; simp [X, T])
          have h := (hc.tendsto 0).eventually (lt_mem_nhds (show
            centObj f (verticalGCS alpha) x t - δ < centObj f (verticalGCS alpha) (X 0) (T 0) by
              rw [h0]; linarith))
          exact nhdsWithin_le_nhds h
        -- determinant polynomial
        let M : Matrix (Σ i : Fin n, ↥(Θ i)) (Σ i : Fin n, ↥(Θ i)) (Polynomial ℝ) :=
          Matrix.of fun r s => (1 - Polynomial.X) * Polynomial.C (N x r s) +
            (Polynomial.X * (1 - Polynomial.X) * Polynomial.C (N y r s) +
              Polynomial.X^2 * Polynomial.C (N z r s))
        have hMe : ∀ e, M.det.eval e = (N (X e)).det := by
          intro e
          have h1 := RingHom.map_det (Polynomial.evalRingHom e) M
          rw [Polynomial.coe_evalRingHom] at h1
          rw [h1]
          congr 1
          ext r s
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply,
            Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
            Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow, N, X]
          split_ifs <;> ring
        have hM0 : M.det ≠ 0 := by
          intro h
          have h1 := hMe 1
          rw [h, Polynomial.eval_zero] at h1
          apply hNz
          rw [h1]
          congr 2
          funext θ i
          simp [X]
        have hev := hICe.and (hIRe.and (hobj.and hlt1))
        obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
        obtain ⟨e, heI, heR⟩ := ((Set.Ioo_infinite hu).diff
          (Polynomial.finite_setOf_isRoot hM0)).nonempty
        obtain ⟨gIC, gIR, gobj, ge1⟩ := hsub heI
        have ge0 : 0 < e := heI.1
        have hdet : (N (X e)).det ≠ 0 := by
          rw [← hMe]; exact heR
        choose π hπ using fun θ => dem (X e θ) (hXS e ge0 ge1 θ)
        obtain ⟨s, hs⟩ := hsolve (X e) hdet (fun i c => interim f (fun θ => T e θ i) i c
          - interim f (fun θ => π θ i * X e θ i) i c)
        have htr : ∀ i, ∀ c ∈ Θ i, interim f (fun θ => (π θ i + s θ) * X e θ i) i c =
            interim f (fun θ => T e θ i) i c := by
          intro i c hc
          have h1 := hs i c hc
          have h2 := iadd (fun θ => π θ i * X e θ i) (fun θ => s θ * X e θ i) i c
          have h3 : (fun θ => (π θ i + s θ) * X e θ i) =
            fun θ => π θ i * X e θ i + s θ * X e θ i := by funext θ; ring
          rw [h3, h2, h1]; ring
        have hut : ∀ i, ∀ b ∈ Θ i, ∀ a, utility f (X e) (fun θ i => (π θ i + s θ) * X e θ i) i b a =
            utility f (X e) (T e) i b a := by
          intro i b hb a
          rw [util, util, htr i b hb]
        refine ⟨fun _ => Finset.univ, fun θ i => π θ i + s θ, X e, ⟨⟨?_, ?_, hXS e ge0 ge1⟩,
          fun θ => hπ θ (s θ)⟩, ?_⟩
        · intro i a ha b hb
          have h1 := gIC i a ha b hb
          rw [← hut i b hb, ← hut i a ha] at h1
          exact h1
        · intro i a ha
          have h1 := gIR i a ha
          rw [← hut i a ha] at h1
          exact h1
        · refine gobj.trans_eq ?_
          unfold centObj decLinObj CS
          rw [esub, esub, esum, esum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [iexp _ i, iexp _ i]
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [htr i c hc]
      have hprob : ∀ θ : Profile Θ, 0 ≤ prob f θ := fun θ =>
        Finset.prod_nonneg fun j _ => (hfpos j _ (θ j).2).le
      have hCne : IsCentFeasible f (simplex n) y ty := by
        refine ⟨fun i a ha b hb => ?_, fun i a ha => (hyIR i a ha).le, hyS⟩
        by_cases hab : a = b
        · rw [hab]
        · exact (hyIC i a ha b hb hab).le
      obtain ⟨q0, p0, x0, hD0, -⟩ := main y ty hCne 1 one_pos
      have hCb : BddAbove {r | ∃ x t : Profile Θ → Fin n → ℝ,
          IsCentFeasible f (simplex n) x t ∧ r = centObj f (verticalGCS alpha) x t} := by
        refine ⟨expect f (fun _ : Profile Θ => ∑ i, |alpha i|), ?_⟩
        rintro r ⟨x, t, ⟨hIC, hIR, hF⟩, rfl⟩
        unfold centObj
        rw [esub, esum]
        have h1 : 0 ≤ ∑ i, expect f (fun θ => t θ i) := by
          refine Finset.sum_nonneg fun i _ => ?_
          rw [iexp _ i]
          refine Finset.sum_nonneg fun c hc => mul_nonneg (hfpos i c hc).le ?_
          have h2 := hIR i c hc
          rw [util] at h2
          have h3 := mul_nonneg (hpos i c hc).le (inonneg (fun θ => x θ i) i c
            (fun θ _ => (hF θ).1 i))
          linarith
        have h2 : expect f (fun θ => verticalGCS alpha (x θ)) ≤
            expect f (fun _ : Profile Θ => ∑ i, |alpha i|) := by
          unfold expect
          refine Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left ?_ (hprob θ)
          show verticalGCS alpha (x θ) ≤ ∑ i, |alpha i|
          rw [hG]
          refine Finset.sum_le_sum fun i _ => ?_
          have hb : ∀ S : Finset (Fin n), 0 ≤ ∑ j ∈ S, x θ j ∧ ∑ j ∈ S, x θ j ≤ 1 := by
            intro S
            refine ⟨Finset.sum_nonneg fun j _ => (hF θ).1 j, ?_⟩
            rw [← (hF θ).2]
            exact Finset.sum_le_univ_sum_of_nonneg (fun j => (hF θ).1 j)
          obtain ⟨u0, u1⟩ := hb (Finset.univ.filter (· ≤ i))
          obtain ⟨l0, l1⟩ := hb (Finset.univ.filter (· < i))
          generalize (∑ j ∈ Finset.univ.filter (· ≤ i), x θ j) = U at *
          generalize (∑ j ∈ Finset.univ.filter (· < i), x θ j) = L at *
          have hUL : |(U^2 - L^2) / 2| ≤ 1 := by
            rw [abs_le]; constructor <;> nlinarith
          calc alpha i * (U^2 - L^2) / 2 = alpha i * ((U^2 - L^2) / 2) := by ring
            _ ≤ |alpha i * ((U^2 - L^2) / 2)| := le_abs_self _
            _ = |alpha i| * |(U^2 - L^2) / 2| := abs_mul _ _
            _ ≤ |alpha i| * 1 := by gcongr
            _ = |alpha i| := mul_one _
        linarith
      have hDC : {r | ∃ (q : Profile Θ → Finset (Fin n)) (p x : Profile Θ → Fin n → ℝ),
          IsDecLinFeasible f (verticalGCS alpha) (simplex n) q p x ∧
            r = decLinObj f (verticalGCS alpha) p x} ⊆
          {r | ∃ x t : Profile Θ → Fin n → ℝ,
          IsCentFeasible f (simplex n) x t ∧ r = centObj f (verticalGCS alpha) x t} := by
        rintro r ⟨q, p, x, hD, rfl⟩
        exact ⟨x, fun θ i => p θ i * x θ i, hD.1, rfl⟩
      refine ⟨le_antisymm ?_ ?_, ⟨_, y, ty, hCne, rfl⟩, hCb, ⟨_, q0, p0, x0, hD0, rfl⟩,
        hCb.mono hDC⟩
      · exact csSup_le_csSup hCb ⟨_, q0, p0, x0, hD0, rfl⟩ hDC
      · refine csSup_le ⟨_, y, ty, hCne, rfl⟩ ?_
        rintro r ⟨x, t, hC, rfl⟩
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        obtain ⟨q, p, x', hD, hlt⟩ := main x t hC δ hδ
        have : decLinObj f (verticalGCS alpha) p x' ≤
            optDecLin Θ f (verticalGCS alpha) (simplex n) :=
          le_csSup (hCb.mono hDC) ⟨q, p, x', hD, rfl⟩
        linarith
