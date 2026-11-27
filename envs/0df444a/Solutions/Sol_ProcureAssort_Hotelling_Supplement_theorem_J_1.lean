-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.theorem_J_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:45:53.351402+00:00
-- url     : https://prove2.me/submissions/bb29f989-d581-46ce-ac84-6f9a005ecfd7

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Multiproduct

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 0 < n) (m : Fin n → ℕ) (hm : ∀ i, 0 < m i)
    (M : QuadraticMarket (Product m)) (hM : M.Valid)
    (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ)
    (hDiff : IncreasingCostDifferences m cost) :
    ∃ (c : ℕ) (d : ℝ), 0 < d ∧
      ∀ (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ), ValidTypes Θ f →
      (∀ i p, StrictMonoOn (multiVirtual m Θ f cost i p) (↑(Θ i) : Set ℝ)) →
        (∃ θ : Profile Θ, multiQ m Θ f M cost θ = Finset.univ ∧
          ∀ θ' : Profile Θ, TypeDistanceLE Θ θ θ' d →
            multiQ m Θ f M cost θ' = Finset.univ) →
      (∀ i, c ≤ (Θ i).card) →
      (∀ i, ∀ a b : ℝ, Consecutive (Θ i) a b →
        ∀ p : Fin (m i), multiVirtual m Θ f cost i p b - multiVirtual m Θ f cost i p a ≤ d/3) →
      sSup (multiDecValues m Θ f M cost) = sSup (multiCentValues m Θ f M cost) ∧
        (multiCentValues m Θ f M cost).Nonempty ∧ BddAbove (multiCentValues m Θ f M cost) ∧
        (multiDecValues m Θ f M cost).Nonempty ∧ BddAbove (multiDecValues m Θ f M cost) := by
          refine ⟨2, 1, one_pos, ?_⟩
          intro Θ f hV hSM hrob hc hcons
          classical
          obtain ⟨hne, hpos, hfpos, hsum⟩ := hV
          have hDC : multiDecValues m Θ f M cost ⊆ multiCentValues m Θ f M cost := by
            rintro r ⟨q, p, x, ⟨hF, _⟩, rfl⟩
            exact ⟨x, _, hF, rfl⟩
          have hS : ∀ (i : Fin n) (b : ℝ), b ∈ Θ i →
              ∑ θ : Profile Θ, (if (θ i : ℝ) = b then probOthers f i θ else 0) = 1 := by
            intro i b hb
            let h : (j : Fin n) → ℝ → ℝ := fun j c => if j = i then (if c = b then 1 else 0) else f j c
            have h1 : ∀ θ : Profile Θ, (if (θ i : ℝ) = b then probOthers f i θ else 0)
                = ∏ j, h j (θ j) := by
              intro θ
              rw [← Finset.mul_prod_erase Finset.univ (fun j => h j (θ j)) (Finset.mem_univ i)]
              have : ∏ j ∈ Finset.univ.erase i, h j (θ j) = probOthers f i θ := by
                unfold probOthers
                apply Finset.prod_congr rfl
                intro j hj
                simp [h, Finset.ne_of_mem_erase hj]
              rw [this]
              by_cases hθ : (θ i : ℝ) = b <;> simp [h, hθ]
            simp_rw [h1]
            rw [← Fintype.prod_sum (fun j (c : ↥(Θ j)) => h j c)]
            apply Finset.prod_eq_one
            intro j _
            rw [Finset.sum_coe_sort (Θ j) (h j)]
            by_cases hji : j = i
            · subst hji
              simp [h, hb]
            · simp [h, hji, hsum j]
          have hexp : ∀ (i : Fin n) (g : Profile Θ → ℝ),
              expect f g = ∑ a ∈ Θ i, f i a * interim f g i a := by
            intro i g
            unfold expect interim
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro θ _
            rw [Finset.sum_eq_single_of_mem (θ i : ℝ) (θ i).2]
            · simp only [if_true]
              unfold prob probOthers
              rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (θ j)) (Finset.mem_univ i)]
              ring
            · intro a _ ha
              simp [Ne.symm ha]
          have hconst : ∀ (i : Fin n) (b : ℝ), b ∈ Θ i → ∀ (g : Profile Θ → ℝ) (G : ℝ),
              (∀ θ : Profile Θ, (θ i : ℝ) = b → g θ = G) → interim f g i b = G := by
            intro i b hb g G hg
            unfold interim
            have : ∀ θ : Profile Θ, (if (θ i : ℝ) = b then probOthers f i θ * g θ else 0)
                = (if (θ i : ℝ) = b then probOthers f i θ else 0) * G := by
              intro θ
              by_cases hθ : (θ i : ℝ) = b
              · simp [hθ, hg θ hθ]
              · simp [hθ]
            simp_rw [this]
            rw [← Finset.sum_mul, hS i b hb, one_mul]
          set K : ℝ := ∑ i, ∑ p : Fin (m i), ∑ a ∈ Θ i, |cost i p a| with hKdef
          have hK : ∀ i (p : Fin (m i)) a, a ∈ Θ i → |cost i p a| ≤ K := by
            intro i p a ha
            have h1 : |cost i p a| ≤ ∑ a ∈ Θ i, |cost i p a| :=
              Finset.single_le_sum (f := fun a => |cost i p a|) (fun _ _ => abs_nonneg _) ha
            have h2 : ∑ a ∈ Θ i, |cost i p a| ≤ ∑ p : Fin (m i), ∑ a ∈ Θ i, |cost i p a| :=
              Finset.single_le_sum (f := fun p => ∑ a ∈ Θ i, |cost i p a|)
                (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ p)
            have h3 : ∑ p : Fin (m i), ∑ a ∈ Θ i, |cost i p a| ≤ K :=
              Finset.single_le_sum (f := fun i => ∑ p : Fin (m i), ∑ a ∈ Θ i, |cost i p a|)
                (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
                (Finset.mem_univ i)
            linarith
          let θ0 : Profile Θ := fun i => ⟨(hne i).choose, (hne i).choose_spec⟩
          have hDne : (multiDecValues m Θ f M cost).Nonempty := by
            let j0 : Product m := ⟨⟨0, hn⟩, ⟨0, hm _⟩⟩
            let x0 : Product m → ℝ := fun k => if k = j0 then 1 else 0
            have hx0 : x0 ∈ productSimplex (Product m) := by
              refine ⟨fun k => by simp only [x0]; split_ifs <;> norm_num, ?_⟩
              simp [x0]
            refine ⟨_, fun _ => {j0}, fun _ _ => K, fun _ => x0, ⟨⟨?_, ?_, fun _ => hx0⟩, ?_⟩, rfl⟩
            · intro i a ha b hb
              unfold multiUtility
              have e : ∀ c ∈ Θ i, interim f (fun θ => multiTransfer m Θ (fun _ _ => K) (fun _ => x0) θ i
                  - ∑ p, cost i p a * (fun _ => x0) θ ⟨i, p⟩) i c
                  = multiTransfer m Θ (fun _ _ => K) (fun _ => x0) θ0 i - ∑ p, cost i p a * x0 ⟨i, p⟩ :=
                fun c hc => hconst i c hc _ _ (fun θ _ => rfl)
              rw [e b hb, e a ha]
            · intro i a ha
              unfold multiUtility
              have e : ∀ c ∈ Θ i, interim f (fun θ => multiTransfer m Θ (fun _ _ => K) (fun _ => x0) θ i
                  - ∑ p, cost i p a * (fun _ => x0) θ ⟨i, p⟩) i c
                  = multiTransfer m Θ (fun _ _ => K) (fun _ => x0) θ0 i - ∑ p, cost i p a * x0 ⟨i, p⟩ :=
                fun c hc => hconst i c hc _ _ (fun θ _ => rfl)
              rw [e a ha]
              unfold multiTransfer
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_nonneg
              intro p _
              have := hK i p a ha
              have hx : 0 ≤ x0 ⟨i, p⟩ := by simp only [x0]; split_ifs <;> norm_num
              have := le_abs_self (cost i p a)
              nlinarith
            · intro θ
              refine ⟨hx0, ?_, ?_⟩
              · intro k hk
                simp only [Finset.mem_singleton] at hk
                simp [x0, hk]
              · intro y hy hy0
                have : y = x0 := by
                  funext k
                  by_cases hk : k = j0
                  · subst hk
                    have h1 := hy.2
                    rw [Finset.sum_eq_single j0 (fun b _ hb => hy0 b (by simpa using hb)) (by simp)] at h1
                    simp [x0, h1]
                  · simp [x0, hk, hy0 k (by simpa using hk)]
                rw [this]
          have hprob1 : ∑ θ : Profile Θ, prob f θ = 1 := by
            unfold prob
            rw [← Fintype.prod_sum (fun j (c : ↥(Θ j)) => f j c)]
            apply Finset.prod_eq_one
            intro j _
            rw [Finset.sum_coe_sort (Θ j) (f j)]
            exact hsum j
          have hprob0 : ∀ θ : Profile Θ, 0 ≤ prob f θ := fun θ =>
            Finset.prod_nonneg (fun j _ => (hfpos j _ (θ j).2).le)
          have hcongr : ∀ i (a : ℝ) (g g' : Profile Θ → ℝ),
              (∀ θ : Profile Θ, (θ i : ℝ) = a → g θ = g' θ) → interim f g i a = interim f g' i a := by
            intro i a g g' h
            unfold interim
            apply Finset.sum_congr rfl
            intro θ _
            split_ifs with hθ
            · rw [h θ hθ]
            · rfl
          set B : ℝ := ∑ k, |M.c k| + (∑ k, ∑ l, |M.D k l|) / 2 + ∑ i, ∑ p : Fin (m i), K with hB
          have hgcs : ∀ (θ : Profile Θ) (y : Product m → ℝ), y ∈ productSimplex (Product m) →
              M.gcs y - ∑ i, ∑ p : Fin (m i), cost i p (θ i) * y ⟨i, p⟩ ≤ B := by
            intro θ y hy
            have hy0 : ∀ k, 0 ≤ y k := hy.1
            have hy1 : ∀ k, y k ≤ 1 := by
              intro k
              rw [← hy.2]
              exact Finset.single_le_sum (fun j _ => hy0 j) (Finset.mem_univ k)
            unfold QuadraticMarket.gcs
            have h1 : ∑ k, M.c k * y k ≤ ∑ k, |M.c k| := by
              apply Finset.sum_le_sum
              intro k _
              have := hy0 k; have := hy1 k
              have := le_abs_self (M.c k); have := neg_abs_le (M.c k)
              nlinarith [abs_nonneg (M.c k)]
            have h2 : -(∑ k, ∑ l, y k * M.D k l * y l) ≤ ∑ k, ∑ l, |M.D k l| := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_le_sum
              intro k _
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_le_sum
              intro l _
              have := hy0 k; have := hy1 k; have := hy0 l; have := hy1 l
              have := le_abs_self (M.D k l); have := neg_abs_le (M.D k l)
              have hyy : 0 ≤ y k * y l := mul_nonneg (hy0 k) (hy0 l)
              have hyy1 : y k * y l ≤ 1 := by nlinarith
              nlinarith [abs_nonneg (M.D k l)]
            have h3 : -(∑ i, ∑ p : Fin (m i), cost i p (θ i) * y ⟨i, p⟩) ≤ ∑ i, ∑ p : Fin (m i), K := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_le_sum
              intro i _
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_le_sum
              intro p _
              have hk := hK i p (θ i) (θ i).2
              have := hy0 ⟨i, p⟩; have := hy1 ⟨i, p⟩
              have := le_abs_self (cost i p (θ i)); have := neg_abs_le (cost i p (θ i))
              nlinarith [abs_nonneg (cost i p (θ i))]
            linarith
          have hCbdd : BddAbove (multiCentValues m Θ f M cost) := by
            refine ⟨B, ?_⟩
            rintro r ⟨x, t, ⟨hIC, hIR, hX⟩, rfl⟩
            have hsplit : multiCentObj m Θ f M x t =
                expect f (fun θ => M.gcs (x θ) - ∑ i, ∑ p : Fin (m i), cost i p (θ i) * x θ ⟨i, p⟩) -
                ∑ i, expect f (fun θ => t θ i - ∑ p : Fin (m i), cost i p (θ i) * x θ ⟨i, p⟩) := by
              unfold multiCentObj expect
              rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro θ _
              rw [← Finset.mul_sum, Finset.sum_sub_distrib]
              ring
            have hnn : ∀ i, 0 ≤ expect f (fun θ => t θ i - ∑ p : Fin (m i), cost i p (θ i) * x θ ⟨i, p⟩) := by
              intro i
              rw [hexp i]
              apply Finset.sum_nonneg
              intro a ha
              apply mul_nonneg (hfpos i a ha).le
              rw [hcongr i a _ (fun θ => t θ i - ∑ p : Fin (m i), cost i p a * x θ ⟨i, p⟩)
                (fun θ hθ => by rw [hθ])]
              exact hIR i a ha
            have hle : expect f (fun θ => M.gcs (x θ) - ∑ i, ∑ p : Fin (m i), cost i p (θ i) * x θ ⟨i, p⟩)
                ≤ B := by
              unfold expect
              calc _ ≤ ∑ θ : Profile Θ, prob f θ * B :=
                    Finset.sum_le_sum (fun θ _ => mul_le_mul_of_nonneg_left (hgcs θ (x θ) (hX θ)) (hprob0 θ))
                _ = B := by rw [← Finset.sum_mul, hprob1, one_mul]
            rw [hsplit]
            have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hnn i)
            linarith
          have hCne : (multiCentValues m Θ f M cost).Nonempty := hDne.mono hDC
          have hDbdd : BddAbove (multiDecValues m Θ f M cost) := hCbdd.mono hDC
          have hle1 : sSup (multiDecValues m Θ f M cost) ≤ sSup (multiCentValues m Θ f M cost) :=
            csSup_le_csSup hCbdd hDne hDC
          have hDpsd : M.D.PosSemidef := by
            unfold QuadraticMarket.D; exact hM.2.1.posSemidef.inv
          have hDsym : ∀ k l, M.D k l = M.D l k := by
            intro k l
            have := hDpsd.isHermitian.apply k l
            simpa using this.symm
          have hquad : ∀ z : Product m → ℝ, 0 ≤ ∑ k, ∑ l, z k * M.D k l * z l := by
            intro z
            have := hDpsd.dotProduct_mulVec_nonneg z
            simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at this
            refine le_of_le_of_eq this ?_
            apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
            ring
          have hDemand : ∀ (x : Product m → ℝ), x ∈ productSimplex (Product m) → ∀ κ : ℝ,
              M.IsDemand Finset.univ (fun k => M.c k - ∑ l, M.D k l * x l + κ) x := by
            intro x hx κ
            refine ⟨hx, fun k hk => absurd (Finset.mem_univ k) hk, ?_⟩
            intro y hy _
            have Syx : ∑ k, ∑ l, x k * M.D k l * y l = ∑ k, ∑ l, y k * M.D k l * x l := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
              rw [hDsym]; ring
            have hz := hquad (fun k => y k - x k)
            have e1 : ∑ k, ∑ l, (y k - x k) * M.D k l * (y l - x l) =
                ∑ k, ∑ l, y k * M.D k l * y l - ∑ k, ∑ l, y k * M.D k l * x l
                - ∑ k, ∑ l, x k * M.D k l * y l + ∑ k, ∑ l, x k * M.D k l * x l := by
              simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
              ring
            have e2 : ∀ z : Product m → ℝ, ∑ k, (M.c k - ∑ l, M.D k l * x l + κ) * z k =
                ∑ k, M.c k * z k - ∑ k, ∑ l, z k * M.D k l * x l + κ * ∑ k, z k := by
              intro z
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl; intro k _
              have : (∑ l, M.D k l * x l) * z k = ∑ l, z k * M.D k l * x l := by
                rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun l _ => by ring)
              linear_combination (-1 : ℝ) * this
            unfold QuadraticMarket.gcs
            rw [e2 y, e2 x, hy.2, hx.2]
            simp only [Syx] at e1
            nlinarith [hz, e1]
          have hinterim_sub : ∀ (i : Fin n) (c : ℝ) (g h : Profile Θ → ℝ),
              interim f (fun θ => g θ - h θ) i c = interim f g i c - interim f h i c := by
            intro i c g h
            unfold interim
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro θ _
            split_ifs <;> ring
          have hobj : ∀ (x : Profile Θ → Product m → ℝ) (t : Profile Θ → Fin n → ℝ),
              multiCentObj m Θ f M x t = expect f (fun θ => M.gcs (x θ)) -
                ∑ i, ∑ a ∈ Θ i, f i a * interim f (fun θ => t θ i) i a := by
            intro x t
            have : ∀ i, expect f (fun θ => t θ i) = ∑ a ∈ Θ i, f i a * interim f (fun θ => t θ i) i a :=
              fun i => hexp i _
            simp_rw [← this]
            unfold multiCentObj expect
            rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro θ _
            rw [← Finset.mul_sum]; ring
          have hred : ∀ (x : Profile Θ → Product m → ℝ) (t : Profile Θ → Fin n → ℝ),
              MultiCentFeasible m Θ f cost x t → ∀ κ : Profile Θ → ℝ,
              (∀ i, ∀ c ∈ Θ i, interim f (fun θ => multiTransfer m Θ
                  (fun θ k => M.c k - ∑ l, M.D k l * x θ l + κ θ) x θ i) i c
                  = interim f (fun θ => t θ i) i c) →
              multiCentObj m Θ f M x t ∈ multiDecValues m Θ f M cost := by
            intro x t hF κ hκ
            obtain ⟨hIC, hIR, hX⟩ := hF
            set P : Profile Θ → Product m → ℝ := fun θ k => M.c k - ∑ l, M.D k l * x θ l + κ θ with hP
            have hU : ∀ i, ∀ b ∈ Θ i, ∀ a, multiUtility m Θ f cost x (multiTransfer m Θ P x) i b a
                = multiUtility m Θ f cost x t i b a := by
              intro i b hb a
              unfold multiUtility
              rw [hinterim_sub i b (fun θ => multiTransfer m Θ P x θ i),
                hinterim_sub i b (fun θ => t θ i), hκ i b hb]
            refine ⟨fun _ => Finset.univ, P, x, ⟨⟨?_, ?_, hX⟩, fun θ => hDemand (x θ) (hX θ) (κ θ)⟩, ?_⟩
            · intro i a ha b hb
              rw [hU i b hb, hU i a ha]; exact hIC i a ha b hb
            · intro i a ha
              rw [hU i a ha]; exact hIR i a ha
            · rw [hobj, hobj]
              congr 1
              apply Finset.sum_congr rfl; intro i _
              apply Finset.sum_congr rfl; intro a ha
              rw [hκ i a ha]
          have hinterim_lin : ∀ (i : Fin n) (c a b : ℝ) (g h : Profile Θ → ℝ),
              interim f (fun θ => a * g θ + b * h θ) i c = a * interim f g i c + b * interim f h i c := by
            intro i c a b g h
            unfold interim
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro θ _
            split_ifs <;> ring
          have hmix : ∀ (x : Profile Θ → Product m → ℝ) (t : Profile Θ → Fin n → ℝ)
              (y : Profile Θ → Product m → ℝ) (s : Profile Θ → Fin n → ℝ),
              MultiCentFeasible m Θ f cost x t → MultiCentFeasible m Θ f cost y s →
              ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
              MultiCentFeasible m Θ f cost (fun θ k => (1 - ε) * x θ k + ε * y θ k)
                (fun θ i => (1 - ε) * t θ i + ε * s θ i) := by
            intro x t y s hx hy ε he0 he1
            have hU : ∀ i b a, multiUtility m Θ f cost (fun θ k => (1 - ε) * x θ k + ε * y θ k)
                (fun θ i => (1 - ε) * t θ i + ε * s θ i) i b a =
                (1 - ε) * multiUtility m Θ f cost x t i b a + ε * multiUtility m Θ f cost y s i b a := by
              intro i b a
              unfold multiUtility
              rw [← hinterim_lin]
              congr 1; funext θ
              have : ∑ p, cost i p a * ((1 - ε) * x θ ⟨i, p⟩ + ε * y θ ⟨i, p⟩) =
                  (1 - ε) * ∑ p, cost i p a * x θ ⟨i, p⟩ + ε * ∑ p, cost i p a * y θ ⟨i, p⟩ := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl; intro p _; ring
              rw [this]; ring
            obtain ⟨hx1, hx2, hx3⟩ := hx
            obtain ⟨hy1, hy2, hy3⟩ := hy
            refine ⟨?_, ?_, ?_⟩
            · intro i a ha b hb
              rw [hU, hU]
              have := hx1 i a ha b hb; have := hy1 i a ha b hb
              nlinarith
            · intro i a ha
              rw [hU]
              have := hx2 i a ha; have := hy2 i a ha
              nlinarith
            · intro θ
              refine ⟨fun k => ?_, ?_⟩
              · have := (hx3 θ).1 k; have := (hy3 θ).1 k
                nlinarith
              · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hx3 θ).2, (hy3 θ).2]
                ring
          have hgcs_conc : ∀ (u v : Product m → ℝ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
              (1 - ε) * M.gcs u + ε * M.gcs v ≤ M.gcs (fun k => (1 - ε) * u k + ε * v k) := by
            intro u v ε he0 he1
            have hq := hquad (fun k => u k - v k)
            have e : (1 - ε) * ∑ k, ∑ l, u k * M.D k l * u l + ε * ∑ k, ∑ l, v k * M.D k l * v l
                - ∑ k, ∑ l, ((1 - ε) * u k + ε * v k) * M.D k l * ((1 - ε) * u l + ε * v l)
                = ε * (1 - ε) * ∑ k, ∑ l, (u k - v k) * M.D k l * (u l - v l) := by
              simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
              ring
            have e2 : ∑ k, M.c k * ((1 - ε) * u k + ε * v k) =
                (1 - ε) * ∑ k, M.c k * u k + ε * ∑ k, M.c k * v k := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl; intro k _; ring
            unfold QuadraticMarket.gcs
            rw [e2]
            have : 0 ≤ ε * (1 - ε) := mul_nonneg he0 (by linarith)
            nlinarith [mul_nonneg this hq]
          have hobj_mix : ∀ (x : Profile Θ → Product m → ℝ) (t : Profile Θ → Fin n → ℝ)
              (y : Profile Θ → Product m → ℝ) (s : Profile Θ → Fin n → ℝ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
              (1 - ε) * multiCentObj m Θ f M x t + ε * multiCentObj m Θ f M y s ≤
              multiCentObj m Θ f M (fun θ k => (1 - ε) * x θ k + ε * y θ k)
                (fun θ i => (1 - ε) * t θ i + ε * s θ i) := by
            intro x t y s ε he0 he1
            unfold multiCentObj expect
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_le_sum; intro θ _
            simp only
            have h1 := hgcs_conc (x θ) (y θ) ε he0 he1
            have h2 : ∑ i, ((1 - ε) * t θ i + ε * s θ i) = (1 - ε) * ∑ i, t θ i + ε * ∑ i, s θ i := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            rw [h2]
            have := hprob0 θ
            nlinarith [mul_le_mul_of_nonneg_left h1 this]
          obtain ⟨Amat, hAmat⟩ : ∃ Amat : (Profile Θ → Product m → ℝ) →
              Matrix ((i : Fin n) × ↥(Θ i)) (Profile Θ) ℝ, ∀ x r θ, Amat x r θ =
                if ((θ r.1 : ℝ) = r.2) then probOthers f r.1 θ * ∑ p, x θ ⟨r.1, p⟩ else 0 :=
            ⟨fun x r θ => if ((θ r.1 : ℝ) = r.2) then probOthers f r.1 θ * ∑ p, x θ ⟨r.1, p⟩ else 0,
              fun _ _ _ => rfl⟩
          have hAmul : ∀ (x : Profile Θ → Product m → ℝ) (κ : Profile Θ → ℝ) r,
              (Matrix.mulVec (Amat x) κ) r = interim f (fun θ => κ θ * ∑ p, x θ ⟨r.1, p⟩) r.1 r.2 := by
            intro x κ r
            simp only [Matrix.mulVec, dotProduct, hAmat]
            unfold interim
            apply Finset.sum_congr rfl; intro θ _
            split_ifs <;> ring
          have hAmix : ∀ (x y : Profile Θ → Product m → ℝ) (ε : ℝ),
              Amat (fun θ k => (1 - ε) * x θ k + ε * y θ k) = (1 - ε) • Amat x + ε • Amat y := by
            intro x y ε
            ext r θ
            simp only [hAmat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
            split_ifs
            · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
            · ring
          have hsolve : ∀ A : Matrix ((i : Fin n) × ↥(Θ i)) (Profile Θ) ℝ, (A * Matrix.transpose A).det ≠ 0 →
              ∀ r, ∃ κ, Matrix.mulVec A κ = r := by
            intro A hA r
            refine ⟨Matrix.mulVec (Matrix.transpose A) (Matrix.mulVec (A * Matrix.transpose A)⁻¹ r), ?_⟩
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
              Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
          have hfull : ∀ A : Matrix ((i : Fin n) × ↥(Θ i)) (Profile Θ) ℝ,
              (∀ v, Matrix.mulVec (Matrix.transpose A) v = 0 → v = 0) → (A * Matrix.transpose A).det ≠ 0 := by
            intro A hA hdet
            obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
            apply hv0
            apply hA
            have h1 : dotProduct v (Matrix.mulVec (A * Matrix.transpose A) v) = 0 := by rw [hv]; simp
            rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at h1
            exact dotProduct_self_eq_zero.mp h1
          have hpoly : ∀ A B : Matrix ((i : Fin n) × ↥(Θ i)) (Profile Θ) ℝ, (B * Matrix.transpose B).det ≠ 0 →
              ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε < 1 ∧
                (((1 - ε) • A + ε • B) * Matrix.transpose ((1 - ε) • A + ε • B)).det ≠ 0 := by
            intro A B hB δ hδ
            let Ap : Matrix ((i : Fin n) × ↥(Θ i)) (Profile Θ) (Polynomial ℝ) := fun r θ =>
              Polynomial.C (A r θ) * (1 - Polynomial.X) + Polynomial.C (B r θ) * Polynomial.X
            have heval : ∀ ε : ℝ, (Ap * Matrix.transpose Ap).det.eval ε =
                (((1 - ε) • A + ε • B) * Matrix.transpose ((1 - ε) • A + ε • B)).det := by
              intro ε
              rw [← Polynomial.coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]
              congr 2
              · ext r θ; rw [Matrix.map_apply]; try rw [Matrix.transpose_apply, Matrix.transpose_apply]
                simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
                  smul_eq_mul, Ap, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
                  Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]; ring
              · ext r θ; rw [Matrix.map_apply]; try rw [Matrix.transpose_apply, Matrix.transpose_apply]
                simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
                  smul_eq_mul, Ap, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
                  Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]; ring
            have hne : (Ap * Matrix.transpose Ap).det ≠ 0 := by
              intro h
              apply hB
              have := heval 1
              rw [h] at this
              simpa using this.symm
            have hfin := Polynomial.finite_setOfPred_isRoot hne
            have hinf : (Set.Ioo (0 : ℝ) (min δ 1)).Infinite := Set.Ioo_infinite (lt_min hδ one_pos)
            obtain ⟨ε, hε1, hε2⟩ := (hinf.sdiff hfin).nonempty
            refine ⟨ε, hε1.1, lt_of_lt_of_le hε1.2 (min_le_left _ _),
              lt_of_lt_of_le hε1.2 (min_le_right _ _), ?_⟩
            rw [← heval]
            exact hε2
          have hint_prod : ∀ (i : Fin n) (c : ℝ), c ∈ Θ i → ∀ u : Fin n → ℝ → ℝ,
              interim f (fun θ : Profile Θ => ∏ l, u l (θ l)) i c =
                u i c * ∏ l ∈ Finset.univ.erase i, ∑ a ∈ Θ l, f l a * u l a := by
            intro i c hc u
            let w : (l : Fin n) → ℝ → ℝ := fun l a =>
              if l = i then (if a = c then u l a else 0) else f l a * u l a
            have h1 : ∀ θ : Profile Θ, (if (θ i : ℝ) = c then probOthers f i θ * ∏ l, u l (θ l) else 0)
                = ∏ l, w l (θ l) := by
              intro θ
              rw [← Finset.mul_prod_erase Finset.univ (fun l => w l (θ l)) (Finset.mem_univ i),
                ← Finset.mul_prod_erase Finset.univ (fun l => u l (θ l)) (Finset.mem_univ i)]
              have : ∏ l ∈ Finset.univ.erase i, w l (θ l) =
                  probOthers f i θ * ∏ l ∈ Finset.univ.erase i, u l (θ l) := by
                unfold probOthers
                rw [← Finset.prod_mul_distrib]
                apply Finset.prod_congr rfl
                intro l hl
                simp [w, Finset.ne_of_mem_erase hl]
              rw [this]
              by_cases hθ : (θ i : ℝ) = c
              · simp only [w, hθ, if_true]; ring
              · simp only [w, hθ, if_true, if_false]; ring
            unfold interim
            simp_rw [h1]
            rw [← Fintype.prod_sum (fun l (a : ↥(Θ l)) => w l a)]
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
            congr 1
            · rw [Finset.sum_coe_sort (Θ i) (w i)]
              simp [w, hc]
            · apply Finset.prod_congr rfl
              intro l hl
              rw [Finset.sum_coe_sort (Θ l) (w l)]
              simp [w, Finset.ne_of_mem_erase hl]
          have hint2 : ∀ (i : Fin n) (c : ℝ), c ∈ Θ i → ∀ (j k : Fin n) (χ ω : ℝ → ℝ), j ≠ k →
              interim f (fun θ : Profile Θ => χ (θ j) * ω (θ k)) i c =
                (if j = i then χ c else ∑ a ∈ Θ j, f j a * χ a) *
                (if k = i then ω c else ∑ a ∈ Θ k, f k a * ω a) := by
            intro i c hc j k χ ω hjk
            let u : Fin n → ℝ → ℝ := fun l a => (if l = j then χ a else 1) * (if l = k then ω a else 1)
            have hu : ∀ θ : Profile Θ, χ (θ j) * ω (θ k) = ∏ l, u l (θ l) := by
              intro θ
              simp only [u, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
            simp_rw [hu]
            rw [hint_prod i c hc u]
            have hs : ∀ l, ∑ a ∈ Θ l, f l a * u l a =
                (if l = j then ∑ a ∈ Θ j, f j a * χ a else 1) *
                (if l = k then ∑ a ∈ Θ k, f k a * ω a else 1) := by
              intro l
              by_cases hl : l = j
              · subst hl; simp [u, hjk]
              · by_cases hl' : l = k
                · subst hl'; simp [u, hl]
                · simp [u, hl, hl', hsum l]
            simp_rw [hs]
            rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
            simp only [u, Finset.mem_erase, ne_eq, Finset.mem_univ, and_true]
            by_cases hji : j = i
            · subst hji
              simp [Ne.symm hjk, hjk]
            · by_cases hki : k = i
              · subst hki; simp [hji, Ne.symm hjk]; ring
              · simp [hji, hki, Ne.symm hji, Ne.symm hki]
          have hint1 : ∀ (i : Fin n) (c : ℝ), c ∈ Θ i → ∀ (j : Fin n) (χ : ℝ → ℝ),
              interim f (fun θ : Profile Θ => χ (θ j)) i c =
                (if j = i then χ c else ∑ a ∈ Θ j, f j a * χ a) := by
            intro i c hc j χ
            have := hint_prod i c hc (fun l a => if l = j then χ a else 1)
            simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at this
            rw [this]
            have hs : ∀ l, ∑ a ∈ Θ l, f l a * (if l = j then χ a else 1) =
                (if l = j then ∑ a ∈ Θ j, f j a * χ a else 1) := by
              intro l
              by_cases hl : l = j
              · subst hl; simp
              · simp [hl, hsum l]
            simp_rw [hs]
            rw [Finset.prod_ite_eq']
            by_cases hji : j = i
            · subst hji; simp
            · simp [hji, Ne.symm hji]
          have hint_sum : ∀ (i : Fin n) (c : ℝ) (S : Finset (Fin n)) (h : Fin n → Profile Θ → ℝ),
              interim f (fun θ => ∑ j ∈ S, h j θ) i c = ∑ j ∈ S, interim f (h j) i c := by
            intro i c S h
            unfold interim
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro θ _
            split_ifs
            · rw [Finset.mul_sum]
            · simp
          have hint_smul : ∀ (i : Fin n) (c a : ℝ) (h : Profile Θ → ℝ),
              interim f (fun θ => a * h θ) i c = a * interim f h i c := by
            intro i c a h
            have := hinterim_lin i c a 0 h h
            simpa using this
          have hint_zero : ∀ (i : Fin n) (c : ℝ), interim f (fun _ : Profile Θ => (0:ℝ)) i c = 0 := by
            intro i c; unfold interim; simp
          have hY : ∃ (y : Profile Θ → Product m → ℝ) (s : Profile Θ → Fin n → ℝ),
              MultiCentFeasible m Θ f cost y s ∧
                ∀ v, Matrix.mulVec (Matrix.transpose (Amat y)) v = 0 → v = 0 := by
            set i0 : Fin n := ⟨0, hn⟩ with hi0
            obtain ⟨mn, hmn⟩ : ∃ mn : Fin n → ℝ, ∀ i, mn i ∈ Θ i :=
              ⟨fun i => (hne i).choose, fun i => (hne i).choose_spec⟩
            obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin n → ℝ → ℝ, ∀ i c,
                ψ i c = (if c = mn i then 1 else 0) - f i (mn i) := ⟨_, fun _ _ => rfl⟩
            have hfmn : ∀ i, 0 < f i (mn i) := fun i => hfpos i _ (hmn i)
            have hflt : ∀ i, f i (mn i) < 1 := by
              intro i
              obtain ⟨a, ha, hane⟩ := Finset.exists_mem_ne (by have := hc i; omega : 1 < (Θ i).card) (mn i)
              have h2 : f i (mn i) + f i a ≤ ∑ c ∈ Θ i, f i c := by
                rw [← Finset.sum_pair (Ne.symm hane)]
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl
                  · exact hmn i
                  · exact ha
                · intro x hx _; exact (hfpos i x hx).le
              have := hfpos i a ha
              rw [hsum i] at h2; linarith
            have hEψ : ∀ i, ∑ a ∈ Θ i, f i a * ψ i a = 0 := by
              intro i
              have : ∀ a ∈ Θ i, f i a * ψ i a = (if a = mn i then f i a else 0) - f i (mn i) * f i a := by
                intro a _; rw [hψ]; split_ifs <;> ring
              rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_ite_eq' (Θ i) (mn i),
                if_pos (hmn i), ← Finset.mul_sum, hsum i]
              ring
            have hψb : ∀ i a, |ψ i a| ≤ 1 := by
              intro i a; rw [hψ, abs_le]; have := hflt i; have := hfmn i
              constructor <;> split_ifs <;> linarith
            have hψmn : ∀ i, ψ i (mn i) = 1 - f i (mn i) := by intro i; rw [hψ]; simp
            have hm2 : ∀ i, 0 < ∑ a ∈ Θ i, f i a * ψ i a ^ 2 := by
              intro i
              have h1 : f i (mn i) * ψ i (mn i) ^ 2 ≤ ∑ a ∈ Θ i, f i a * ψ i a ^ 2 :=
                Finset.single_le_sum (f := fun a => f i a * ψ i a ^ 2)
                  (fun a ha => mul_nonneg (hfpos i a ha).le (sq_nonneg _)) (hmn i)
              have h3 : 0 < 1 - f i (mn i) := by linarith [hflt i]
              have : 0 < f i (mn i) * ψ i (mn i) ^ 2 := by rw [hψmn]; exact mul_pos (hfmn i) (pow_pos h3 2)
              linarith
            have hnpos : (0:ℝ) < n := by exact_mod_cast hn
            have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
            obtain ⟨s0, hs0⟩ : ∃ s0 : ℝ, s0 = 1 / (n:ℝ) ^ 2 := ⟨_, rfl⟩
            have hs0pos : 0 < s0 := by rw [hs0]; positivity
            obtain ⟨Y, hYdef⟩ : ∃ Y : Fin n → Profile Θ → ℝ, ∀ i θ, Y i θ = 1 / n + s0 * ψ i0 (θ i0) *
                (if i = i0 then ∑ j ∈ Finset.univ.erase i0, ψ j (θ j) else -ψ i (θ i)) :=
              ⟨_, fun _ _ => rfl⟩
            have hYsum : ∀ θ : Profile Θ, ∑ i, Y i θ = 1 := by
              intro θ
              have h1 : ∑ i ∈ Finset.univ.erase i0, (if i = i0 then ∑ j ∈ Finset.univ.erase i0, ψ j (θ j)
                  else -ψ i (θ i)) = -∑ j ∈ Finset.univ.erase i0, ψ j (θ j) := by
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl; intro i hi
                rw [if_neg (Finset.ne_of_mem_erase hi)]
              have h0 : ∑ i, (if i = i0 then ∑ j ∈ Finset.univ.erase i0, ψ j (θ j)
                  else -ψ i (θ i)) = 0 := by
                rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0), if_pos rfl, h1]; ring
              simp only [hYdef, Finset.sum_add_distrib, ← Finset.mul_sum, h0, mul_zero, add_zero]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp
            have hYnn : ∀ i θ, 0 ≤ Y i θ := by
              intro i θ
              rw [hYdef]
              have hb : |(if i = i0 then ∑ j ∈ Finset.univ.erase i0, ψ j (θ j) else -ψ i (θ i))| ≤ n := by
                split_ifs
                · calc _ ≤ ∑ j ∈ Finset.univ.erase i0, |ψ j (θ j)| := Finset.abs_sum_le_sum_abs _ _
                    _ ≤ ∑ j ∈ Finset.univ.erase i0, (1:ℝ) := Finset.sum_le_sum (fun j _ => hψb j _)
                    _ ≤ ∑ j : Fin n, (1:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
                        (Finset.erase_subset _ _) (fun _ _ _ => zero_le_one)
                    _ = n := by simp
                · rw [abs_neg]; linarith [hψb i (θ i)]
              have h2 : |s0 * ψ i0 (θ i0) * (if i = i0 then ∑ j ∈ Finset.univ.erase i0, ψ j (θ j)
                  else -ψ i (θ i))| ≤ 1 / n := by
                rw [abs_mul, abs_mul, abs_of_pos hs0pos]
                calc s0 * |ψ i0 (θ i0)| * _ ≤ s0 * 1 * n := by
                      apply mul_le_mul (mul_le_mul_of_nonneg_left (hψb _ _) hs0pos.le) hb (abs_nonneg _)
                        (by positivity)
                  _ = 1 / n := by rw [hs0]; field_simp
              have := neg_abs_le (s0 * ψ i0 (θ i0) * (if i = i0 then ∑ j ∈ Finset.univ.erase i0, ψ j (θ j)
                  else -ψ i (θ i)))
              linarith
            have hYint : ∀ i, ∀ b ∈ Θ i, interim f (Y i) i b = 1 / n := by
              intro i b hb
              have e : Y i = fun θ => 1 * (1 / (n:ℝ)) + s0 * (ψ i0 (θ i0) *
                  (if i = i0 then ∑ j ∈ Finset.univ.erase i0, ψ j (θ j) else -ψ i (θ i))) := by
                funext θ; rw [hYdef]; ring
              rw [e, hinterim_lin, hconst i b hb (fun _ => 1 / (n:ℝ)) _ (fun _ _ => rfl)]
              have : interim f (fun θ : Profile Θ => ψ i0 (θ i0) *
                  (if i = i0 then ∑ j ∈ Finset.univ.erase i0, ψ j (θ j) else -ψ i (θ i))) i b = 0 := by
                by_cases hi : i = i0
                · subst hi
                  simp only [if_true, Finset.mul_sum]
                  rw [hint_sum]
                  apply Finset.sum_eq_zero; intro j hj
                  rw [hint2 i0 b hb i0 j _ _ (Ne.symm (Finset.ne_of_mem_erase hj)),
                    if_neg (Finset.ne_of_mem_erase hj), hEψ j, mul_zero]
                · simp only [hi, if_false]
                  have := hint2 i b hb i0 i (ψ i0) (fun a => -ψ i a) (Ne.symm hi)
                  simp only at this
                  rw [this, if_neg (Ne.symm hi), hEψ i0, zero_mul]
              rw [this]; ring
            obtain ⟨y, hydef⟩ : ∃ y : Profile Θ → Product m → ℝ, ∀ θ k,
                y θ k = if k.2 = ⟨0, hm k.1⟩ then Y k.1 θ else 0 := ⟨_, fun _ _ => rfl⟩
            have hysum : ∀ θ i, ∑ p, y θ ⟨i, p⟩ = Y i θ := by
              intro θ i
              rw [Finset.sum_eq_single (⟨0, hm i⟩ : Fin (m i))]
              · rw [hydef]; exact if_pos rfl
              · intro p _ hp; rw [hydef]; exact if_neg hp
              · intro h; exact absurd (Finset.mem_univ _) h
            have hycost : ∀ θ i a, ∑ p, cost i p a * y θ ⟨i, p⟩ = cost i ⟨0, hm i⟩ a * Y i θ := by
              intro θ i a
              rw [Finset.sum_eq_single (⟨0, hm i⟩ : Fin (m i))]
              · rw [hydef]; rw [if_pos rfl]
              · intro p _ hp; rw [hydef, if_neg hp, mul_zero]
              · intro h; exact absurd (Finset.mem_univ _) h
            have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK ⟨0, hn⟩ ⟨0, hm _⟩ (mn _) (hmn _))
            refine ⟨y, fun _ _ => K + 1, ?_, ?_⟩
            · have hU : ∀ i, ∀ b ∈ Θ i, ∀ a, multiUtility m Θ f cost y (fun _ _ => K + 1) i b a =
                  K + 1 - cost i ⟨0, hm i⟩ a * (1 / n) := by
                intro i b hb a
                unfold multiUtility
                have e : (fun θ : Profile Θ => K + 1 - ∑ p, cost i p a * y θ ⟨i, p⟩) =
                    fun θ => 1 * (K + 1) + (-cost i ⟨0, hm i⟩ a) * Y i θ := by
                  funext θ; rw [hycost]; ring
                rw [e, hinterim_lin, hconst i b hb (fun _ => K + 1) _ (fun _ _ => rfl), hYint i b hb]
                ring
              refine ⟨?_, ?_, ?_⟩
              · intro i a ha b hb
                rw [hU i b hb, hU i a ha]
              · intro i a ha
                rw [hU i a ha]
                have h1 := hK i ⟨0, hm i⟩ a ha
                have h2 := le_abs_self (cost i ⟨0, hm i⟩ a)
                have h3 : 1 / (n:ℝ) ≤ 1 := by rw [div_le_one hnpos]; exact hn1
                have h4 : 0 < 1 / (n:ℝ) := by positivity
                nlinarith
              · intro θ
                refine ⟨fun k => ?_, ?_⟩
                · rw [hydef]; split_ifs
                  · exact hYnn _ _
                  · exact le_refl 0
                · rw [Fintype.sum_sigma]
                  simp only [hysum]
                  exact hYsum θ
            · intro v hv
              have hθ : ∀ θ : Profile Θ, ∑ i, probOthers f i θ * Y i θ * v ⟨i, θ i⟩ = 0 := by
                intro θ
                have := congrFun hv θ
                simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hAmat, Pi.zero_apply,
                  Fintype.sum_sigma] at this
                rw [← this]
                apply Finset.sum_congr rfl; intro i _
                rw [Finset.sum_eq_single (θ i)]
                · simp only [if_true, hysum]
                · intro c _ hc
                  rw [if_neg (fun h => hc (Subtype.ext h).symm), zero_mul]
                · intro h; exact absurd (Finset.mem_univ _) h
              obtain ⟨g, hg⟩ : ∃ g : Fin n → ℝ → ℝ, ∀ i (c : ↥(Θ i)), g i c = v ⟨i, c⟩ / f i c :=
                ⟨fun i a => if h : a ∈ Θ i then v ⟨i, ⟨a, h⟩⟩ / f i a else 0,
                  fun i c => by simp⟩
              have hE : ∀ θ : Profile Θ, ∑ i, Y i θ * g i (θ i) = 0 := by
                intro θ
                have hp : 0 < prob f θ := Finset.prod_pos (fun j _ => hfpos j _ (θ j).2)
                have h1 : prob f θ * ∑ i, Y i θ * g i (θ i) = 0 := by
                  rw [← hθ θ, Finset.mul_sum]
                  apply Finset.sum_congr rfl; intro i _
                  have hpr : prob f θ = f i (θ i) * probOthers f i θ := by
                    unfold prob probOthers
                    rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (θ j)) (Finset.mem_univ i)]
                  rw [hg, hpr]
                  have := (hfpos i _ (θ i).2).ne'
                  field_simp
                rcases mul_eq_zero.mp h1 with h | h
                · exact absurd h hp.ne'
                · exact h
              obtain ⟨E0, hE0⟩ : ∃ E0 : Finset (Fin n), E0 = Finset.univ.erase i0 := ⟨_, rfl⟩
              obtain ⟨Eg, hEg⟩ : ∃ Eg : Fin n → ℝ, ∀ l, Eg l = ∑ a ∈ Θ l, f l a * g l a :=
                ⟨_, fun _ => rfl⟩
              obtain ⟨Eψg, hEψg⟩ : ∃ Eψg : Fin n → ℝ, ∀ l,
                  Eψg l = ∑ a ∈ Θ l, f l a * (ψ l a * g l a) := ⟨_, fun _ => rfl⟩
              have hmemE0 : ∀ l, l ∈ E0 ↔ l ≠ i0 := by intro l; rw [hE0]; simp
              have hI0 : ∀ i c, c ∈ Θ i → interim f (fun θ => Y i0 θ * g i0 (θ i0)) i c =
                  1 * ((1 / n) * (if i0 = i then g i0 c else Eg i0)) + s0 * ∑ j ∈ E0,
                    ((if i0 = i then ψ i0 c * g i0 c else Eψg i0) * (if j = i then ψ j c else 0)) := by
                intro i c hc
                have e : (fun θ : Profile Θ => Y i0 θ * g i0 (θ i0)) = fun θ =>
                    1 * ((1 / (n:ℝ)) * g i0 (θ i0)) +
                      s0 * ∑ j ∈ E0, ψ i0 (θ i0) * g i0 (θ i0) * ψ j (θ j) := by
                  funext θ; rw [hYdef, if_pos rfl, ← Finset.mul_sum, hE0]; ring
                rw [e, hinterim_lin, hint_smul, hint1 i c hc i0 (g i0), ← hEg i0, hint_sum]
                congr 2
                apply Finset.sum_congr rfl; intro j hj
                have := hint2 i c hc i0 j (fun a => ψ i0 a * g i0 a) (ψ j) (Ne.symm ((hmemE0 j).1 hj))
                try simp only at this
                rw [this, hEψ j, ← hEψg i0]
              have hIl : ∀ l ∈ E0, ∀ i c, c ∈ Θ i → interim f (fun θ => Y l θ * g l (θ l)) i c =
                  1 * ((1 / n) * (if l = i then g l c else Eg l)) + (-s0) *
                    ((if i0 = i then ψ i0 c else 0) * (if l = i then ψ l c * g l c else Eψg l)) := by
                intro l hl i c hc
                have hl0 := (hmemE0 l).1 hl
                have e : (fun θ : Profile Θ => Y l θ * g l (θ l)) = fun θ =>
                    1 * ((1 / (n:ℝ)) * g l (θ l)) + (-s0) * (ψ i0 (θ i0) * (ψ l (θ l) * g l (θ l))) := by
                  funext θ; rw [hYdef, if_neg hl0]; ring
                rw [e, hinterim_lin, hint_smul, hint1 i c hc l (g l), ← hEg l]
                have := hint2 i c hc i0 l (ψ i0) (fun a => ψ l a * g l a) (Ne.symm hl0)
                try simp only at this
                rw [this, hEψ i0, ← hEψg l]
              have hTot : ∀ i c, c ∈ Θ i → interim f (fun θ => Y i0 θ * g i0 (θ i0)) i c +
                  ∑ l ∈ E0, interim f (fun θ => Y l θ * g l (θ l)) i c = 0 := by
                intro i c hc
                have h1 : interim f (fun θ : Profile Θ => ∑ l, Y l θ * g l (θ l)) i c = 0 := by
                  rw [show (fun θ : Profile Θ => ∑ l, Y l θ * g l (θ l)) = fun _ => 0 from funext hE,
                    hint_zero]
                rw [hint_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)] at h1
                rw [hE0]; exact h1
              obtain ⟨U, hU⟩ : ∃ U : ℝ, U = ∑ l ∈ E0, Eg l := ⟨_, rfl⟩
              obtain ⟨S1, hS1⟩ : ∃ S1 : ℝ, S1 = ∑ l ∈ E0, Eψg l := ⟨_, rfl⟩
              have hSA : ∀ c ∈ Θ i0, g i0 c = -U + n * s0 * S1 * ψ i0 c := by
                intro c hc
                have h := hTot i0 c hc
                rw [hI0 i0 c hc, Finset.sum_congr rfl (fun l hl => hIl l hl i0 c hc)] at h
                have k1 : ∑ j ∈ E0, ((if i0 = i0 then ψ i0 c * g i0 c else Eψg i0) *
                    (if j = i0 then ψ j c else 0)) = 0 :=
                  Finset.sum_eq_zero (fun j hj => by rw [if_neg ((hmemE0 j).1 hj), mul_zero])
                have k2 : ∑ l ∈ E0, (1 * ((1 / (n:ℝ)) * (if l = i0 then g l c else Eg l)) + (-s0) *
                    ((if i0 = i0 then ψ i0 c else 0) * (if l = i0 then ψ l c * g l c else Eψg l))) =
                    (1 / n) * U + (-s0) * (ψ i0 c * S1) := by
                  rw [hU, hS1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl; intro l hl
                  rw [if_neg ((hmemE0 l).1 hl), if_neg ((hmemE0 l).1 hl), if_pos rfl]; ring
                rw [k1, k2, if_pos rfl] at h
                field_simp at h
                linear_combination h
              have hSB : ∀ j ∈ E0, ∀ b ∈ Θ j, g j b = Eg j - U - Eg i0 - n * s0 * Eψg i0 * ψ j b := by
                intro j hj b hb
                have hj0 := (hmemE0 j).1 hj
                have hij : (i0 = j) = False := propext ⟨fun h => hj0 h.symm, False.elim⟩
                have h := hTot j b hb
                rw [hI0 j b hb, Finset.sum_congr rfl (fun l hl => hIl l hl j b hb)] at h
                simp only [hij, ↓reduceIte, zero_mul, mul_zero, add_zero] at h
                have k1 : ∑ j' ∈ E0, Eψg i0 * (if j' = j then ψ j' b else 0) = Eψg i0 * ψ j b := by
                  simp only [mul_ite, mul_zero]
                  rw [Finset.sum_ite_eq' E0 j, if_pos hj]
                have k2 : ∑ l ∈ E0, 1 * ((1 / (n:ℝ)) * (if l = j then g l b else Eg l)) =
                    (1 / n) * (g j b - Eg j + U) := by
                  rw [← Finset.add_sum_erase E0 _ hj, hU, ← Finset.add_sum_erase E0 _ hj, if_pos rfl]
                  have k2a : ∀ l ∈ E0.erase j, 1 * ((1 / (n:ℝ)) * (if l = j then g l b else Eg l)) =
                      (1 / n) * Eg l := by
                    intro l hl; rw [if_neg (Finset.ne_of_mem_erase hl)]; ring
                  rw [Finset.sum_congr rfl k2a, ← Finset.mul_sum]; ring
                rw [k1, k2] at h
                field_simp at h
                linear_combination h
              have hfq : ∀ l (A B : ℝ), ∑ a ∈ Θ l, f l a * (ψ l a * (A + B * ψ l a)) =
                  B * ∑ a ∈ Θ l, f l a * ψ l a ^ 2 := by
                intro l A B
                have : ∀ a ∈ Θ l, f l a * (ψ l a * (A + B * ψ l a)) =
                    A * (f l a * ψ l a) + B * (f l a * ψ l a ^ 2) := by intro a _; ring
                rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
                  hEψ l]; ring
              have hfl : ∀ l (A B : ℝ), ∑ a ∈ Θ l, f l a * (A + B * ψ l a) = A := by
                intro l A B
                have : ∀ a ∈ Θ l, f l a * (A + B * ψ l a) = A * f l a + B * (f l a * ψ l a) := by
                  intro a _; ring
                rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
                  hEψ l, hsum l]; ring
              have hEg0 : Eg i0 = -U := by
                rw [hEg, Finset.sum_congr rfl (fun c hc => by rw [hSA c hc]), hfl]
              have hEψg0 : Eψg i0 = n * s0 * S1 * ∑ a ∈ Θ i0, f i0 a * ψ i0 a ^ 2 := by
                rw [hEψg, Finset.sum_congr rfl (fun c hc => by rw [hSA c hc]), hfq]
              have hEψgj : ∀ j ∈ E0, Eψg j = -(n * s0 * Eψg i0) * ∑ a ∈ Θ j, f j a * ψ j a ^ 2 := by
                intro j hj
                rw [hEψg, Finset.sum_congr rfl (fun c hc => by
                  rw [hSB j hj c hc, show Eg j - U - Eg i0 - n * s0 * Eψg i0 * ψ j c =
                    (Eg j - U - Eg i0) + (-(n * s0 * Eψg i0)) * ψ j c by ring]), hfq]
              have hS1' : S1 = -(n * s0 * Eψg i0) * ∑ j ∈ E0, ∑ a ∈ Θ j, f j a * ψ j a ^ 2 := by
                rw [hS1, Finset.mul_sum]
                exact Finset.sum_congr rfl hEψgj
              have hψ0z : Eψg i0 = 0 := by
                have hM0 := hm2 i0
                have hMs : 0 ≤ ∑ j ∈ E0, ∑ a ∈ Θ j, f j a * ψ j a ^ 2 :=
                  Finset.sum_nonneg (fun j _ => (hm2 j).le)
                rw [hS1'] at hEψg0
                have : Eψg i0 * (1 + (n * s0) ^ 2 * (∑ a ∈ Θ i0, f i0 a * ψ i0 a ^ 2) *
                    ∑ j ∈ E0, ∑ a ∈ Θ j, f j a * ψ j a ^ 2) = 0 := by linear_combination hEψg0
                rcases mul_eq_zero.mp this with h | h
                · exact h
                · nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (n * s0)) hM0.le) hMs]
              have hS1z : S1 = 0 := by rw [hS1', hψ0z]; ring
              have hgc : ∀ l, ∀ a ∈ Θ l, g l a = Eg l := by
                intro l a ha
                by_cases hl : l = i0
                · subst hl; rw [hSA a ha, hS1z, hEg0]; ring
                · rw [hSB l ((hmemE0 l).2 hl) a ha, hψ0z, hEg0]; ring
              have hpt : ∀ θ : Profile Θ, ∑ l, Y l θ * g l (θ l) = 1 / n * (Eg i0 + U) +
                  s0 * ψ i0 (θ i0) * ∑ l ∈ E0, (Eg i0 - Eg l) * ψ l (θ l) := by
                intro θ
                rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0), ← hE0]
                have e1 : ∑ l ∈ E0, Y l θ * g l (θ l) =
                    1 / n * U - s0 * ψ i0 (θ i0) * ∑ l ∈ E0, ψ l (θ l) * Eg l := by
                  rw [hU, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
                  apply Finset.sum_congr rfl; intro l hl
                  rw [hYdef, if_neg ((hmemE0 l).1 hl), hgc l _ (θ l).2]; ring
                have e2 : ∑ l ∈ E0, (Eg i0 - Eg l) * ψ l (θ l) =
                    Eg i0 * ∑ l ∈ E0, ψ l (θ l) - ∑ l ∈ E0, ψ l (θ l) * Eg l := by
                  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                  apply Finset.sum_congr rfl; intro l _; ring
                rw [e1, e2, hYdef, if_pos rfl, hgc i0 _ (θ i0).2, ← hE0]
                ring
              have hC : ∀ j ∈ E0, Eg j = Eg i0 := by
                intro j hj
                have hj0 := (hmemE0 j).1 hj
                have hb := hmn j
                have h0 : interim f (fun θ : Profile Θ => ψ i0 (θ i0) * ∑ l, Y l θ * g l (θ l)) j (mn j)
                    = 0 := by
                  rw [show (fun θ : Profile Θ => ψ i0 (θ i0) * ∑ l, Y l θ * g l (θ l)) = fun _ => 0 from
                    funext (fun θ => by rw [hE θ, mul_zero]), hint_zero]
                have e : (fun θ : Profile Θ => ψ i0 (θ i0) * ∑ l, Y l θ * g l (θ l)) = fun θ =>
                    1 * ((1 / n * (Eg i0 + U)) * ψ i0 (θ i0)) +
                      s0 * ∑ l ∈ E0, (Eg i0 - Eg l) * (ψ i0 (θ i0) ^ 2 * ψ l (θ l)) := by
                  funext θ
                  rw [hpt θ]
                  have : ∑ l ∈ E0, (Eg i0 - Eg l) * (ψ i0 (θ i0) ^ 2 * ψ l (θ l)) =
                      ψ i0 (θ i0) ^ 2 * ∑ l ∈ E0, (Eg i0 - Eg l) * ψ l (θ l) := by
                    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
                  rw [this]; ring
                rw [e, hinterim_lin, hint_smul, hint1 j (mn j) hb i0 (ψ i0), if_neg (Ne.symm hj0), hEψ i0,
                  hint_sum] at h0
                have k : ∑ l ∈ E0, interim f (fun θ : Profile Θ => (Eg i0 - Eg l) *
                    (ψ i0 (θ i0) ^ 2 * ψ l (θ l))) j (mn j) =
                    (Eg i0 - Eg j) * ((∑ a ∈ Θ i0, f i0 a * ψ i0 a ^ 2) * ψ j (mn j)) := by
                  rw [← Finset.add_sum_erase E0 _ hj]
                  have h2 := hint2 j (mn j) hb i0 j (fun a => ψ i0 a ^ 2) (ψ j) (Ne.symm hj0)
                  try simp only at h2
                  rw [hint_smul, h2, if_neg (Ne.symm hj0), if_true]
                  have hz : ∑ l ∈ E0.erase j, interim f (fun θ : Profile Θ => (Eg i0 - Eg l) *
                      (ψ i0 (θ i0) ^ 2 * ψ l (θ l))) j (mn j) = 0 := by
                    apply Finset.sum_eq_zero
                    intro l hl
                    have hlj := Finset.ne_of_mem_erase hl
                    have hl0 := (hmemE0 l).1 (Finset.mem_of_mem_erase hl)
                    have h2 := hint2 j (mn j) hb i0 l (fun a => ψ i0 a ^ 2) (ψ l) (Ne.symm hl0)
                    try simp only at h2
                    rw [hint_smul, h2, if_neg hlj, hEψ l]; ring
                  rw [hz, add_zero]
                rw [k] at h0
                have hψj : 0 < ψ j (mn j) := by rw [hψmn]; linarith [hflt j]
                have hpos : 0 < s0 * ((∑ a ∈ Θ i0, f i0 a * ψ i0 a ^ 2) * ψ j (mn j)) :=
                  mul_pos hs0pos (mul_pos (hm2 i0) hψj)
                have : (Eg i0 - Eg j) * (s0 * ((∑ a ∈ Θ i0, f i0 a * ψ i0 a ^ 2) * ψ j (mn j))) = 0 := by
                  linear_combination h0
                rcases mul_eq_zero.mp this with h | h
                · linarith
                · linarith
              have hall : ∀ l, Eg l = Eg i0 := by
                intro l
                by_cases hl : l = i0
                · rw [hl]
                · exact hC l ((hmemE0 l).2 hl)
              have hsumEg : ∑ l, Eg l = 0 := by
                rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0), ← hE0, ← hU, hEg0]; ring
              have hEg0z : Eg i0 = 0 := by
                rw [Finset.sum_congr rfl (fun l _ => hall l), Finset.sum_const, Finset.card_univ,
                  Fintype.card_fin, nsmul_eq_mul] at hsumEg
                rcases mul_eq_zero.mp hsumEg with h | h
                · exact absurd h hnpos.ne'
                · exact h
              funext r
              obtain ⟨i, c⟩ := r
              have h1 := hg i c
              rw [hgc i c c.2, hall i, hEg0z] at h1
              have hf := (hfpos i c c.2).ne'
              rw [eq_comm, div_eq_zero_iff] at h1
              rcases h1 with h | h
              · simpa using h
              · exact absurd h hf
          have hle2 : sSup (multiCentValues m Θ f M cost) ≤ sSup (multiDecValues m Θ f M cost) := by
            obtain ⟨y, s, hys, hker⟩ := hY
            have hBdet := hfull (Amat y) hker
            apply csSup_le hCne
            rintro r ⟨x, t, hxt, rfl⟩
            by_contra hlt
            push Not at hlt
            have hgap : 0 < multiCentObj m Θ f M x t - sSup (multiDecValues m Θ f M cost) := by linarith
            have hΔ : 0 < |multiCentObj m Θ f M x t - multiCentObj m Θ f M y s| + 1 := by positivity
            obtain ⟨ε, he0, heδ, he1, hdet⟩ := hpoly (Amat x) (Amat y) hBdet _ (div_pos hgap hΔ)
            have hF' := hmix x t y s hxt hys ε he0.le he1.le
            have hA' := hAmix x y ε
            obtain ⟨κ, hκ⟩ := hsolve (Amat (fun θ k => (1 - ε) * x θ k + ε * y θ k))
              (by rw [hA']; exact hdet)
              (fun r => interim f (fun θ => (1 - ε) * t θ r.1 + ε * s θ r.1) r.1 r.2 -
                interim f (fun θ => ∑ k : Fin (m r.1), (M.c ⟨r.1, k⟩ - ∑ l, M.D ⟨r.1, k⟩ l *
                  ((1 - ε) * x θ l + ε * y θ l)) * ((1 - ε) * x θ ⟨r.1, k⟩ + ε * y θ ⟨r.1, k⟩)) r.1 r.2)
            have hmem := hred _ _ hF' κ (by
              intro i c hc
              have h0 := congrFun hκ ⟨i, ⟨c, hc⟩⟩
              rw [hAmul] at h0
              simp only at h0
              have e : ∀ θ, multiTransfer m Θ (fun θ k => M.c k - ∑ l, M.D k l *
                  ((1 - ε) * x θ l + ε * y θ l) + κ θ) (fun θ k => (1 - ε) * x θ k + ε * y θ k) θ i =
                  1 * (∑ k : Fin (m i), (M.c ⟨i, k⟩ - ∑ l, M.D ⟨i, k⟩ l *
                    ((1 - ε) * x θ l + ε * y θ l)) * ((1 - ε) * x θ ⟨i, k⟩ + ε * y θ ⟨i, k⟩)) +
                  1 * (κ θ * ∑ p, ((1 - ε) * x θ ⟨i, p⟩ + ε * y θ ⟨i, p⟩)) := by
                intro θ
                unfold multiTransfer
                simp only [one_mul]
                rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl; intro k _; ring
              simp_rw [e]
              rw [hinterim_lin]
              linarith)
            have h1 := le_csSup hDbdd hmem
            have h2 := hobj_mix x t y s ε he0.le he1.le
            have h3a := le_abs_self (multiCentObj m Θ f M x t - multiCentObj m Θ f M y s)
            have h3 : ε * (multiCentObj m Θ f M x t - multiCentObj m Θ f M y s) ≤
                ε * (|multiCentObj m Θ f M x t - multiCentObj m Θ f M y s| + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) he0.le
            have h4 : ε * (|multiCentObj m Θ f M x t - multiCentObj m Θ f M y s| + 1) <
                multiCentObj m Θ f M x t - sSup (multiDecValues m Θ f M cost) := by
              have := (lt_div_iff₀ hΔ).mp heδ
              linarith
            nlinarith
          exact ⟨le_antisymm hle1 hle2, hCne, hCbdd, hDne, hDbdd⟩
