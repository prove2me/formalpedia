-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:41:11.113644+00:00
-- url     : https://prove2.me/submissions/fed69d63-269e-4745-991f-68c75e62f623

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 2 ≤ n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (hDD : M.StrictDD) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f)
    (hConditions : ∃ (θ : Profile Θ) (d : ℝ),
      affQ M Θ f θ = Finset.univ ∧
      (∀ θ' : Profile Θ, (∀ i, |virtualCost Θ f i (θ' i) - virtualCost Θ f i (θ i)| ≤ d) →
        affQ M Θ f θ' = Finset.univ) ∧
      (∀ i, 3 ≤ (Θ i).card) ∧
      (∀ i, ∀ a b : ℝ, Consecutive (Θ i) a b →
        virtualCost Θ f i b - virtualCost Θ f i a ≤ d / 2)) :
    optDecLin Θ f M.gcs (simplex n) = optCent Θ f M.gcs (simplex n) ∧
      ValuesWellDefined Θ f M.gcs := by
        classical
        obtain ⟨θ0, d, hall, hnb, hcard, hgap⟩ := hConditions
        obtain ⟨hne, hpos, hfpos, hsum⟩ := hTypes
        set C := {r | ∃ x t : Profile Θ → Fin n → ℝ, IsCentFeasible f (simplex n) x t ∧
          r = centObj f M.gcs x t} with hC
        set D := {r | ∃ (q : Profile Θ → Finset (Fin n)) (p x : Profile Θ → Fin n → ℝ),
          IsDecLinFeasible f M.gcs (simplex n) q p x ∧ r = decLinObj f M.gcs p x} with hD
        have hDC : D ⊆ C := by
          rintro r ⟨q, p, x, ⟨hc, _⟩, rfl⟩
          exact ⟨x, fun θ i => p θ i * x θ i, hc, by simp [decLinObj, centObj, CS]⟩
        have hsimp : simplex n = stdSimplex ℝ (Fin n) := rfl
        have hcont : ∀ K : ℝ, Continuous (fun y : Fin n → ℝ => M.gcs y - ∑ i, K * y i) := by
          intro K
          unfold QuadraticMarket.gcs
          fun_prop
        have hsne : (simplex n).Nonempty := by
          refine ⟨fun j => if j = ⟨0, by omega⟩ then 1 else 0, ?_, ?_⟩
          · intro j; dsimp only; split_ifs <;> norm_num
          · simp
        have hGb : ∃ B, ∀ y ∈ simplex n, M.gcs y ≤ B := by
          obtain ⟨B, hB⟩ := (isCompact_stdSimplex ℝ (Fin n)).exists_bound_of_continuousOn
            (f := M.gcs) (by simpa using (hcont 0).continuousOn)
          exact ⟨B, fun y hy => (le_abs_self _).trans (hB y hy)⟩
        have hdecomp : ∀ (g : Profile Θ → ℝ) (i : Fin n),
            expect f g = ∑ c ∈ Θ i, f i c * interim f g i c := by
          intro g i
          unfold expect interim
          have : ∀ θ : Profile Θ, prob f θ * g θ =
              ∑ c ∈ Θ i, (if (θ i : ℝ) = c then f i c * (probOthers f i θ * g θ) else 0) := by
            intro θ
            rw [Finset.sum_ite_eq _ _ (fun c => f i c * (probOthers f i θ * g θ)), if_pos (θ i).2]
            unfold prob probOthers
            rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (θ j)) (Finset.mem_univ i)]
            ring
          simp_rw [this]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun θ _ => ?_)
          split_ifs <;> simp
        have hinterim_lin : ∀ (g h : Profile Θ → ℝ) (i : Fin n) (c k : ℝ),
            interim f (fun θ => g θ - k * h θ) i c = interim f g i c - k * interim f h i c := by
          intro g h i c k
          unfold interim
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun θ _ => ?_)
          split_ifs <;> ring
        have hpo_nn : ∀ i (θ : Profile Θ), 0 ≤ probOthers f i θ := fun i θ =>
          Finset.prod_nonneg (fun j _ => (hfpos j _ (θ j).2).le)
        have hprob_nn : ∀ θ : Profile Θ, 0 ≤ prob f θ := fun θ =>
          Finset.prod_nonneg (fun j _ => (hfpos j _ (θ j).2).le)
        have hf_le : ∀ i, ∀ c ∈ Θ i, f i c ≤ 1 := by
          intro i c hc
          rw [← hsum i]
          exact Finset.single_le_sum (fun b hb => (hfpos i b hb).le) hc
        have hprob_le : ∀ θ : Profile Θ, prob f θ ≤ 1 := fun θ =>
          Finset.prod_le_one (fun j _ => (hfpos j _ (θ j).2).le) (fun j _ => hf_le j _ (θ j).2)
        have hCb : BddAbove C := by
          obtain ⟨B, hB⟩ := hGb
          refine ⟨max B 0 * Fintype.card (Profile Θ), ?_⟩
          rintro r ⟨x, t, ⟨hIC, hIR, hX⟩, rfl⟩
          have ht : ∀ i, 0 ≤ expect f (fun θ => t θ i) := by
            intro i
            rw [hdecomp _ i]
            refine Finset.sum_nonneg (fun c hc => mul_nonneg (hfpos i c hc).le ?_)
            have h1 := hIR i c hc
            unfold utility at h1
            rw [hinterim_lin] at h1
            have h2 : 0 ≤ interim f (fun θ => x θ i) i c := by
              unfold interim
              refine Finset.sum_nonneg (fun θ _ => ?_)
              split_ifs
              · exact mul_nonneg (hpo_nn i θ) ((hX θ).1 i)
              · exact le_rfl
            nlinarith [hpos i c hc]
          have hsplit : centObj f M.gcs x t =
              expect f (fun θ => M.gcs (x θ)) - ∑ i, expect f (fun θ => t θ i) := by
            simp only [centObj, expect, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
            congr 1
            exact Finset.sum_comm
          have hg : expect f (fun θ => M.gcs (x θ)) ≤ max B 0 * Fintype.card (Profile Θ) := by
            unfold expect
            calc ∑ θ, prob f θ * M.gcs (x θ) ≤ ∑ _θ : Profile Θ, max B 0 := by
                  refine Finset.sum_le_sum (fun θ _ => ?_)
                  calc prob f θ * M.gcs (x θ) ≤ prob f θ * max B 0 :=
                        mul_le_mul_of_nonneg_left ((hB _ (hX θ)).trans (le_max_left _ _)) (hprob_nn θ)
                    _ ≤ max B 0 := mul_le_of_le_one_left (le_max_right _ _) (hprob_le θ)
              _ = max B 0 * Fintype.card (Profile Θ) := by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
          show centObj f M.gcs x t ≤ _
          rw [hsplit]
          have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => ht i)
          linarith
        have hW : ∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, ∀ k : ℝ,
            interim f (fun _ : Profile Θ => k) i a = interim f (fun _ : Profile Θ => k) i b := by
          intro i a ha b hb k
          unfold interim
          let ea : ↥(Θ i) := ⟨a, ha⟩
          let eb : ↥(Θ i) := ⟨b, hb⟩
          let σ : Profile Θ ≃ Profile Θ := Equiv.piCongrRight
            (fun j => Equiv.swap (Function.update θ0 i ea j) (Function.update θ0 i eb j))
          have hσi : ∀ θ : Profile Θ, σ θ i = Equiv.swap ea eb (θ i) := by
            intro θ; simp [σ]
          have hσj : ∀ θ : Profile Θ, ∀ j, j ≠ i → σ θ j = θ j := by
            intro θ j hj; simp [σ, Function.update_of_ne hj]
          refine Fintype.sum_equiv σ _ _ (fun θ => ?_)
          have hpo : probOthers f i (σ θ) = probOthers f i θ := by
            unfold probOthers
            refine Finset.prod_congr rfl (fun j hj => ?_)
            rw [hσj θ j (Finset.ne_of_mem_erase hj)]
          have hiff : ((σ θ i : ℝ) = b) ↔ ((θ i : ℝ) = a) := by
            rw [hσi]
            have e1 : ((Equiv.swap ea eb (θ i) : ℝ) = b) ↔ Equiv.swap ea eb (θ i) = eb := by
              rw [Subtype.ext_iff]
            have e2 : ((θ i : ℝ) = a) ↔ θ i = ea := by rw [Subtype.ext_iff]
            rw [e1, e2, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
          rw [hpo]
          by_cases h : (θ i : ℝ) = a
          · rw [if_pos h, if_pos (hiff.mpr h)]
          · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
        have hDne : D.Nonempty := by
          set K : ℝ := ∑ i, ∑ c ∈ Θ i, c with hK
          have hKa : ∀ i, ∀ a ∈ Θ i, a ≤ K := by
            intro i a ha
            calc a ≤ ∑ c ∈ Θ i, c := Finset.single_le_sum (fun c hc => (hpos i c hc).le) ha
              _ ≤ K := Finset.single_le_sum (f := fun i => ∑ c ∈ Θ i, c)
                    (fun j _ => Finset.sum_nonneg (fun c hc => (hpos j c hc).le)) (Finset.mem_univ i)
          obtain ⟨y0, hy0, hmax⟩ := (isCompact_stdSimplex ℝ (Fin n)).exists_isMaxOn hsne
            (hcont K).continuousOn
          refine ⟨_, fun _ => Finset.univ, fun _ _ => K, fun _ => y0, ⟨⟨?_, ?_, fun _ => hy0⟩, ?_⟩, rfl⟩
          · intro i a ha b hb
            exact le_of_eq (hW i b hb a ha _)
          · intro i a ha
            unfold utility interim
            refine Finset.sum_nonneg (fun θ _ => ?_)
            split_ifs
            · refine mul_nonneg (hpo_nn i θ) ?_
              have : 0 ≤ y0 i := hy0.1 i
              nlinarith [hKa i a ha]
            · exact le_rfl
          · intro θ
            refine ⟨hy0, by simp, fun z hz _ => ?_⟩
            have := hmax hz
            simpa [CS] using this
        have hge : sSup C ≤ sSup D := by
          have hdem : ∀ θ : Profile Θ, M.IsDemand Finset.univ (vvec Θ f θ) (affX M Θ f θ) := by
            intro θ
            obtain ⟨y0, hy0, hmax⟩ := (isCompact_stdSimplex ℝ (Fin n)).exists_isMaxOn hsne
              (show Continuous (fun y : Fin n → ℝ => M.gcs y - ∑ i, vvec Θ f θ i * y i) by
                unfold QuadraticMarket.gcs; fun_prop).continuousOn
            exact Classical.epsilon_spec (p := M.IsDemand Finset.univ (vvec Θ f θ))
              ⟨y0, hy0, by simp, fun z hz _ => hmax hz⟩
          have hinterim_mul : ∀ (h : ℝ → ℝ) (g : Profile Θ → ℝ) (i : Fin n) (c : ℝ),
              interim f (fun θ => h (θ i) * g θ) i c = h c * interim f g i c := by
            intro h g i c
            unfold interim
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun θ _ => ?_)
            split_ifs with hc
            · beta_reduce; rw [hc]; ring
            · ring
          have hmy : ∀ x t : Profile Θ → Fin n → ℝ, IsCentFeasible f (simplex n) x t → ∀ i,
              expect f (fun θ => virtualCost Θ f i (θ i) * x θ i) ≤ expect f (fun θ => t θ i) := by
            intro x t hfe i
            obtain ⟨hIC, hIR, -⟩ := hfe
            set X : ℝ → ℝ := fun c => interim f (fun θ => x θ i) i c with hXdef
            set T : ℝ → ℝ := fun c => interim f (fun θ => t θ i) i c with hTdef
            have hUeq : ∀ a b, utility f x t i b a = T b - a * X b := by
              intro a b
              unfold utility
              rw [hinterim_lin]
            have hpred : ∀ c ∈ Θ i, ∀ c' ∈ Θ i, c < c' → (∀ b ∈ Θ i, c < b → c' ≤ b) →
                pred Θ i c' = c := by
              intro c hc c' hc' hlt hmin
              have hne' : ((Θ i).filter (· < c')).Nonempty := ⟨c, Finset.mem_filter.mpr ⟨hc, hlt⟩⟩
              rw [pred, dif_pos hne']
              refine le_antisymm (Finset.max'_le _ _ _ (fun b hb => ?_))
                (Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hc, hlt⟩))
              obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
              by_contra hcon
              push_neg at hcon
              exact absurd (hmin b hb1 hcon) (not_le.mpr hb2)
            have hU : ∀ m : ℕ, ∀ c ∈ Θ i, ((Θ i).filter (c < ·)).card = m →
                ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * X b ≤ T c - c * X c := by
              intro m
              induction m using Nat.strong_induction_on with
              | _ m ih =>
                intro c hc hm
                by_cases hS : ((Θ i).filter (c < ·)).Nonempty
                · set S := (Θ i).filter (c < ·) with hSdef
                  set c' := S.min' hS with hc'def
                  have hc'S : c' ∈ S := Finset.min'_mem S hS
                  obtain ⟨hc'Θ, hcc'⟩ := Finset.mem_filter.mp hc'S
                  have hmin : ∀ b ∈ Θ i, c < b → c' ≤ b := fun b hb hcb =>
                    Finset.min'_le S b (Finset.mem_filter.mpr ⟨hb, hcb⟩)
                  have herase : S.erase c' = (Θ i).filter (c' < ·) := by
                    ext b
                    simp only [Finset.mem_erase, Finset.mem_filter, hSdef]
                    constructor
                    · rintro ⟨hne, hb, hcb⟩
                      exact ⟨hb, lt_of_le_of_ne (hmin b hb hcb) (Ne.symm hne)⟩
                    · rintro ⟨hb, hcb⟩
                      exact ⟨ne_of_gt hcb, hb, lt_trans hcc' hcb⟩
                  have hcard' : ((Θ i).filter (c' < ·)).card < m := by
                    rw [← herase, Finset.card_erase_of_mem hc'S, ← hm]
                    exact Nat.sub_lt (Finset.card_pos.mpr hS) one_pos
                  have ih' := ih _ hcard' c' hc'Θ rfl
                  rw [← Finset.add_sum_erase S _ hc'S, herase, hpred c hc c' hc'Θ hcc' hmin]
                  have hic := hIC i c hc c' hc'Θ
                  rw [hUeq, hUeq] at hic
                  linarith
                · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty]
                  have := hIR i c hc
                  rw [hUeq] at this
                  linarith
            have hU' : ∀ c ∈ Θ i,
                ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * X b ≤ T c - c * X c :=
              fun c hc => hU _ c hc rfl
            have hcdf : ∀ b ∈ Θ i, cdfF Θ f i (pred Θ i b) * (b - pred Θ i b) =
                (∑ c ∈ (Θ i).filter (· < b), f i c) * (b - pred Θ i b) := by
              intro b hb
              by_cases hne' : ((Θ i).filter (· < b)).Nonempty
              · congr 1
                unfold cdfF
                congr 1
                ext c
                simp only [Finset.mem_filter]
                constructor
                · rintro ⟨hc, hcm⟩
                  refine ⟨hc, lt_of_le_of_lt hcm ?_⟩
                  rw [pred, dif_pos hne']
                  exact (Finset.mem_filter.mp (Finset.max'_mem _ hne')).2
                · rintro ⟨hc, hcb⟩
                  refine ⟨hc, ?_⟩
                  rw [pred, dif_pos hne']
                  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hc, hcb⟩)
              · have : pred Θ i b = b := by rw [pred, dif_neg hne']
                rw [this, sub_self, mul_zero, mul_zero]
            have hv : ∀ b ∈ Θ i, f i b * virtualCost Θ f i b =
                f i b * b + cdfF Θ f i (pred Θ i b) * (b - pred Θ i b) := by
              intro b hb
              have := (hfpos i b hb).ne'
              unfold virtualCost
              field_simp
            rw [hdecomp _ i, hdecomp (fun θ => t θ i) i]
            have hL : ∑ c ∈ Θ i, f i c * interim f (fun θ => virtualCost Θ f i (θ i) * x θ i) i c =
                ∑ c ∈ Θ i, f i c * c * X c +
                  ∑ b ∈ Θ i, (∑ c ∈ (Θ i).filter (· < b), f i c) * (b - pred Θ i b) * X b := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun b hb => ?_)
              rw [hinterim_mul (virtualCost Θ f i) (fun θ => x θ i) i b, ← mul_assoc, hv b hb,
                hcdf b hb]
              ring
            have hR : ∑ c ∈ Θ i, f i c * c * X c +
                  ∑ b ∈ Θ i, (∑ c ∈ (Θ i).filter (· < b), f i c) * (b - pred Θ i b) * X b ≤
                ∑ c ∈ Θ i, f i c * T c := by
              have hswap : ∑ b ∈ Θ i, (∑ c ∈ (Θ i).filter (· < b), f i c) * (b - pred Θ i b) * X b =
                  ∑ c ∈ Θ i, f i c * ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * X b := by
                simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun b _ => ?_))
                split_ifs <;> ring
              rw [hswap, ← Finset.sum_add_distrib]
              refine Finset.sum_le_sum (fun c hc => ?_)
              have := mul_le_mul_of_nonneg_left (hU' c hc) (hfpos i c hc).le
              nlinarith
            rw [hL]
            exact hR
          set V := expect f (fun θ => M.gcs (affX M Θ f θ) -
            ∑ i, vvec Θ f θ i * affX M Θ f θ i) with hV
          have hub : ∀ r ∈ C, r ≤ V := by
            rintro r ⟨x, t, hfe, rfl⟩
            have hsplit : centObj f M.gcs x t =
                expect f (fun θ => M.gcs (x θ)) - ∑ i, expect f (fun θ => t θ i) := by
              simp only [centObj, expect, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
              congr 1
              exact Finset.sum_comm
            have hsplit2 : expect f (fun θ => M.gcs (x θ) - ∑ i, vvec Θ f θ i * x θ i) =
                expect f (fun θ => M.gcs (x θ)) -
                  ∑ i, expect f (fun θ => virtualCost Θ f i (θ i) * x θ i) := by
              simp only [expect, vvec, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
              congr 1
              exact Finset.sum_comm
            have h1 : expect f (fun θ => M.gcs (x θ) - ∑ i, vvec Θ f θ i * x θ i) ≤ V := by
              unfold expect
              refine Finset.sum_le_sum (fun θ _ => mul_le_mul_of_nonneg_left ?_ (hprob_nn θ))
              exact (hdem θ).2.2 (x θ) (hfe.2.2 θ) (by simp)
            have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hmy x t hfe i)
            rw [hsplit]
            linarith
          have hach : V ≤ sSup D := by
            have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
            have hypt : ∀ y z : Fin n → ℝ,
                M.gcs z - ∑ i, (M.c i - ∑ j, M.D i j * y j) * z i ≤
                M.gcs y - ∑ i, (M.c i - ∑ j, M.D i j * y j) * y i := by
              intro y z
              have hDpd : M.D.PosDef := hM.2.1.inv
              have hsym : ∀ i j, M.D i j = M.D j i := by
                intro i j
                have := hDpd.1.apply j i
                simpa using this
              have hq : 0 ≤ ∑ i, ∑ j, (z i - y i) * M.D i j * (z j - y j) := by
                have := hDpd.posSemidef.dotProduct_mulVec_nonneg (z - y)
                simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using this
              have hzy : ∑ i, ∑ j, y i * M.D i j * z j = ∑ i, ∑ j, z i * M.D i j * y j := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
                rw [hsym j i]; ring
              have hex : ∑ i, ∑ j, (z i - y i) * M.D i j * (z j - y j) =
                  ∑ i, ∑ j, z i * M.D i j * z j - ∑ i, ∑ j, z i * M.D i j * y j -
                  ∑ i, ∑ j, y i * M.D i j * z j + ∑ i, ∑ j, y i * M.D i j * y j := by
                simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
                ring
              have hg : ∀ w : Fin n → ℝ, ∑ i, (M.c i - ∑ j, M.D i j * y j) * w i =
                  ∑ i, M.c i * w i - ∑ i, ∑ j, w i * M.D i j * y j := by
                intro w
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [sub_mul, Finset.sum_mul]
                congr 1
                exact Finset.sum_congr rfl (fun j _ => by ring)
              rw [hg, hg]
              unfold QuadraticMarket.gcs
              linarith
            obtain ⟨Lop, hLop⟩ : ∃ Lop : (Profile Θ → Fin n → ℝ) →
                ((((i : Fin n) × ↥(Θ i)) → ℝ) →ₗ[ℝ] (Profile Θ → ℝ)),
                ∀ x β θ, Lop x β θ = ∑ i, β ⟨i, θ i⟩ * x θ i := by
              refine ⟨fun x => { toFun := fun β θ => ∑ i, β ⟨i, θ i⟩ * x θ i,
                                 map_add' := ?_, map_smul' := ?_ }, fun x β θ => rfl⟩
              · intro a b; funext θ
                simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
              · intro a b; funext θ
                simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]
            have hmyEq : ∀ (x : Profile Θ → Fin n → ℝ) (i : Fin n),
                expect f (fun θ => virtualCost Θ f i (θ i) * x θ i) =
                ∑ c ∈ Θ i, f i c * (c * interim f (fun θ => x θ i) i c +
                  ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * interim f (fun θ => x θ i) i b) := by
              intro x i
              set X : ℝ → ℝ := fun c => interim f (fun θ => x θ i) i c with hXdef
              have hcdf : ∀ b ∈ Θ i, cdfF Θ f i (pred Θ i b) * (b - pred Θ i b) =
                  (∑ c ∈ (Θ i).filter (· < b), f i c) * (b - pred Θ i b) := by
                intro b hb
                by_cases hne' : ((Θ i).filter (· < b)).Nonempty
                · congr 1
                  unfold cdfF
                  congr 1
                  ext c
                  simp only [Finset.mem_filter]
                  constructor
                  · rintro ⟨hc, hcm⟩
                    refine ⟨hc, lt_of_le_of_lt hcm ?_⟩
                    rw [pred, dif_pos hne']
                    exact (Finset.mem_filter.mp (Finset.max'_mem _ hne')).2
                  · rintro ⟨hc, hcb⟩
                    refine ⟨hc, ?_⟩
                    rw [pred, dif_pos hne']
                    exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hc, hcb⟩)
                · have : pred Θ i b = b := by rw [pred, dif_neg hne']
                  rw [this, sub_self, mul_zero, mul_zero]
              have hv : ∀ b ∈ Θ i, f i b * virtualCost Θ f i b =
                  f i b * b + cdfF Θ f i (pred Θ i b) * (b - pred Θ i b) := by
                intro b hb
                have := (hfpos i b hb).ne'
                unfold virtualCost
                field_simp
              rw [hdecomp _ i]
              have hL : ∑ c ∈ Θ i, f i c * interim f (fun θ => virtualCost Θ f i (θ i) * x θ i) i c =
                  ∑ c ∈ Θ i, f i c * c * X c +
                    ∑ b ∈ Θ i, (∑ c ∈ (Θ i).filter (· < b), f i c) * (b - pred Θ i b) * X b := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl (fun b hb => ?_)
                rw [hinterim_mul (virtualCost Θ f i) (fun θ => x θ i) i b, ← mul_assoc, hv b hb,
                  hcdf b hb]
                ring
              have hswap : ∑ b ∈ Θ i, (∑ c ∈ (Θ i).filter (· < b), f i c) * (b - pred Θ i b) * X b =
                    ∑ c ∈ Θ i, f i c * ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * X b := by
                  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun b _ => ?_))
                  split_ifs <;> ring
              rw [hL, hswap, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun c _ => by ring)
            have himpl : ∀ xs : Profile Θ → Fin n → ℝ, (∀ θ, xs θ ∈ simplex n) →
                (∀ (θ : Profile Θ) (i : Fin n) (c' : ↥(Θ i)), (θ i : ℝ) < c' →
                  xs (Function.update θ i c') i ≤ xs θ i) →
                (∀ β, Lop xs β = 0 → β = 0) →
                expect f (fun θ => M.gcs (xs θ) - ∑ i, vvec Θ f θ i * xs θ i) ≤ sSup D := by
              intro xs hxS hpt0 hinj
              set Xs : Fin n → ℝ → ℝ := fun i c => interim f (fun θ => xs θ i) i c with hXs
              set Ts : Fin n → ℝ → ℝ := fun i c => c * Xs i c +
                ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * Xs i b with hTs
              set g : Profile Θ → Fin n → ℝ := fun θ i => M.c i - ∑ j, M.D i j * xs θ j with hg
              have hprob_pos : ∀ θ : Profile Θ, 0 < prob f θ := fun θ =>
                Finset.prod_pos (fun j _ => hfpos j _ (θ j).2)
              have hsolve : ∀ h : ((i : Fin n) × ↥(Θ i)) → ℝ, ∃ u : Profile Θ → ℝ,
                  ∀ i (c : ↥(Θ i)), ∑ θ : Profile Θ, (if θ i = c then u θ * xs θ i else 0) = h ⟨i, c⟩ := by
                intro h
                obtain ⟨R, hR⟩ := (Lop xs).exists_leftInverse_of_injective
                  (LinearMap.ker_eq_bot'.mpr hinj)
                refine ⟨fun θ => ∑ s, h s * R (fun θ' => if θ = θ' then 1 else 0) s, fun i c => ?_⟩
                set e : ((i : Fin n) × ↥(Θ i)) → ℝ := Pi.single ⟨i, c⟩ 1 with he
                have hLe : ∀ θ : Profile Θ, Lop xs e θ = if θ i = c then xs θ i else 0 := by
                  intro θ
                  rw [hLop, Finset.sum_eq_single i]
                  · by_cases hc : θ i = c
                    · rw [if_pos hc, he, hc, Pi.single_eq_same, one_mul]
                    · rw [if_neg hc, he, Pi.single_eq_of_ne, zero_mul]
                      intro h'
                      exact hc (by simpa using h')
                  · intro j _ hj
                    rw [he, Pi.single_eq_of_ne, zero_mul]
                    intro h'
                    exact hj (congrArg Sigma.fst h')
                  · simp
                have hRe : R (Lop xs e) = e := by
                  have := LinearMap.congr_fun hR e
                  simpa using this
                calc _ = ∑ θ : Profile Θ, ∑ s, h s * (Lop xs e θ *
                        R (fun θ' => if θ = θ' then 1 else 0) s) := by
                      refine Finset.sum_congr rfl (fun θ _ => ?_)
                      rw [hLe]
                      split_ifs
                      · rw [Finset.sum_mul]
                        exact Finset.sum_congr rfl (fun s _ => by ring)
                      · simp
                  _ = ∑ s, h s * R (Lop xs e) s := by
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl (fun s _ => ?_)
                      rw [← Finset.mul_sum, R.pi_apply_eq_sum_univ (Lop xs e), Finset.sum_apply]
                      rfl
                  _ = h ⟨i, c⟩ := by
                      rw [hRe, Finset.sum_eq_single ⟨i, c⟩]
                      · rw [he, Pi.single_eq_same, mul_one]
                      · intro s _ hs
                        rw [he, Pi.single_eq_of_ne hs, mul_zero]
                      · simp
              have hk : ∃ k : Profile Θ → ℝ, ∀ i, ∀ c ∈ Θ i,
                  interim f (fun θ => (g θ i + k θ) * xs θ i) i c = Ts i c := by
                obtain ⟨u, hu⟩ := hsolve (fun s => f s.1 s.2 *
                  (Ts s.1 s.2 - interim f (fun θ => g θ s.1 * xs θ s.1) s.1 s.2))
                refine ⟨fun θ => u θ / prob f θ, fun i c hc => ?_⟩
                have h1 := hu i ⟨c, hc⟩
                have h2 : f i c * interim f (fun θ => u θ / prob f θ * xs θ i) i c =
                    f i c * (Ts i c - interim f (fun θ => g θ i * xs θ i) i c) := by
                  rw [← h1]
                  unfold interim
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun θ _ => ?_)
                  by_cases hθ : (θ i : ℝ) = c
                  · rw [if_pos hθ, if_pos (Subtype.ext hθ)]
                    have hpr : prob f θ = f i c * probOthers f i θ := by
                      unfold prob probOthers
                      rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (θ j)) (Finset.mem_univ i),
                        hθ]
                    have hp0 := (hprob_pos θ).ne'
                    rw [← mul_assoc, ← hpr]
                    field_simp
                  · rw [if_neg hθ, if_neg (fun h' => hθ (by rw [h'])), mul_zero]
                have h3 := mul_left_cancel₀ (hfpos i c hc).ne' h2
                have h4 : interim f (fun θ => (g θ i + u θ / prob f θ) * xs θ i) i c =
                    interim f (fun θ => g θ i * xs θ i) i c +
                    interim f (fun θ => u θ / prob f θ * xs θ i) i c := by
                  unfold interim
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl (fun θ _ => ?_)
                  split_ifs <;> ring
                rw [h4, h3]; ring
              have hICs : ∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, Ts i b - a * Xs i b ≤ Ts i a - a * Xs i a := by
                intro i
                have hpl : ∀ b, pred Θ i b ≤ b := by
                  intro b
                  unfold pred
                  split_ifs with hne'
                  · exact ((Finset.mem_filter.mp (Finset.max'_mem _ hne')).2).le
                  · exact le_rfl
                have hpred : ∀ c ∈ Θ i, ∀ c' ∈ Θ i, c < c' → (∀ b ∈ Θ i, c < b → c' ≤ b) →
                    pred Θ i c' = c := by
                  intro c hc c' hc' hlt hmin
                  have hne' : ((Θ i).filter (· < c')).Nonempty := ⟨c, Finset.mem_filter.mpr ⟨hc, hlt⟩⟩
                  rw [pred, dif_pos hne']
                  refine le_antisymm (Finset.max'_le _ _ _ (fun b hb => ?_))
                    (Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hc, hlt⟩))
                  obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
                  by_contra hcon
                  exact absurd (hmin b hb1 (lt_of_not_ge hcon)) (not_le.mpr hb2)
                have hmono : ∀ c ∈ Θ i, ∀ c' ∈ Θ i, c ≤ c' → Xs i c' ≤ Xs i c := by
                  intro c hc c' hc' hcc
                  rcases eq_or_lt_of_le hcc with h | h
                  · rw [h]
                  have hpt : ∀ θ : Profile Θ, (θ i : ℝ) = c →
                      xs (Function.update θ i ⟨c', hc'⟩) i ≤ xs θ i := by
                    intro θ hθ
                    exact hpt0 θ i ⟨c', hc'⟩ (by rw [hθ]; exact h)
                  let ea : ↥(Θ i) := ⟨c, hc⟩
                  let eb : ↥(Θ i) := ⟨c', hc'⟩
                  let σ : Profile Θ ≃ Profile Θ := Equiv.piCongrRight
                    (fun j => Equiv.swap (Function.update θ0 i ea j) (Function.update θ0 i eb j))
                  have hσi : ∀ θ : Profile Θ, σ θ i = Equiv.swap ea eb (θ i) := by
                    intro θ; simp [σ]
                  have hσj : ∀ θ : Profile Θ, ∀ j, j ≠ i → σ θ j = θ j := by
                    intro θ j hj; simp [σ, Function.update_of_ne hj]
                  simp only [hXs, interim]
                  rw [← Equiv.sum_comp σ]
                  refine Finset.sum_le_sum (fun θ _ => ?_)
                  by_cases hθ : (θ i : ℝ) = c
                  · have hθe : θ i = ea := Subtype.ext hθ
                    have hσθ : σ θ = Function.update θ i eb := by
                      funext j
                      by_cases hj : j = i
                      · subst hj; rw [hσi, Function.update_self, hθe, Equiv.swap_apply_left]
                      · rw [hσj θ j hj, Function.update_of_ne hj]
                    have hpo : probOthers f i (Function.update θ i eb) = probOthers f i θ := by
                      unfold probOthers
                      refine Finset.prod_congr rfl (fun j hj => ?_)
                      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
                    rw [hσθ, if_pos (by simp [eb]), if_pos hθ, hpo]
                    exact mul_le_mul_of_nonneg_left (hpt θ hθ) (hpo_nn i θ)
                  · rw [if_neg hθ, if_neg]
                    intro hc2
                    apply hθ
                    have : σ θ i = eb := Subtype.ext hc2
                    rw [hσi, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at this
                    rw [this]
                have htele : ∀ b ∈ Θ i, ∀ m : ℕ, ∀ a ∈ Θ i, a ≤ b →
                    ((Θ i).filter (fun b' => a < b' ∧ b' ≤ b)).card = m →
                    ∑ b' ∈ (Θ i).filter (fun b' => a < b' ∧ b' ≤ b), (b' - pred Θ i b') = b - a := by
                  intro b hb m
                  induction m using Nat.strong_induction_on with
                  | _ m ih =>
                    intro a ha hab hm
                    rcases eq_or_lt_of_le hab with h | h
                    · subst h
                      rw [sub_self]
                      refine Finset.sum_eq_zero (fun b' hb' => ?_)
                      obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hb'
                      linarith
                    · set S := (Θ i).filter (a < ·) with hSdef
                      have hS : S.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, h⟩⟩
                      set c' := S.min' hS with hc'def
                      obtain ⟨hc'Θ, hac'⟩ := Finset.mem_filter.mp (Finset.min'_mem S hS)
                      have hmin : ∀ x ∈ Θ i, a < x → c' ≤ x := fun x hx hax =>
                        Finset.min'_le S x (Finset.mem_filter.mpr ⟨hx, hax⟩)
                      have hc'b : c' ≤ b := hmin b hb h
                      have hmem : c' ∈ (Θ i).filter (fun b' => a < b' ∧ b' ≤ b) :=
                        Finset.mem_filter.mpr ⟨hc'Θ, hac', hc'b⟩
                      have herase : ((Θ i).filter (fun b' => a < b' ∧ b' ≤ b)).erase c' =
                          (Θ i).filter (fun b' => c' < b' ∧ b' ≤ b) := by
                        ext x
                        simp only [Finset.mem_erase, Finset.mem_filter]
                        constructor
                        · rintro ⟨hne, hx, hax, hxb⟩
                          exact ⟨hx, lt_of_le_of_ne (hmin x hx hax) (Ne.symm hne), hxb⟩
                        · rintro ⟨hx, hcx, hxb⟩
                          exact ⟨ne_of_gt hcx, hx, lt_trans hac' hcx, hxb⟩
                      have hcard' : ((Θ i).filter (fun b' => c' < b' ∧ b' ≤ b)).card < m := by
                        rw [← herase, Finset.card_erase_of_mem hmem, ← hm]
                        exact Nat.sub_lt (Finset.card_pos.mpr ⟨c', hmem⟩) one_pos
                      rw [← Finset.add_sum_erase _ _ hmem, herase, ih _ hcard' c' hc'Θ hc'b rfl,
                        hpred a ha c' hc'Θ hac' hmin]
                      ring
                have hsplitS : ∀ a b, a ≤ b →
                    ∑ b' ∈ (Θ i).filter (a < ·), (b' - pred Θ i b') * Xs i b' =
                      ∑ b' ∈ (Θ i).filter (fun b' => a < b' ∧ b' ≤ b), (b' - pred Θ i b') * Xs i b' +
                      ∑ b' ∈ (Θ i).filter (b < ·), (b' - pred Θ i b') * Xs i b' := by
                  intro a b hab
                  rw [← Finset.sum_filter_add_sum_filter_not ((Θ i).filter (a < ·)) (· ≤ b),
                    Finset.filter_filter, Finset.filter_filter]
                  congr 2
                  · ext x; simp only [Finset.mem_filter, not_le]
                    constructor
                    · rintro ⟨hx, -, hbx⟩; exact ⟨hx, hbx⟩
                    · rintro ⟨hx, hbx⟩; exact ⟨hx, lt_of_le_of_lt hab hbx, hbx⟩
                intro a ha b hb
                simp only [hTs]
                rcases le_total a b with hab | hab
                · rw [hsplitS a b hab]
                  have hT := htele b hb _ a ha hab rfl
                  have : (b - a) * Xs i b ≤
                      ∑ b' ∈ (Θ i).filter (fun b' => a < b' ∧ b' ≤ b), (b' - pred Θ i b') * Xs i b' := by
                    rw [← hT, Finset.sum_mul]
                    refine Finset.sum_le_sum (fun x hx => ?_)
                    obtain ⟨hx, -, hxb⟩ := Finset.mem_filter.mp hx
                    exact mul_le_mul_of_nonneg_left (hmono x hx b hb hxb) (by linarith [hpl x])
                  nlinarith
                · rw [hsplitS b a hab]
                  have hT := htele a ha _ b hb hab rfl
                  have : ∑ b' ∈ (Θ i).filter (fun b' => b < b' ∧ b' ≤ a), (b' - pred Θ i b') * Xs i b'
                      ≤ (a - b) * Xs i b := by
                    rw [← hT, Finset.sum_mul]
                    refine Finset.sum_le_sum (fun x hx => ?_)
                    obtain ⟨hx, hbx, -⟩ := Finset.mem_filter.mp hx
                    exact mul_le_mul_of_nonneg_left (hmono b hb x hx hbx.le) (by linarith [hpl x])
                  nlinarith
              obtain ⟨k, hkT⟩ := hk
              have hsum1 : ∀ θ, ∑ i, xs θ i = 1 := fun θ => (hxS θ).2
              have hut : ∀ i a b, b ∈ Θ i → utility f xs (fun θ i => (g θ i + k θ) * xs θ i) i b a =
                  Ts i b - a * Xs i b := by
                intro i a b hb
                unfold utility
                rw [hinterim_lin, hkT i b hb]
              refine le_csSup (hCb.mono hDC) ⟨fun _ => Finset.univ, fun θ i => g θ i + k θ, xs,
                ⟨⟨?_, ?_, fun θ => hxS θ⟩, fun θ => ⟨hxS θ, by simp, fun z hz _ => ?_⟩⟩, ?_⟩
              · intro i a ha b hb
                rw [hut i a b hb, hut i a a ha]
                exact hICs i a ha b hb
              · intro i a ha
                rw [hut i a a ha]
                simp only [hTs, add_sub_cancel_left]
                refine Finset.sum_nonneg (fun b hb => mul_nonneg ?_ ?_)
                · have : pred Θ i b ≤ b := by
                    unfold pred
                    split_ifs with hne'
                    · exact ((Finset.mem_filter.mp (Finset.max'_mem _ hne')).2).le
                    · exact le_rfl
                  linarith
                · simp only [hXs, interim]
                  refine Finset.sum_nonneg (fun θ _ => ?_)
                  split_ifs
                  · exact mul_nonneg (hpo_nn i θ) ((hxS θ).1 i)
                  · exact le_rfl
              · have h1 := hypt (xs θ) z
                have hz1 : ∑ i, z i = 1 := hz.2
                simp only [CS]
                simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hz1, hsum1 θ]
                simp only [hg]
                linarith
              · have hp : ∀ i, expect f (fun θ => (g θ i + k θ) * xs θ i) =
                    expect f (fun θ => virtualCost Θ f i (θ i) * xs θ i) := by
                  intro i
                  rw [hdecomp (fun θ => (g θ i + k θ) * xs θ i) i, hmyEq xs i]
                  refine Finset.sum_congr rfl (fun c hc => ?_)
                  rw [hkT i c hc]
                have hsp : ∀ t : Profile Θ → Fin n → ℝ,
                    expect f (fun θ => M.gcs (xs θ) - ∑ i, t θ i) =
                    expect f (fun θ => M.gcs (xs θ)) - ∑ i, expect f (fun θ => t θ i) := by
                  intro t
                  simp only [expect, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
                  congr 1
                  exact Finset.sum_comm
                simp only [decLinObj, CS]
                rw [hsp (fun θ i => (g θ i + k θ) * xs θ i), hsp (fun θ i => vvec Θ f θ i * xs θ i)]
                congr 1
                exact Finset.sum_congr rfl (fun i _ => (hp i).symm)
            obtain ⟨y, hyS, hypt0, hyinj⟩ : ∃ y : Profile Θ → Fin n → ℝ, (∀ θ, y θ ∈ simplex n) ∧
                (∀ (θ : Profile Θ) (i : Fin n) (c' : ↥(Θ i)), (θ i : ℝ) < c' →
                  y (Function.update θ i c') i ≤ y θ i) ∧ (∀ β, Lop y β = 0 → β = 0) := by
              set N : ℝ := (n : ℝ) with hNdef
              have hN0 : 0 < N := by linarith
              set K : ℝ := ∑ i, ∑ c ∈ Θ i, c with hK
              have hKa : ∀ i, ∀ a ∈ Θ i, a ≤ K := by
                intro i a ha
                calc a ≤ ∑ c ∈ Θ i, c := Finset.single_le_sum (fun c hc => (hpos i c hc).le) ha
                  _ ≤ K := Finset.single_le_sum (f := fun i => ∑ c ∈ Θ i, c)
                        (fun j _ => Finset.sum_nonneg (fun c hc => (hpos j c hc).le)) (Finset.mem_univ i)
              have hK0 : 0 ≤ K := Finset.sum_nonneg
                (fun j _ => Finset.sum_nonneg (fun c hc => (hpos j c hc).le))
              set τ : ℝ := 1 / (N * (K + 1)) with hτ
              have hτ0 : 0 < τ := by positivity
              have hτK : τ * K ≤ 1 / N := by
                rw [hτ, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hN0]
                nlinarith
              have hcardn : ∑ _i : Fin n, (1:ℝ) = N := by simp [hNdef]
              have hupd1 : ∀ (φ : (j : Fin n) → ↥(Θ j) → ℝ) (θ : Profile Θ) (i : Fin n) (a : ↥(Θ i)),
                  ∑ l, φ l (Function.update θ i a l) = φ i a + ∑ l ∈ Finset.univ.erase i, φ l (θ l) := by
                intro φ θ i a
                rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
                congr 1
                refine Finset.sum_congr rfl (fun l hl => ?_)
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
              have hupd2 : ∀ (φ : (j : Fin n) → ↥(Θ j) → ℝ) (θ : Profile Θ) (i j : Fin n), j ≠ i →
                  ∀ (a : ↥(Θ i)) (e : ↥(Θ j)),
                  ∑ l, φ l (Function.update (Function.update θ j e) i a l) =
                    φ i a + φ j e + ∑ l ∈ (Finset.univ.erase i).erase j, φ l (θ l) := by
                intro φ θ i j hji a e
                rw [hupd1, ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩),
                  Function.update_self, ← add_assoc]
                congr 1
                refine Finset.sum_congr rfl (fun l hl => ?_)
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
              refine ⟨fun θ i => 1 / N + τ * ((∑ j, (θ j : ℝ)) / N - θ i), ?_, ?_, ?_⟩
              · intro θ
                constructor
                · intro i
                  have h1 : (θ i : ℝ) ≤ K := hKa i _ (θ i).2
                  have h2 : 0 ≤ (∑ j, (θ j : ℝ)) / N :=
                    div_nonneg (Finset.sum_nonneg (fun j _ => (hpos j _ (θ j).2).le)) hN0.le
                  show 0 ≤ 1 / N + τ * ((∑ j, (θ j : ℝ)) / N - θ i)
                  nlinarith
                · have e1 : ∀ i : Fin n, 1 / N + τ * ((∑ j, (θ j : ℝ)) / N - θ i) =
                      (1 / N + τ * ((∑ j, (θ j : ℝ)) / N)) * 1 - τ * θ i := by intro i; ring
                  simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, hcardn]
                  field_simp
                  ring
              · intro θ i c' hc'
                have h1 := hupd1 (fun j a => (a : ℝ)) θ i c'
                have h2 := hupd1 (fun j a => (a : ℝ)) θ i (θ i)
                rw [Function.update_eq_self] at h2
                beta_reduce at h1 h2 ⊢
                rw [h1, h2, Function.update_self]
                have h3 : ((c' : ℝ) - θ i) / N ≤ (c' : ℝ) - θ i := by
                  apply div_le_self <;> linarith
                have h4 : ((c' : ℝ) + ∑ l ∈ Finset.univ.erase i, (θ l : ℝ)) / N - c' ≤
                    ((θ i : ℝ) + ∑ l ∈ Finset.univ.erase i, (θ l : ℝ)) / N - θ i := by
                  have : ((c' : ℝ) + ∑ l ∈ Finset.univ.erase i, (θ l : ℝ)) / N =
                    ((θ i : ℝ) + ∑ l ∈ Finset.univ.erase i, (θ l : ℝ)) / N + ((c' : ℝ) - θ i) / N := by
                    ring
                  rw [this]; linarith
                have := mul_le_mul_of_nonneg_left h4 hτ0.le
                linarith
              · intro β hβ
                have hF : ∀ θ : Profile Θ, (1 + τ * ∑ j, (θ j : ℝ)) * ∑ i, β ⟨i, θ i⟩ =
                    N * τ * ∑ i, (θ i : ℝ) * β ⟨i, θ i⟩ := by
                  intro θ
                  have h1 := congrFun hβ θ
                  rw [hLop] at h1
                  have e1 : ∀ i : Fin n, β ⟨i, θ i⟩ * (1 / N + τ * ((∑ j, (θ j : ℝ)) / N - θ i)) =
                      (1 / N + τ * ((∑ j, (θ j : ℝ)) / N)) * β ⟨i, θ i⟩ - τ * (θ i * β ⟨i, θ i⟩) := by
                    intro i; ring
                  simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, Pi.zero_apply] at h1
                  field_simp at h1
                  linarith
                have hmain : ∀ i : Fin n, ∃ gi : ℝ, (∀ a : ↥(Θ i), β ⟨i, a⟩ = gi) ∧
                    ∑ l, β ⟨l, θ0 l⟩ = N * gi := by
                  intro i
                  obtain ⟨j, hji⟩ : ∃ j : Fin n, j ≠ i := by
                    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
                    exact exists_ne i
                  obtain ⟨e1, he1, e2, he2, e3, he3, he12, -, -⟩ := Finset.two_lt_card.mp (hcard j)
                  obtain ⟨a1, ha1, a2, ha2, a3, ha3, ha12, ha13, ha23⟩ := Finset.two_lt_card.mp (hcard i)
                  set w := ∑ l ∈ (Finset.univ.erase i).erase j, (θ0 l : ℝ) with hw
                  set r0 := ∑ l ∈ (Finset.univ.erase i).erase j, β ⟨l, θ0 l⟩ with hr0
                  set r1 := ∑ l ∈ (Finset.univ.erase i).erase j, (θ0 l : ℝ) * β ⟨l, θ0 l⟩ with hr1
                  have Eq : ∀ (a : ↥(Θ i)) (e : ↥(Θ j)),
                      (1 + τ * ((a : ℝ) + e + w)) * (β ⟨i, a⟩ + β ⟨j, e⟩ + r0) =
                      N * τ * ((a : ℝ) * β ⟨i, a⟩ + (e : ℝ) * β ⟨j, e⟩ + r1) := by
                    intro a e
                    have h := hF (Function.update (Function.update θ0 j e) i a)
                    rw [hupd2 (fun l b => (b : ℝ)) θ0 i j hji a e,
                      hupd2 (fun l b => β ⟨l, b⟩) θ0 i j hji a e,
                      hupd2 (fun l b => (b : ℝ) * β ⟨l, b⟩) θ0 i j hji a e] at h
                    exact h
                  have hS0 : ∑ l, β ⟨l, θ0 l⟩ = β ⟨i, θ0 i⟩ + β ⟨j, θ0 j⟩ + r0 := by
                    have h := hupd2 (fun l b => β ⟨l, b⟩) θ0 i j hji (θ0 i) (θ0 j)
                    simpa using h
                  let E1 : ↥(Θ j) := ⟨e1, he1⟩
                  let E2 : ↥(Θ j) := ⟨e2, he2⟩
                  let A1 : ↥(Θ i) := ⟨a1, ha1⟩
                  let A2 : ↥(Θ i) := ⟨a2, ha2⟩
                  let A3 : ↥(Θ i) := ⟨a3, ha3⟩
                  have hne12 : e1 - e2 ≠ 0 := sub_ne_zero.mpr he12
                  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * (e1 - e2) = -(β ⟨j, E1⟩ - β ⟨j, E2⟩) :=
                    ⟨-(β ⟨j, E1⟩ - β ⟨j, E2⟩) / (e1 - e2), div_mul_cancel₀ _ hne12⟩
                  have haff : ∀ a : ↥(Θ i), β ⟨i, a⟩ = (β ⟨i, A1⟩ - s * a1) + s * a := by
                    intro a
                    have q1 := Eq a E1
                    have q2 := Eq a E2
                    have q3 := Eq A1 E1
                    have q4 := Eq A1 E2
                    have hz : τ * (e1 - e2) * (β ⟨i, a⟩ - ((β ⟨i, A1⟩ - s * a1) + s * a)) = 0 := by
                      have hE1 : (E1 : ℝ) = e1 := rfl
                      have hE2 : (E2 : ℝ) = e2 := rfl
                      have hA1 : (A1 : ℝ) = a1 := rfl
                      rw [hE1] at q1 q3
                      rw [hE2] at q2 q4
                      rw [hA1] at q3 q4
                      linear_combination q1 - q2 - q3 + q4 - τ * ((a : ℝ) - a1) * hs
                    rcases mul_eq_zero.mp hz with h | h
                    · exact absurd h (mul_ne_zero hτ0.ne' hne12)
                    · linarith
                  set gi := β ⟨i, A1⟩ - s * a1 with hgi
                  have hquad : ∀ (a : ↥(Θ i)) (e : ↥(Θ j)), τ * s * (1 - N) * (a : ℝ) ^ 2 +
                      (τ * (gi + β ⟨j, e⟩ + r0) + s * (1 + τ * (e + w)) - N * τ * gi) * a +
                      ((1 + τ * (e + w)) * (gi + β ⟨j, e⟩ + r0) - N * τ * (e * β ⟨j, e⟩ + r1)) = 0 := by
                    intro a e
                    have q := Eq a e
                    rw [haff a] at q
                    linear_combination q
                  have hlin : ∀ (a b : ↥(Θ i)) (e : ↥(Θ j)), (a : ℝ) ≠ b →
                      τ * s * (1 - N) * ((a : ℝ) + b) +
                      (τ * (gi + β ⟨j, e⟩ + r0) + s * (1 + τ * (e + w)) - N * τ * gi) = 0 := by
                    intro a b e hab
                    refine mul_left_cancel₀ (sub_ne_zero.mpr hab) ?_
                    linear_combination hquad a e - hquad b e
                  have hs0 : s = 0 := by
                    have q1 := hlin A1 A2 E1 ha12
                    have q2 := hlin A1 A3 E1 ha13
                    have hz : (τ * (1 - N) * (a2 - a3)) * s = 0 := by
                      have hA1 : (A1 : ℝ) = a1 := rfl
                      have hA2 : (A2 : ℝ) = a2 := rfl
                      have hA3 : (A3 : ℝ) = a3 := rfl
                      rw [hA1, hA2] at q1
                      rw [hA1, hA3] at q2
                      linear_combination q1 - q2
                    rcases mul_eq_zero.mp hz with h | h
                    · exact absurd h (mul_ne_zero (mul_ne_zero hτ0.ne' (by linarith))
                        (sub_ne_zero.mpr ha23))
                    · exact h
                  refine ⟨gi, fun a => by rw [haff a, hs0]; ring, ?_⟩
                  have q := hlin A1 A2 (θ0 j) ha12
                  rw [hs0] at q
                  rw [hS0, haff (θ0 i), hs0]
                  refine mul_left_cancel₀ hτ0.ne' ?_
                  linear_combination q
                choose gi hg1 hg2 using hmain
                have hS : ∑ l, β ⟨l, θ0 l⟩ = 0 := by
                  have h := hF θ0
                  have e1 : N * τ * ∑ i, (θ0 i : ℝ) * β ⟨i, θ0 i⟩ =
                      τ * (∑ i, (θ0 i : ℝ)) * ∑ l, β ⟨l, θ0 l⟩ := by
                    have e2 : ∑ i, (θ0 i : ℝ) * β ⟨i, θ0 i⟩ =
                        (∑ i, (θ0 i : ℝ)) * ((∑ l, β ⟨l, θ0 l⟩) / N) := by
                      rw [Finset.sum_mul]
                      refine Finset.sum_congr rfl (fun i _ => ?_)
                      rw [hg2 i, hg1 i]; field_simp
                    rw [e2]; field_simp
                  rw [e1] at h
                  linarith
                funext s
                obtain ⟨i, a⟩ := s
                have h := hg2 i
                rw [hS] at h
                rw [hg1 i a, Pi.zero_apply]
                rcases mul_eq_zero.mp h.symm with h | h
                · exact absurd h hN0.ne'
                · exact h
            set xs := affX M Θ f with hxs
            have hxS : ∀ θ, xs θ ∈ simplex n := fun θ => (hdem θ).1
            have hxpt : ∀ (θ : Profile Θ) (i : Fin n) (c' : ↥(Θ i)), (θ i : ℝ) < c' →
                  xs (Function.update θ i c') i ≤ xs θ i := by
              intro θ i c' hc
              set θ' := Function.update θ i c' with hθ'
              have h1 := (hdem θ).2.2 (xs θ') (hdem θ').1 (by simp)
              have h2 := (hdem θ').2.2 (xs θ) (hdem θ).1 (by simp)
              have hvj : ∀ j, j ≠ i → vvec Θ f θ' j = vvec Θ f θ j := by
                intro j hj; simp [vvec, θ', Function.update_of_ne hj]
              have hvi : vvec Θ f θ i < vvec Θ f θ' i := by
                simp only [vvec, θ', Function.update_self]
                exact hReg i (θ i).2 c'.2 hc
              have key : ∀ y : Fin n → ℝ, ∑ j, vvec Θ f θ' j * y j - ∑ j, vvec Θ f θ j * y j =
                  (vvec Θ f θ' i - vvec Θ f θ i) * y i := by
                intro y
                rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
                · ring
                · intro j _ hj; rw [hvj j hj]; ring
                · simp
              have k1 := key (xs θ)
              have k2 := key (xs θ')
              nlinarith
            set xm : ℝ → Profile Θ → Fin n → ℝ := fun l θ i => l * xs θ i + (1 - l) * y θ i with hxm
            set Φ : ℝ → ℝ := fun l => expect f (fun θ => M.gcs (xm l θ) -
              ∑ i, vvec Θ f θ i * xm l θ i) with hΦ
            have hΦc : Continuous Φ := by
              simp only [hΦ, hxm, expect, QuadraticMarket.gcs]
              fun_prop
            have hΦ1 : Φ 1 = V := by
              simp [hΦ, hxm, hV]
            have hlamc : ContinuousAt (fun κ : ℝ => (1 + κ)⁻¹) 0 := by
              refine ContinuousAt.inv₀ (by fun_prop) (by norm_num)
            have hcomp : Filter.Tendsto (fun κ : ℝ => Φ ((1 + κ)⁻¹)) (nhds 0) (nhds V) := by
              have h := (hΦc.continuousAt (x := (1 + (0:ℝ))⁻¹)).comp (f := fun κ : ℝ => (1 + κ)⁻¹)
                (x := 0) hlamc
              have h' : Filter.Tendsto (Φ ∘ fun κ : ℝ => (1 + κ)⁻¹) (nhds 0)
                (nhds (Φ ((1 + (0:ℝ))⁻¹))) := h
              rw [add_zero, inv_one, hΦ1] at h'
              exact h'
            by_contra hcon
            have hlt : sSup D < V := lt_of_not_ge hcon
            obtain ⟨R, hR⟩ := (Lop y).exists_leftInverse_of_injective
                  (LinearMap.ker_eq_bot'.mpr hyinj)
            set T : Module.End ℝ (((i : Fin n) × ↥(Θ i)) → ℝ) := R ∘ₗ Lop xs with hT
            have hfin : Set.Finite {κ : ℝ | T.HasEigenvalue (-κ)} :=
              (Module.End.finite_hasEigenvalue T).preimage (f := fun κ : ℝ => -κ)
                (neg_injective.injOn)
            have ev1 := hcomp.eventually (lt_mem_nhds hlt)
            have ev2 : ∀ᶠ κ in nhds (0:ℝ), κ ∉ {κ : ℝ | T.HasEigenvalue (-κ)} \ {0} :=
              (hfin.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
            have ev3 : ∀ᶠ κ in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < κ := self_mem_nhdsWithin
            obtain ⟨κ, ⟨hκ1, hκ2⟩, hκ3⟩ :=
              (((ev1.and ev2).filter_mono nhdsWithin_le_nhds).and ev3).exists
            have hκe : ¬ T.HasEigenvalue (-κ) := fun h => hκ2 ⟨h, ne_of_gt hκ3⟩
            set l := (1 + κ)⁻¹ with hl
            have hl0 : 0 < l := by positivity
            have hl1 : 1 - l = l * κ := by rw [hl]; field_simp; ring
            have hl2 : 0 ≤ 1 - l := by rw [hl1]; positivity
            have hfinal : Φ l ≤ sSup D := by
              refine himpl (xm l) ?_ ?_ ?_
              · intro θ
                refine ⟨fun i => add_nonneg (mul_nonneg hl0.le ((hxS θ).1 i))
                  (mul_nonneg hl2 ((hyS θ).1 i)), ?_⟩
                simp only [hxm, Finset.sum_add_distrib, ← Finset.mul_sum]
                rw [(hxS θ).2, (hyS θ).2]; ring
              · intro θ i c' hc
                exact add_le_add (mul_le_mul_of_nonneg_left (hxpt θ i c' hc) hl0.le)
                  (mul_le_mul_of_nonneg_left (hypt0 θ i c' hc) hl2)
              · intro β hβ
                have h1 : Lop xs β + κ • Lop y β = 0 := by
                  funext θ
                  have h := congrFun hβ θ
                  rw [hLop] at h
                  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
                  rw [hLop, hLop]
                  refine mul_left_cancel₀ hl0.ne' ?_
                  rw [mul_zero, ← h, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  simp only [hxm]
                  rw [hl1]; ring
                have h2 := congrArg R h1
                rw [map_add, map_smul, map_zero] at h2
                have h3 : R (Lop y β) = β := by
                  have := LinearMap.congr_fun hR β
                  simpa using this
                rw [h3] at h2
                by_contra hne
                refine hκe (Module.End.hasEigenvalue_of_hasEigenvector (x := β)
                  ⟨Module.End.mem_eigenspace_iff.mpr ?_, hne⟩)
                rw [neg_smul]
                exact eq_neg_of_add_eq_zero_left h2
            exact absurd hκ1 (not_lt.mpr hfinal)
          exact (csSup_le (hDne.mono hDC) hub).trans hach
        refine ⟨le_antisymm (csSup_le_csSup hCb hDne hDC) hge, ?_⟩
        exact ⟨hDne.mono hDC, hCb, hDne, hCb.mono hDC⟩
