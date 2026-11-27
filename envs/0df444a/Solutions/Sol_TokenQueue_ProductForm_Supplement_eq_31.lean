-- Prove2me | solution 1 for TokenQueue.ProductForm.Supplement.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:34.354799+00:00
-- url     : https://prove2.me/submissions/ccf92a2f-d70d-4833-9ef6-ede170fa0bed

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_TokenQueue_ProductForm_Model
import Definitions.Def_TokenQueue_ProductForm_Supplement_CustomerChain

open TokenQueue
open TokenQueue.ProductForm
open TokenQueue.ProductForm.Supplement

open Finset

/-- **Eq. (31)**, p. 25 (proof of Theorem 2). In every stationary law `Q` of the customer-level
chain, given the descriptor `x = (T₁,n₁,…,T_i,n_i)`, the type counts `(N_j^{(c)})_{c}` of the
`n_j` inactive customers of block `j` are multinomial with population `n_j` and parameters
`θ_{c,j}`, independently across blocks; stated multiplicatively. -/
theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (hstab : Summable (weight P)) (Q : CState C T → ℝ) (hQ : IsStationaryLaw P Q)
    (x : State T) (n : Fin x.1.length → C → ℕ) (hn : ∀ j, ∑ c, n j c = (x.1.get j).2) :
    prob Q (fun y => desc y = x.1 ∧ ∀ j : Fin x.1.length, ∀ c, Nseg y j c = n j c) =
      prob Q (fun y => desc y = x.1) *
        ∏ j : Fin x.1.length,
          (((x.1.get j).2.factorial : ℝ) / ∏ c, ((n j c).factorial : ℝ)) *
            ∏ c, theta P ((toks x.1).take (j + 1)) c ^ n j c := by
              have gen_rec : ∀ {β γ : Type} (b : γ) (step : γ → List β → β → γ),
                  ∃ f : List β → γ, f [] = b ∧ ∀ l a, f (l ++ [a]) = step (f l) l a := by
                intro β γ b step
                refine ⟨fun l => List.reverseRecOn l b (fun l a ih => step ih l a), ?_, ?_⟩
                · simp
                · intro l a
                  simp


              have gen_L : ∀ (β : Type) [Fintype β] [DecidableEq β], ∃ L : ℕ → Finset (List β),
                  (∀ n l, l ∈ L n ↔ l.length = n) ∧ (∀ F : List β → ℝ, ∑ l ∈ L 0, F l = F []) ∧
                  ∀ n (F : List β → ℝ), ∑ l ∈ L (n+1), F l = ∑ l ∈ L n, ∑ a, F (l ++ [a]) := by
                intro β _ _
                have hm : ∀ n (l : List β), l ∈ (List.finite_length_eq β n).toFinset ↔ l.length = n := by
                  intro n l; simp
                refine ⟨fun n => (List.finite_length_eq β n).toFinset, hm, ?_, ?_⟩
                · intro F
                  have : (List.finite_length_eq β 0).toFinset = {[]} := by
                    ext l; rw [hm]; simp
                  simp only [this, Finset.sum_singleton]
                · intro n F
                  rw [← Finset.sum_product']
                  symm
                  refine Finset.sum_bij (fun x _ => x.1 ++ [x.2]) ?_ ?_ ?_ ?_
                  · rintro ⟨l, a⟩ h
                    rw [Finset.mem_product, hm] at h
                    rw [hm]; simp [h.1]
                  · rintro ⟨l, a⟩ _ ⟨l', a'⟩ _ h
                    have := List.append_inj' h rfl
                    simp at this
                    simp [this.1, this.2]
                  · intro l h
                    rw [hm] at h
                    have hne : l ≠ [] := by rintro rfl; simp at h
                    refine ⟨(l.dropLast, l.getLast hne), ?_, List.dropLast_append_getLast hne⟩
                    rw [Finset.mem_product, hm]
                    simp [h]
                  · intros; rfl


              have U_nil : ∀ (P : Params C T) (hz : List (C ⊕ T) → List T)
                  (U : List (C ⊕ T) → T → (List (C ⊕ T) → ℝ) → ℝ)
                  (_ : ∀ w t g, U w t g = ∑ i ∈ range w.length, if w[i]? = some (Sum.inr t) then P.s (hz (w.take (i+1))) * g (w.eraseIdx i) else 0),
                  ∀ t g, U [] t g = 0 := by
                intro P hz U hU t g
                rw [hU]; simp


              have U_snoc : ∀ (P : Params C T) (hz : List (C ⊕ T) → List T)
                  (_ : ∀ a b, hz (a ++ b) = hz a ++ hz b) (_ : ∀ c, hz [Sum.inl c] = []) (_ : ∀ t, hz [Sum.inr t] = [t])
                  (U : List (C ⊕ T) → T → (List (C ⊕ T) → ℝ) → ℝ)
                  (_ : ∀ w t g, U w t g = ∑ i ∈ range w.length, if w[i]? = some (Sum.inr t) then P.s (hz (w.take (i+1))) * g (w.eraseIdx i) else 0),
                  ∀ w a t g, U (w ++ [a]) t g = U w t (fun v => g (v ++ [a])) +
                    if a = Sum.inr t then P.s (hz w ++ [t]) * g w else 0 := by
                intro P hz happ h1 h2 U hU w a t g
                rw [hU, hU]
                rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
                congr 1
                · refine Finset.sum_congr rfl fun i hi => ?_
                  rw [Finset.mem_range] at hi
                  rw [List.getElem?_append_left hi, List.take_append_of_le_length (by omega), List.eraseIdx_append_of_lt_length hi]
                · have e1 : (w ++ [a])[w.length]? = some a := by simp
                  rw [e1]
                  have e2 : (w ++ [a]).take (w.length + 1) = w ++ [a] := by
                    rw [List.take_of_length_le]; simp
                  have e3 : (w ++ [a]).eraseIdx w.length = w := by
                    rw [List.eraseIdx_append_of_length_le le_rfl]; simp
                  rw [e2, e3]
                  by_cases h : a = Sum.inr t
                  · subst h; simp [happ, h2]
                  · simp [h]


              have U_congr : ∀ (P : Params C T) (hz : List (C ⊕ T) → List T)
                  (_ : ∀ a b, hz (a ++ b) = hz a ++ hz b) (_ : ∀ c, hz [Sum.inl c] = []) (_ : ∀ t, hz [Sum.inr t] = [t])
                  (U : List (C ⊕ T) → T → (List (C ⊕ T) → ℝ) → ℝ)
                  (_ : ∀ t g, U [] t g = 0)
                  (_ : ∀ w a t g, U (w ++ [a]) t g = U w t (fun v => g (v ++ [a])) +
                    if a = Sum.inr t then P.s (hz w ++ [t]) * g w else 0),
                  ∀ w t g g', (∀ v, (t :: hz v).Perm (hz w) → v.length + 1 = w.length → g v = g' v) → U w t g = U w t g' := by
                intro P hz happ h1 h2 U U0 US w
                induction w using List.reverseRecOn with
                | nil => intro t g g' _; rw [U0, U0]
                | append_singleton w a ih =>
                  intro t g g' h
                  rw [US, US]
                  congr 1
                  · apply ih
                    intro v hv hl
                    apply h
                    · rw [happ, happ, ← List.cons_append]; exact hv.append_right _
                    · simp; omega
                  · by_cases ha : a = Sum.inr t
                    · rw [if_pos ha, if_pos ha, h w]
                      · rw [happ, ha, h2]; exact (List.perm_append_singleton t (hz w)).symm
                      · simp
                    · rw [if_neg ha, if_neg ha]


              have rt_congr : ∀ (P : Params C T) (rt : List T → C ⊕ T → ℝ)
                  (_ : ∀ l c, rt l (Sum.inl c) = if P.tok c ⊆ l.toFinset then P.lam c else 0)
                  (_ : ∀ l t, rt l (Sum.inr t) = lamTok P l.toFinset t),
                  ∀ l l' a, l.Perm l' → rt l a = rt l' a := by
                intro P rt r1 r2 l l' a h
                have := List.toFinset_eq_of_perm _ _ h
                rcases a with c | t
                · rw [r1, r1, this]
                · rw [r2, r2, this]


              have kfun_snoc : ∀ (P : Params C T) (l : List T) (t : T), kfun P (l ++ [t]) = kfun P l + P.s (l ++ [t]) := by
                intro P l t
                unfold kfun
                rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
                congr 1
                · refine Finset.sum_congr rfl fun i hi => ?_
                  rw [Finset.mem_range] at hi
                  rw [List.take_append_of_le_length (by omega)]
                · rw [List.take_of_length_le]; simp


              have piLam_snoc : ∀ (P : Params C T) (l : List T) (t : T), piLam P (l ++ [t]) = piLam P l * lamTok P l.toFinset t := by
                intro P l t
                have key : ∀ l : List T, piLam P l = ∏ j ∈ range l.length, (l[j]?.elim 1 (fun u => lamTok P (l.take j).toFinset u)) := by
                  intro l
                  unfold piLam
                  rw [← Fin.prod_univ_eq_prod_range (fun j => (l[j]?.elim 1 (fun u => lamTok P (l.take j).toFinset u)))]
                  refine Finset.prod_congr rfl fun j _ => ?_
                  simp
                rw [key, key, List.length_append, List.length_singleton, Finset.prod_range_succ]
                congr 1
                · refine Finset.prod_congr rfl fun i hi => ?_
                  rw [Finset.mem_range] at hi
                  rw [List.take_append_of_le_length (by omega), List.getElem?_append_left hi]
                · simp


              have rt_sum : ∀ (P : Params C T) (_ : P.Standing) (rt : List T → C ⊕ T → ℝ)
                  (_ : ∀ l c, rt l (Sum.inl c) = if P.tok c ⊆ l.toFinset then P.lam c else 0)
                  (_ : ∀ l t, rt l (Sum.inr t) = lamTok P l.toFinset t),
                  (∀ l : List T, ∑ a, rt l a = lamTot P) ∧ (∀ l : List T, ∑ t, lamTok P l.toFinset t = lamTot P - lamU P l.toFinset) ∧
                  (∀ (l : List T) t, t ∈ l → lamTok P l.toFinset t = 0) ∧ (∀ (l : List T) a, 0 ≤ rt l a) := by
                intro P hS rt r1 r2
                obtain ⟨hlam, hne, ha0, haz, has, hs, heta⟩ := hS
                have A : ∀ l : List T, ∑ t, lamTok P l.toFinset t = lamTot P - lamU P l.toFinset := by
                  intro l
                  unfold lamTok lamTot lamU
                  rw [Finset.sum_comm, Finset.sum_filter, ← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl fun c _ => ?_
                  rw [← Finset.mul_sum]
                  by_cases h : P.tok c ⊆ l.toFinset
                  · rw [if_pos h, Finset.sum_eq_zero]
                    · ring
                    · intro t _
                      apply haz
                      rw [Finset.sdiff_eq_empty_iff_subset.mpr h]; simp
                  · rw [if_neg h]
                    have hn : (P.tok c \ l.toFinset).Nonempty := by
                      rw [Finset.sdiff_nonempty]; exact h
                    have := has c _ hn
                    rw [← Finset.sum_subset (Finset.subset_univ (P.tok c \ l.toFinset)), this]
                    · ring
                    · intro t _ ht
                      exact haz _ _ _ ht
                refine ⟨?_, A, ?_, ?_⟩
                · intro l
                  rw [Fintype.sum_sum_type]
                  simp only [r1, r2]
                  rw [A, lamU, Finset.sum_filter]; ring
                · intro l t ht
                  unfold lamTok
                  refine Finset.sum_eq_zero fun c _ => ?_
                  rw [haz, mul_zero]
                  simp [ht]
                · intro l a
                  rcases a with c | t
                  · rw [r1]; split_ifs
                    · exact (hlam c).le
                    · exact le_rfl
                  · rw [r2]; exact Finset.sum_nonneg fun c _ => mul_nonneg (hlam c).le (ha0 _ _ _)


              obtain ⟨hlam, hne, ha0, haz, has, hs, heta⟩ := id hS
              obtain ⟨hz, hznil, hzapp, hzl, hzr⟩ : ∃ hz : List (C ⊕ T) → List T, hz [] = [] ∧ (∀ a b, hz (a ++ b) = hz a ++ hz b) ∧ (∀ c, hz [Sum.inl c] = []) ∧ (∀ t, hz [Sum.inr t] = [t]) :=
                ⟨fun z => z.filterMap (fun a => a.elim (fun _ => none) some), rfl, fun a b => List.filterMap_append, fun c => rfl, fun t => rfl⟩
              obtain ⟨rt, r1, r2⟩ : ∃ rt : List T → C ⊕ T → ℝ, (∀ l c, rt l (Sum.inl c) = if P.tok c ⊆ l.toFinset then P.lam c else 0) ∧ (∀ l t, rt l (Sum.inr t) = lamTok P l.toFinset t) :=
                ⟨fun l a => Sum.elim (fun c => if P.tok c ⊆ l.toFinset then P.lam c else 0) (fun t => lamTok P l.toFinset t) a, fun _ _ => rfl, fun _ _ => rfl⟩
              obtain ⟨U, hU⟩ : ∃ U : List (C ⊕ T) → T → (List (C ⊕ T) → ℝ) → ℝ, ∀ w t g, U w t g = ∑ i ∈ range w.length, if w[i]? = some (Sum.inr t) then P.s (hz (w.take (i+1))) * g (w.eraseIdx i) else 0 := ⟨_, fun _ _ _ => rfl⟩
              have U0 := U_nil P hz U hU
              have US := U_snoc P hz hzapp hzl hzr U hU
              have Uc := U_congr P hz hzapp hzl hzr U U0 US
              have rc := rt_congr P rt r1 r2
              have ks := kfun_snoc P
              have pls := piLam_snoc P
              obtain ⟨rs, ls, lz, rn⟩ := rt_sum P hS rt r1 r2
              obtain ⟨L, Lm, L0, LS⟩ := gen_L (C ⊕ T)
              obtain ⟨p, p0, pS⟩ := gen_rec (β := C ⊕ T) (1 : ℝ) (fun r z a => r * (rt (hz z) a / (kfun P (hz (z ++ [a])) * P.eta (z.length + 1))))
              obtain ⟨V, V0, VS⟩ := gen_rec (β := C ⊕ T) True (fun v z a => v ∧ (Sum.elim (fun c => P.tok c ⊆ (hz z).toFinset) (fun t => t ∉ hz z) a))
              obtain ⟨ps, ps0, psl, psr⟩ : ∃ ps : T → List (C ⊕ T) → List (C ⊕ T), (∀ t, ps t [] = []) ∧ (∀ t c l, ps t (Sum.inl c :: l) = if t ∈ P.tok c then Sum.inr t :: l else Sum.inl c :: ps t l) ∧ (∀ t u l, ps t (Sum.inr u :: l) = Sum.inr u :: ps t l) :=
                ⟨fun t l => List.rec [] (fun a l ih => Sum.elim (fun c => if t ∈ P.tok c then Sum.inr t :: l else Sum.inl c :: ih) (fun u => Sum.inr u :: ih) a) l, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
              obtain ⟨cmp, hcmp⟩ : ∃ cmp : T → List (C ⊕ T) → Prop, ∀ t l, cmp t l ↔ ∃ c, Sum.inl c ∈ l ∧ t ∈ P.tok c := ⟨_, fun _ _ => Iff.rfl⟩
              classical

              have V_nodup : ∀ z, V z → (hz z).Nodup := by
                intro z
                induction z using List.reverseRecOn with
                | nil => intro _; rw [hznil]; exact List.nodup_nil
                | append_singleton w a ih =>
                  intro h
                  rw [VS] at h
                  rcases a with c | t
                  · rw [hzapp, hzl, List.append_nil]; exact ih h.1
                  · rw [hzapp, hzr]
                    have h2 : t ∉ hz w := h.2
                    rw [(List.perm_append_singleton t (hz w)).nodup_iff]
                    exact List.nodup_cons.mpr ⟨h2, ih h.1⟩


              have cmp_snoc : ∀ t l a, cmp t (l ++ [a]) ↔ cmp t l ∨ ∃ c, a = Sum.inl c ∧ t ∈ P.tok c := by
                intro t l a
                rw [hcmp, hcmp]
                constructor
                · rintro ⟨c, hc, ht⟩
                  rw [List.mem_append, List.mem_singleton] at hc
                  rcases hc with hc | hc
                  · exact Or.inl ⟨c, hc, ht⟩
                  · exact Or.inr ⟨c, hc.symm, ht⟩
                · rintro (⟨c, hc, ht⟩ | ⟨c, hc, ht⟩)
                  · exact ⟨c, by simp [hc], ht⟩
                  · exact ⟨c, by simp [hc], ht⟩


              have V_cmp : ∀ z t, V z → t ∉ hz z → ¬ cmp t z := by
                intro z
                induction z using List.reverseRecOn with
                | nil => intro t _ _; rw [hcmp]; simp
                | append_singleton w a ih =>
                  intro t h ht
                  rw [VS] at h
                  rw [cmp_snoc]
                  rw [hzapp, List.mem_append, not_or] at ht
                  rintro (h3 | ⟨c, rfl, hc⟩)
                  · exact ih t h.1 ht.1 h3
                  · have h2 : P.tok c ⊆ (hz w).toFinset := h.2
                    exact ht.1 (List.mem_toFinset.mp (h2 hc))


              have p_V : ∀ z, ¬ V z → p z = 0 := by
                intro z
                induction z using List.reverseRecOn with
                | nil => intro h; rw [V0] at h; exact absurd trivial h
                | append_singleton w a ih =>
                  intro h
                  rw [VS] at h
                  rw [pS]
                  by_cases hw : V w
                  · have h3 : rt (hz w) a = 0 := by
                      rcases a with c | t
                      · rw [r1, if_neg]
                        intro h4; exact h ⟨hw, h4⟩
                      · rw [r2]; apply lz
                        by_contra h4; exact h ⟨hw, h4⟩
                    rw [h3]; simp
                  · rw [ih hw]; simp


              have k_nonneg : ∀ l, 0 ≤ kfun P l := by
                intro l
                exact Finset.sum_nonneg fun _ _ => hs _


              have p_nonneg : ∀ z, 0 ≤ p z := by
                intro z
                induction z using List.reverseRecOn with
                | nil => rw [p0]; norm_num
                | append_singleton w a ih =>
                  rw [pS]
                  exact mul_nonneg ih (div_nonneg (rn _ _) (mul_nonneg (k_nonneg _) (heta _ (by omega)).le))


              have k_pos : ∀ z, V z → z ≠ [] → 0 < kfun P (hz z) := by
                intro z hv hz0
                apply hk _ (V_nodup z hv)
                revert hv hz0
                induction z using List.reverseRecOn with
                | nil => intro _ h; exact absurd rfl h
                | append_singleton w a ih =>
                  intro h _
                  rw [VS] at h
                  rcases a with c | t
                  · rw [hzapp, hzl, List.append_nil]
                    have h2 : P.tok c ⊆ (hz w).toFinset := h.2
                    obtain ⟨t, ht⟩ := hne c
                    have := h2 ht
                    intro h3; rw [h3] at this; simp at this
                  · rw [hzapp, hzr]; simp


              have ps_no : ∀ t l, ¬ cmp t l → ps t l = l := by
                intro t l
                induction l with
                | nil => intro _; rw [ps0]
                | cons a l ih =>
                  intro h
                  have h' : ¬ cmp t l := by
                    intro h3; apply h; rw [hcmp] at h3 ⊢
                    obtain ⟨c, hc, ht⟩ := h3
                    exact ⟨c, by simp [hc], ht⟩
                  rcases a with c | u
                  · rw [psl, if_neg, ih h']
                    intro h3; apply h; rw [hcmp]; exact ⟨c, by simp, h3⟩
                  · rw [psr, ih h']


              have ps_len : ∀ t l, (ps t l).length = l.length := by
                intro t l
                induction l with
                | nil => rw [ps0]
                | cons a l ih =>
                  rcases a with c | u
                  · rw [psl]; split_ifs <;> simp [ih]
                  · rw [psr]; simp [ih]


              have cmp_consl : ∀ t c l, cmp t (Sum.inl c :: l) ↔ t ∈ P.tok c ∨ cmp t l := by
                intro t c l
                rw [hcmp, hcmp]
                constructor
                · rintro ⟨d, hd, ht⟩
                  rw [List.mem_cons] at hd
                  rcases hd with hd | hd
                  · left; cases hd; exact ht
                  · exact Or.inr ⟨d, hd, ht⟩
                · rintro (h | ⟨d, hd, ht⟩)
                  · exact ⟨c, by simp, h⟩
                  · exact ⟨d, by simp [hd], ht⟩


              have cmp_consr : ∀ t u l, cmp t (Sum.inr u :: l) ↔ cmp t l := by
                intro t u l
                rw [hcmp, hcmp]
                simp


              have ps_snoc_c : ∀ t l a, cmp t l → ps t (l ++ [a]) = ps t l ++ [a] := by
                intro t l a
                induction l with
                | nil => intro h; rw [hcmp] at h; simp at h
                | cons b l ih =>
                  intro h
                  rcases b with c | u
                  · rw [List.cons_append, psl, psl]
                    by_cases h3 : t ∈ P.tok c
                    · rw [if_pos h3, if_pos h3]; simp
                    · rw [if_neg h3, if_neg h3, ih]
                      · simp
                      · rw [cmp_consl] at h; tauto
                  · rw [List.cons_append, psr, psr, ih]
                    · simp
                    · rwa [cmp_consr] at h


              have ps_snoc_n : ∀ t l c, ¬ cmp t l → t ∈ P.tok c → ps t (l ++ [Sum.inl c]) = l ++ [Sum.inr t] := by
                intro t l a
                induction l with
                | nil => intro h h3; rw [List.nil_append, psl, if_pos h3]; rfl
                | cons b l ih =>
                  intro h h3
                  rcases b with c | u
                  · rw [cmp_consl, not_or] at h
                    rw [List.cons_append, psl, if_neg h.1, ih h.2 h3]; simp
                  · rw [cmp_consr] at h
                    rw [List.cons_append, psr, ih h h3]; simp


              have ps_perm : ∀ t l, cmp t l → (hz (ps t l)).Perm (t :: hz l) := by
                intro t l
                have e1 : ∀ c l, hz (Sum.inl c :: l) = hz l := by
                  intro c l
                  have := hzapp [Sum.inl c] l
                  rw [hzl] at this; simpa using this
                have e2 : ∀ u l, hz (Sum.inr u :: l) = u :: hz l := by
                  intro c l
                  have := hzapp [Sum.inr c] l
                  rw [hzr] at this; simpa using this
                induction l with
                | nil => intro h; rw [hcmp] at h; simp at h
                | cons b l ih =>
                  intro h
                  rcases b with c | u
                  · rw [psl]
                    by_cases h3 : t ∈ P.tok c
                    · rw [if_pos h3, e1, e2]
                    · rw [if_neg h3, e1, e1]
                      apply ih
                      rw [cmp_consl] at h; tauto
                  · rw [psr, e2, e2]
                    rw [cmp_consr] at h
                    exact ((ih h).cons u).trans (List.Perm.swap _ _ _)


              have p_step : ∀ w b, p (w ++ [b]) * P.eta (w.length + 1) = p w * (rt (hz w) b / kfun P (hz w ++ hz [b])) := by
                intro w b
                rw [pS, hzapp]
                have := heta (w.length + 1) (by omega)
                by_cases h : kfun P (hz w ++ hz [b]) = 0
                · rw [h]; simp
                · field_simp


              have U_smul : ∀ w t g r, U w t (fun v => r * g v) = r * U w t g := by
                intro w t g r
                rw [hU, hU, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                split_ifs
                · ring
                · simp


              have U_zero : ∀ w t, U w t (fun _ => 0) = 0 := by
                intro w t
                rw [hU]
                refine Finset.sum_eq_zero fun i _ => ?_
                split_ifs <;> simp


              have U_sum : ∀ {ι : Type} (s : Finset ι) w t (g : ι → List (C ⊕ T) → ℝ), U w t (fun v => ∑ i ∈ s, g i v) = ∑ i ∈ s, U w t (g i) := by
                intro ι s w t g
                simp only [hU]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun i _ => ?_
                split_ifs
                · rw [Finset.mul_sum]
                · simp


              have U_add : ∀ w t g g', U w t (fun v => g v + g' v) = U w t g + U w t g' := by
                intro w t g g'
                simp only [hU]
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun i _ => ?_
                split_ifs
                · rw [mul_add]
                · simp


              have U_nonneg : ∀ w t g, (∀ v, 0 ≤ g v) → 0 ≤ U w t g := by
                intro w t g hg
                rw [hU]
                refine Finset.sum_nonneg fun i _ => ?_
                split_ifs
                · exact mul_nonneg (hs _) (hg _)
                · simp


              have U_one : ∀ w, ∑ t, U w t (fun _ => 1) = kfun P (hz w) := by
                intro w
                induction w using List.reverseRecOn with
                | nil => simp only [U0, hznil]; simp [kfun]
                | append_singleton w a ih =>
                  simp only [US]
                  rw [Finset.sum_add_distrib, ih, hzapp]
                  rcases a with c | u
                  · rw [hzl]; simp
                  · rw [hzr, ks]; simp


              have Kf : ∀ l l' b, l.Perm l' → (l' ++ hz [b]).Nodup → rt l b / kfun P (l ++ hz [b]) = rt l' b / kfun P (l' ++ hz [b]) := by
                intro l l' b h hnd
                rw [rc l l' b h, h2 _ _ hnd (h.symm.append_right _)]


              have p_pi : ∀ z, piLam P (hz z) = 0 → p z = 0 := by
                intro z
                induction z using List.reverseRecOn with
                | nil => intro h; rw [hznil] at h; simp [piLam] at h
                | append_singleton w a ih =>
                  intro h
                  rw [pS]
                  rcases a with c | t
                  · rw [hzapp, hzl, List.append_nil] at h
                    rw [ih h]; simp
                  · rw [hzapp, hzr, pls] at h
                    rcases mul_eq_zero.mp h with h | h
                    · rw [ih h]; simp
                    · rw [r2, h]; simp


              have commL : ∀ z b t, V (z ++ [b]) → t ∉ hz (z ++ [b]) → p z * lamTok P (hz z).toFinset t * rt (t :: hz z) b = p z * rt (hz z) b * lamTok P (hz z ++ hz [b]).toFinset t := by
                intro z b t hV ht
                have hnd := V_nodup _ hV
                rcases b with c | u
                · rw [VS] at hV
                  have h3 : P.tok c ⊆ (hz z).toFinset := hV.2
                  rw [r1, r1, if_pos h3, if_pos, hzl, List.append_nil]
                  · ring
                  · refine h3.trans ?_
                    rw [List.toFinset_cons]; exact Finset.subset_insert _ _
                · rw [hzapp, hzr] at ht hnd
                  rw [hzr, r2, r2]
                  by_cases h0 : piLam P (hz z) = 0
                  · rw [p_pi z h0]; simp
                  · have e : piLam P (hz z ++ [t] ++ [u]) = piLam P (hz z ++ [u] ++ [t]) := by
                      apply h1
                      · have : (hz z ++ [u] ++ [t]).Nodup := by
                          rw [(List.perm_append_singleton t (hz z ++ [u])).nodup_iff, List.nodup_cons]
                          exact ⟨ht, hnd⟩
                        rw [List.append_assoc] at this ⊢
                        refine (List.Perm.nodup_iff ?_).mp this
                        exact (List.Perm.swap _ _ _).append_left _
                      · rw [List.append_assoc, List.append_assoc]
                        exact (List.Perm.swap _ _ _).append_left _
                    rw [pls, pls, pls, pls] at e
                    have e2 : (t :: hz z).toFinset = (hz z ++ [t]).toFinset := List.toFinset_eq_of_perm _ _ (List.perm_append_singleton t (hz z)).symm
                    rw [e2]
                    have e3 : lamTok P (hz z).toFinset t * lamTok P (hz z ++ [t]).toFinset u = lamTok P (hz z).toFinset u * lamTok P (hz z ++ [u]).toFinset t := by
                      apply mul_left_cancel₀ h0
                      linarith
                    rw [mul_assoc, e3]; ring


              have Jl : ∀ z t, V z → t ∉ hz z → ∑ w ∈ L (z.length + 1), p w * U w t (fun v => if v = z then 1 else 0) * P.eta (z.length + 1) = p z * lamTok P (hz z).toFinset t := by
                intro z
                induction z using List.reverseRecOn with
                | nil =>
                  intro t _ _
                  have hk1 : 0 < kfun P [t] := hk _ (List.nodup_singleton t) (by simp)
                  have hks : kfun P [t] = P.s [t] := by
                    have := ks [] t
                    rw [List.nil_append] at this; rw [this]; simp [kfun]
                  rw [List.length_nil, LS, L0]
                  have eU : ∀ a, U [a] t (fun v => if v = [] then (1:ℝ) else 0) = if a = Sum.inr t then P.s [t] else 0 := by
                    intro a
                    have := US [] a t (fun v => if v = [] then (1:ℝ) else 0)
                    rw [List.nil_append] at this
                    rw [this, U0, hznil]; simp
                  simp only [List.nil_append, eU]
                  rw [Finset.sum_eq_single (Sum.inr t)]
                  · have h3 := p_step [] (Sum.inr t)
                    rw [List.nil_append, List.length_nil, zero_add, p0, hznil, hzr, List.nil_append, r2, one_mul] at h3
                    rw [if_pos rfl, zero_add, mul_right_comm, h3, hks, p0, hznil]
                    rw [hks] at hk1
                    rw [one_mul]; field_simp
                  · intro b _ hb; rw [if_neg hb]; simp
                  · simp
                | append_singleton z b ih =>
                  intro t hV ht
                  have hV' := hV
                  rw [VS] at hV'
                  have ht' := ht
                  rw [hzapp, List.mem_append, not_or] at ht'
                  have hnd := V_nodup _ hV
                  have hc := commL z b t hV ht
                  have IH := ih t hV'.1 ht'.1
                  have hnd2 : ((t :: hz z) ++ hz [b]).Nodup := by
                    rw [List.cons_append, List.nodup_cons, ← hzapp]
                    exact ⟨ht, hnd⟩
                  have hlen : (z ++ [b]).length = z.length + 1 := by simp
                  rw [hlen, LS]
                  have key : ∀ w ∈ L (z.length + 1), ∑ a, p (w ++ [a]) * U (w ++ [a]) t (fun v => if v = z ++ [b] then 1 else 0) * P.eta (z.length + 1 + 1) =
                      p w * U w t (fun v => if v = z then 1 else 0) * (rt (t :: hz z) b / kfun P ((t :: hz z) ++ hz [b])) +
                      (if w = z ++ [b] then (p w * (lamTok P (hz w).toFinset t / kfun P (hz w ++ [t]))) * P.s (hz w ++ [t]) else 0) := by
                    intro w hw
                    rw [Lm] at hw
                    have e1 : ∀ a, U w t (fun v => if v ++ [a] = z ++ [b] then (1:ℝ) else 0) = if a = b then U w t (fun v => if v = z then 1 else 0) else 0 := by
                      intro a
                      by_cases hab : a = b
                      · rw [if_pos hab, hab]
                        simp
                      · rw [if_neg hab]
                        refine Eq.trans ?_ (U_zero w t)
                        congr 1; funext v
                        rw [if_neg]; intro h
                        have := List.append_inj' h rfl
                        simp at this; exact hab this.2
                    have e2 : ∀ a, p (w ++ [a]) * U (w ++ [a]) t (fun v => if v = z ++ [b] then 1 else 0) * P.eta (z.length + 1 + 1) =
                        (if a = b then p (w ++ [a]) * P.eta (z.length + 1 + 1) * U w t (fun v => if v = z then 1 else 0) else 0) +
                        (if a = Sum.inr t then p (w ++ [a]) * P.eta (z.length + 1 + 1) * (P.s (hz w ++ [t]) * if w = z ++ [b] then 1 else 0) else 0) := by
                      intro a
                      rw [US, e1]
                      split_ifs <;> ring
                    simp only [e2]
                    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' , Finset.sum_ite_eq']
                    simp only [Finset.mem_univ, if_true]
                    rw [← hw, p_step, p_step, hzr, r2]
                    congr 1
                    · by_cases hp : (t :: hz z).Perm (hz w)
                      · rw [Kf (hz w) (t :: hz z) b hp.symm hnd2]; ring
                      · have : U w t (fun v => if v = z then 1 else 0) = 0 := by
                          refine Eq.trans ?_ (U_zero w t)
                          apply Uc
                          intro v hv _
                          rw [if_neg]; rintro rfl; exact hp hv
                        rw [this]; simp
                    · split_ifs <;> ring
                  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq', if_pos (by rw [Lm]; exact hlen)]
                  rw [← Finset.sum_mul] at IH
                  have hst := p_step z b
                  have hkp := k_pos _ hV (by simp)
                  have hperm : ((t :: hz z) ++ hz [b]).Perm (hz z ++ hz [b] ++ [t]) := by
                    rw [List.cons_append]; exact (List.perm_append_singleton t _).symm
                  rw [hzapp] at hkp ⊢
                  rw [h2 _ _ hnd2 hperm, ks]
                  have hs0 := hs (hz z ++ hz [b] ++ [t])
                  have het := heta (z.length + 1) (by omega)
                  set S := ∑ w ∈ L (z.length + 1), p w * U w t (fun v => if v = z then 1 else 0)
                  set k := kfun P (hz z ++ hz [b])
                  set s := P.s (hz z ++ hz [b] ++ [t])
                  set η := P.eta (z.length + 1)
                  set lt := lamTok P (hz z ++ hz [b]).toFinset t
                  set X := p (z ++ [b])
                  have hks : 0 < k + s := by linarith
                  have e5 : S * rt (t :: hz z) b = X * k * lt := by
                    have : η * (S * rt (t :: hz z) b) = η * (X * k * lt) := by
                      have h6 : X * η * k = p z * rt (hz z) b := by
                        rw [hst]; field_simp
                      calc η * (S * rt (t :: hz z) b) = (S * η) * rt (t :: hz z) b := by ring
                        _ = (X * η * k) * lt := by rw [IH, hc, h6]
                        _ = _ := by ring
                    exact mul_left_cancel₀ het.ne' this
                  rw [← mul_div_assoc, e5]
                  field_simp


              have Bz : ∀ w a z, p (w ++ [a]) * ∑ t, U (w ++ [a]) t (fun v => if cmp t v ∧ ps t v = z then (1:ℝ) else 0) = p (w ++ [a]) * ∑ t, U w t (fun v => if cmp t (v ++ [a]) ∧ ps t (v ++ [a]) = z then (1:ℝ) else 0) := by
                intro w a z
                rw [Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun t _ => ?_
                rw [US]
                by_cases ha : a = Sum.inr t
                · rw [if_pos ha]
                  by_cases hV : V (w ++ [a])
                  · have hV2 := hV
                    rw [VS, ha] at hV2
                    rw [if_neg]
                    · ring
                    · intro h; exact V_cmp w t hV2.1 hV2.2 h.1
                  · rw [p_V _ hV]; simp
                · rw [if_neg ha, add_zero]


              have Dz : ∀ t v a z b, (if cmp t (v ++ [a]) ∧ ps t (v ++ [a]) = z ++ [b] then (1:ℝ) else 0) =
                  (if a = b then (if cmp t v ∧ ps t v = z then (1:ℝ) else 0) else 0) +
                  (if (∃ c, a = Sum.inl c ∧ t ∈ P.tok c) ∧ b = Sum.inr t then (if ¬ cmp t v ∧ v = z then (1:ℝ) else 0) else 0) := by
                intro t v a z b
                have hinj : ∀ (l l' : List (C ⊕ T)) x y, l ++ [x] = l' ++ [y] ↔ l = l' ∧ x = y := by
                  intro l l' x y
                  constructor
                  · intro h
                    have := List.append_inj' h rfl
                    simpa using this
                  · rintro ⟨rfl, rfl⟩; rfl
                by_cases hc : cmp t v
                · simp only [ps_snoc_c t v a hc, hinj, cmp_snoc]
                  by_cases hab : a = b <;> simp [hc, hab]
                · by_cases hca : ∃ c, a = Sum.inl c ∧ t ∈ P.tok c
                  · obtain ⟨c, rfl, htc⟩ := hca
                    simp only [ps_snoc_n t v c hc htc, hinj, cmp_snoc]
                    by_cases hb : b = Sum.inr t
                    · subst hb
                      simp [hc, htc]
                    · have : ¬ (Sum.inr t = b) := fun h => hb h.symm
                      simp [hc, hb, this]
                  · have : ¬ cmp t (v ++ [a]) := by
                      rw [cmp_snoc]; exact not_or.mpr ⟨hc, hca⟩
                    rw [if_neg (fun h => this h.1)]
                    simp [hc, hca]


              have Bl : ∀ z, V z → ∑ w ∈ L (z.length + 1), p w * (∑ t, U w t (fun v => if cmp t v ∧ ps t v = z then (1:ℝ) else 0)) * P.eta (z.length + 1) = p z * lamU P (hz z).toFinset := by
                intro z
                induction z using List.reverseRecOn with
                | nil =>
                  intro _
                  rw [Finset.sum_eq_zero]
                  · rw [hznil, lamU, Finset.sum_filter, Finset.sum_eq_zero]
                    · simp
                    · intro c _
                      rw [if_neg]
                      intro h
                      obtain ⟨t, ht⟩ := hne c
                      have := h ht
                      simp at this
                  · intro w hw
                    rw [Finset.sum_eq_zero]
                    · simp
                    · intro t _
                      refine Eq.trans ?_ (U_zero w t)
                      congr 1; funext v
                      rw [if_neg]
                      rintro ⟨h3, h4⟩
                      have h5 := ps_len t v
                      rw [h4] at h5
                      have : v = [] := List.length_eq_zero_iff.mp h5.symm
                      rw [this, hcmp] at h3; simp at h3
                | append_singleton z b ih =>
                  intro hV
                  have hV' := hV
                  rw [VS] at hV'
                  have hnd := V_nodup _ hV
                  have IH := ih hV'.1
                  have hlen : (z ++ [b]).length = z.length + 1 := by simp
                  rw [hlen, LS]
                  rw [hzapp] at hnd
                  have key : ∀ w ∈ L (z.length + 1), ∑ a, p (w ++ [a]) * (∑ t, U (w ++ [a]) t (fun v => if cmp t v ∧ ps t v = z ++ [b] then (1:ℝ) else 0)) * P.eta (z.length + 1 + 1) =
                      p w * (∑ t, U w t (fun v => if cmp t v ∧ ps t v = z then (1:ℝ) else 0)) * (rt (hz z) b / kfun P (hz z ++ hz [b])) +
                      ∑ t, (if b = Sum.inr t then p w * U w t (fun v => if v = z then 1 else 0) * ((lamU P (t :: hz z).toFinset - lamU P (hz z).toFinset) / kfun P (t :: hz z)) else 0) := by
                    intro w hw
                    rw [Lm] at hw
                    simp only [Bz, Dz]
                    have e1 : ∀ a t, U w t (fun v => (if a = b then (if cmp t v ∧ ps t v = z then (1:ℝ) else 0) else 0) +
                        (if (∃ c, a = Sum.inl c ∧ t ∈ P.tok c) ∧ b = Sum.inr t then (if ¬ cmp t v ∧ v = z then (1:ℝ) else 0) else 0)) =
                        (if a = b then U w t (fun v => if cmp t v ∧ ps t v = z then (1:ℝ) else 0) else 0) +
                        (if (∃ c, a = Sum.inl c ∧ t ∈ P.tok c) ∧ b = Sum.inr t then U w t (fun v => if v = z then (1:ℝ) else 0) else 0) := by
                      intro a t
                      rw [U_add]
                      congr 1
                      · split_ifs
                        · rfl
                        · exact U_zero w t
                      · split_ifs with h
                        · obtain ⟨_, rfl⟩ := h
                          have : ¬ cmp t z := V_cmp z t hV'.1 hV'.2
                          congr 1; funext v
                          by_cases hv : v = z
                          · subst hv; simp [this]
                          · simp [hv]
                        · exact U_zero w t
                    simp only [e1]
                    simp only [Finset.sum_add_distrib, mul_add, add_mul]
                    congr 1
                    · rw [Finset.sum_eq_single b]
                      · simp only [if_true]
                        rw [mul_right_comm, ← hw, p_step, mul_right_comm]
                        by_cases hB : (∑ t, U w t (fun v => if cmp t v ∧ ps t v = z then (1:ℝ) else 0)) = 0
                        · rw [hB]; simp
                        · have hp : (hz w).Perm (hz z) := by
                            by_contra hp
                            apply hB
                            refine Finset.sum_eq_zero fun t _ => ?_
                            refine Eq.trans ?_ (U_zero w t)
                            apply Uc
                            intro v hv _
                            rw [if_neg]
                            rintro ⟨h3, rfl⟩
                            exact hp (hv.symm.trans (ps_perm t v h3).symm)
                          rw [Kf (hz w) (hz z) b hp hnd]
                      · intro a _ hab
                        simp [hab]
                      · simp
                    · simp only [Finset.mul_sum, Finset.sum_mul]
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun t _ => ?_
                      by_cases hb : b = Sum.inr t
                      · subst hb
                        rw [if_pos rfl]
                        simp only [and_true]
                        rw [Fintype.sum_sum_type]
                        have z2 : ∑ u : T, p (w ++ [Sum.inr u]) * (if ∃ c, (Sum.inr u : C ⊕ T) = Sum.inl c ∧ t ∈ P.tok c then U w t (fun v => if v = z then (1:ℝ) else 0) else 0) * P.eta (z.length + 1 + 1) = 0 := by
                          refine Finset.sum_eq_zero fun u _ => ?_
                          rw [if_neg]
                          · simp
                          · rintro ⟨c, h, _⟩; cases h
                        rw [z2, add_zero]
                        by_cases hB : U w t (fun v => if v = z then (1:ℝ) else 0) = 0
                        · rw [hB]; simp
                        · have hp : (t :: hz z).Perm (hz w) := by
                            by_contra hp
                            apply hB
                            refine Eq.trans ?_ (U_zero w t)
                            apply Uc
                            intro v hv _
                            rw [if_neg]
                            rintro rfl
                            exact hp hv
                          have h6 : ∀ c, p (w ++ [Sum.inl c]) * P.eta (z.length + 1 + 1) = p w * ((if P.tok c ⊆ (t :: hz z).toFinset then P.lam c else 0) / kfun P (t :: hz z)) := by
                            intro c
                            rw [← hw, p_step, hzl, List.append_nil, rc _ _ _ hp.symm, r1, h2 (t :: hz z) (hz w) _ hp]
                            exact List.nodup_cons.mpr ⟨hV'.2, V_nodup _ hV'.1⟩
                          have h7 : ∀ c, p (w ++ [Sum.inl c]) * (if ∃ d, (Sum.inl c : C ⊕ T) = Sum.inl d ∧ t ∈ P.tok d then U w t (fun v => if v = z then (1:ℝ) else 0) else 0) * P.eta (z.length + 1 + 1) =
                             (p w * U w t (fun v => if v = z then (1:ℝ) else 0) / kfun P (t :: hz z)) * ((if P.tok c ⊆ (t :: hz z).toFinset then P.lam c else 0) - (if P.tok c ⊆ (hz z).toFinset then P.lam c else 0)) := by
                            intro c
                            rw [mul_right_comm, h6]
                            have ht : t ∉ hz z := hV'.2
                            by_cases htc : t ∈ P.tok c
                            · rw [if_pos (show ∃ d, (Sum.inl c : C ⊕ T) = Sum.inl d ∧ t ∈ P.tok d from ⟨c, rfl, htc⟩), if_neg (show ¬ P.tok c ⊆ (hz z).toFinset from fun h => ht (List.mem_toFinset.mp (h htc)))]
                              ring
                            · rw [if_neg (show ¬ ∃ d, (Sum.inl c : C ⊕ T) = Sum.inl d ∧ t ∈ P.tok d by rintro ⟨d, h, h'⟩; cases h; exact htc h')]
                              have : P.tok c ⊆ (t :: hz z).toFinset ↔ P.tok c ⊆ (hz z).toFinset := by
                                rw [List.toFinset_cons, Finset.subset_insert_iff_of_notMem htc]
                              simp only [this, sub_self, mul_zero]
                          rw [Finset.sum_congr rfl (fun c _ => h7 c), ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
                          unfold lamU
                          ring
                      · rw [if_neg hb]
                        refine Finset.sum_eq_zero fun a _ => ?_
                        rw [if_neg (fun h => hb h.2)]; simp
                  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_comm]
                  rw [← Finset.sum_mul] at IH
                  have het := heta (z.length + 1) (by omega)
                  have hst := p_step z b
                  have e8 : ∑ w ∈ L (z.length + 1), p w * (∑ t, U w t (fun v => if cmp t v ∧ ps t v = z then (1:ℝ) else 0)) * (rt (hz z) b / kfun P (hz z ++ hz [b])) = p (z ++ [b]) * lamU P (hz z).toFinset := by
                    rw [← Finset.sum_mul]
                    apply mul_right_cancel₀ het.ne'
                    rw [mul_right_comm, IH, mul_right_comm _ _ (P.eta _), hst]; ring
                  rw [← Finset.sum_mul] at e8
                  rw [e8]
                  rcases b with c | u
                  · rw [hzapp, hzl, List.append_nil]; simp
                  · rw [Finset.sum_eq_single u]
                    · simp only [if_true]
                      have hJ := Jl z u hV'.1 hV'.2
                      rw [← Finset.sum_mul] at hJ
                      have hk3 : kfun P (u :: hz z) = kfun P (hz z ++ [u]) := by
                        apply h2
                        · exact List.nodup_cons.mpr ⟨hV'.2, V_nodup _ hV'.1⟩
                        · exact (List.perm_append_singleton u _).symm
                      have e9 : ∑ w ∈ L (z.length + 1), p w * U w u (fun v => if v = z then (1:ℝ) else 0) * ((lamU P (u :: hz z).toFinset - lamU P (hz z).toFinset) / kfun P (u :: hz z)) = p (z ++ [Sum.inr u]) * (lamU P (u :: hz z).toFinset - lamU P (hz z).toFinset) := by
                        rw [← Finset.sum_mul]
                        apply mul_right_cancel₀ het.ne'
                        rw [mul_right_comm, hJ, mul_right_comm _ _ (P.eta _), hst, hzr, r2, hk3]; ring
                      rw [e9, hzapp, hzr, List.toFinset_eq_of_perm _ _ (List.perm_append_singleton u (hz z))]
                      ring
                    · intro t _ ht
                      refine Finset.sum_eq_zero fun w _ => ?_
                      rw [if_neg]
                      intro h; cases h; exact ht rfl
                    · simp


              have Il : ∀ z, V z → ∑ w ∈ L (z.length + 1), p w * (∑ t, U w t (fun v => if ps t v = z then (1:ℝ) else 0)) * P.eta (z.length + 1) = p z * lamTot P := by
                intro z hV
                have e1 : ∀ w t, U w t (fun v => if ps t v = z then (1:ℝ) else 0) = U w t (fun v => if cmp t v ∧ ps t v = z then (1:ℝ) else 0) + U w t (fun v => if ¬ cmp t v ∧ v = z then (1:ℝ) else 0) := by
                  intro w t
                  rw [← U_add]
                  congr 1; funext v
                  by_cases hc : cmp t v
                  · simp [hc]
                  · simp [hc, ps_no t v hc]
                have e2 : ∀ w t, p w * U w t (fun v => if ¬ cmp t v ∧ v = z then (1:ℝ) else 0) = if t ∈ hz z then 0 else p w * U w t (fun v => if v = z then (1:ℝ) else 0) := by
                  intro w t
                  split_ifs with h
                  · by_cases hVw : V w
                    · have : U w t (fun v => if ¬ cmp t v ∧ v = z then (1:ℝ) else 0) = 0 := by
                        refine Eq.trans ?_ (U_zero w t)
                        apply Uc
                        intro v hv _
                        rw [if_neg]
                        rintro ⟨_, rfl⟩
                        have := hv.nodup_iff.mpr (V_nodup w hVw)
                        rw [List.nodup_cons] at this
                        exact this.1 h
                      rw [this, mul_zero]
                    · rw [p_V w hVw, zero_mul]
                  · have := V_cmp z t hV h
                    congr 2; funext v
                    by_cases hv : v = z
                    · subst hv; simp [this]
                    · simp [hv]
                simp only [e1, Finset.sum_add_distrib, mul_add, add_mul]
                rw [Bl z hV]
                have e3 : ∑ w ∈ L (z.length + 1), p w * (∑ t, U w t (fun v => if ¬ cmp t v ∧ v = z then (1:ℝ) else 0)) * P.eta (z.length + 1) = ∑ t, p z * lamTok P (hz z).toFinset t := by
                  simp only [Finset.mul_sum, e2, Finset.sum_mul]
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun t _ => ?_
                  by_cases h : t ∈ hz z
                  · simp [h, lz]
                  · simp only [h, if_false]
                    exact Jl z t hV h
                rw [e3, ← Finset.mul_sum, ls]; ring


              have Fsum : ∀ (m : List (C ⊕ T) → ℝ) N, ∑ z ∈ L N, ∑ w ∈ L (N + 1), m w * (∑ t, U w t (fun v => if ps t v = z then (1:ℝ) else 0)) * P.eta (N + 1) = ∑ w ∈ L (N + 1), m w * kfun P (hz w) * P.eta (N + 1) := by
                intro m N
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun w hw => ?_
                rw [Lm] at hw
                rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_comm, ← U_one]
                congr 2
                refine Finset.sum_congr rfl fun t _ => ?_
                rw [← U_sum]
                apply Uc
                intro v _ hv
                rw [Finset.sum_ite_eq, if_pos]
                rw [Lm, ps_len]; omega


              have pF : ∀ N, ∑ w ∈ L (N + 1), p w * kfun P (hz w) * P.eta (N + 1) = lamTot P * ∑ w ∈ L N, p w := by
                intro N
                rw [LS, Finset.mul_sum]
                refine Finset.sum_congr rfl fun w hw => ?_
                rw [Lm] at hw
                rw [← rs (hz w), Finset.sum_mul]
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [mul_right_comm, ← hw, p_step, hzapp]
                by_cases hV : V (w ++ [a])
                · have := k_pos _ hV (by simp)
                  rw [hzapp] at this
                  field_simp
                · have h3 := p_step w a
                  rw [p_V _ hV, zero_mul] at h3
                  rw [← h3, zero_mul]
                  by_cases hw0 : p w = 0
                  · rw [hw0, mul_zero]
                  · have hVw : V w := by
                      by_contra h; exact hw0 (p_V w h)
                    have : rt (hz w) a = 0 := by
                      rcases a with c | t
                      · rw [r1, if_neg]; intro h
                        apply hV; rw [VS]; exact ⟨hVw, h⟩
                      · rw [r2]; apply lz
                        by_contra h
                        apply hV; rw [VS]; exact ⟨hVw, h⟩
                    rw [this, zero_mul]


              have uniq : ∀ (m0 : List (C ⊕ T) → ℝ), (∀ z, 0 ≤ m0 z) → (∀ z, ¬ V z → m0 z = 0) → Filter.Tendsto (fun N => ∑ z ∈ L N, m0 z) Filter.atTop (nhds 0) →
                  (m0 [] * lamTot P = ∑ w ∈ L 1, m0 w * (∑ t, U w t (fun v => if ps t v = [] then (1:ℝ) else 0)) * P.eta 1) →
                  (∀ z a, m0 (z ++ [a]) * (lamTot P + P.eta (z.length + 1) * kfun P (hz (z ++ [a]))) = m0 z * rt (hz z) a + ∑ w ∈ L (z.length + 1 + 1), m0 w * (∑ t, U w t (fun v => if ps t v = z ++ [a] then (1:ℝ) else 0)) * P.eta (z.length + 1 + 1)) →
                  ∀ z, m0 z = m0 [] * p z := by
                intro m0 hm0 hmV hten hb0 hbS
                have hc : 0 ≤ m0 [] := hm0 []
                have hlam0 : 0 ≤ lamTot P := Finset.sum_nonneg fun c _ => (hlam c).le
                obtain ⟨c, hcd⟩ : ∃ c, c = m0 [] := ⟨_, rfl⟩
                rw [← hcd]
                rw [← hcd] at hc
                obtain ⟨m, hm⟩ : ∃ m : List (C ⊕ T) → ℝ, ∀ z, m z = min (m0 z) (c * p z) := ⟨_, fun _ => rfl⟩
                have hmle0 : ∀ z, m z ≤ m0 z := fun z => by rw [hm]; exact min_le_left _ _
                have hmlep : ∀ z, m z ≤ c * p z := fun z => by rw [hm]; exact min_le_right _ _
                have hW : ∀ w t z, 0 ≤ U w t (fun v => if ps t v = z then (1:ℝ) else 0) := by
                  intro w t z
                  apply U_nonneg
                  intro v; dsimp only; split_ifs <;> norm_num
                have hWs : ∀ w z, 0 ≤ ∑ t, U w t (fun v => if ps t v = z then (1:ℝ) else 0) := fun w z => Finset.sum_nonneg fun t _ => hW w t z
                have hen : ∀ n : ℕ, 0 ≤ P.eta (n + 1) := fun n => (heta _ (by omega)).le
                have mono : ∀ (f g : List (C ⊕ T) → ℝ) N z, (∀ w, f w ≤ g w) → ∑ w ∈ L (N+1), f w * (∑ t, U w t (fun v => if ps t v = z then (1:ℝ) else 0)) * P.eta (N+1) ≤ ∑ w ∈ L (N+1), g w * (∑ t, U w t (fun v => if ps t v = z then (1:ℝ) else 0)) * P.eta (N+1) := by
                  intro f g N z hfg
                  refine Finset.sum_le_sum fun w _ => ?_
                  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hfg w) (hWs w z)) (hen N)
                -- balance for c * p
                have Icp : ∀ z, V z → ∑ w ∈ L (z.length + 1), (c * p w) * (∑ t, U w t (fun v => if ps t v = z then (1:ℝ) else 0)) * P.eta (z.length + 1) = c * p z * lamTot P := by
                  intro z hV
                  rw [mul_assoc, ← Il z hV, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun w _ => ?_
                  ring
                -- sub-balance for m
                have hs0 : ∑ w ∈ L 1, m w * (∑ t, U w t (fun v => if ps t v = [] then (1:ℝ) else 0)) * P.eta 1 ≤ m [] * lamTot P := by
                  have e0 : m [] = m0 [] := by rw [hm, p0, ← hcd]; simp
                  rw [e0, hb0]
                  exact mono m m0 0 [] hmle0
                have hsS : ∀ z a, m z * rt (hz z) a + ∑ w ∈ L (z.length + 1 + 1), m w * (∑ t, U w t (fun v => if ps t v = z ++ [a] then (1:ℝ) else 0)) * P.eta (z.length + 1 + 1) ≤ m (z ++ [a]) * (lamTot P + P.eta (z.length + 1) * kfun P (hz (z ++ [a]))) := by
                  intro z a
                  have hle : m z * rt (hz z) a + ∑ w ∈ L (z.length + 1 + 1), m w * (∑ t, U w t (fun v => if ps t v = z ++ [a] then (1:ℝ) else 0)) * P.eta (z.length + 1 + 1) ≤ m0 (z ++ [a]) * (lamTot P + P.eta (z.length + 1) * kfun P (hz (z ++ [a]))) := by
                    rw [hbS]
                    exact add_le_add (mul_le_mul_of_nonneg_right (hmle0 z) (rn _ _)) (mono m m0 _ _ hmle0)
                  by_cases hV : V (z ++ [a])
                  · have hle2 : m z * rt (hz z) a + ∑ w ∈ L (z.length + 1 + 1), m w * (∑ t, U w t (fun v => if ps t v = z ++ [a] then (1:ℝ) else 0)) * P.eta (z.length + 1 + 1) ≤ (c * p (z ++ [a])) * (lamTot P + P.eta (z.length + 1) * kfun P (hz (z ++ [a]))) := by
                      have i1 := Icp _ hV
                      have hlen : (z ++ [a]).length = z.length + 1 := by simp
                      rw [hlen] at i1
                      have i2 := mono m (fun z => c * p z) (z.length + 1) (z ++ [a]) hmlep
                      have i3 : (c * p (z ++ [a])) * (P.eta (z.length + 1) * kfun P (hz (z ++ [a]))) = c * p z * rt (hz z) a := by
                        have k := k_pos _ hV (by simp)
                        have := p_step z a
                        rw [← hzapp] at this
                        calc (c * p (z ++ [a])) * (P.eta (z.length + 1) * kfun P (hz (z ++ [a]))) = c * (p (z ++ [a]) * P.eta (z.length + 1)) * kfun P (hz (z ++ [a])) := by ring
                          _ = _ := by rw [this]; field_simp
                      rw [mul_add, i3, ← i1, add_comm]
                      exact add_le_add i2 (mul_le_mul_of_nonneg_right (hmlep z) (rn _ _))
                    rw [hm (z ++ [a])]
                    rcases min_choice (m0 (z ++ [a])) (c * p (z ++ [a])) with h | h
                    · rw [h]; exact hle
                    · rw [h]; exact hle2
                  · have e1 : m (z ++ [a]) = 0 := by rw [hm, hmV _ hV, p_V _ hV]; simp
                    rw [hmV _ hV] at hle
                    rw [e1]; exact hle
                -- flux notation
                obtain ⟨F, hF⟩ : ∃ F : (List (C ⊕ T) → ℝ) → ℕ → ℝ, ∀ f N, F f N = ∑ w ∈ L N, f w * kfun P (hz w) * P.eta N := ⟨_, fun _ _ => rfl⟩
                obtain ⟨M, hM⟩ : ∃ M : (List (C ⊕ T) → ℝ) → ℕ → ℝ, ∀ f N, M f N = ∑ w ∈ L N, f w := ⟨_, fun _ _ => rfl⟩
                have Fs0 : ∀ f, ∑ w ∈ L 1, f w * (∑ t, U w t (fun v => if ps t v = [] then (1:ℝ) else 0)) * P.eta 1 = F f 1 := by
                  intro f
                  have := Fsum f 0
                  rw [L0] at this
                  rw [hF, ← this]
                have FsS : ∀ f N, ∑ z ∈ L N, ∑ a, (f z * rt (hz z) a + ∑ w ∈ L (z.length + 1 + 1), f w * (∑ t, U w t (fun v => if ps t v = z ++ [a] then (1:ℝ) else 0)) * P.eta (z.length + 1 + 1)) = lamTot P * M f N + F f (N + 2) := by
                  intro f N
                  simp only [Finset.sum_add_distrib]
                  congr 1
                  · rw [hM, Finset.mul_sum]
                    refine Finset.sum_congr rfl fun z _ => ?_
                    rw [← Finset.mul_sum, rs, mul_comm]
                  · have := Fsum f (N + 1)
                    rw [LS] at this
                    rw [hF, ← this]
                    refine Finset.sum_congr rfl fun z hz' => ?_
                    rw [Lm] at hz'
                    rw [hz']
                have FsR : ∀ f N, ∑ z ∈ L N, ∑ a, f (z ++ [a]) * (lamTot P + P.eta (z.length + 1) * kfun P (hz (z ++ [a]))) = lamTot P * M f (N + 1) + F f (N + 1) := by
                  intro f N
                  rw [hM, hF, LS, LS, Finset.mul_sum, ← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun z hz' => ?_
                  rw [Lm] at hz'
                  rw [hz', Finset.mul_sum, ← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun a _ => ?_
                  ring
                have M0 : ∀ f, M f 0 = f [] := fun f => by rw [hM, L0]
                have cut0 : ∀ N, F m0 (N + 1) = lamTot P * M m0 N := by
                  intro N
                  induction N with
                  | zero => rw [M0, zero_add, ← Fs0, ← hb0, mul_comm]
                  | succ N ih =>
                    have e := FsR m0 N
                    simp only [hbS] at e
                    rw [FsS] at e
                    have e' : F m0 (N + 1 + 1) = F m0 (N + 2) := rfl
                    rw [e']; linarith
                have E0 : F m 1 ≤ lamTot P * M m 0 := by
                  rw [M0, ← Fs0, mul_comm (lamTot P)]; exact hs0
                have Emono : ∀ N, lamTot P * M m N - F m (N + 1) ≤ lamTot P * M m (N + 1) - F m (N + 1 + 1) := by
                  intro N
                  have e := FsR m N
                  have e2 := FsS m N
                  have : lamTot P * M m N + F m (N + 2) ≤ lamTot P * M m (N + 1) + F m (N + 1) := by
                    rw [← e, ← e2]
                    exact Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun a _ => hsS z a
                  have e' : F m (N + 1 + 1) = F m (N + 2) := rfl
                  rw [e']; linarith
                have Em : Monotone (fun N => lamTot P * M m N - F m (N + 1)) := monotone_nat_of_le_succ Emono
                have hm_nonneg : ∀ z, 0 ≤ m z := fun z => by rw [hm]; exact le_min (hm0 z) (mul_nonneg hc (p_nonneg z))
                have hF_nonneg : ∀ N, 0 ≤ F m (N + 1) := by
                  intro N
                  rw [hF]
                  exact Finset.sum_nonneg fun w _ => mul_nonneg (mul_nonneg (hm_nonneg w) (k_nonneg _)) (hen N)
                have cutm : ∀ N, F m (N + 1) = lamTot P * M m N := by
                  intro N
                  apply le_antisymm
                  · have := Em (Nat.zero_le N)
                    simp only [zero_add] at this
                    linarith
                  · have h3 : lamTot P * M m N - F m (N + 1) ≤ 0 := by
                      have ht2 : Filter.Tendsto (fun K => lamTot P * ∑ z ∈ L K, m0 z) Filter.atTop (nhds (lamTot P * 0)) := hten.const_mul _
                      rw [mul_zero] at ht2
                      refine ge_of_tendsto ht2 ?_
                      filter_upwards [Filter.eventually_ge_atTop N] with K hK
                      have i1 := Em hK
                      simp only at i1
                      have i2 := hF_nonneg K
                      have i3 : M m K ≤ ∑ z ∈ L K, m0 z := by
                        rw [hM]; exact Finset.sum_le_sum fun w _ => hmle0 w
                      have i4 := mul_le_mul_of_nonneg_left i3 hlam0
                      linarith
                    linarith
                have cutp : ∀ N, F (fun z => c * p z) (N + 1) = lamTot P * M (fun z => c * p z) N := by
                  intro N
                  have := pF N
                  rw [hF, hM, ← Finset.mul_sum, mul_left_comm, ← this, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun w _ => ?_
                  ring
                have main : ∀ N, ∀ z ∈ L N, m0 z = m z ∧ c * p z = m z := by
                  intro N
                  induction N with
                  | zero =>
                    intro z hz'
                    rw [Lm] at hz'
                    have : z = [] := List.length_eq_zero_iff.mp hz'
                    subst this
                    rw [hm, p0, ← hcd]; simp
                  | succ N ih =>
                    have a1 : M m0 N = M m N := by
                      rw [hM, hM]; exact Finset.sum_congr rfl fun z hz' => (ih z hz').1
                    have a2 : M (fun z => c * p z) N = M m N := by
                      rw [hM, hM]; exact Finset.sum_congr rfl fun z hz' => (ih z hz').2
                    have gen : ∀ f : List (C ⊕ T) → ℝ, (∀ z, m z ≤ f z) → (∀ z, ¬ V z → f z = 0) → F f (N + 1) = F m (N + 1) → ∀ z ∈ L (N + 1), f z = m z := by
                      intro f hf hfV hFf z hz'
                      by_cases hV : V z
                      · have h0 : ∑ w ∈ L (N + 1), (f w - m w) * kfun P (hz w) * P.eta (N + 1) = 0 := by
                          rw [hF, hF] at hFf
                          rw [← sub_eq_zero.mpr hFf, ← Finset.sum_sub_distrib]
                          refine Finset.sum_congr rfl fun w _ => ?_
                          ring
                        rw [Finset.sum_eq_zero_iff_of_nonneg] at h0
                        · have h3 := h0 z hz'
                          rw [Lm] at hz'
                          have k := k_pos z hV (by rintro rfl; simp at hz')
                          have e := heta (N + 1) (by omega)
                          have h4 : f z - m z = 0 := by
                            rcases mul_eq_zero.mp h3 with h3 | h3
                            · rcases mul_eq_zero.mp h3 with h3 | h3
                              · exact h3
                              · exact absurd h3 k.ne'
                            · exact absurd h3 e.ne'
                          linarith
                        · intro w _
                          exact mul_nonneg (mul_nonneg (sub_nonneg.mpr (hf w)) (k_nonneg _)) (hen N)
                      · rw [hfV z hV, hm, hmV z hV, p_V z hV]; simp
                    intro z hz'
                    refine ⟨gen m0 hmle0 hmV ?_ z hz', gen (fun z => c * p z) hmlep (fun z h => by simp [p_V z h]) ?_ z hz'⟩
                    · rw [cut0, cutm, a1]
                    · rw [cutp, cutm, a2]
                intro z
                obtain ⟨b1, b2⟩ := main z.length z (by rw [Lm])
                rw [b1, b2]


              obtain ⟨π, hπ⟩ : ∃ π : CState C T → List (C ⊕ T), ∀ y, π y = y.map (fun q => q.2.elim (Sum.inl q.1) Sum.inr) := ⟨_, fun _ => rfl⟩
              obtain ⟨Y, Ym, Y0, YS⟩ := gen_L (C × Option T)
              obtain ⟨Qb, hQb⟩ : ∃ Qb : List (C ⊕ T) → ℝ, ∀ z, Qb z = ∑ y ∈ Y z.length, if π y = z then Q y else 0 := ⟨_, fun _ => rfl⟩

              have hz_cl : ∀ c l, hz (Sum.inl c :: l) = hz l := by
                intro c l
                have := hzapp [Sum.inl c] l
                rw [hzl] at this; simpa using this


              have hz_cr : ∀ t l, hz (Sum.inr t :: l) = t :: hz l := by
                intro c l
                have := hzapp [Sum.inr c] l
                rw [hzr] at this; simpa using this


              have pi_app : ∀ a b, π (a ++ b) = π a ++ π b := by
                intro a b; rw [hπ, hπ, hπ, List.map_append]


              have pi_len : ∀ a, (π a).length = a.length := by
                intro a; rw [hπ, List.length_map]


              have hz_pi : ∀ y, hz (π y) = heldToks y := by
                intro y
                induction y with
                | nil => rw [hπ]; exact hznil
                | cons q y ih =>
                  rw [hπ] at ih ⊢
                  obtain ⟨c, o⟩ := q
                  rw [List.map_cons]
                  cases o with
                  | none =>
                    have : heldToks ((c, none) :: y) = heldToks y := rfl
                    rw [this, ← ih]; exact hz_cl _ _
                  | some t =>
                    have : heldToks ((c, some t) :: y) = t :: heldToks y := rfl
                    rw [this, ← ih]; exact hz_cr _ _


              have ps_pi : ∀ t y, π (passToken P t y) = ps t (π y) := by
                intro t y
                have hc : ∀ q y, π (q :: y) = (q.2.elim (Sum.inl q.1) Sum.inr) :: π y := by
                  intro q y; rw [hπ, hπ, List.map_cons]
                have hn : π [] = [] := by rw [hπ]; rfl
                induction y with
                | nil => rw [hn, ps0, passToken, hn]
                | cons q y ih =>
                  obtain ⟨c, o⟩ := q
                  cases o with
                  | none =>
                    rw [passToken, hc]
                    simp only [Option.elim]
                    rw [psl]
                    by_cases h : t ∈ P.tok c
                    · rw [if_pos h, if_pos h, hc]; rfl
                    · rw [if_neg h, if_neg h, hc, ih]; rfl
                  | some u =>
                    rw [passToken, hc, hc, ih]
                    simp only [Option.elim]
                    rw [psr]


              have V_pi : ∀ y, Valid P y → V (π y) := by
                intro y
                induction y using List.reverseRecOn with
                | nil =>
                  intro _
                  have hn : π [] = [] := by rw [hπ]; rfl
                  rw [hn, V0]; trivial
                | append_singleton y q ih =>
                  rintro ⟨v1, v2, v3⟩
                  have hy : Valid P y := by
                    refine ⟨?_, ?_, ?_⟩
                    · have : heldToks (y ++ [q]) = heldToks y ++ heldToks [q] := by
                        unfold heldToks; rw [List.filterMap_append]
                      rw [this] at v1
                      exact v1.of_append_left
                    · intro i hi t ht
                      have := v2 i (by simp; omega) t
                      rw [List.getElem_append_left hi] at this
                      exact this ht
                    · intro i hi ht
                      have := v3 i (by simp; omega)
                      rw [List.getElem_append_left hi, List.take_append_of_le_length hi.le] at this
                      exact this ht
                  obtain ⟨c, o⟩ := q
                  have e1 : π [(c, o)] = [o.elim (Sum.inl c) Sum.inr] := by rw [hπ]; rfl
                  rw [pi_app, e1, VS, hz_pi]
                  refine ⟨ih hy, ?_⟩
                  cases o with
                  | none =>
                    have := v3 y.length (by simp)
                    simp only [List.getElem_concat_length, List.take_left] at this
                    exact this trivial
                  | some t =>
                    have e : heldToks (y ++ [(c, some t)]) = heldToks y ++ [t] := by
                      unfold heldToks; rw [List.filterMap_append]; rfl
                    rw [e, (List.perm_append_singleton t _).nodup_iff, List.nodup_cons] at v1
                    exact v1.1


              have ct_sum : ∀ y (g : List (C ⊕ T) → ℝ), ((ctrans P y).map (fun e => e.2.2 * g (π e.1))).sum = ∑ a, rt (hz (π y)) a * g (π y ++ [a]) + (∑ t, U (π y) t (fun v => g (ps t v))) * P.eta y.length := by
                intro y g
                unfold ctrans
                simp only
                rw [List.map_append, List.sum_append]
                congr 1
                · rw [Fintype.sum_sum_type]
                  have e1 : ∀ (l : List C) (f : C → List (CState C T × Option ℕ × ℝ)), ((l.flatMap f).map (fun e => e.2.2 * g (π e.1))).sum = (l.map (fun c => ((f c).map (fun e => e.2.2 * g (π e.1))).sum)).sum := by
                    intro l f
                    induction l with
                    | nil => simp
                    | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]
                  rw [e1, Finset.sum_map_toList]
                  have e2 : ∀ c, ((if P.tok c ⊆ held y then [(y ++ [(c, (none : Option T))], (none : Option ℕ), P.lam c)]
                      else (P.tok c \ held y).toList.map fun t => (y ++ [(c, some t)], none, P.lam c * P.assign c (held y) t)).map (fun e => e.2.2 * g (π e.1))).sum =
                      rt (hz (π y)) (Sum.inl c) * g (π y ++ [Sum.inl c]) + ∑ t, P.lam c * P.assign c (held y) t * g (π y ++ [Sum.inr t]) := by
                    intro c
                    have eS : (hz (π y)).toFinset = held y := by rw [hz_pi]; rfl
                    rw [r1, eS]
                    by_cases h : P.tok c ⊆ held y
                    · rw [if_pos h, if_pos h, Finset.sum_eq_zero]
                      · have e3 : π [(c, (none : Option T))] = [Sum.inl c] := by rw [hπ]; rfl
                        simp [pi_app, e3]
                      · intro t _
                        rw [haz]
                        · simp
                        · rw [Finset.sdiff_eq_empty_iff_subset.mpr h]; simp
                    · rw [if_neg h, if_neg h, List.map_map, Finset.sum_map_toList, zero_mul, zero_add]
                      rw [← Finset.sum_subset (Finset.subset_univ (P.tok c \ held y))]
                      · refine Finset.sum_congr rfl fun t _ => ?_
                        have e3 : π [(c, some t)] = [Sum.inr t] := by rw [hπ]; rfl
                        simp [pi_app, e3]
                      · intro t _ ht
                        rw [haz _ _ _ ht]; simp
                  rw [Finset.sum_congr rfl (fun c _ => e2 c), Finset.sum_add_distrib]
                  congr 1
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun t _ => ?_
                  have eS : (hz (π y)).toFinset = held y := by rw [hz_pi]; rfl
                  rw [r2, eS, lamTok, Finset.sum_mul]
                · have e1 : ∀ (l : List (Fin y.length)) (f : Fin y.length → List (CState C T × Option ℕ × ℝ)), ((l.flatMap f).map (fun e => e.2.2 * g (π e.1))).sum = (l.map (fun c => ((f c).map (fun e => e.2.2 * g (π e.1))).sum)).sum := by
                    intro l f
                    induction l with
                    | nil => simp
                    | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]
                  rw [e1, ← Fin.sum_univ_def]
                  simp only [hU]
                  rw [Finset.sum_comm, Finset.sum_mul, pi_len, Finset.sum_range]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  have ei : y[(i:ℕ)]? = some (y.get i) := by simp
                  have eπ : (π y)[(i:ℕ)]? = some ((y.get i).2.elim (Sum.inl (y.get i).1) Sum.inr) := by
                    rw [hπ, List.getElem?_map, ei]; rfl
                  rw [eπ]
                  unfold depRate
                  rw [ei]
                  rcases hq : y.get i with ⟨c, o⟩
                  cases o with
                  | none => simp
                  | some t =>
                    simp only [Option.elim, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Option.some.injEq, Sum.inr.injEq]
                    rw [Finset.sum_ite_eq]
                    simp only [Finset.mem_univ, if_true]
                    have e5 : (π y).take (i + 1) = π (y.take (i + 1)) := by
                      rw [hπ, hπ, List.map_take]
                    have e6 : (π y).eraseIdx i = π (y.eraseIdx i) := by
                      rw [hπ, hπ, List.eraseIdx_map]
                    rw [e5, e6, hz_pi, ps_pi]; ring


              have crate_fin : ∀ y (S : Finset (CState C T)), ∑ y' ∈ S, crate P y y' = ((ctrans P y).map (fun e => if e.1 ∈ S then e.2.2 else 0)).sum := by
                intro y S
                unfold crate
                induction ctrans P y with
                | nil => simp
                | cons e l ih =>
                  rw [List.map_cons, List.sum_cons, ← ih]
                  have : ∀ y', (((e :: l).filter (fun e => e.1 = y')).map fun e => e.2.2).sum = (if e.1 = y' then e.2.2 else 0) + ((l.filter (fun e => e.1 = y')).map fun e => e.2.2).sum := by
                    intro y'
                    by_cases h : e.1 = y'
                    · rw [List.filter_cons_of_pos (by simpa using h)]; simp [h]
                    · rw [List.filter_cons_of_neg (by simpa using h)]; simp [h]
                  rw [Finset.sum_congr rfl (fun y' _ => this y'), Finset.sum_add_distrib, Finset.sum_ite_eq]


              have crate_tsum : ∀ y, ∑' y', crate P y y' = lamTot P + kfun P (hz (π y)) * P.eta y.length := by
                intro y
                rw [tsum_eq_sum (s := ((ctrans P y).map Prod.fst).toFinset)]
                · rw [crate_fin]
                  have := ct_sum y (fun _ => 1)
                  simp only [mul_one] at this
                  rw [rs, U_one] at this
                  rw [← this]
                  congr 1
                  apply List.map_congr_left
                  intro e he
                  rw [if_pos]
                  rw [List.mem_toFinset, List.mem_map]
                  exact ⟨e, he, rfl⟩
                · intro y' hy'
                  unfold crate
                  rw [List.filter_eq_nil_iff.mpr]
                  · simp
                  · intro e he h
                    apply hy'
                    rw [List.mem_toFinset, List.mem_map]
                    exact ⟨e, he, by simpa using h⟩


              have crate_fib : ∀ z y', ∑ y ∈ (Y z.length).filter (fun y => π y = z), crate P y' y = ∑ a, rt (hz (π y')) a * (if π y' ++ [a] = z then 1 else 0) + (∑ t, U (π y') t (fun v => if ps t v = z then 1 else 0)) * P.eta y'.length := by
                intro z y'
                rw [crate_fin, ← ct_sum y' (fun v => if v = z then 1 else 0)]
                congr 1
                apply List.map_congr_left
                intro e he
                simp only [Finset.mem_filter, Ym]
                by_cases h : π e.1 = z
                · rw [if_pos ⟨by rw [← h, pi_len], h⟩, if_pos h, mul_one]
                · rw [if_neg (fun h' => h h'.2), if_neg h, mul_zero]


              have Qb_sum : ∀ N (g : List (C ⊕ T) → ℝ), ∑ z ∈ L N, Qb z * g z = ∑ y ∈ Y N, Q y * g (π y) := by
                intro N g
                have : ∀ z ∈ L N, Qb z * g z = ∑ y ∈ Y N, if π y = z then Q y * g (π y) else 0 := by
                  intro z hz'
                  rw [Lm] at hz'
                  rw [hQb, hz', Finset.sum_mul]
                  refine Finset.sum_congr rfl fun y _ => ?_
                  split_ifs with h
                  · rw [h]
                  · simp
                rw [Finset.sum_congr rfl this, Finset.sum_comm]
                refine Finset.sum_congr rfl fun y hy => ?_
                rw [Ym] at hy
                rw [Finset.sum_ite_eq, if_pos]
                rw [Lm, pi_len, hy]


              have Qb_nonneg : ∀ z, 0 ≤ Qb z := by
                intro z
                rw [hQb]
                refine Finset.sum_nonneg fun y _ => ?_
                split_ifs
                · exact hQ.1 y
                · exact le_rfl


              have Qb_V : ∀ z, ¬ V z → Qb z = 0 := by
                intro z h
                rw [hQb]
                refine Finset.sum_eq_zero fun y _ => ?_
                split_ifs with h'
                · apply hQ.2.2.1
                  intro hv
                  apply h
                  rw [← h']; exact V_pi y hv
                · rfl


              have Qb_ten : Filter.Tendsto (fun N => ∑ z ∈ L N, Qb z) Filter.atTop (nhds 0) := by
                have e : ∀ N, ∑ z ∈ L N, Qb z = ∑ y ∈ Y N, Q y := by
                  intro N
                  have := Qb_sum N (fun _ => 1)
                  simpa using this
                simp only [e]
                have hsum : Summable Q := hQ.2.1.summable
                rw [Metric.tendsto_atTop]
                intro ε hε
                obtain ⟨s, hs'⟩ := summable_iff_vanishing_norm.mp hsum ε hε
                refine ⟨s.sup List.length + 1, fun N hN => ?_⟩
                rw [dist_zero_right]
                apply hs'
                rw [Finset.disjoint_left]
                intro y hy hy'
                rw [Ym] at hy
                have : y.length ≤ s.sup List.length := Finset.le_sup (f := List.length) hy'
                omega


              have Qb_bal : ∀ z, Qb z * (lamTot P + P.eta z.length * kfun P (hz z)) = ∑' y', Q y' * (∑ a, rt (hz (π y')) a * (if π y' ++ [a] = z then 1 else 0) + (∑ t, U (π y') t (fun v => if ps t v = z then 1 else 0)) * P.eta y'.length) := by
                intro z
                simp only [← crate_fib]
                simp only [Finset.mul_sum]
                rw [Summable.tsum_finsetSum]
                · rw [hQb, ← Finset.sum_filter, Finset.sum_mul]
                  refine Finset.sum_congr rfl fun y hy => ?_
                  rw [Finset.mem_filter, Ym] at hy
                  have := hQ.2.2.2.2.2 y
                  rw [← this, crate_tsum, hy.2, hy.1]; ring
                · intro y _
                  exact hQ.2.2.2.2.1 y


              have Dep_supp : ∀ z w, w.length ≠ z.length + 1 → ∑ t, U w t (fun v => if ps t v = z then (1:ℝ) else 0) = 0 := by
                intro z w h
                refine Finset.sum_eq_zero fun t _ => ?_
                refine Eq.trans ?_ (U_zero w t)
                apply Uc
                intro v _ hv
                rw [if_neg]
                rintro rfl
                rw [ps_len] at h
                exact h hv.symm


              have Qb0 : Qb [] * lamTot P = ∑ w ∈ L 1, Qb w * (∑ t, U w t (fun v => if ps t v = [] then (1:ℝ) else 0)) * P.eta 1 := by
                have := Qb_bal []
                have e0 : kfun P (hz []) = 0 := by rw [hznil]; simp [kfun]
                rw [e0, mul_zero, add_zero] at this
                rw [this, tsum_eq_sum (s := Y 1)]
                · simp only [mul_assoc]
                  rw [Qb_sum 1 (fun w => (∑ t, U w t (fun v => if ps t v = [] then (1:ℝ) else 0)) * P.eta 1)]
                  refine Finset.sum_congr rfl fun y hy => ?_
                  rw [Ym] at hy
                  rw [hy]; simp
                · intro y hy
                  rw [Ym] at hy
                  rw [Dep_supp [] (π y) (by rw [pi_len]; simpa using hy)]
                  simp


              have QbS : ∀ z a, Qb (z ++ [a]) * (lamTot P + P.eta (z.length + 1) * kfun P (hz (z ++ [a]))) = Qb z * rt (hz z) a + ∑ w ∈ L (z.length + 1 + 1), Qb w * (∑ t, U w t (fun v => if ps t v = z ++ [a] then (1:ℝ) else 0)) * P.eta (z.length + 1 + 1) := by
                intro z a
                have := Qb_bal (z ++ [a])
                have hlen : (z ++ [a]).length = z.length + 1 := by simp
                rw [hlen] at this
                rw [this]
                have hinj : ∀ (l : List (C ⊕ T)) x, (if l ++ [x] = z ++ [a] then (1:ℝ) else 0) = if x = a then (if l = z then 1 else 0) else 0 := by
                  intro l x
                  by_cases h : l ++ [x] = z ++ [a]
                  · have h' := List.append_inj' h rfl
                    simp only [List.cons.injEq, and_true] at h'
                    simp [h'.1, h'.2]
                  · rw [if_neg h]
                    split_ifs with h3 h4
                    · subst h3; subst h4; exact absurd rfl h
                    · rfl
                    · rfl
                have e1 : ∀ y, ∑ x, rt (hz (π y)) x * (if π y ++ [x] = z ++ [a] then (1:ℝ) else 0) = if π y = z then rt (hz z) a else 0 := by
                  intro y
                  simp only [hinj]
                  rw [Finset.sum_eq_single a]
                  · rw [if_pos rfl]
                    split_ifs with h
                    · rw [h]; simp
                    · simp
                  · intro b _ hb; rw [if_neg hb, mul_zero]
                  · simp
                simp only [e1]
                have hdis : Disjoint (Y z.length) (Y (z.length + 1 + 1)) := by
                  rw [Finset.disjoint_left]
                  intro y h3 h4
                  rw [Ym] at h3 h4
                  omega
                rw [tsum_eq_sum (s := Y z.length ∪ Y (z.length + 1 + 1)), Finset.sum_union hdis]
                · congr 1
                  · rw [hQb, Finset.sum_mul]
                    refine Finset.sum_congr rfl fun y hy => ?_
                    rw [Ym] at hy
                    rw [Dep_supp _ _ (by rw [pi_len, hlen]; omega)]
                    split_ifs <;> simp
                  · simp only [mul_assoc]
                    rw [Qb_sum (z.length + 1 + 1) (fun w => (∑ t, U w t (fun v => if ps t v = z ++ [a] then (1:ℝ) else 0)) * P.eta (z.length + 1 + 1))]
                    refine Finset.sum_congr rfl fun y hy => ?_
                    rw [Ym] at hy
                    rw [if_neg, hy, zero_add]
                    intro h
                    have := pi_len y
                    rw [h] at this; omega
                · intro y hy
                  rw [Finset.mem_union, not_or, Ym, Ym] at hy
                  rw [Dep_supp _ _ (by rw [pi_len, hlen]; omega), if_neg]
                  · simp
                  · intro h
                    have := pi_len y
                    rw [h] at this; exact hy.1 this.symm


              have Qb_eq : ∀ z, Qb z = Qb [] * p z := by
                exact uniq Qb Qb_nonneg Qb_V Qb_ten Qb0 QbS


              obtain ⟨W, Wm, W0, WS⟩ := gen_L C
              obtain ⟨bz, bz0, bzS⟩ := gen_rec (β := C ⊕ T) ([] : List (T × List C)) (fun b z a => Sum.elim (fun c => b.modifyLast (fun q => (q.1, q.2 ++ [c]))) (fun t => b ++ [(t, [])]) a)
              obtain ⟨dz, hdz⟩ : ∃ dz : List (C ⊕ T) → List (T × ℕ), ∀ z, dz z = (bz z).map (fun q => (q.1, q.2.length)) := ⟨_, fun _ => rfl⟩
              obtain ⟨H, hH⟩ : ∃ H : (ℕ → List C → ℝ) → List (T × List C) → ℝ, ∀ h b, H h b = ∏ j ∈ range b.length, h j ((b[j]?.map Prod.snd).getD []) := ⟨_, fun _ _ => rfl⟩
              obtain ⟨R, hR⟩ : ∃ R : List (T × ℕ) → (ℕ → List C → ℝ) → ℝ, ∀ x h, R x h = ∏ j ∈ range x.length, ∑ w ∈ W ((x[j]?.map Prod.snd).getD 0), (w.map (fun c => rt ((toks x).take (j + 1)) (Sum.inl c))).prod * h j w := ⟨_, fun _ _ => rfl⟩

              have bz_l : ∀ z c, bz (z ++ [Sum.inl c]) = (bz z).modifyLast (fun q => (q.1, q.2 ++ [c])) := by
                intro z c; rw [bzS]; rfl


              have bz_r : ∀ z t, bz (z ++ [Sum.inr t]) = bz z ++ [(t, [])] := by
                intro z c; rw [bzS]; rfl


              have bz_blocks : ∀ y, bz (π y) = (blocks y).map Prod.snd := by
                intro y
                induction y using List.reverseRecOn with
                | nil =>
                  have hn : π [] = [] := by rw [hπ]; rfl
                  rw [hn, bz0]; rfl
                | append_singleton y q ih =>
                  obtain ⟨c, o⟩ := q
                  have e1 : π [(c, o)] = [o.elim (Sum.inl c) Sum.inr] := by rw [hπ]; rfl
                  rw [pi_app, e1]
                  clear e1
                  have e2 : blocks (y ++ [(c, o)]) = (match o with
                    | none => (blocks y).modifyLast (fun b => (b.1, b.2.1, b.2.2 ++ [c]))
                    | some t => blocks y ++ [(c, t, [])]) := by
                    unfold blocks; rw [List.foldl_append]; cases o <;> rfl
                  rw [e2]
                  cases o with
                  | none =>
                    simp only [Option.elim]
                    rw [bz_l, ih]
                    rcases List.eq_nil_or_concat (blocks y) with h | ⟨l, b, h⟩
                    · rw [h]; rfl
                    · rw [List.concat_eq_append] at h
                      rw [h, List.map_append, List.map_singleton, List.modifyLast_concat, List.modifyLast_concat, List.map_append]; rfl
                  | some t =>
                    simp only [Option.elim]
                    rw [bz_r, ih, List.map_append]; rfl


              have dz_desc : ∀ y, dz (π y) = desc y := by
                intro y
                rw [hdz, bz_blocks, List.map_map]; rfl


              have bz_hz : ∀ z, (bz z).map Prod.fst = hz z := by
                intro z
                induction z using List.reverseRecOn with
                | nil => rw [bz0, hznil]; rfl
                | append_singleton z a ih =>
                  rcases a with c | t
                  · rw [bz_l, hzapp, hzl, List.append_nil, ← ih]
                    rcases List.eq_nil_or_concat (bz z) with h | ⟨l, b, h⟩
                    · rw [h]; rfl
                    · rw [List.concat_eq_append] at h
                      rw [h, List.modifyLast_concat, List.map_append, List.map_append]; rfl
                  · rw [bz_r, hzapp, hzr, List.map_append, ih]; rfl


              have dz_hz : ∀ z, toks (dz z) = hz z := by
                intro z
                rw [← bz_hz, hdz, toks, List.map_map]; rfl


              have phi_snoc : ∀ (x : List (T × ℕ)) t m, phi (x ++ [(t, m)]) = phi x + 1 + m := by
                intro x t m
                unfold phi
                simp; omega


              have dz_r : ∀ z t, dz (z ++ [Sum.inr t]) = dz z ++ [(t, 0)] := by
                intro z t
                rw [hdz, hdz, bz_r, List.map_append]; rfl


              have bz_l2 : ∀ z c l q, bz z = l ++ [q] → bz (z ++ [Sum.inl c]) = l ++ [(q.1, q.2 ++ [c])] := by
                intro z c l q h
                rw [bz_l, h, List.modifyLast_concat]


              have dz_len : ∀ z, V z → z.length = phi (dz z) := by
                intro z
                induction z using List.reverseRecOn with
                | nil => intro _; rw [hdz, bz0]; rfl
                | append_singleton z a ih =>
                  intro hV
                  have hV' := hV
                  rw [VS] at hV'
                  have ih := ih hV'.1
                  rcases a with c | t
                  · rcases List.eq_nil_or_concat (bz z) with h | ⟨l, b, h⟩
                    · exfalso
                      have := bz_hz z
                      rw [h] at this
                      have h3 : P.tok c ⊆ (hz z).toFinset := hV'.2
                      rw [← this] at h3
                      obtain ⟨t, ht⟩ := hne c
                      have := h3 ht
                      simp at this
                    · rw [List.concat_eq_append] at h
                      rw [hdz, h, List.map_append, List.map_singleton, phi_snoc] at ih
                      rw [hdz, bz_l2 z c l b h, List.map_append, List.map_singleton, phi_snoc]
                      simp only [List.length_append, List.length_singleton]
                      omega
                  · rw [dz_r, phi_snoc]; simp [ih]


              have H_nil : ∀ h, H h [] = 1 := by
                intro h; rw [hH]; simp


              have H_snoc : ∀ h b q, H h (b ++ [q]) = H h b * h b.length q.2 := by
                intro h b q
                rw [hH, hH, List.length_append, List.length_singleton, Finset.prod_range_succ]
                congr 1
                · refine Finset.prod_congr rfl fun j hj => ?_
                  rw [Finset.mem_range] at hj
                  rw [List.getElem?_append_left hj]
                · simp


              have R_snoc : ∀ h x t m, R (x ++ [(t, m)]) h = R x h * ∑ w ∈ W m, (w.map (fun c => rt (toks x ++ [t]) (Sum.inl c))).prod * h x.length w := by
                intro h x t m
                have e : toks (x ++ [(t, m)]) = toks x ++ [t] := by unfold toks; rw [List.map_append]; rfl
                have el : (toks x).length = x.length := by unfold toks; simp
                rw [hR, hR, List.length_append, List.length_singleton, Finset.prod_range_succ, e]
                congr 1
                · refine Finset.prod_congr rfl fun j hj => ?_
                  rw [Finset.mem_range] at hj
                  rw [List.getElem?_append_left hj, List.take_append_of_le_length (by omega)]
                · rw [List.take_of_length_le (by simp [el])]
                  simp


              have claim : ∀ x : List (T × ℕ), ∃ A : ℝ, ∀ h : ℕ → List C → ℝ, ∑ z ∈ L (phi x), (if dz z = x then p z * H h (bz z) else 0) = A * R x h := by
                have hinj : ∀ (l l' : List (T × ℕ)) x y, l ++ [x] = l' ++ [y] ↔ l = l' ∧ x = y := by
                  intro l l' x y
                  constructor
                  · intro h
                    have := List.append_inj' h rfl
                    simpa using this
                  · rintro ⟨rfl, rfl⟩; rfl
                have hml : ∀ f, List.modifyLast f ([] : List (T × List C)) = [] := fun f => rfl
                intro x
                induction x using List.reverseRecOn with
                | nil =>
                  refine ⟨1, fun h => ?_⟩
                  have e : phi ([] : List (T × ℕ)) = 0 := rfl
                  rw [e, L0, hdz, bz0, hR, p0, H_nil]; simp
                | append_singleton x tm ihx =>
                  obtain ⟨t, m⟩ := tm
                  induction m with
                  | zero =>
                    obtain ⟨A, hA⟩ := ihx
                    refine ⟨A * (lamTok P (toks x).toFinset t / (kfun P (toks x ++ [t]) * P.eta (phi x + 1))), fun h => ?_⟩
                    have key : ∀ z ∈ L (phi x), ∑ a, (if dz (z ++ [a]) = x ++ [(t, 0)] then p (z ++ [a]) * H h (bz (z ++ [a])) else 0) =
                        (if dz z = x then p z * H h (bz z) else 0) * ((lamTok P (toks x).toFinset t / (kfun P (toks x ++ [t]) * P.eta (phi x + 1))) * h x.length []) := by
                      intro z hz'
                      rw [Lm] at hz'
                      rw [Fintype.sum_sum_type]
                      have z1 : ∑ c : C, (if dz (z ++ [Sum.inl c]) = x ++ [(t, 0)] then p (z ++ [Sum.inl c]) * H h (bz (z ++ [Sum.inl c])) else 0) = 0 := by
                        refine Finset.sum_eq_zero fun c _ => ?_
                        rw [if_neg]
                        rcases List.eq_nil_or_concat (bz z) with hb | ⟨l, b, hb⟩
                        · rw [hdz, bz_l, hb, hml]
                          simp
                        · rw [List.concat_eq_append] at hb
                          rw [hdz, bz_l2 z c l b hb, List.map_append, List.map_singleton, hinj]
                          rintro ⟨_, h'⟩
                          simp at h'
                      rw [z1, zero_add, Finset.sum_eq_single t]
                      · by_cases hd : dz z = x
                        · rw [dz_r, if_pos (by rw [hd]), if_pos hd, bz_r, H_snoc, pS, r2, hzapp, hzr, ← dz_hz, hd, hz']
                          have : (bz z).length = x.length := by rw [← hd, hdz, List.length_map]
                          rw [this]; ring
                        · rw [dz_r, if_neg (fun h' => hd ((hinj _ _ _ _).mp h').1), if_neg hd, zero_mul]
                      · intro u _ hu
                        rw [dz_r, if_neg]
                        rw [hinj]
                        rintro ⟨_, h'⟩
                        simp at h'; exact hu h'
                      · simp
                    rw [phi_snoc, add_zero, LS, Finset.sum_congr rfl key, ← Finset.sum_mul, hA, R_snoc, W0]
                    simp only [List.map_nil, List.prod_nil, one_mul]
                    ring
                  | succ m ihm =>
                    obtain ⟨A, hA⟩ := ihm
                    refine ⟨A * (1 / (kfun P (toks x ++ [t]) * P.eta (phi x + 1 + m + 1))), fun h => ?_⟩
                    obtain ⟨h', hh'⟩ : ∃ h' : ℕ → List C → ℝ, ∀ j w, h' j w = if j = x.length then ∑ c, rt (toks x ++ [t]) (Sum.inl c) * h x.length (w ++ [c]) else h j w := ⟨_, fun _ _ => rfl⟩
                    have hA' := hA h'
                    have key : ∀ z ∈ L (phi x + 1 + m), ∑ a, (if dz (z ++ [a]) = x ++ [(t, m + 1)] then p (z ++ [a]) * H h (bz (z ++ [a])) else 0) =
                        (if dz z = x ++ [(t, m)] then p z * H h' (bz z) else 0) * (1 / (kfun P (toks x ++ [t]) * P.eta (phi x + 1 + m + 1))) := by
                      intro z hz'
                      rw [Lm] at hz'
                      rw [Fintype.sum_sum_type]
                      have z1 : ∑ u : T, (if dz (z ++ [Sum.inr u]) = x ++ [(t, m + 1)] then p (z ++ [Sum.inr u]) * H h (bz (z ++ [Sum.inr u])) else 0) = 0 := by
                        refine Finset.sum_eq_zero fun u _ => ?_
                        rw [dz_r, if_neg]
                        rw [hinj]
                        rintro ⟨_, h3⟩
                        simp at h3
                      rw [z1, add_zero]
                      rcases List.eq_nil_or_concat (bz z) with hb | ⟨l, b, hb⟩
                      · have hd : dz z = [] := by rw [hdz, hb]; rfl
                        rw [hd, if_neg (by simp), zero_mul]
                        refine Finset.sum_eq_zero fun c _ => ?_
                        rw [if_neg]
                        rw [hdz, bz_l, hb, hml]
                        simp
                      · rw [List.concat_eq_append] at hb
                        by_cases hd : dz z = x ++ [(t, m)]
                        · rw [if_pos hd]
                          have hd2 := hd
                          rw [hdz, hb, List.map_append, List.map_singleton, hinj] at hd2
                          have hll : l.length = x.length := by rw [← hd2.1, List.length_map]
                          have hb1 : b.1 = t := congrArg Prod.fst hd2.2
                          have hb2 : b.2.length = m := congrArg Prod.snd hd2.2
                          have htk : hz z = toks x ++ [t] := by
                            rw [← dz_hz, hd]; unfold toks; rw [List.map_append]; rfl
                          have hHH : H h' l = H h l := by
                            rw [hH, hH]
                            refine Finset.prod_congr rfl fun j hj => ?_
                            rw [Finset.mem_range, hll] at hj
                            rw [hh', if_neg hj.ne]
                          rw [hb, H_snoc, hHH, hll, hh', if_pos rfl, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
                          refine Finset.sum_congr rfl fun c _ => ?_
                          rw [hdz, bz_l2 z c l b hb, if_pos]
                          · rw [H_snoc, hll, pS, hzapp, hzl, List.append_nil, htk, hz']; ring
                          · rw [List.map_append, List.map_singleton, hinj]
                            refine ⟨hd2.1, ?_⟩
                            simp [hb1, hb2]
                        · rw [if_neg hd, zero_mul]
                          refine Finset.sum_eq_zero fun c _ => ?_
                          rw [if_neg]
                          intro h3
                          apply hd
                          rw [hdz, bz_l2 z c l b hb, List.map_append, List.map_singleton, hinj] at h3
                          rw [hdz, hb, List.map_append, List.map_singleton, hinj]
                          refine ⟨h3.1, ?_⟩
                          have h4 := h3.2
                          simp only [List.length_append, List.length_singleton, Prod.mk.injEq] at h4 ⊢
                          exact ⟨h4.1, by omega⟩
                    rw [phi_snoc] at hA'
                    rw [phi_snoc, ← add_assoc, LS, Finset.sum_congr rfl key, ← Finset.sum_mul, hA', R_snoc, R_snoc]
                    have hRR : R x h' = R x h := by
                      rw [hR, hR]
                      refine Finset.prod_congr rfl fun j hj => ?_
                      rw [Finset.mem_range] at hj
                      refine Finset.sum_congr rfl fun w _ => ?_
                      rw [hh', if_neg hj.ne]
                    have hW : ∑ w ∈ W m, (w.map (fun c => rt (toks x ++ [t]) (Sum.inl c))).prod * h' x.length w = ∑ w ∈ W (m + 1), (w.map (fun c => rt (toks x ++ [t]) (Sum.inl c))).prod * h x.length w := by
                      rw [WS]
                      refine Finset.sum_congr rfl fun w _ => ?_
                      rw [hh', if_pos rfl, Finset.mul_sum]
                      refine Finset.sum_congr rfl fun c _ => ?_
                      rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]; ring
                    rw [hRR, hW]; ring


              have word1 : ∀ (f : C → ℝ) m, ∑ w ∈ W m, (w.map f).prod = (∑ c, f c) ^ m := by
                intro f m
                induction m with
                | zero => rw [W0]; simp
                | succ m ih =>
                  rw [WS, pow_succ, ← ih, Finset.sum_mul]
                  refine Finset.sum_congr rfl fun w _ => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun c _ => ?_
                  rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]


              have word2 : ∀ (f : C → ℝ) m (n : C → ℕ), ∑ c, n c = m → ∑ w ∈ W m, (w.map f).prod * (if ∀ c, w.count c = n c then 1 else 0) = ((m.factorial : ℝ) / ∏ c, ((n c).factorial : ℝ)) * ∏ c, f c ^ n c := by
                intro f m
                induction m with
                | zero =>
                  intro n hn0
                  have h0 : ∀ c, n c = 0 := by
                    intro c
                    exact (Finset.sum_eq_zero_iff.mp hn0) c (Finset.mem_univ c)
                  rw [W0]; simp [h0]
                | succ m ih =>
                  intro n hnm
                  rw [WS, Finset.sum_comm]
                  have key : ∀ c, ∑ w ∈ W m, ((w ++ [c]).map f).prod * (if ∀ d, (w ++ [c]).count d = n d then (1:ℝ) else 0) = (n c : ℝ) * (((m.factorial : ℝ) / ∏ c, ((n c).factorial : ℝ)) * ∏ c, f c ^ n c) := by
                    intro c
                    by_cases h0 : n c = 0
                    · rw [h0, Nat.cast_zero, zero_mul]
                      refine Finset.sum_eq_zero fun w _ => ?_
                      rw [if_neg, mul_zero]
                      intro h3
                      have := h3 c
                      rw [h0, List.count_append] at this
                      simp at this
                    · obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero h0
                      have hs1 : ∑ d, Function.update n c k d = m := by
                        have e1 := Finset.sum_update_of_mem (Finset.mem_univ c) n k
                        have e2 := Finset.add_sum_erase Finset.univ n (Finset.mem_univ c)
                        rw [Finset.sdiff_singleton_eq_erase] at e1
                        omega
                      have hi := ih _ hs1
                      have e3 : ∀ w : List C, (∀ d, (w ++ [c]).count d = n d) ↔ (∀ d, w.count d = Function.update n c k d) := by
                        intro w
                        refine forall_congr' fun d => ?_
                        rw [List.count_append]
                        by_cases hd : d = c
                        · subst hd; simp [hk']
                        · have : List.count d [c] = 0 := by
                            rw [List.count_eq_zero]; simpa using hd
                          rw [this, Function.update_of_ne hd, add_zero]
                      have e4 : ∑ w ∈ W m, ((w ++ [c]).map f).prod * (if ∀ d, (w ++ [c]).count d = n d then (1:ℝ) else 0) = (∑ w ∈ W m, (w.map f).prod * (if ∀ d, w.count d = Function.update n c k d then (1:ℝ) else 0)) * f c := by
                        rw [Finset.sum_mul]
                        refine Finset.sum_congr rfl fun w _ => ?_
                        rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
                        simp only [e3 w]; ring
                      rw [e4, hi]
                      have p1 : ∏ d, ((Function.update n c k d).factorial : ℝ) = (k.factorial : ℝ) * ∏ d ∈ univ.erase c, ((n d).factorial : ℝ) := by
                        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Function.update_self]
                        congr 1
                        refine Finset.prod_congr rfl fun d hd => ?_
                        rw [Function.update_of_ne (Finset.ne_of_mem_erase hd)]
                      have p2 : ∏ d, f d ^ (Function.update n c k d) = f c ^ k * ∏ d ∈ univ.erase c, f d ^ n d := by
                        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Function.update_self]
                        congr 1
                        refine Finset.prod_congr rfl fun d hd => ?_
                        rw [Function.update_of_ne (Finset.ne_of_mem_erase hd)]
                      rw [p1, p2, ← Finset.mul_prod_erase univ (fun d => ((n d).factorial : ℝ)) (Finset.mem_univ c), ← Finset.mul_prod_erase univ (fun d => f d ^ n d) (Finset.mem_univ c)]
                      have q1 : (0:ℝ) < ∏ d ∈ univ.erase c, ((n d).factorial : ℝ) := Finset.prod_pos fun d _ => by positivity
                      have q2 : (0:ℝ) < (k.factorial : ℝ) := by positivity
                      rw [hk', Nat.succ_eq_add_one, Nat.factorial_succ, pow_succ]
                      push_cast
                      field_simp
                  rw [Finset.sum_congr rfl (fun c _ => key c), ← Finset.sum_mul, ← Nat.cast_sum, hnm, Nat.factorial_succ]
                  push_cast
                  ring


              have prQ : ∀ (E : CState C T → Prop) (g : List (C ⊕ T) → ℝ), (∀ y, (if E y then (1:ℝ) else 0) = g (π y)) → (∀ z, dz z ≠ x.1 → g z = 0) → prob Q E = Qb [] * ∑ z ∈ L (phi x.1), p z * g z := by
                intro E g hg hg0
                unfold prob
                have e1 : ∀ y, Set.indicator {y | E y} Q y = Q y * g (π y) := by
                  intro y
                  rw [← hg, Set.indicator_apply]
                  by_cases h : E y
                  · simp [h]
                  · simp [h]
                simp only [e1]
                rw [tsum_eq_sum (s := Y (phi x.1))]
                · rw [← Qb_sum, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun z _ => ?_
                  rw [Qb_eq z]; ring
                · intro y hy
                  by_cases hv : Valid P y
                  · rw [hg0, mul_zero]
                    intro hd
                    apply hy
                    rw [Ym, ← pi_len, dz_len _ (V_pi y hv), hd]
                  · rw [hQ.2.2.1 y hv, zero_mul]
              obtain ⟨A, hA⟩ := claim x.1
              obtain ⟨n', hn'⟩ : ∃ n' : ℕ → C → ℕ, ∀ j : Fin x.1.length, n' j = n j := by
                refine ⟨fun j c => if hj : j < x.1.length then n ⟨j, hj⟩ c else 0, fun j => ?_⟩
                funext c
                simp
              obtain ⟨h, hh⟩ : ∃ h : ℕ → List C → ℝ, ∀ j w, h j w = if ∀ c, w.count c = n' j c then 1 else 0 := ⟨_, fun _ _ => rfl⟩
              have hP1 : prob Q (fun y => desc y = x.1) = Qb [] * (A * R x.1 (fun _ _ => 1)) := by
                rw [prQ (fun y => desc y = x.1) (fun z => if dz z = x.1 then 1 else 0), ← hA]
                · congr 1
                  refine Finset.sum_congr rfl fun z _ => ?_
                  have : H (fun _ _ => 1) (bz z) = 1 := by rw [hH]; simp
                  rw [this]; split_ifs <;> simp
                · intro y
                  simp only [dz_desc]
                  split_ifs <;> rfl
                · intro z hzn; simp [hzn]
              have hP2 : prob Q (fun y => desc y = x.1 ∧ ∀ j : Fin x.1.length, ∀ c, Nseg y j c = n j c) = Qb [] * (A * R x.1 h) := by
                rw [prQ (fun y => desc y = x.1 ∧ ∀ j : Fin x.1.length, ∀ c, Nseg y j c = n j c) (fun z => if dz z = x.1 then H h (bz z) else 0), ← hA]
                · congr 1
                  refine Finset.sum_congr rfl fun z _ => ?_
                  split_ifs <;> simp
                · intro y
                  simp only [dz_desc]
                  by_cases hd : desc y = x.1
                  · rw [if_pos hd]
                    have hlen : (bz (π y)).length = x.1.length := by
                      rw [← hd, ← dz_desc, hdz, List.length_map]
                    have hNs : ∀ (j : ℕ) c, j < x.1.length → Nseg y j c = (((bz (π y))[j]?.map Prod.snd).getD []).count c := by
                      intro j c hj
                      rw [← hlen] at hj
                      rw [bz_blocks, List.length_map] at hj
                      unfold Nseg
                      rw [bz_blocks, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
                    rw [hH]
                    simp only [hh]
                    rw [Finset.prod_ite_zero, hlen]
                    simp only [Finset.prod_const_one]
                    have : (desc y = x.1 ∧ ∀ j : Fin x.1.length, ∀ c, Nseg y j c = n j c) ↔ (∀ i ∈ range x.1.length, ∀ c, (((bz (π y))[i]?.map Prod.snd).getD []).count c = n' i c) := by
                      constructor
                      · rintro ⟨_, h3⟩ i hi c
                        rw [Finset.mem_range] at hi
                        have := h3 ⟨i, hi⟩ c
                        rw [← hNs i c hi, this, ← hn']
                      · intro h3
                        refine ⟨hd, fun j c => ?_⟩
                        rw [hNs j c j.2, h3 j (Finset.mem_range.mpr j.2), hn']
                    by_cases h4 : (∀ i ∈ range x.1.length, ∀ c, (((bz (π y))[i]?.map Prod.snd).getD []).count c = n' i c)
                    · rw [if_pos h4, if_pos (this.mpr h4)]
                    · rw [if_neg h4, if_neg (fun h5 => h4 (this.mp h5))]
                  · rw [if_neg hd, if_neg (fun h5 => hd h5.1)]
                · intro z hzn; simp [hzn]
              rw [hP1, hP2, mul_assoc, mul_assoc]
              congr 2
              rw [hR, hR, Finset.prod_range, Finset.prod_range, ← Finset.prod_mul_distrib]
              refine Finset.prod_congr rfl fun j _ => ?_
              have ej : ((x.1[(j:ℕ)]?.map Prod.snd).getD 0) = (x.1.get j).2 := by simp
              rw [ej]
              simp only [hh, mul_one]
              obtain ⟨l, hl⟩ : ∃ l, l = (toks x.1).take (j + 1) := ⟨_, rfl⟩
              rw [← hl]
              have hnj := hn j
              rw [← hn'] at hnj ⊢
              rw [word2 (fun c => rt l (Sum.inl c)) _ _ hnj, word1]
              have hlU : ∑ c, rt l (Sum.inl c) = lamU P l.toFinset := by
                simp only [r1]
                rw [lamU, Finset.sum_filter]
              rw [hlU]
              have hth : ∀ c, theta P l c = rt l (Sum.inl c) / lamU P l.toFinset := by
                intro c
                rw [theta, r1]
                split_ifs <;> simp
              simp only [hth, div_pow]
              rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hnj]
              by_cases h0 : lamU P l.toFinset = 0
              · rw [h0]
                by_cases hm0 : (x.1.get j).2 = 0
                · rw [hm0]; simp
                · have : ∃ c, n' j c ≠ 0 := by
                    by_contra hcon
                    push Not at hcon
                    apply hm0
                    rw [← hnj]; exact Finset.sum_eq_zero fun c _ => hcon c
                  obtain ⟨c, hc⟩ := this
                  have hf0 : rt l (Sum.inl c) = 0 := by
                    rw [← hlU, Finset.sum_eq_zero_iff_of_nonneg (fun c _ => rn _ _)] at h0
                    exact h0 c (Finset.mem_univ c)
                  have : ∏ c, rt l (Sum.inl c) ^ n' j c = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ c)
                    rw [hf0, zero_pow hc]
                  rw [this]; simp
              · have : lamU P l.toFinset ^ (x.1.get j).2 ≠ 0 := pow_ne_zero _ h0
                field_simp
